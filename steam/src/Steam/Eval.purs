-- | Running a program
-- | ([Bytecode](../../../docs/technical-references/05-Backend/01-Bytecode.md),
-- | [Abstract Machine](../../../docs/technical-references/07-Runtime/01-Abstract-Machine.md)).
-- |
-- | The interpreter holds a **stack** of its own, and every entry of it says what
-- | it does with a value that reaches it. A call pushes a `Resume` carrying the
-- | activation and the register its value belongs in; a tail call pushes nothing,
-- | which is the whole of what makes it a tail call.
-- |
-- | **A branch is not a call.** `BRIF`, `BRC`, `BRL`, and `BRK` select a `Node` of
-- | the activation they stand in, and so does a `JMP` once it has written its
-- | arguments into the join point's registers.
-- |
-- | **A known call and an unknown call are different transfers.** `CALLK` and
-- | `TAILK` name a function entry whose arity is settled, so the closure a global
-- | slot holds is entered with exactly the arguments it takes and nothing about the
-- | call is resolved while it runs (D30). `CALLU` and `TAILU` are where under- and
-- | over-application are resolved: too few arguments build a partial application
-- | over the callee, whatever kind it is, and too many call it and apply the rest
-- | to what comes back. **Applying a continuation is an ordinary `CALLU`**, a
-- | continuation being a function value of one argument.
-- |
-- | A run reaches several modules: a closure names the module its function belongs
-- | to, and an activation runs against the tables of that module, so what resolves
-- | either is the registry.
module Steam.Eval
  ( Class(..)
  , Bug(..)
  , Failure(..)
  , EVAL
  , enter
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Foldable (traverse_)
import Data.Generic.Rep (class Generic)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Run (EFFECT, Run, liftEffect)
import Run.Except (EXCEPT)
import Run.Except as Except
import Steam.Module (CalleeTarget(..), CtorRef, GlobalSlot, Loaded, Prepared, Registry)
import Steam.Value (Activation, Callee(..), Closure, Continuation, CtorId, ForeignId, KeyId, ModuleId, StackEntry(..), Value(..), matchesConstant, reinstate, valueOfConstant)
import Stella.Compiler.Bytecode.Instr (CalleeIx(..), ConstIx(..), CtorIx(..), FuncIx(..), GlobalIx(..), Instr(..), Join, JoinName, KeyIx(..), Reg(..), Tail(..))
import Stella.Compiler.Bytecode.Module (Constant)
import Stella.Compiler.Primitive (PrimOp, arityOfOp)
import Type.Row (type (+))

-- | What an instruction expected of a register it read. The class of every value
-- | is settled before a `.dmo` exists, so a mismatch here is not a program's
-- | error but a defect above it.
data Class
  = ABoolean
  | AConstructorValue
  | ARecord
  | AVariant
  | AClosure
  | ACallable

-- | A state no `.dmo` admits. Reaching one is a defect in the interpreter, in
-- | lowering, or in a check a loader owes.
data Bug
  -- | A register or a capture slot read before anything was written into it.
  = RegisterHoldsNothing Reg
  | CaptureHoldsNothing P.Int
  -- | A global slot read before its module was initialized.
  | GlobalHoldsNothing GlobalIx
  -- | An index naming nothing in the table it stands in.
  | NoSuchConstant ConstIx
  | NoSuchKey KeyIx
  | NoSuchCtor CtorIx
  | NoSuchCallee CalleeIx
  | NoSuchGlobal GlobalIx
  | NoSuchFunction FuncIx
  | NoSuchJoin JoinName
  -- | A value of the wrong class in a register an instruction reads.
  | NotOfClass Class
  -- | A module the registry does not hold, which a closure or an activation
  -- | named.
  | NoSuchModule ModuleId
  -- | A closure built with a number of capture slots the function it runs does not
  -- | have, as the count declared and the count given.
  | WrongCaptureCount FuncIx P.Int P.Int
  -- | A capture slot outside what the closure has.
  | CaptureOutOfRange FuncIx P.Int
  -- | A capture slot filled twice. Each is filled once, where the group it belongs
  -- | to is built.
  | CaptureAlreadyFilled P.Int
  -- | A number of arguments the callee does not take, as the arity and the count.
  | WrongArgumentCount FuncIx P.Int P.Int
  | WrongCtorArity CtorId P.Int P.Int
  | WrongJumpArity JoinName P.Int P.Int
  -- | A partial application that is not partial, as the arity and the count.
  | PapNotBelowArity P.Int P.Int
  -- | An application supplying no argument, which nothing produces.
  | NoArgument
  -- | A field of a constructor value the constructor does not have.
  | NoSuchField CtorId P.Int
  -- | A `FIELD` whose constructor is not the one the value carries, which the
  -- | branch that selected it would have settled.
  | CtorMismatch CtorId CtorId
  -- | A key an operation found present where rows make it absent, or absent where
  -- | they make it present (D4).
  | KeyPresent KeyId
  | KeyAbsent KeyId
  -- | A dispatch none of whose cases matched, where it carries no default. A
  -- | dispatch whose cases exhaust needs none, and one whose cases do not was
  -- | given one.
  | NoBranchTaken
  -- | `VABS`, whose operand's type is uninhabited, so nothing reaches it.
  | Unreachable

-- | What ends a run before its value.
data Failure
  = Bug Bug
  -- | An instruction outside what this interpreter carries out, by its mnemonic.
  | Unimplemented P.String

-- | Running a program reads and writes references, and ends either in a value or
-- | in a failure.
type EVAL r = (EXCEPT Failure + EFFECT + r)

-- | The modules a run may reach, and the stack under whatever is running.
type Machine =
  { registry :: Registry
  , stack :: Ref (P.Array StackEntry)
  }

-- | Where a run stands: inside an activation, carrying a value to whatever takes
-- | it, or done.
data State
  = Running Activation
  | Returning Value
  | Finished Value

-- | What executing one instruction leaves the machine to do.
data Next
  = Advance
  -- | A call to a function whose entry and arity are both settled: the activation
  -- | to enter, with the register the value it produces belongs in. Nothing about
  -- | it is resolved at run time (D30).
  | Known Reg Activation
  -- | A call to a value: the callee and its arguments, with the register the value
  -- | belongs in. This is where under- and over-application are resolved.
  | Unknown Reg Value (P.Array Value)

-- Registers, captures, and tables -------------------------------------------------

readReg :: forall r. Activation -> Reg -> Run (EVAL r) Value
readReg activation reg = do
  regs <- liftEffect (Ref.read activation.regs)
  case Map.lookup reg regs of
    Just value -> pure value
    Nothing -> bug (RegisterHoldsNothing reg)

writeReg :: forall r. Activation -> Reg -> Value -> Run (EVAL r) Unit
writeReg activation reg value =
  liftEffect (Ref.modify_ (Map.insert reg value) activation.regs)

-- | A capture of the closure the activation was entered through. **Captures are
-- | not registers**, and a slot is filled where the closure is built.
readCapture :: forall r. Activation -> P.Int -> Run (EVAL r) Value
readCapture activation i = do
  captures <- liftEffect (Ref.read activation.closure.captures)
  case Map.lookup i captures of
    Just value -> pure value
    Nothing -> bug (CaptureHoldsNothing i)

constantAt :: forall r. Loaded -> ConstIx -> Run (EVAL r) Constant
constantAt loaded ix@(ConstIx i) = case Array.index loaded.constants i of
  Just constant -> pure constant
  Nothing -> bug (NoSuchConstant ix)

keyAt :: forall r. Loaded -> KeyIx -> Run (EVAL r) KeyId
keyAt loaded ix@(KeyIx i) = case Array.index loaded.keys i of
  Just key -> pure key
  Nothing -> bug (NoSuchKey ix)

ctorAt :: forall r. Loaded -> CtorIx -> Run (EVAL r) CtorRef
ctorAt loaded ix@(CtorIx i) = case Array.index loaded.ctors i of
  Just ctor -> pure ctor
  Nothing -> bug (NoSuchCtor ix)

calleeAt :: forall r. Loaded -> CalleeIx -> Run (EVAL r) CalleeTarget
calleeAt loaded ix@(CalleeIx i) = case Array.index loaded.callees i of
  Just callee -> pure callee
  Nothing -> bug (NoSuchCallee ix)

functionAt :: forall r. Loaded -> FuncIx -> Run (EVAL r) Prepared
functionAt loaded ix@(FuncIx i) = case Array.index loaded.functions i of
  Just function -> pure function
  Nothing -> bug (NoSuchFunction ix)

-- | What a global slot holds. A module's imports are initialized before it is and
-- | its own globals in declaration order, so nothing reads a slot still empty.
globalAt :: forall r. Loaded -> GlobalIx -> Run (EVAL r) Value
globalAt loaded ix@(GlobalIx i) = case Array.index loaded.globals i of
  Nothing -> bug (NoSuchGlobal ix)
  Just slot -> readSlot ix slot

readSlot :: forall r. GlobalIx -> GlobalSlot -> Run (EVAL r) Value
readSlot ix slot = do
  held <- liftEffect (Ref.read slot)
  case held of
    Just value -> pure value
    Nothing -> bug (GlobalHoldsNothing ix)

-- | The module a closure or an activation names.
loadedOf :: forall r. Machine -> ModuleId -> Run (EVAL r) Loaded
loadedOf machine moduleId = case Map.lookup moduleId machine.registry of
  Just loaded -> pure loaded
  Nothing -> bug (NoSuchModule moduleId)

-- | The join point a transfer names, from the table loading built. Nothing here
-- | searches the function's join points.
joinAt :: forall r. Prepared -> JoinName -> Run (EVAL r) Join
joinAt function name = case Map.lookup name function.joins of
  Just join -> pure join
  Nothing -> bug (NoSuchJoin name)

bug :: forall r a. Bug -> Run (EVAL r) a
bug = Except.throw <<< Bug

unimplemented :: forall r a. P.String -> Run (EVAL r) a
unimplemented = Except.throw <<< Unimplemented

-- The stack ------------------------------------------------------------------------

-- | The last entry is the top, so pushing appends and a segment is re-pushed in
-- | the order it stands.
push :: forall r. Machine -> StackEntry -> Run (EVAL r) Unit
push machine entry =
  liftEffect (Ref.modify_ (\stack -> Array.snoc stack entry) machine.stack)

pushAll :: forall r. Machine -> P.Array StackEntry -> Run (EVAL r) Unit
pushAll machine entries =
  liftEffect (Ref.modify_ (\stack -> stack <> entries) machine.stack)

pop :: forall r. Machine -> Run (EVAL r) (Maybe StackEntry)
pop machine = do
  stack <- liftEffect (Ref.read machine.stack)
  case Array.unsnoc stack of
    Just { init, last } -> do
      liftEffect (Ref.write init machine.stack)
      pure (Just last)
    Nothing -> pure Nothing

-- Entering and applying ------------------------------------------------------------

-- | Run a closure with its arguments to the value it returns.
-- |
-- | **The closure says which function runs**, so the code that runs and the
-- | captures `CAPT` reads cannot come from two different functions.
enter :: forall r. Registry -> Closure -> P.Array Value -> Run (EVAL r) Value
enter registry closure args = do
  stack <- liftEffect (Ref.new [])
  let machine = { registry, stack }
  activation <- activationOf machine closure args
  loop machine (Running activation)

loop :: forall r. Machine -> State -> Run (EVAL r) Value
loop machine state = case state of
  Finished value -> pure value
  _ -> step machine state >>= loop machine

-- | One step of the machine.
step :: forall r. Machine -> State -> Run (EVAL r) State
step machine = case _ of
  Finished value -> pure (Finished value)

  -- a value reaching the bottom of the stack is what the run produces
  Returning value -> do
    entry <- pop machine
    case entry of
      Nothing -> pure (Finished value)
      Just (Resume activation dest) -> do
        writeReg activation dest value
        pure (Running activation)
      Just (ApplyRemaining args) -> applyTo machine value args
      Just (HandlerMarker _) -> unimplemented "a handler marker"
      Just (RegionFrame _) -> unimplemented "a region frame"

  -- an activation runs against the tables of its own module, which is the one its
  -- function belongs to
  Running activation -> do
    loaded <- loadedOf machine activation.func.module
    case Array.index activation.node.code activation.ip of
      Just instruction -> do
        next <- exec machine loaded activation instruction
        case next of
          Advance -> pure (Running (resuming activation))
          -- the activation is suspended at the instruction after the call, which
          -- is where the value the call produces is written
          Known dest entered -> do
            push machine (Resume (resuming activation) dest)
            pure (Running entered)
          Unknown dest callee args -> do
            push machine (Resume (resuming activation) dest)
            applyTo machine callee args
      Nothing -> transfer machine loaded activation
  where
  resuming activation = activation { ip = activation.ip + 1 }

-- | Apply a value to arguments.
-- |
-- | Every application takes this path: a call instruction, the rest of an
-- | over-application, and a continuation alike.
applyTo :: forall r. Machine -> Value -> P.Array Value -> Run (EVAL r) State
applyTo machine callee args = case callee of
  VClos closure -> applyCallee machine (CalleeClosure closure) args
  -- the arguments a partial application holds stand before the ones it is given
  VPap pap -> applyCallee machine pap.callee (pap.args <> args)
  VCont continuation -> resume machine continuation args
  _ -> bug (NotOfClass ACallable)

-- | Apply a callee to arguments, whichever kind it is.
-- |
-- | **The count decides before the kind does.** Too few arguments build a partial
-- | application over that callee, whatever it is — a foreign and an operation
-- | included, neither of which is carried out until the last argument arrives. Too
-- | many call it with the arity it takes and leave the rest for what comes back.
applyCallee :: forall r. Machine -> Callee -> P.Array Value -> Run (EVAL r) State
applyCallee machine callee args = do
  resolved <- resolve machine callee
  let arity = arityOf resolved
  case compare (Array.length args) arity of
    LT -> pure (Returning (VPap { callee, args }))
    EQ -> saturated machine resolved args
    GT -> do
      push machine (ApplyRemaining (Array.drop arity args))
      saturated machine resolved (Array.take arity args)

-- | A callee with what applying it takes to hand: how many arguments it takes, and
-- | where it is a closure, the function entering it runs. The callee is resolved
-- | once, so a saturated application enters the body without looking it up again.
data Resolved
  = ResolvedClosure Closure Prepared
  | ResolvedCtor CtorId P.Int
  | ResolvedForeign ForeignId P.Int
  | ResolvedPrim PrimOp P.Int

resolve :: forall r. Machine -> Callee -> Run (EVAL r) Resolved
resolve machine = case _ of
  CalleeClosure closure -> map (ResolvedClosure closure) (functionOf machine closure)
  CalleeCtor ctor arity -> pure (ResolvedCtor ctor arity)
  CalleeForeign entry arity -> pure (ResolvedForeign entry arity)
  CalleePrim op -> pure (ResolvedPrim op (arityOfOp op))

arityOf :: Resolved -> P.Int
arityOf = case _ of
  ResolvedClosure _ function -> function.nparams
  ResolvedCtor _ arity -> arity
  ResolvedForeign _ arity -> arity
  ResolvedPrim _ arity -> arity

-- | Carry out a callee that has every argument it takes.
-- |
-- | **A closure is entered directly**: no partial application and no intermediate
-- | function value is built, and nothing stands between the call and the body. What
-- | entering does make is the activation and the registers it runs in, which a call
-- | needs of its own since the caller's are still live under it.
saturated :: forall r. Machine -> Resolved -> P.Array Value -> Run (EVAL r) State
saturated _ resolved args = case resolved of
  ResolvedClosure closure function -> map Running (activationIn closure function args)
  ResolvedCtor ctor _ -> pure (Returning (VData ctor args))
  ResolvedForeign _ _ -> unimplemented "a foreign"
  ResolvedPrim _ _ -> unimplemented "an operation"

-- | Apply a continuation, which takes one argument.
-- |
-- | The segment is re-pushed and the argument reaches its top, which is the
-- | activation that performed the operation. Arguments past the first are work
-- | pending on what the segment returns, so they stand below it.
resume :: forall r. Machine -> Continuation -> P.Array Value -> Run (EVAL r) State
resume machine continuation args = case Array.uncons args of
  Nothing -> bug NoArgument
  Just { head, tail: rest } -> do
    when (not (Array.null rest)) (push machine (ApplyRemaining rest))
    segment <- liftEffect (reinstate continuation)
    pushAll machine segment
    pure (Returning head)

-- | The function a closure runs.
functionOf :: forall r. Machine -> Closure -> Run (EVAL r) Prepared
functionOf machine closure = do
  loaded <- loadedOf machine closure.func.module
  functionAt loaded closure.func.func

-- | The activation entering a closure makes, resolving the function it runs.
activationOf :: forall r. Machine -> Closure -> P.Array Value -> Run (EVAL r) Activation
activationOf machine closure args = do
  function <- functionOf machine closure
  activationIn closure function args

-- | The same, where the function is already to hand. The arguments occupy the
-- | first `nparams` registers, which is where the function's code reads them.
activationIn :: forall r. Closure -> Prepared -> P.Array Value -> Run (EVAL r) Activation
activationIn closure function args = do
  let given = Array.length args
  when (given /= function.nparams)
    (bug (WrongArgumentCount closure.func.func function.nparams given))
  regs <- liftEffect (Ref.new (Map.fromFoldable (Array.mapWithIndex parameter args)))
  pure
    { func: closure.func
    , closure
    , regs
    , node: function.body
    , ip: 0
    }
  where
  parameter i value = Tuple (Reg i) value

-- Tails -----------------------------------------------------------------------------

-- | What ends the node an activation stands in.
transfer :: forall r. Machine -> Loaded -> Activation -> Run (EVAL r) State
transfer machine loaded activation = do
  function <- functionOf machine activation.closure
  case activation.node.tail of
    RET s -> map Returning (readReg activation s)

    BRIF s whenTrue whenFalse -> do
      value <- readReg activation s
      case value of
        VBoolean true -> pure (enters whenTrue)
        VBoolean false -> pure (enters whenFalse)
        _ -> bug (NotOfClass ABoolean)

    -- a constructor value carries the identity the loader resolved, so a dispatch
    -- here reaches values another module built
    BRC s cases fallback -> do
      value <- readReg activation s
      case value of
        VData ctor _ -> do
          selected <- traverse (\one -> map { ctor: _, body: one.body } (ctorAt loaded one.ctor)) cases
          branch (map _.body (Array.find (\one -> one.ctor.id == ctor) selected)) fallback
        _ -> bug (NotOfClass AConstructorValue)

    -- identity of a literal is equality of the value, a `Number`'s bit pattern
    -- deciding and all NaNs taken as one (D37)
    BRL s cases fallback -> do
      value <- readReg activation s
      selected <- traverse (\one -> map { lit: _, body: one.body } (constantAt loaded one.lit)) cases
      case Array.find (\one -> matchesConstant value one.lit) selected of
        Just one -> pure (enters one.body)
        Nothing -> pure (enters fallback)

    BRK s cases fallback -> do
      value <- readReg activation s
      case value of
        VVariant key _ -> do
          selected <- traverse (\one -> map { key: _, body: one.body } (keyAt loaded one.key)) cases
          branch (map _.body (Array.find (\one -> one.key == key) selected)) fallback
        _ -> bug (NotOfClass AVariant)

    -- the writes are a parallel move: every argument is read before any parameter
    -- is written, an argument register being a parameter of the join point it
    -- enters
    JMP name args -> do
      values <- traverse (readReg activation) args
      join <- joinAt function name
      let given = Array.length values
      when (given /= Array.length join.params)
        (bug (WrongJumpArity name (Array.length join.params) given))
      traverse_ (\(Tuple param value) -> writeReg activation param value)
        (Array.zip join.params values)
      pure (enters join.body)

    -- a tail call pushes nothing, so the value the callee returns reaches
    -- whatever this activation's own return would have reached
    TAILK global args -> do
      values <- traverse (readReg activation) args
      map Running (known machine loaded global values)

    TAILU s args -> do
      callee <- readReg activation s
      values <- traverse (readReg activation) args
      applyTo machine callee values

    TAILFFI _ _ -> unimplemented "TAILFFI"
    TAILHNDL _ _ _ _ _ -> unimplemented "TAILHNDL"
  where
  enters node = Running (activation { node = node, ip = 0 })

  branch selected fallback = case selected, fallback of
    Just body, _ -> pure (enters body)
    Nothing, Just body -> pure (enters body)
    Nothing, Nothing -> bug NoBranchTaken

-- Instructions -----------------------------------------------------------------------

exec :: forall r. Machine -> Loaded -> Activation -> Instr -> Run (EVAL r) Next
exec machine loaded activation = case _ of
  LOADK d ix -> do
    constant <- constantAt loaded ix
    advance (writeReg activation d (valueOfConstant constant))

  -- the constructor of a `LOADC` takes no fields, so the value is complete as it
  -- stands
  LOADC d ix -> do
    ctor <- ctorAt loaded ix
    when (ctor.arity /= 0) (bug (WrongCtorArity ctor.id ctor.arity 0))
    advance (writeReg activation d (VData ctor.id []))

  LOADG d ix -> do
    value <- globalAt loaded ix
    advance (writeReg activation d value)

  MOVE d s -> advance (readReg activation s >>= writeReg activation d)

  CAPT d i -> advance (readCapture activation i >>= writeReg activation d)

  -- the closure belongs to the module whose code builds it, and carries the
  -- capture slots that module's function declares
  CLOS d func captured -> do
    values <- traverse (readReg activation) captured
    expectCaptures loaded func (Array.length values)
    captures <- liftEffect (Ref.new (Map.fromFoldable (Array.mapWithIndex Tuple values)))
    advance (writeReg activation d (VClos { func: { module: loaded.id, func }, captures }))

  -- a recursive group allocates every member before any capture list is filled,
  -- which is what a guarded `letrec` needs (D14)
  CLOSN d func slots -> do
    expectCaptures loaded func slots
    captures <- liftEffect (Ref.new Map.empty)
    advance (writeReg activation d (VClos { func: { module: loaded.id, func }, captures }))

  -- a slot is filled once: what a group's members capture of each other is
  -- settled where the group is built
  SETCAP s i source -> do
    closure <- readClosure activation s
    function <- functionOf machine closure
    when (i < 0 || i >= function.ncaptures)
      (bug (CaptureOutOfRange closure.func.func i))
    value <- readReg activation source
    filled <- liftEffect (Ref.read closure.captures)
    when (Map.member i filled) (bug (CaptureAlreadyFilled i))
    advance (liftEffect (Ref.modify_ (Map.insert i value) closure.captures))

  PAP d ix args -> do
    target <- calleeAt loaded ix
    values <- traverse (readReg activation) args
    callee <- calleeOf target
    arity <- map arityOf (resolve machine callee)
    let given = Array.length values
    when (given >= arity) (bug (PapNotBelowArity arity given))
    advance (writeReg activation d (VPap { callee, args: values }))

  CTOR d ix args -> do
    ctor <- ctorAt loaded ix
    values <- traverse (readReg activation) args
    let given = Array.length values
    when (given /= ctor.arity) (bug (WrongCtorArity ctor.id ctor.arity given))
    advance (writeReg activation d (VData ctor.id values))

  -- a known call names a function entry whose arity is settled, so nothing about
  -- it is resolved here: the closure a slot holds is entered with exactly the
  -- arguments it takes (D30)
  CALLK d global args -> do
    values <- traverse (readReg activation) args
    map (Known d) (known machine loaded global values)

  CALLU d s args -> do
    callee <- readReg activation s
    values <- traverse (readReg activation) args
    pure (Unknown d callee values)

  FIELD d s ix i -> do
    ctor <- ctorAt loaded ix
    value <- readReg activation s
    case value of
      VData held fields
        | held /= ctor.id -> bug (CtorMismatch ctor.id held)
        | otherwise -> case Array.index fields i of
            Just field -> advance (writeReg activation d field)
            Nothing -> bug (NoSuchField ctor.id i)
      _ -> bug (NotOfClass AConstructorValue)

  RNEW d -> advance (writeReg activation d (VRecord Map.empty))

  -- a row is sharp, so the key an extension adds is absent from the record it
  -- extends (D4)
  REXT d ix sv sr -> do
    key <- keyAt loaded ix
    value <- readReg activation sv
    record <- readRecord activation sr
    when (Map.member key record) (bug (KeyPresent key))
    advance (writeReg activation d (VRecord (Map.insert key value record)))

  RSEL d ix s -> do
    key <- keyAt loaded ix
    record <- readRecord activation s
    case Map.lookup key record of
      Just value -> advance (writeReg activation d value)
      Nothing -> bug (KeyAbsent key)

  RRES d ix s -> do
    key <- keyAt loaded ix
    record <- readRecord activation s
    when (not (Map.member key record)) (bug (KeyAbsent key))
    advance (writeReg activation d (VRecord (Map.delete key record)))

  RUPD d ix sr sv -> do
    key <- keyAt loaded ix
    record <- readRecord activation sr
    value <- readReg activation sv
    when (not (Map.member key record)) (bug (KeyAbsent key))
    advance (writeReg activation d (VRecord (Map.insert key value record)))

  -- the two rows are disjoint, which is what makes one union of them
  RMRG d s1 s2 -> do
    left <- readRecord activation s1
    right <- readRecord activation s2
    case Array.find (\key -> Map.member key right) (Array.fromFoldable (Map.keys left)) of
      Just key -> bug (KeyPresent key)
      Nothing -> advance (writeReg activation d (VRecord (Map.union left right)))

  VINJ d ix s -> do
    key <- keyAt loaded ix
    value <- readReg activation s
    advance (writeReg activation d (VVariant key value))

  VPAY d ix s -> do
    key <- keyAt loaded ix
    value <- readReg activation s
    case value of
      VVariant held payload
        | held == key -> advance (writeReg activation d payload)
        | otherwise -> bug (KeyAbsent key)
      _ -> bug (NotOfClass AVariant)

  VABS _ _ -> bug Unreachable

  FFI _ _ _ -> unimplemented "FFI"
  PRIM _ _ _ -> unimplemented "PRIM"
  PERF _ _ _ _ -> unimplemented "PERF"
  HNDL _ _ _ _ _ _ -> unimplemented "HNDL"
  CGET _ _ -> unimplemented "CGET"
  CSET _ _ _ -> unimplemented "CSET"
  where
  advance = map (const Advance)

-- | The activation a known call enters. A global slot holds a closure, and the
-- | count of arguments is the arity that closure's function takes.
known :: forall r. Machine -> Loaded -> GlobalIx -> P.Array Value -> Run (EVAL r) Activation
known machine loaded global args = do
  value <- globalAt loaded global
  case value of
    VClos closure -> activationOf machine closure args
    _ -> bug (NotOfClass AClosure)

-- | That a closure carries the capture slots its function declares.
expectCaptures :: forall r. Loaded -> FuncIx -> P.Int -> Run (EVAL r) Unit
expectCaptures loaded func given = do
  function <- functionAt loaded func
  when (given /= function.ncaptures)
    (bug (WrongCaptureCount func function.ncaptures given))

-- | The callee a `CALLEES` entry stands for.
calleeOf :: forall r. CalleeTarget -> Run (EVAL r) Callee
calleeOf = case _ of
  TargetGlobal slot -> do
    held <- liftEffect (Ref.read slot)
    case held of
      Just (VClos closure) -> pure (CalleeClosure closure)
      _ -> bug (NotOfClass AClosure)
  TargetCtor ctor arity -> pure (CalleeCtor ctor arity)
  TargetForeign entry arity -> pure (CalleeForeign entry arity)
  TargetPrim op -> pure (CalleePrim op)

readRecord :: forall r. Activation -> Reg -> Run (EVAL r) (Map.Map KeyId Value)
readRecord activation reg = do
  value <- readReg activation reg
  case value of
    VRecord record -> pure record
    _ -> bug (NotOfClass ARecord)

readClosure :: forall r. Activation -> Reg -> Run (EVAL r) Closure
readClosure activation reg = do
  value <- readReg activation reg
  case value of
    VClos closure -> pure closure
    _ -> bug (NotOfClass AClosure)

derive instance Eq Class
derive instance Generic Class _

instance Show Class where
  show = genericShow

derive instance Eq Bug
derive instance Generic Bug _

instance Show Bug where
  show = genericShow

derive instance Eq Failure
derive instance Generic Failure _

instance Show Failure where
  show = genericShow
