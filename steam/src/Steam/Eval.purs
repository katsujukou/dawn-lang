-- | Running the instructions of one activation
-- | ([Bytecode](../../../docs/technical-references/05-Backend/01-Bytecode.md)).
-- |
-- | What is here is the part of a run that stays inside one activation: the
-- | instructions that read and write its registers, and the tails that select a
-- | `Node` of the same function. **A branch is not a call** — `BRIF`, `BRC`,
-- | `BRL`, and `BRK` continue in the activation they stand in, and so does a `JMP`
-- | once it has written its arguments into the join point's registers.
-- |
-- | A `Node` is a straight run of instructions ending in exactly one tail, and a
-- | branch holds its branches inline, which is what keeps a decision tree a tree.
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
import Effect.Ref as Ref
import Run (EFFECT, Run, liftEffect)
import Run.Except (EXCEPT)
import Run.Except as Except
import Steam.Module (CtorRef, Loaded, Prepared)
import Steam.Value (Activation, Closure, CtorId, KeyId, ModuleId, Value(..), matchesConstant, valueOfConstant)
import Stella.Compiler.Bytecode.Instr (ConstIx(..), CtorIx(..), FuncIx(..), Instr(..), Join, JoinName, KeyIx(..), Node, Reg(..), Tail(..))
import Stella.Compiler.Bytecode.Module (Constant)
import Type.Row (type (+))

-- | What an instruction expected of a register it read. The class of every value
-- | is settled before a `.dmo` exists, so a mismatch here is not a program's
-- | error but a defect above it.
data Class
  = ABoolean
  | AConstructorValue
  | ARecord
  | AVariant

-- | A state no `.dmo` admits. Reaching one is a defect in the interpreter, in
-- | lowering, or in a check a loader owes.
data Bug
  -- | A register or a capture slot read before anything was written into it.
  = RegisterHoldsNothing Reg
  | CaptureHoldsNothing P.Int
  -- | An index naming nothing in the table it stands in.
  | NoSuchConstant ConstIx
  | NoSuchKey KeyIx
  | NoSuchCtor CtorIx
  | NoSuchFunction FuncIx
  | NoSuchJoin JoinName
  -- | A value of the wrong class in a register an instruction reads.
  | NotOfClass Class
  -- | A closure naming a function of a module other than the one it is run
  -- | against, as the module it names and the module it reached.
  | ClosureOfAnotherModule ModuleId ModuleId
  -- | A number of arguments the callee does not take, as the arity and the count.
  | WrongArgumentCount FuncIx P.Int P.Int
  | WrongCtorArity CtorId P.Int P.Int
  | WrongJumpArity JoinName P.Int P.Int
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

-- | Running an activation reads and writes references, and ends either in a value
-- | or in a failure.
type EVAL r = (EXCEPT Failure + EFFECT + r)

-- Registers and tables ----------------------------------------------------------

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

functionAt :: forall r. Loaded -> FuncIx -> Run (EVAL r) Prepared
functionAt loaded ix@(FuncIx i) = case Array.index loaded.functions i of
  Just function -> pure function
  Nothing -> bug (NoSuchFunction ix)

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

-- Entering a function ------------------------------------------------------------

-- | Enter a closure with its arguments and run it to the value it returns.
-- |
-- | **The closure says which function runs**, so the code that runs and the
-- | captures `CAPT` reads cannot come from two different functions.
-- |
-- | The arguments occupy the first `nparams` registers, which is where the
-- | function's code reads them; a call that supplies any other number is one no
-- | lowering produces.
enter :: forall r. Loaded -> Closure -> P.Array Value -> Run (EVAL r) Value
enter loaded closure args = do
  when (closure.func.module /= loaded.id)
    (bug (ClosureOfAnotherModule closure.func.module loaded.id))
  function <- functionAt loaded ix
  let given = Array.length args
  when (given /= function.nparams)
    (bug (WrongArgumentCount ix function.nparams given))
  regs <- liftEffect (Ref.new (Map.fromFoldable (Array.mapWithIndex parameter args)))
  runNode loaded
    { func: closure.func
    , closure
    , regs
    , node: function.body
    , ip: 0
    }
    function
    function.body
  where
  ix = closure.func.func

  parameter i value = Tuple (Reg i) value

-- | Run a node to the value its tail produces.
runNode :: forall r. Loaded -> Activation -> Prepared -> Node -> Run (EVAL r) Value
runNode loaded activation function node = do
  traverse_ (exec loaded activation) node.code
  case node.tail of
    RET s -> readReg activation s

    BRIF s whenTrue whenFalse -> do
      value <- readReg activation s
      case value of
        VBoolean true -> again whenTrue
        VBoolean false -> again whenFalse
        _ -> bug (NotOfClass ABoolean)

    -- a constructor value carries the identity the loader resolved, so a
    -- dispatch here reaches values another module built
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
        Just one -> again one.body
        Nothing -> again fallback

    BRK s cases fallback -> do
      value <- readReg activation s
      case value of
        VVariant key _ -> do
          selected <- traverse (\one -> map { key: _, body: one.body } (keyAt loaded one.key)) cases
          branch (map _.body (Array.find (\one -> one.key == key) selected)) fallback
        _ -> bug (NotOfClass AVariant)

    -- the writes are a parallel move: every argument is read before any
    -- parameter is written, an argument register being a parameter of the join
    -- point it enters
    JMP name args -> do
      values <- traverse (readReg activation) args
      join <- joinAt function name
      let given = Array.length values
      when (given /= Array.length join.params)
        (bug (WrongJumpArity name (Array.length join.params) given))
      traverse_ (\(Tuple param value) -> writeReg activation param value)
        (Array.zip join.params values)
      again join.body

    TAILK _ _ -> unimplemented "TAILK"
    TAILU _ _ -> unimplemented "TAILU"
    TAILFFI _ _ -> unimplemented "TAILFFI"
    TAILHNDL _ _ _ _ _ -> unimplemented "TAILHNDL"
  where
  again = runNode loaded activation function

  branch selected fallback = case selected, fallback of
    Just body, _ -> again body
    Nothing, Just body -> again body
    Nothing, Nothing -> bug NoBranchTaken

-- Instructions -------------------------------------------------------------------

exec :: forall r. Loaded -> Activation -> Instr -> Run (EVAL r) Unit
exec loaded activation = case _ of
  LOADK d ix -> do
    constant <- constantAt loaded ix
    writeReg activation d (valueOfConstant constant)

  -- the constructor of a `LOADC` takes no fields, so the value is complete as
  -- it stands
  LOADC d ix -> do
    ctor <- ctorAt loaded ix
    when (ctor.arity /= 0) (bug (WrongCtorArity ctor.id ctor.arity 0))
    writeReg activation d (VData ctor.id [])

  MOVE d s -> readReg activation s >>= writeReg activation d

  CAPT d i -> readCapture activation i >>= writeReg activation d

  CTOR d ix args -> do
    ctor <- ctorAt loaded ix
    values <- traverse (readReg activation) args
    let given = Array.length values
    when (given /= ctor.arity) (bug (WrongCtorArity ctor.id ctor.arity given))
    writeReg activation d (VData ctor.id values)

  FIELD d s ix i -> do
    ctor <- ctorAt loaded ix
    value <- readReg activation s
    case value of
      VData held fields
        | held /= ctor.id -> bug (CtorMismatch ctor.id held)
        | otherwise -> case Array.index fields i of
            Just field -> writeReg activation d field
            Nothing -> bug (NoSuchField ctor.id i)
      _ -> bug (NotOfClass AConstructorValue)

  RNEW d -> writeReg activation d (VRecord Map.empty)

  -- a row is sharp, so the key an extension adds is absent from the record it
  -- extends (D4)
  REXT d ix sv sr -> do
    key <- keyAt loaded ix
    value <- readReg activation sv
    record <- readRecord activation sr
    when (Map.member key record) (bug (KeyPresent key))
    writeReg activation d (VRecord (Map.insert key value record))

  RSEL d ix s -> do
    key <- keyAt loaded ix
    record <- readRecord activation s
    case Map.lookup key record of
      Just value -> writeReg activation d value
      Nothing -> bug (KeyAbsent key)

  RRES d ix s -> do
    key <- keyAt loaded ix
    record <- readRecord activation s
    when (not (Map.member key record)) (bug (KeyAbsent key))
    writeReg activation d (VRecord (Map.delete key record))

  RUPD d ix sr sv -> do
    key <- keyAt loaded ix
    record <- readRecord activation sr
    value <- readReg activation sv
    when (not (Map.member key record)) (bug (KeyAbsent key))
    writeReg activation d (VRecord (Map.insert key value record))

  -- the two rows are disjoint, which is what makes one union of them
  RMRG d s1 s2 -> do
    left <- readRecord activation s1
    right <- readRecord activation s2
    case Array.find (\key -> Map.member key right) (Map.keys left # Array.fromFoldable) of
      Just key -> bug (KeyPresent key)
      Nothing -> writeReg activation d (VRecord (Map.union left right))

  VINJ d ix s -> do
    key <- keyAt loaded ix
    value <- readReg activation s
    writeReg activation d (VVariant key value)

  VPAY d ix s -> do
    key <- keyAt loaded ix
    value <- readReg activation s
    case value of
      VVariant held payload
        | held == key -> writeReg activation d payload
        | otherwise -> bug (KeyAbsent key)
      _ -> bug (NotOfClass AVariant)

  VABS _ _ -> bug Unreachable

  CLOS _ _ _ -> unimplemented "CLOS"
  CLOSN _ _ _ -> unimplemented "CLOSN"
  SETCAP _ _ _ -> unimplemented "SETCAP"
  PAP _ _ _ -> unimplemented "PAP"
  LOADG _ _ -> unimplemented "LOADG"
  CALLK _ _ _ -> unimplemented "CALLK"
  CALLU _ _ _ -> unimplemented "CALLU"
  FFI _ _ _ -> unimplemented "FFI"
  PRIM _ _ _ -> unimplemented "PRIM"
  PERF _ _ _ _ -> unimplemented "PERF"
  HNDL _ _ _ _ _ _ -> unimplemented "HNDL"
  CGET _ _ -> unimplemented "CGET"
  CSET _ _ _ -> unimplemented "CSET"

readRecord :: forall r. Activation -> Reg -> Run (EVAL r) (Map.Map KeyId Value)
readRecord activation reg = do
  value <- readReg activation reg
  case value of
    VRecord record -> pure record
    _ -> bug (NotOfClass ARecord)

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
