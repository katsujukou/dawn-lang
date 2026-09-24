-- | `HNDL`, `PERF`, and the cells of a region, written in bytecode by hand.
-- |
-- | The fixture stands for one effect of one operation. Two handlers of it are
-- | written: one whose clause is `fast` and reads and writes a cell, and one whose
-- | clause is `full` and holds the continuation.
-- |
-- | | Function | What it is |
-- | | --- | --- |
-- | | 0 | a body that performs the operation once and returns what comes back |
-- | | 1 | a body that performs it twice and returns the second value |
-- | | 2 | the return clause: it returns its argument |
-- | | 3 | a `fast` clause: it reads the cell, writes the argument, and returns what it read |
-- | | 4 | a `full` clause: it applies the continuation once |
-- | | 5 | a `full` clause: it applies the continuation twice and returns the second answer |
-- | | 6 | a `full` clause: it returns without resuming |
-- | | 7 | the return clause of the counting handler: it reads the cell |
-- |
-- | The callers after those install one of the two handlers over one of the bodies.
module Test.Steam.Handlers (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Run (runBaseEffect)
import Run.Except as Except
import Steam.Eval (Bug(..), Failure(..), enter)
import Steam.Module (Loaded, Registry, prepare)
import Steam.Value (Closure, CtorId(..), KeyId(..), ModuleId(..), OpId(..), Value(..))
import Stella.Compiler.Bytecode.Instr (ConstIx(..), FuncIx(..), Function, HandlerIx(..), Instr(..), KeyIx(..), Node, OpIx(..), PrimIx(..), Reg(..), Tail(..))
import Stella.Compiler.Primitive (PrimOp(..))
import Stella.Compiler.Bytecode.Module (Constant(..))
import Stella.Compiler.MiddleEnd.IR (ClauseForm(..))
import Stella.Compiler.MiddleEnd.Rep (Rep(..))
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- The fixture ----------------------------------------------------------------------

-- | The key of the effect, and the key of the one cell a region opens.
effectKey :: KeyId
effectKey = KeyId 10

cellKey :: KeyId
cellKey = KeyId 11

-- | The key of a second effect, which one handler of the fixture does not answer.
otherKey :: KeyId
otherKey = KeyId 12

nextOp :: OpId
nextOp = OpId 20

-- | The operation of that second effect.
stopOp :: OpId
stopOp = OpId 21

returning :: P.Array Instr -> Reg -> Node
returning code reg = { code, tail: RET reg }

fn :: { nparams :: P.Int, nregs :: P.Int, ncaptures :: P.Int } -> Node -> Function
fn counts body =
  { nparams: counts.nparams
  , regs: Array.replicate counts.nregs RepVal
  , captures: Array.replicate counts.ncaptures RepVal
  , joins: []
  , body
  }

plain :: P.Int -> Node -> Function
plain nregs = fn { nparams: 0, nregs, ncaptures: 0 }

functions :: P.Array Function
functions =
  -- 0: perform once, return what the operation gave
  [ plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , PERF (Reg 1) (KeyIx 0) (OpIx 0) (Reg 0)
          ]
          (Reg 1)
      )

  -- 1: perform twice, return the second value
  , plain 3
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , PERF (Reg 1) (KeyIx 0) (OpIx 0) (Reg 0)
          , PERF (Reg 2) (KeyIx 0) (OpIx 0) (Reg 0)
          ]
          (Reg 2)
      )

  -- 2: a return clause that hands back what reached it
  , fn { nparams: 1, nregs: 1, ncaptures: 0 } (returning [] (Reg 0))

  -- 3: a `fast` clause: what it returns is what the cell held, and the cell takes
  -- the operation's argument
  , fn { nparams: 1, nregs: 3, ncaptures: 0 }
      ( returning
          [ CGET (Reg 1) (KeyIx 1)
          , CSET (Reg 2) (KeyIx 1) (Reg 0)
          ]
          (Reg 1)
      )

  -- 4: a `full` clause: the argument, then the continuation applied to it once
  , fn { nparams: 2, nregs: 3, ncaptures: 0 }
      (returning [ CALLU (Reg 2) (Reg 1) [ Reg 0 ] ] (Reg 2))

  -- 5: a `full` clause applying the continuation twice, with a different value each
  -- time, and returning the two answers added: what each application produced is
  -- what the body computed from the value that application resumed with
  , fn { nparams: 2, nregs: 6, ncaptures: 0 }
      ( returning
          [ CALLU (Reg 2) (Reg 1) [ Reg 0 ]
          , LOADK (Reg 3) (ConstIx 2)
          , CALLU (Reg 4) (Reg 1) [ Reg 3 ]
          , PRIM (Reg 5) (PrimIx 0) [ Reg 2, Reg 4 ]
          ]
          (Reg 5)
      )

  -- 6: a `full` clause that never resumes
  , fn { nparams: 2, nregs: 3, ncaptures: 0 }
      (returning [ LOADK (Reg 2) (ConstIx 2) ] (Reg 2))

  -- 7: the counting handler's return clause: the answer is what the cell holds
  , fn { nparams: 1, nregs: 2, ncaptures: 0 }
      (returning [ CGET (Reg 1) (KeyIx 1) ] (Reg 1))

  -- 8: the counting handler over the body that performs twice
  , plain 5
      ( returning
          [ CLOS (Reg 0) (FuncIx 1) []
          , CLOS (Reg 1) (FuncIx 7) []
          , CLOS (Reg 2) (FuncIx 3) []
          , LOADK (Reg 3) (ConstIx 1)
          , HNDL (Reg 4) (HandlerIx 0) (Reg 0) (Reg 1) [ Reg 2 ] [ Reg 3 ]
          ]
          (Reg 4)
      )

  -- 9: the same handler, with the return clause that hands the body's value back
  , plain 5
      ( returning
          [ CLOS (Reg 0) (FuncIx 1) []
          , CLOS (Reg 1) (FuncIx 2) []
          , CLOS (Reg 2) (FuncIx 3) []
          , LOADK (Reg 3) (ConstIx 1)
          , HNDL (Reg 4) (HandlerIx 0) (Reg 0) (Reg 1) [ Reg 2 ] [ Reg 3 ]
          ]
          (Reg 4)
      )

  -- 10: a handler whose clause is `full` and resumes once, over the body that
  -- performs once
  , plain 4
      ( returning
          [ CLOS (Reg 0) (FuncIx 0) []
          , CLOS (Reg 1) (FuncIx 2) []
          , CLOS (Reg 2) (FuncIx 4) []
          , HNDL (Reg 3) (HandlerIx 1) (Reg 0) (Reg 1) [ Reg 2 ] []
          ]
          (Reg 3)
      )

  -- 11: the same with the clause that resumes twice
  , plain 4
      ( returning
          [ CLOS (Reg 0) (FuncIx 0) []
          , CLOS (Reg 1) (FuncIx 2) []
          , CLOS (Reg 2) (FuncIx 5) []
          , HNDL (Reg 3) (HandlerIx 1) (Reg 0) (Reg 1) [ Reg 2 ] []
          ]
          (Reg 3)
      )

  -- 12: the same with the clause that never resumes
  , plain 4
      ( returning
          [ CLOS (Reg 0) (FuncIx 0) []
          , CLOS (Reg 1) (FuncIx 2) []
          , CLOS (Reg 2) (FuncIx 6) []
          , HNDL (Reg 3) (HandlerIx 1) (Reg 0) (Reg 1) [ Reg 2 ] []
          ]
          (Reg 3)
      )

  -- 13: the counting handler installed in tail position
  , plain 4
      { code:
          [ CLOS (Reg 0) (FuncIx 1) []
          , CLOS (Reg 1) (FuncIx 7) []
          , CLOS (Reg 2) (FuncIx 3) []
          , LOADK (Reg 3) (ConstIx 1)
          ]
      , tail: TAILHNDL (HandlerIx 0) (Reg 0) (Reg 1) [ Reg 2 ] [ Reg 3 ]
      }

  -- 14: a `perform` with no handler of its key installed
  , plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , PERF (Reg 1) (KeyIx 0) (OpIx 0) (Reg 0)
          ]
          (Reg 1)
      )

  -- 15: the counting handler over a body that performs nothing, so the region
  -- closes before the return clause reads it
  , plain 5
      ( returning
          [ CLOS (Reg 0) (FuncIx 16) []
          , CLOS (Reg 1) (FuncIx 7) []
          , CLOS (Reg 2) (FuncIx 3) []
          , LOADK (Reg 3) (ConstIx 1)
          , HNDL (Reg 4) (HandlerIx 0) (Reg 0) (Reg 1) [ Reg 2 ] [ Reg 3 ]
          ]
          (Reg 4)
      )

  -- 16: a body that performs nothing
  , plain 1 (returning [ LOADK (Reg 0) (ConstIx 2) ] (Reg 0))

  -- 17: a `full` clause of a handler owning a region: it resumes, writes the cell,
  -- resumes again, and adds what the two applications produced
  , fn { nparams: 2, nregs: 7, ncaptures: 0 }
      ( returning
          [ CALLU (Reg 2) (Reg 1) [ Reg 0 ]
          , LOADK (Reg 3) (ConstIx 2)
          , CSET (Reg 4) (KeyIx 1) (Reg 3)
          , CALLU (Reg 5) (Reg 1) [ Reg 0 ]
          , PRIM (Reg 6) (PrimIx 0) [ Reg 2, Reg 5 ]
          ]
          (Reg 6)
      )

  -- 18: that handler over the body that performs once, the cell starting at 5
  , plain 5
      ( returning
          [ CLOS (Reg 0) (FuncIx 0) []
          , CLOS (Reg 1) (FuncIx 7) []
          , CLOS (Reg 2) (FuncIx 17) []
          , LOADK (Reg 3) (ConstIx 3)
          , HNDL (Reg 4) (HandlerIx 2) (Reg 0) (Reg 1) [ Reg 2 ] [ Reg 3 ]
          ]
          (Reg 4)
      )

  -- 19: a body that installs the counting handler over the performing body, so two
  -- markers of one key stand on the stack at once
  , plain 5
      ( returning
          [ CLOS (Reg 0) (FuncIx 0) []
          , CLOS (Reg 1) (FuncIx 2) []
          , CLOS (Reg 2) (FuncIx 3) []
          , LOADK (Reg 3) (ConstIx 1)
          , HNDL (Reg 4) (HandlerIx 0) (Reg 0) (Reg 1) [ Reg 2 ] [ Reg 3 ]
          ]
          (Reg 4)
      )

  -- 20: the `full` handler that answers 9 without resuming, installed over that
  -- body: the inner handler is the one that answers, so this one never hears of it
  , plain 4
      ( returning
          [ CLOS (Reg 0) (FuncIx 19) []
          , CLOS (Reg 1) (FuncIx 2) []
          , CLOS (Reg 2) (FuncIx 6) []
          , HNDL (Reg 3) (HandlerIx 1) (Reg 0) (Reg 1) [ Reg 2 ] []
          ]
          (Reg 3)
      )

  -- 21: a body performing the operation of the second effect
  , plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , PERF (Reg 1) (KeyIx 2) (OpIx 1) (Reg 0)
          ]
          (Reg 1)
      )

  -- 22: a body installing the counting handler, which answers the first effect, over
  -- a body performing the second
  , plain 5
      ( returning
          [ CLOS (Reg 0) (FuncIx 21) []
          , CLOS (Reg 1) (FuncIx 2) []
          , CLOS (Reg 2) (FuncIx 3) []
          , LOADK (Reg 3) (ConstIx 1)
          , HNDL (Reg 4) (HandlerIx 0) (Reg 0) (Reg 1) [ Reg 2 ] [ Reg 3 ]
          ]
          (Reg 4)
      )

  -- 23: a handler of the second effect over that, which is where the operation the
  -- inner handler does not answer arrives
  , plain 4
      ( returning
          [ CLOS (Reg 0) (FuncIx 22) []
          , CLOS (Reg 1) (FuncIx 2) []
          , CLOS (Reg 2) (FuncIx 6) []
          , HNDL (Reg 3) (HandlerIx 3) (Reg 0) (Reg 1) [ Reg 2 ] []
          ]
          (Reg 3)
      )
  ]

-- | The module, with the two handlers its code installs.
-- |
-- | | Handler | What it is |
-- | | --- | --- |
-- | | 0 | one `fast` clause, owning a region of one cell |
-- | | 1 | one `full` clause, owning no region |
-- | | 2 | one `full` clause, owning a region of one cell |
-- | | 3 | one `full` clause of the second effect, owning no region |
loaded :: Loaded
loaded =
  { id: ModuleId 0
  , constants: [ CInt 1, CInt 0, CInt 9, CInt 5 ]
  , keys: [ effectKey, cellKey, otherKey ]
  , ops: [ nextOp, stopOp ]
  , ctors: []
  , foreigns: []
  , globals: []
  , callees: []
  , prims: [ IntAdd ]
  , handlers:
      [ { key: effectKey
        , cells: [ cellKey ]
        , opClauses: [ { op: nextOp, form: ClauseFast } ]
        }
      , { key: effectKey
        , cells: []
        , opClauses: [ { op: nextOp, form: ClauseFull } ]
        }
      , { key: effectKey
        , cells: [ cellKey ]
        , opClauses: [ { op: nextOp, form: ClauseFull } ]
        }
      , { key: otherKey
        , cells: []
        , opClauses: [ { op: stopOp, form: ClauseFull } ]
        }
      ]
  , unit: VData (CtorId 999) []
  , functions: Array.mapMaybe prepared functions
  }
  where
  prepared function = case prepare function of
    Right p -> Just p
    Left _ -> Nothing

registry :: Registry
registry = Map.fromFoldable [ Tuple (ModuleId 0) loaded ]

closureOf :: P.Int -> Effect Closure
closureOf i = do
  captures <- Ref.new Map.empty
  pure { func: { module: ModuleId 0, func: FuncIx i }, captures }

runs :: P.Int -> Aff (Either Failure Value)
runs i = liftEffect do
  closure <- closureOf i
  runBaseEffect (Except.runExcept (enter registry closure []))

-- | What a run produced, as far as a test needs it.
data Held
  = AnInt P.Int
  | Elsewhere

held :: Either Failure Value -> Either Failure Held
held = map case _ of
  VInt n -> AnInt n
  _ -> Elsewhere

spec :: Spec Unit
spec = describe "Steam.Handlers" do

  describe "a fast clause and a region of cells" do
    it "returns what the cell held, and the write is seen by the next perform" do
      -- the body performs twice with the argument 1; the cell starts at 0, so the
      -- first perform gives 0 and the second gives 1
      result <- runs 9
      held result `shouldEqual` Right (AnInt 1)

    it "closes the region before the return clause runs" do
      -- the return clause of function 7 reads the cell, and by then the owner has
      -- closed the region
      result <- runs 8
      held result `shouldEqual` Left (Bug (NoCellDeclared cellKey))

    it "closes it the same way where the handler is installed in tail position" do
      result <- runs 13
      held result `shouldEqual` Left (Bug (NoCellDeclared cellKey))

    it "closes it where the body performs nothing" do
      result <- runs 15
      held result `shouldEqual` Left (Bug (NoCellDeclared cellKey))

  describe "a full clause" do
    it "resumes the computation the perform was in" do
      -- the clause applies the continuation to the operation's argument, so the
      -- body's `perform` gives 1 and the body returns it
      result <- runs 10
      held result `shouldEqual` Right (AnInt 1)

    it "resumes it as often as it applies the continuation, each from the capture" do
      -- the clause resumes with 1 and then with 9, and adds what the two
      -- applications produced: each ran the body from where the `perform` stood
      -- (D33)
      result <- runs 11
      held result `shouldEqual` Right (AnInt 10)

    it "may answer without resuming at all" do
      result <- runs 12
      held result `shouldEqual` Right (AnInt 9)

  describe "a full clause of a handler owning a region" do
    it "reaches the one frame from every application of its continuation" do
      -- the frame stayed behind when the segment was split, so it stands outside
      -- what either application carries: the clause writes 9 into the cell between
      -- the two resumptions, and the return clause each resumption reaches reads the
      -- cell — 5 the first time and 9 the second (D36)
      result <- runs 18
      held result `shouldEqual` Right (AnInt 14)

  describe "handlers that nest" do
    it "answers at the innermost marker of the key" do
      -- two markers of one key stand on the stack. The counting handler is the inner
      -- one, and its `fast` clause answers with what its cell held, which is 0; had
      -- the outer `full` clause answered, the run would have produced its 9
      result <- runs 20
      held result `shouldEqual` Right (AnInt 0)

    it "carries an operation the inner handler does not answer to the outer one" do
      -- the inner handler answers the first effect and the body performs the second,
      -- so the marker that answers is the outer one, which returns 9 without
      -- resuming
      result <- runs 23
      held result `shouldEqual` Right (AnInt 9)

  describe "what no .dmo admits" do
    it "a perform with no handler of its key installed" do
      -- effect safety rules this out: a handler of the key encloses every `perform`
      -- of it
      result <- runs 14
      held result `shouldEqual` Left (Bug (NoHandlerInstalled effectKey))

derive instance Eq Held

instance Show Held where
  show = case _ of
    AnInt n -> "AnInt " <> show n
    Elsewhere -> "Elsewhere"
