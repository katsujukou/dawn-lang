-- | `translate`, over the handler slice.
-- |
-- | The slice is the effectful counterpart of the vertical slice: it performs an
-- | operation and interprets it twice over, once with a handler owning a region
-- | of cells. What each construct lowers to is written out in full, so that a
-- | difference from the Translation document is a defect in one of the two.
module Test.Stella.Compiler.MiddleEnd.Effects (spec) where

import Prelude

import Prim as P

-- Everything Mid IR offers is reached through the facade, which is what a
-- lowering imports. A member missing from its re-export list fails this module
-- rather than going unnoticed.
import Stella.Compiler.Primitive (PrimOp(..))
import Stella.Compiler.Interface (noImports)
import Stella.Compiler.MiddleEnd (Rep(..), TranslateError, translate)
import Stella.Compiler.MiddleEnd as M
import Stella.Compiler.TypedCore (Literal(..), Module, declare, declareAnnotated, primSignature)
import Stella.Compiler.TypedCore.Prim (unitCtor, unitTy)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Test.Stella.Compiler.TypedCore.HandlerSlice (always0Name, cellKey, counterEff, counterKey, counterName, handlerSlice, nextOp, seededSlice, twiceCountedName, twiceName)
import Test.Stella.Compiler.TypedCore.VerticalSlice (intModule)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | The slice, checked and translated. `Base.Int` stands behind it for the
-- | arithmetic, as it does behind the vertical slice.
translated :: Module P.Int -> Either P.String M.Module
translated m = case declare primSignature intModule of
  Left _ -> Left "Base.Int did not declare"
  Right s1 -> case declareAnnotated s1 m of
    Left _ -> Left "the slice did not declare"
    Right declared -> case translate noImports m declared of
      Left err -> Left (show (err :: TranslateError))
      Right result -> Right result.module

functionOf :: Module P.Int -> P.Int -> Either P.String M.Function
functionOf m i = do
  mid <- translated m
  case Array.find (\f -> f.id == M.FuncId i) mid.functions of
    Just f -> Right f
    Nothing -> Left ("no function #" <> show i)

-- | `Prim.Unit`, which every operation of the slice takes and which the fast
-- | clause's write produces.
unit' :: Rep
unit' = RepData unitTy

performNext :: M.Comp
performNext = M.CPerform counterKey nextOp (M.ACtor unitCtor)

-- | A handler owning the one cell of the slice, whose clause is `fast`. The
-- | slice installs two of these, which differ in the functions they name and in
-- | nothing else.
countingHandler :: P.Int -> P.Int -> M.Handler
countingHandler returnClause clause =
  { key: counterKey
  , cells: [ cellKey ]
  , returnClause: { func: M.FuncId returnClause, captures: [] }
  , opClauses:
      [ { op: nextOp
        , form: M.ClauseFast
        , clause: { func: M.FuncId clause, captures: [] }
        }
      ]
  }

-- | The handler of `always0`: one `full` clause, and no region at all.
always0Handler :: M.Handler
always0Handler =
  { key: counterKey
  , cells: []
  , returnClause: { func: M.FuncId 7, captures: [] }
  , opClauses:
      [ { op: nextOp, form: M.ClauseFull, clause: { func: M.FuncId 8, captures: [] } } ]
  }

spec :: Spec Unit
spec = describe "Stella.Compiler.MiddleEnd.Effects » the handler slice" do

  it "names each performed operation by its own name and its element's key" do
    -- nothing consults the ambient effect row, which is erased: a `perform`
    -- finds its handler by key, and the operation is looked up among the
    -- clauses of the one handler that key selected
    map _.body (functionOf handlerSlice 0) `shouldEqual` Right
      ( M.ELet (M.Local 1) RepInt performNext
          ( M.ELet (M.Local 2) RepInt performNext
              (M.ETail (M.CPrim IntAdd [ M.ALocal (M.Local 1), M.ALocal (M.Local 2) ]))
          )
      )

  it "carries the keys of a handler's region and nothing else of it" do
    -- the region variable and the cells' types were annotations the checker
    -- used; the keys pair with the initial values by position (D36)
    map _.body (functionOf handlerSlice 1) `shouldEqual` Right
      ( M.ETail
          ( M.CHandle (countingHandler 3 4) (M.FuncId 2)
              [ M.ALocal (M.Local 0) ]
              [ M.ALit (LitInt 0) ]
          )
      )

  it "lifts the handled computation into a function of no parameters" do
    -- it is entered from the `handle` rather than run where it was written, so
    -- what it names it captures
    functionOf handlerSlice 2 `shouldEqual` Right
      { id: M.FuncId 2
      , params: []
      , captures: [ { local: M.Local 0, rep: RepClos } ]
      , body: M.ETail (M.CCallUnknown (M.ALocal (M.Local 0)) [ M.ACtor unitCtor ])
      }

  it "gives a fast clause one parameter and builds no continuation" do
    -- a `fast` clause binds the operation's argument alone, so implementing one
    -- asks nothing of a backend beyond an ordinary call (D28)
    functionOf handlerSlice 4 `shouldEqual` Right
      { id: M.FuncId 4
      , params: [ { local: M.Local 0, rep: unit' } ]
      , captures: []
      , body:
          M.ELet (M.Local 1) RepInt (M.CReadCell cellKey)
            ( M.ELet (M.Local 2) RepInt
                (M.CPrim IntAdd [ M.ALocal (M.Local 1), M.ALit (LitInt 1) ])
                ( M.ELet (M.Local 3) unit' (M.CWriteCell cellKey (M.ALocal (M.Local 2)))
                    (M.ERet (M.ALocal (M.Local 1)))
                )
            )
      }

  it "gives a full clause the argument and the continuation" do
    -- the continuation is an ordinary value of `Rep Clos`, applied by an
    -- ordinary unknown call, and nothing bounds how often
    functionOf handlerSlice 8 `shouldEqual` Right
      { id: M.FuncId 8
      , params:
          [ { local: M.Local 0, rep: unit' }
          , { local: M.Local 1, rep: RepClos }
          ]
      , captures: []
      , body: M.ETail (M.CCallUnknown (M.ALocal (M.Local 1)) [ M.ALit (LitInt 0) ])
      }

  it "leaves a handler declaring no region with no cells and no initial values" do
    map _.body (functionOf handlerSlice 5) `shouldEqual` Right
      (M.ETail (M.CHandle always0Handler (M.FuncId 6) [ M.ALocal (M.Local 0) ] []))

  it "binds an initial value that is a computation ahead of the handle" do
    -- an initial value is evaluated before the region is opened and the handler
    -- installed, so its binding stands outside the `handle`
    map _.body (functionOf seededSlice 1) `shouldEqual` Right
      ( M.ELet (M.Local 1) RepInt
          (M.CPrim IntAdd [ M.ALit (LitInt 1), M.ALit (LitInt 2) ])
          ( M.ETail
              ( M.CHandle (countingHandler 3 4) (M.FuncId 2)
                  [ M.ALocal (M.Local 0) ]
                  [ M.ALocal (M.Local 1) ]
              )
          )
      )

  it "binds a handle whose value the rest of the body reads" do
    -- a `handle` is a computation, so a `let` binds it like any other and
    -- whatever consumes the value is reached in the ordinary way
    map _.body (functionOf handlerSlice 9) `shouldEqual` Right
      ( M.ELet (M.Local 1) RepInt
          (M.CHandle (countingHandler 11 12) (M.FuncId 10) [] [ M.ALit (LitInt 0) ])
          (M.ERet (M.ALocal (M.Local 1)))
      )

  it "records the operations each effect declares, and no signature" do
    -- an operation's argument and resume types were consumed by type checking
    map _.effects (translated handlerSlice) `shouldEqual` Right
      [ { ref: counterEff, ops: [ nextOp ] } ]

  it "installs every value of the slice as a function, each a handler or not" do
    map _.globals (translated handlerSlice) `shouldEqual` Right
      [ { ref: twiceName, init: M.GFunc (M.FuncId 0) }
      , { ref: counterName, init: M.GFunc (M.FuncId 1) }
      , { ref: always0Name, init: M.GFunc (M.FuncId 5) }
      , { ref: twiceCountedName, init: M.GFunc (M.FuncId 9) }
      ]
