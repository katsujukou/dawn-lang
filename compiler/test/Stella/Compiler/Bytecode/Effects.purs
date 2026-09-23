-- | `lower`, over the handler slice.
-- |
-- | The slice is carried through checking, translation, and lowering, and what
-- | comes out is written down in full: a difference from the Bytecode document
-- | is a defect in one of the two.
module Test.Stella.Compiler.Bytecode.Effects (spec) where

import Prelude

import Prim as P

-- Everything the bytecode offers is reached through the facade, which is what a
-- machine imports. A member missing from its re-export list fails this module
-- rather than going unnoticed.
import Stella.Compiler.Bytecode (ConstIx(..), CtorIx(..), Dmo, FuncIx(..), Function, HandlerEntry, HandlerIx(..), Instr(..), Key(..), KeyIx(..), LowerError, OpIx(..), PrimIx(..), Reg(..), Tail(..), lower)
import Stella.Compiler.MidIR (ClauseForm(..), Rep(..), translate)
import Stella.Compiler.TypedCore (Module, Symbol(..), declare, declareAnnotated, primSignature)
import Stella.Compiler.TypedCore.Prim (unitTy)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Test.Stella.Compiler.TypedCore.HandlerSlice (counterEff, handlerSlice, nextOp)
import Test.Stella.Compiler.TypedCore.VerticalSlice (intModule)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

lowered :: Module P.Int -> Either P.String Dmo
lowered m = case declare primSignature intModule of
  Left _ -> Left "Base.Int did not declare"
  Right s1 -> case declareAnnotated s1 m of
    Left _ -> Left "the slice did not declare"
    Right declared -> case translate m declared of
      Left err -> Left (show err)
      Right mid -> case lower mid of
        Left err -> Left (show (err :: LowerError))
        Right out -> Right out.dmo

functionOf :: P.Int -> Either P.String Function
functionOf i = do
  dmo <- lowered handlerSlice
  case Array.index dmo.functions i of
    Just f -> Right f
    Nothing -> Left ("no function #" <> show i)

-- | `Prim.Unit`, which every operation of the slice takes and which a write
-- | produces.
unit' :: Rep
unit' = RepData unitTy

-- | The entry of a handler owning the one cell of the slice. Two of them are
-- | installed and both reach this entry: the closures and the initial values are
-- | supplied in registers, so nothing here tells the two sites apart.
countingEntry :: HandlerEntry
countingEntry =
  { key: KeyIx 0
  , cells: [ KeyIx 1 ]
  , opClauses: [ { op: OpIx 0, form: ClauseFast } ]
  }

spec :: Spec Unit
spec = describe "Stella.Compiler.Bytecode.Effects » the handler slice" do

  it "performs an operation by the key of its element and its own name" do
    -- `PERF` is not a `Tail`: where the clause is `fast`, control returns to the
    -- instruction after it with the clause's value in the destination
    map _.body (functionOf 0) `shouldEqual` Right
      { code:
          [ LOADC (Reg 3) (CtorIx 0)
          , PERF (Reg 1) (KeyIx 0) (OpIx 0) (Reg 3)
          , LOADC (Reg 4) (CtorIx 0)
          , PERF (Reg 2) (KeyIx 0) (OpIx 0) (Reg 4)
          , PRIM (Reg 5) (PrimIx 0) [ Reg 1, Reg 2 ]
          ]
      , tail: RET (Reg 5)
      }

  it "installs a handler in tail position, its region's value beside its clauses" do
    -- every closure the instruction takes is built by an ordinary `CLOS`, and
    -- the last vector is the initial value of each cell of the region
    map _.body (functionOf 1) `shouldEqual` Right
      { code:
          [ CLOS (Reg 1) (FuncIx 2) [ Reg 0 ]
          , CLOS (Reg 2) (FuncIx 3) []
          , CLOS (Reg 3) (FuncIx 4) []
          , LOADK (Reg 4) (ConstIx 0)
          ]
      , tail: TAILHNDL (HandlerIx 0) (Reg 1) (Reg 2) [ Reg 3 ] [ Reg 4 ]
      }

  it "carries a Rep per register of that function, the closures' among them" do
    map _.regs (functionOf 1) `shouldEqual` Right
      [ RepClos, RepClos, RepClos, RepClos, RepInt ]

  it "reads and writes a cell by its key, the write producing no value of its own" do
    -- `CGET` and `CSET` find the innermost frame declaring the key, as `PERF`
    -- finds the innermost marker of one; a write's destination takes `Prim.Unit`
    map _.body (functionOf 4) `shouldEqual` Right
      { code:
          [ CGET (Reg 1) (KeyIx 1)
          , LOADK (Reg 4) (ConstIx 1)
          , PRIM (Reg 2) (PrimIx 0) [ Reg 1, Reg 4 ]
          , CSET (Reg 3) (KeyIx 1) (Reg 2)
          ]
      , tail: RET (Reg 1)
      }
    map _.regs (functionOf 4) `shouldEqual` Right
      [ unit', RepInt, RepInt, unit', RepInt ]

  it "supplies no initial value where the handler declares no region" do
    map _.body (functionOf 5) `shouldEqual` Right
      { code:
          [ CLOS (Reg 1) (FuncIx 6) [ Reg 0 ]
          , CLOS (Reg 2) (FuncIx 7) []
          , CLOS (Reg 3) (FuncIx 8) []
          ]
      , tail: TAILHNDL (HandlerIx 1) (Reg 1) (Reg 2) [ Reg 3 ] []
      }

  it "installs a handler whose value is consumed as an ordinary instruction" do
    -- the marker stands between the calling activation and the body's, so what
    -- the return clause gives arrives in the destination by the route a call's
    -- value arrives by
    map _.body (functionOf 9) `shouldEqual` Right
      { code:
          [ CLOS (Reg 2) (FuncIx 10) []
          , CLOS (Reg 3) (FuncIx 11) []
          , CLOS (Reg 4) (FuncIx 12) []
          , LOADK (Reg 5) (ConstIx 0)
          , HNDL (Reg 1) (HandlerIx 0) (Reg 2) (Reg 3) [ Reg 4 ] [ Reg 5 ]
          ]
      , tail: RET (Reg 1)
      }

  it "applies a continuation with an ordinary unknown call" do
    -- a continuation is a function value, and nothing bounds how often one may
    -- be applied (D33)
    map _.body (functionOf 8) `shouldEqual` Right
      { code: [ LOADK (Reg 2) (ConstIx 0) ]
      , tail: TAILU (Reg 1) [ Reg 2 ]
      }

  it "interns the key of an element and the key of a cell alike" do
    -- a key is compared for equality and for nothing else. No region key is
    -- among them: erasure keeps no region element (D36)
    map _.keys (lowered handlerSlice) `shouldEqual` Right
      [ KEffect counterEff, KSymbol (Symbol "n") ]

  it "interns an operation's name, which is all a clause is found by" do
    map _.ops (lowered handlerSlice) `shouldEqual` Right [ nextOp ]

  it "holds one entry per handler, with its cells' keys and its clauses' forms" do
    -- the markers survive: they say which reduction applies, and a backend
    -- lowers the two differently (D28)
    map _.handlers (lowered handlerSlice) `shouldEqual` Right
      [ countingEntry
      , { key: KeyIx 0
        , cells: []
        , opClauses: [ { op: OpIx 0, form: ClauseFull } ]
        }
      ]
