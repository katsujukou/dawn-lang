-- | The effectful fragment carried the whole way: Typed Core, translated, lowered,
-- | encoded, decoded, loaded, and run.
-- |
-- | One module declares one effect and two values, each a `handle` that
-- | initialization evaluates. What the global slots hold afterwards is the
-- | assertion, so the `HANDLERS` table's order, the operands of `HNDL`, and which
-- | cell a clause reaches are all read the way lowering wrote them.
-- |
-- | | Value | What it holds |
-- | | --- | --- |
-- | | `counted` | a `fast` clause over a region of one cell, performed twice |
-- | | `resumedTwice` | a `full` clause applying its continuation twice |
module Test.Steam.Effectful (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Run (runBaseEffect)
import Run.Except as Except
import Steam.Load (LoadError(..), Store, emptyStore, globalNamed, load, noIdentities)
import Steam.Value (Value(..))
import Stella.Compiler.Bytecode (Dmo, decode, encode, lower)
import Stella.Compiler.Interface (noImports)
import Stella.Compiler.MiddleEnd (translate)
import Stella.Compiler.TypedCore (Decl(..), EffName(..), Export(..), Expr(..), Ident(..), Layout, Literal(..), Module, ModuleName(..), OpClause(..), OpName(..), Qualified(..), RowEntry(..), RowKey(..), Symbol(..), TyVar(..), Type(..), declareAnnotated, monoScheme, primSignature)
import Stella.Compiler.TypedCore.Prim (fn, intTy, pureFn, unitCtor, unitTy)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- The Core modules -----------------------------------------------------------------

intModuleName :: ModuleName
intModuleName = ModuleName "Base.Int"

mainModuleName :: ModuleName
mainModuleName = ModuleName "Main"

intAdd :: Qualified Ident
intAdd = Qualified intModuleName (Ident "add")

intSub :: Qualified Ident
intSub = Qualified intModuleName (Ident "sub")

counterEff :: Qualified EffName
counterEff = Qualified mainModuleName (EffName "Counter")

-- | The key of the element a handler of `Counter` removes, derived from the effect
-- | at the head of the payload (D16).
counterKey :: RowKey
counterKey = EffectKey counterEff

-- | The key of the one cell the region declares.
cellKey :: RowKey
cellKey = SymbolKey (Symbol "n")

nextOp :: OpName
nextOp = OpName "next"

countedName :: Qualified Ident
countedName = Qualified mainModuleName (Ident "counted")

subtractName :: Qualified Ident
subtractName = Qualified mainModuleName (Ident "subtract")

curriedName :: Qualified Ident
curriedName = Qualified mainModuleName (Ident "curried")

foldedOrderName :: Qualified Ident
foldedOrderName = Qualified mainModuleName (Ident "foldedOrder")

chainedOrderName :: Qualified Ident
chainedOrderName = Qualified mainModuleName (Ident "chainedOrder")

resumedName :: Qualified Ident
resumedName = Qualified mainModuleName (Ident "resumedTwice")

int :: Type
int = TCon intTy []

unit' :: Type
unit' = TCon unitTy []

-- | `( Counter )`, the row the handled computation stands at. It is closed, so
-- | nothing here is polymorphic in a residual row and no `Lacks` is assumed.
counterRow :: Type
counterRow = TRowExtend (RowEffectEntry counterEff []) TRowEmpty

-- | `r`, the region variable `cells` binds.
regionVar :: TyVar
regionVar = TyVar "r"

-- | `( region r ( n : Int ) )`, the row the operation clauses of a handler owning a
-- | region stand at. The handled computation and the return clause stand at `()`,
-- | which is what keeps a cell out of the answer (D36).
clauseRow :: Type
clauseRow = TRowExtend (RowRegionEntry (TVar regionVar) layoutRow) TRowEmpty

-- | `( n : Int )`, the layout of the region as a row.
layoutRow :: Type
layoutRow = TRowExtend (RowTypeEntry cellKey int) TRowEmpty

-- | `cells [r] ( n : Int )`.
cellLayout :: Layout
cellLayout = { var: regionVar, cells: [ { key: cellKey, ty: int } ] }

-- | `perform Counter.next Prim.Unit`.
performNext :: Expr P.Int
performNext = Perform 0 counterKey nextOp [] (Global 0 unitCtor [])

-- | `Base.Int.add x y` at a row that is not empty. The arrows of a foreign are
-- | pure and containment is never inserted, so each application carries a widening
-- | of its own (D8).
added :: Type -> Expr P.Int -> Expr P.Int -> Expr P.Int
added row x y =
  App 0 (OpenEff 0 row (App 0 (OpenEff 0 row (Global 0 intAdd [])) x)) y

intModule :: Module P.Int
intModule =
  { annotation: 0
  , name: intModuleName
  , imports: []
  , exports: [ ExportValue (Ident "add"), ExportValue (Ident "sub") ]
  , decls:
      [ DeclForeign 1
          { name: Ident "add"
          , scheme: monoScheme (pureFn int (pureFn int int))
          , attributes: []
          }
      , DeclForeign 2
          { name: Ident "sub"
          , scheme: monoScheme (pureFn int (pureFn int int))
          , attributes: []
          }
      ]
  }

mainModule :: Module P.Int
mainModule =
  { annotation: 0
  , name: mainModuleName
  , imports: [ intModuleName ]
  , exports: []
  , decls:
      [ counterEffectDecl
      , countedDecl
      , resumedDecl
      , subtractDecl
      , curriedDecl
      , foldedOrderDecl
      , chainedOrderDecl
      ]
  }

-- | `effect Counter where next : Unit ->* Int`.
counterEffectDecl :: Decl P.Int
counterEffectDecl = DeclEffect 1
  { name: EffName "Counter"
  , params: []
  , operations:
      [ { name: nextOp, tyBinders: [], argument: unit', resumesWith: int } ]
  , attributes: []
  }

-- | Two performs under a handler whose clause reads the cell and leaves it one
-- | higher: the first gives 0 and the second 1, and their sum is what the value
-- | holds. Nothing here is a lambda, so initialization evaluates it.
countedDecl :: Decl P.Int
countedDecl = DeclNonRec 2
  { name: Ident "counted"
  , scheme: monoScheme int
  , value:
      Handle 0
        ( Let 0 (Ident "a") int performNext
            $ Let 0 (Ident "b") int performNext
            $ added counterRow (Var 0 (Ident "a")) (Var 0 (Ident "b"))
        )
        { element: RowEffectEntry counterEff []
        , cells: Just cellLayout
        , returnClause: { binder: Ident "x", ty: int, body: Var 0 (Ident "x") }
        , opClauses:
            [ FastClause
                { op: nextOp
                , tyBinders: []
                , argBinder: { name: Ident "u", ty: unit' }
                , body:
                    Let 0 (Ident "v") int (ReadCell 0 cellKey)
                      $ Let 0 (Ident "w") unit'
                          ( WriteCell 0 cellKey
                              (added clauseRow (Var 0 (Ident "v")) (Lit 0 (LitInt 1)))
                          )
                      $ Var 0 (Ident "v")
                }
            ]
        }
        [ Lit 0 (LitInt 0) ]
  , attributes: []
  }

-- | One perform under a handler whose clause holds the continuation and applies it
-- | twice. The two applications are bound in order, so the first resumes with 1 and
-- | the second with 2; each runs the rest of the computation from where the
-- | `perform` stood, and the sum is 3 (D33).
resumedDecl :: Decl P.Int
resumedDecl = DeclNonRec 3
  { name: Ident "resumedTwice"
  , scheme: monoScheme int
  , value:
      Handle 0 performNext
        { element: RowEffectEntry counterEff []
        , cells: Nothing
        , returnClause: { binder: Ident "x", ty: int, body: Var 0 (Ident "x") }
        , opClauses:
            [ FullClause
                { op: nextOp
                , tyBinders: []
                , argBinder: { name: Ident "u", ty: unit' }
                , contBinder: { name: Ident "k", ty: fn int TRowEmpty int }
                , body:
                    Let 0 (Ident "first") int (App 0 (Var 0 (Ident "k")) (Lit 0 (LitInt 1)))
                      $ Let 0 (Ident "second") int
                          (App 0 (Var 0 (Ident "k")) (Lit 0 (LitInt 2)))
                      $ added TRowEmpty (Var 0 (Ident "first")) (Var 0 (Ident "second"))
                }
            ]
        }
        []
  , attributes: []
  }

-- | `subtract n y = y - n`, a function of two parameters: its definitional arity is
-- | two, so a saturated application of it folds into one call (D30).
subtractDecl :: Decl P.Int
subtractDecl = DeclNonRec 4
  { name: Ident "subtract"
  , scheme: monoScheme (pureFn int (pureFn int int))
  , value:
      Lam 0 (Ident "n") int
        $ Lam 0 (Ident "y") int
        $ App 0 (App 0 (Global 0 intSub []) (Var 0 (Ident "y"))) (Var 0 (Ident "n"))
  , attributes: []
  }

-- | The same function with a definitional arity of **one**: its right-hand side has
-- | one leading lambda and its body is a partial application, so applying it to two
-- | arguments is a call of one and then an application of what comes back.
curriedDecl :: Decl P.Int
curriedDecl = DeclNonRec 5
  { name: Ident "curried"
  , scheme: monoScheme (pureFn int (pureFn int int))
  , value:
      Lam 0 (Ident "n") int
        $ App 0 (Global 0 subtractName []) (Var 0 (Ident "n"))
  , attributes: []
  }

-- | Which of two arguments is evaluated first, read off the values the operation
-- | gave: the counting handler answers 0 to the first `perform` and 1 to the next,
-- | and `subtract` takes the first argument as `n` and the second as `y`.
-- |
-- | **An application evaluates its argument before its function** (D35), so a spine
-- | is evaluated right to left: the second argument performs first and gets 0, the
-- | first gets 1, and `y - n` is `0 - 1`. Had it gone the other way the value would
-- | be `1 - 0`.
foldedOrderDecl :: Decl P.Int
foldedOrderDecl = DeclNonRec 6
  { name: Ident "foldedOrder"
  , scheme: monoScheme int
  , value: counting (spine subtractName)
  , attributes: []
  }

-- | The same spine over the function whose arity is one, which no fold collects into
-- | a single call. **What it performs is what the folded form performs**, which is
-- | what argument-before-function buys (D30, D35).
chainedOrderDecl :: Decl P.Int
chainedOrderDecl = DeclNonRec 7
  { name: Ident "chainedOrder"
  , scheme: monoScheme int
  , value: counting (spine curriedName)
  , attributes: []
  }

-- | `f (perform next) (perform next)`, with nothing between the two to sequence
-- | them: the order is the application's own.
spine :: Qualified Ident -> Expr P.Int
spine f =
  App 0 (OpenEff 0 counterRow (App 0 (OpenEff 0 counterRow (Global 0 f [])) performNext))
    performNext

-- | That computation under the counting handler, whose `fast` clause answers with
-- | the cell and leaves it one higher.
counting :: Expr P.Int -> Expr P.Int
counting body =
  Handle 0 body
    { element: RowEffectEntry counterEff []
    , cells: Just cellLayout
    , returnClause: { binder: Ident "x", ty: int, body: Var 0 (Ident "x") }
    , opClauses:
        [ FastClause
            { op: nextOp
            , tyBinders: []
            , argBinder: { name: Ident "u", ty: unit' }
            , body:
                Let 0 (Ident "v") int (ReadCell 0 cellKey)
                  $ Let 0 (Ident "w") unit'
                      ( WriteCell 0 cellKey
                          (added clauseRow (Var 0 (Ident "v")) (Lit 0 (LitInt 1)))
                      )
                  $ Var 0 (Ident "v")
            }
        ]
    }
    [ Lit 0 (LitInt 0) ]

-- Compiling and loading them --------------------------------------------------------

-- | The two modules lowered and carried through the container.
compiled :: Either P.String { int :: Dmo, main :: Dmo }
compiled = case declareAnnotated primSignature intModule of
  Left _ -> Left "Base.Int did not declare"
  Right intDeclared -> do
    intDmo <- through intModule intDeclared
    case declareAnnotated intDeclared.signature mainModule of
      Left _ -> Left "Main did not declare"
      Right mainDeclared -> do
        mainDmo <- through mainModule mainDeclared
        pure { int: intDmo, main: mainDmo }
  where
  through m declared = case translate noImports m declared of
    Left err -> Left (show err)
    Right mid -> case lower mid of
      Left err -> Left (show err)
      Right out -> case encode out.dmo of
        Left err -> Left (show err)
        Right bytes -> case decode bytes of
          Left err -> Left (show err)
          Right dmo -> Right dmo

fresh :: Effect Store
fresh = map emptyStore (Ref.new noIdentities)

loading :: P.Array Dmo -> Aff (Either LoadError Store)
loading modules = liftEffect do
  store <- fresh
  runBaseEffect (Except.runExcept (Array.foldM load store modules))

valueOf :: Store -> Qualified Ident -> Aff (Maybe Value)
valueOf store name = liftEffect case globalNamed store name of
  Nothing -> pure Nothing
  Just slot -> Ref.read slot

held :: Maybe Value -> Maybe P.Int
held = case _ of
  Just (VInt n) -> Just n
  _ -> Nothing

spec :: Spec Unit
spec = describe "Steam, over the effectful fragment" do

  it "evaluates an argument before the function of an application" do
    -- the second argument of the spine performs first and is answered 0, the first
    -- is answered 1, and `subtract` computes `y - n` — so `0 - 1` (D35)
    case compiled of
      Left err -> fail err
      Right dmos -> do
        outcome <- loading [ dmos.int, dmos.main ]
        case outcome of
          Left err -> fail (show err)
          Right store -> do
            value <- valueOf store foldedOrderName
            held value `shouldEqual` Just (-1)

  it "performs the same sequence whether the spine folds or not" do
    -- the same spine over a function of arity one: a call of one argument and then
    -- an application of what came back. Collecting a spine into one call moves no
    -- effect, which is what argument-before-function is for (D30)
    case compiled of
      Left err -> fail err
      Right dmos -> do
        outcome <- loading [ dmos.int, dmos.main ]
        case outcome of
          Left err -> fail (show err)
          Right store -> do
            folded <- valueOf store foldedOrderName
            chained <- valueOf store chainedOrderName
            held chained `shouldEqual` held folded
            held chained `shouldEqual` Just (-1)

  it "refuses a handler declaring one cell twice" do
    -- a cell is found by its key, so which of two a `CGET` meant would otherwise
    -- depend on the order of the table
    case compiled of
      Left err -> fail err
      Right dmos -> do
        outcome <- loading
          [ dmos.int
          , dmos.main
              { handlers = map (\h -> h { cells = h.cells <> h.cells }) dmos.main.handlers }
          ]
        case outcome of
          Left (CellKeyTwice _) -> pure unit
          _ -> fail "expected a duplicated cell to be refused"

  it "refuses a handler holding two clauses for one operation" do
    case compiled of
      Left err -> fail err
      Right dmos -> do
        outcome <- loading
          [ dmos.int
          , dmos.main
              { handlers = map (\h -> h { opClauses = h.opClauses <> h.opClauses })
                  dmos.main.handlers
              }
          ]
        case outcome of
          Left (ClauseTwice _) -> pure unit
          _ -> fail "expected a duplicated clause to be refused"

  it "runs a handler owning a region, as initialization evaluates the value" do
    case compiled of
      Left err -> fail err
      Right dmos -> do
        outcome <- loading [ dmos.int, dmos.main ]
        case outcome of
          Left err -> fail (show err)
          Right store -> do
            -- the cell starts at 0; the first perform gives 0 and leaves 1, the
            -- second gives 1 and leaves 2, and the body adds them
            value <- valueOf store countedName
            held value `shouldEqual` Just 1

  it "runs a full clause applying its continuation twice" do
    case compiled of
      Left err -> fail err
      Right dmos -> do
        outcome <- loading [ dmos.int, dmos.main ]
        case outcome of
          Left err -> fail (show err)
          Right store -> do
            -- each application resumes the computation the `perform` was in: the
            -- first with 1 and the second with 2, in the order the bindings fix
            value <- valueOf store resumedName
            held value `shouldEqual` Just 3
