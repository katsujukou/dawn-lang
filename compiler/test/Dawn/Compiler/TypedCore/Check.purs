-- | Term typing.
-- |
-- | The cases the Implementation Plan singles out are here: an arrow's row
-- | against the ambient row, the value restriction, what a `perform` reads its
-- | signature from, which type a clause body is checked at given its form, and
-- | the local totality of a dispatch.
module Test.Dawn.Compiler.TypedCore.Check (spec) where

import Prelude

import Prim as P

import Dawn.Compiler.TypedCore (Decl(..), DecisionTree(..), EffName(..), Expr(..), Handler, Ident(..), JoinName(..), Kind(..), Layout, Literal(..), Module, ModuleName(..), OpClause(..), Occurrence(..), OpName(..), Qualified(..), RowElemKind(..), RowEntry(..), RowKey(..), Symbol(..), TyName(..), TyVar(..), Type(..))
import Dawn.Compiler.TypedCore.Check (CheckError(..), Env, check, envOf, infer, typeOf)
import Dawn.Compiler.TypedCore.Kinding (KindError(..))
import Dawn.Compiler.TypedCore.Context (bindVar, emptyContext)
import Dawn.Compiler.TypedCore.Declare (declare)
import Dawn.Compiler.TypedCore.Prim (fn, intTy, primSignature, pureFn, stringTy, unitTy)
import Dawn.Compiler.TypedCore.Signature (Signature)
import Dawn.Compiler.TypedCore.Type (Constraint(..))
import Data.Either (Either(..), either)
import Data.Maybe (Maybe(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

main :: ModuleName
main = ModuleName "Main"

value :: P.String -> Qualified Ident
value name = Qualified main (Ident name)

consoleEff :: Qualified EffName
consoleEff = Qualified main (EffName "Console")

stateEff :: Qualified EffName
stateEff = Qualified main (EffName "State")

maybeTy :: Qualified TyName
maybeTy = Qualified main (TyName "Maybe")

int :: Type
int = TCon intTy []

string :: Type
string = TCon stringTy []

unitT :: Type
unitT = TCon unitTy []

maybeOf :: Type -> Type
maybeOf ty = TApp (TCon maybeTy []) ty

record :: Type -> Type
record row = TApp (TCon (Qualified (ModuleName "Prim") (TyName "Record")) []) row

variant :: Type -> Type
variant row = TApp (TCon (Qualified (ModuleName "Prim") (TyName "Variant")) []) row

-- | `( Console )`
consoleRow :: Type
consoleRow = TRowExtend (RowEffectEntry consoleEff []) TRowEmpty

-- | `( cache : State Int )`, oneLit effect under a written key.
cacheRow :: Type
cacheRow = TRowExtend (RowLabelledEffectEntry (Symbol "cache") stateEff [ int ]) TRowEmpty

cacheKey :: RowKey
cacheKey = SymbolKey (Symbol "cache")

nameKey :: RowKey
nameKey = SymbolKey (Symbol "name")

sizeKey :: RowKey
sizeKey = SymbolKey (Symbol "size")

-- | The declarations these cases are checked against.
fixtures :: Module Unit
fixtures =
  { annotation: unit
  , name: main
  , imports: []
  , exports: []
  , decls:
      [ DeclEffect unit
          { name: EffName "Console"
          , params: []
          , operations: [ { name: OpName "log", tyBinders: [], argument: string, resumesWith: unitT } ]
          , attributes: []
          }
      , DeclEffect unit
          { name: EffName "State"
          , params: [ { name: TyVar "s", kind: KType } ]
          , operations:
              [ { name: OpName "get", tyBinders: [], argument: unitT, resumesWith: TVar (TyVar "s") }
              , { name: OpName "put", tyBinders: [], argument: TVar (TyVar "s"), resumesWith: unitT }
              ]
          , attributes: []
          }
      , DeclEffect unit
          { name: EffName "Fail"
          , params: []
          , operations:
              [ { name: OpName "abort"
                , tyBinders: [ { name: TyVar "a", kind: KType } ]
                , argument: unitT
                , resumesWith: TVar (TyVar "a")
                }
              ]
          , attributes: []
          }
      -- an effect whose one operation resumes with a value, so that a handler
      -- owning a region has something to answer a `readCell` with
      , DeclEffect unit
          { name: EffName "Counter"
          , params: []
          , operations: [ { name: OpName "next", tyBinders: [], argument: unitT, resumesWith: int } ]
          , attributes: []
          }
      -- a second abort-shaped effect, so that one can be translated into the
      -- other by a clause that resumes at neither
      , DeclEffect unit
          { name: EffName "Fail2"
          , params: []
          , operations:
              [ { name: OpName "abort"
                , tyBinders: [ { name: TyVar "a", kind: KType } ]
                , argument: unitT
                , resumesWith: TVar (TyVar "a")
                }
              ]
          , attributes: []
          }
      , DeclData unit
          { name: TyName "Void"
          , kindVars: []
          , params: []
          , constructors: []
          , isNewtype: false
          , attributes: []
          }
      , DeclData unit
          { name: TyName "Wrap"
          , kindVars: []
          , params: []
          , constructors:
              [ { name: Ident "Absurd", tag: 0, fields: [ TCon (Qualified main (TyName "Void")) [] ] }
              , { name: Ident "Plain", tag: 1, fields: [] }
              ]
          , isNewtype: false
          , attributes: []
          }
      , DeclData unit
          { name: TyName "Maybe"
          , kindVars: []
          , params: [ { name: TyVar "a", kind: KType } ]
          , constructors:
              [ { name: Ident "Nothing", tag: 0, fields: [] }
              , { name: Ident "Just", tag: 1, fields: [ TVar (TyVar "a") ] }
              ]
          , isNewtype: false
          , attributes: []
          }
      ]
  }

sig :: Signature
sig = either (const primSignature) identity (declare primSignature fixtures)

env :: Env
env = envOf sig emptyContext

-- | `Γ` with `f : Int -> Int` and `x : Int`.
applied :: Env
applied = env
  { context = bindVar (bindVar emptyContext (Ident "f") (pureFn int int)) (Ident "x") int }

inferAt :: Type -> Expr Unit -> Either CheckError Type
inferAt rho expr = case infer env rho expr of
  Left failure -> Left failure.error
  Right checked -> Right (typeOf checked)

inferIn :: Env -> Type -> Expr Unit -> Either CheckError Type
inferIn e rho expr = case infer e rho expr of
  Left failure -> Left failure.error
  Right checked -> Right (typeOf checked)

checkAt :: Type -> Type -> Expr Unit -> Either CheckError Unit
checkAt rho expected expr = case check env rho expected expr of
  Left failure -> Left failure.error
  Right _ -> Right unit

lam :: P.String -> Type -> Expr Unit -> Expr Unit
lam name ty body = Lam unit (Ident name) ty body

var :: P.String -> Expr Unit
var name = Var unit (Ident name)

primUnit :: Expr Unit
primUnit = Global unit (Qualified (ModuleName "Prim") (Ident "Unit")) []

oneLit :: Expr Unit
oneLit = Lit unit (LitInt 1)

emptyRecord :: Expr Unit
emptyRecord = RecordEmpty unit

failEff :: Qualified EffName
failEff = Qualified main (EffName "Fail")

fail2Eff :: Qualified EffName
fail2Eff = Qualified main (EffName "Fail2")

-- | `( Fail2 )`
fail2Row :: Type
fail2Row = TRowExtend (RowEffectEntry fail2Eff []) TRowEmpty

-- | `handle (perform Fail.abort [Int] ()) with { handles Fail ; … }`, with the
-- | binders and the continuation type of the clause supplied.
aborting :: P.Array { name :: TyVar, kind :: Kind } -> Type -> Expr Unit
aborting tyBinders contType =
  Handle unit (Perform unit (EffectKey failEff) (OpName "abort") [ int ] primUnit)
    { element: RowEffectEntry failEff []
    , cells: Nothing
    , returnClause: { binder: Ident "x", ty: int, body: oneLit }
    , opClauses:
        [ FullClause
            { op: OpName "abort"
            , tyBinders
            , argBinder: { name: Ident "u", ty: unitT }
            , contBinder: { name: Ident "k", ty: contType }
            , body: oneLit
            }
        ]
    }
    []

-- | `{ handles Console ; return (x : α) -> e ; full log (s, k) -> 1 }`, with the
-- | return type, the return body, and the continuation type supplied.
consoleHandler :: Type -> Expr Unit -> Type -> Handler Unit
consoleHandler alpha returned contType =
  { element: RowEffectEntry consoleEff []
  , cells: Nothing
  , returnClause: { binder: Ident "x", ty: alpha, body: returned }
  , opClauses:
      [ FullClause
          { op: OpName "log"
          , tyBinders: []
          , argBinder: { name: Ident "s", ty: string }
          , contBinder: { name: Ident "k", ty: contType }
          , body: returned
          }
      ]
  }

-- | `handle (perform Console.log "x") with { handles Console ; return (x : Unit) -> 1 ; … }`,
-- | with the clause supplied. The handle stands at `Int`.
logging :: OpClause Unit -> Expr Unit
logging clause =
  Handle unit (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (LitString "x")))
    { element: RowEffectEntry consoleEff []
    , cells: Nothing
    , returnClause: { binder: Ident "x", ty: unitT, body: oneLit }
    , opClauses: [ clause ]
    }
    []

counterEff :: Qualified EffName
counterEff = Qualified main (EffName "Counter")

regionVar :: TyVar
regionVar = TyVar "r"

nKey :: RowKey
nKey = SymbolKey (Symbol "n")

-- | `cells [r] ( n : Int )`, one cell holding an `Int`.
oneCell :: Layout
oneCell = { var: regionVar, cells: [ { key: nKey, ty: int } ] }

-- | `handle (perform Counter.next ()) with { handles Counter ; … } @ ( ē )`,
-- | with the layout, the initial values, the return clause's body, and the
-- | clause supplied. Both the handled computation and the answer are `Int`.
counting
  :: Maybe Layout
  -> P.Array (Expr Unit)
  -> Expr Unit
  -> OpClause Unit
  -> Expr Unit
counting cells initial returned clause =
  Handle unit (Perform unit (EffectKey counterEff) (OpName "next") [] primUnit)
    { element: RowEffectEntry counterEff []
    , cells
    , returnClause: { binder: Ident "x", ty: int, body: returned }
    , opClauses: [ clause ]
    }
    initial

-- | `fast next (_ : Unit) -> e`, whose body must have the type `next` resumes
-- | with, `Int`.
fastNext :: Expr Unit -> OpClause Unit
fastNext body =
  FastClause
    { op: OpName "next"
    , tyBinders: []
    , argBinder: { name: Ident "u", ty: unitT }
    , body
    }

-- | `fast log (msg : String) -> e`, with the body supplied. `log` resumes with
-- | `Unit`, so that is the type the body is checked at.
fastLog :: Expr Unit -> OpClause Unit
fastLog body =
  FastClause
    { op: OpName "log"
    , tyBinders: []
    , argBinder: { name: Ident "s", ty: string }
    , body
    }

-- | `full log (s : String, k : Unit -{()}-> Int) -> e`, over the same handler.
fullLog :: Expr Unit -> OpClause Unit
fullLog body =
  FullClause
    { op: OpName "log"
    , tyBinders: []
    , argBinder: { name: Ident "s", ty: string }
    , contBinder: { name: Ident "k", ty: pureFn unitT int }
    , body
    }

spec :: Spec Unit
spec = describe "TypedCore.Check" do
  it "declares the fixtures" do
    map (const unit) (declare primSignature fixtures) `shouldEqual` Right unit

  describe "basic rules" do
    it "gives a literal its type under any ambient row" do
      inferAt consoleRow oneLit `shouldEqual` Right int

    it "refuses a variable no binder introduced" do
      inferAt TRowEmpty (var "x") `shouldEqual` Left (UnboundVar (Ident "x"))

    it "reads a constructor's type from the declaration" do
      inferAt TRowEmpty (Global unit (value "Just") [])
        `shouldEqual` Right
          (TForall (TyVar "a") KType (pureFn (TVar (TyVar "a")) (maybeOf (TVar (TyVar "a")))))

    it "refuses a global instantiated at a number of kinds its scheme does not bind" do
      -- `Main.Just` binds none, so `[[Type]]` is an arity error
      inferAt TRowEmpty (Global unit (value "Just") [ KType ])
        `shouldEqual` Left (GlobalKindArgCount (value "Just") 0 1)

    it "synthesizes a lambda at the ambient row" do
      inferAt consoleRow (lam "n" int (var "n"))
        `shouldEqual` Right (fn int consoleRow int)

    it "checks one against the row its type writes" do
      checkAt consoleRow (pureFn int int) (lam "n" int (var "n"))
        `shouldEqual` Right unit

    it "requires an arrow's row to be the ambient row" do
      -- containment is never inserted, so a pure function is not applicable
      -- where effects may occur
      inferIn applied consoleRow (App unit (var "f") (var "x"))
        `shouldEqual` Left (RowMismatch consoleRow TRowEmpty)

    it "lets openEff widen it" do
      inferIn applied consoleRow
        (App unit (OpenEff unit consoleRow (var "f")) (var "x"))
        `shouldEqual` Right int

    it "substitutes at a type application" do
      inferAt TRowEmpty
        (TyApp unit (TyLam unit (TyVar "a") KType (lam "n" (TVar (TyVar "a")) (var "n"))) int)
        `shouldEqual` Right (pureFn int int)

    it "requires the body of a type abstraction to be a value form" do
      inferAt TRowEmpty
        (TyLam unit (TyVar "a") KType (App unit (lam "n" int (var "n")) oneLit))
        `shouldEqual` Left NotAValueForm

    it "re-derives a constraint at its elimination" do
      let constraint = Lacks nameKey TRowEmpty
      inferAt TRowEmpty
        (ConstraintApp unit (ConstraintLam unit constraint (lam "n" int (var "n"))))
        `shouldEqual` Right (pureFn int int)

    it "refuses a global the signature does not declare" do
      inferAt TRowEmpty (Global unit (value "ghost") [])
        `shouldEqual` Left (UndeclaredGlobal (value "ghost"))

    it "refuses an application of something that is not a function" do
      inferAt TRowEmpty (App unit oneLit oneLit) `shouldEqual` Left (NotAFunction int)

    it "refuses a type application of something that is not a forall" do
      inferAt TRowEmpty (TyApp unit oneLit int) `shouldEqual` Left (NotAForall int)

    it "refuses a constraint application of something that carries no constraint" do
      inferAt TRowEmpty (ConstraintApp unit oneLit) `shouldEqual` Left (NotConstrained int)

    it "refuses a selection from something that is not a record" do
      inferAt TRowEmpty (RecordSelect unit nameKey oneLit) `shouldEqual` Left (NotARecord int)

    it "refuses a weakening of something that is not a variant" do
      inferAt TRowEmpty (VariantWeaken unit nameKey int oneLit)
        `shouldEqual` Left (NotAVariant int)

    it "refuses a constraint abstraction checked against another constraint" do
      let
        assumed = Lacks nameKey TRowEmpty
        expected = Lacks cacheKey TRowEmpty
        abstraction = ConstraintLam unit assumed oneLit
      checkAt TRowEmpty (TConstrained expected int) abstraction
        `shouldEqual` Left (ConstraintMismatch expected assumed)

  describe "records" do
    it "selects what was extended" do
      inferAt TRowEmpty
        (RecordSelect unit nameKey (RecordExtend unit nameKey oneLit emptyRecord))
        `shouldEqual` Right int

    it "refuses a key the row already carries" do
      let inner = RecordExtend unit nameKey oneLit emptyRecord
      inferAt TRowEmpty (RecordExtend unit nameKey oneLit inner)
        `shouldEqual` Left (NotEntailed (Lacks nameKey (TRowExtend (RowTypeEntry nameKey int) TRowEmpty)))

    it "refuses a selection the row has no element for" do
      inferAt TRowEmpty (RecordSelect unit sizeKey emptyRecord)
        `shouldEqual` Left (NoElementAt sizeKey TRowEmpty)

    it "removes an element at a restriction" do
      inferAt TRowEmpty
        (RecordRestrict unit nameKey (RecordExtend unit nameKey oneLit emptyRecord))
        `shouldEqual` Right (record TRowEmpty)

    it "lets an update change the type of an element" do
      inferAt TRowEmpty
        ( RecordUpdate unit nameKey
            (RecordExtend unit nameKey oneLit emptyRecord)
            (Lit unit (LitString "s"))
        )
        `shouldEqual` Right (record (TRowExtend (RowTypeEntry nameKey string) TRowEmpty))

    it "requires the two sides of a merge to be disjoint" do
      let left = RecordExtend unit nameKey oneLit emptyRecord
      inferAt TRowEmpty (RecordMerge unit left left)
        `shouldEqual` Left
          ( NotEntailed
              ( Disjoint (TRowExtend (RowTypeEntry nameKey int) TRowEmpty)
                  (TRowExtend (RowTypeEntry nameKey int) TRowEmpty)
              )
          )

  describe "variants" do
    it "synthesizes the variant of the key alone" do
      inferAt TRowEmpty (VariantInject unit nameKey oneLit)
        `shouldEqual` Right (variant (TRowExtend (RowTypeEntry nameKey int) TRowEmpty))

    it "checks an injection against a wider variant" do
      let wide = variant (TRowExtend (RowTypeEntry nameKey int) (TRowExtend (RowTypeEntry sizeKey string) TRowEmpty))
      checkAt TRowEmpty wide (VariantInject unit nameKey oneLit) `shouldEqual` Right unit

    it "widens one with weaken" do
      inferAt TRowEmpty (VariantWeaken unit sizeKey string (VariantInject unit nameKey oneLit))
        `shouldEqual` Right
          ( variant
              (TRowExtend (RowTypeEntry sizeKey string) (TRowExtend (RowTypeEntry nameKey int) TRowEmpty))
          )

  describe "perform" do
    it "takes the element the key names" do
      inferAt consoleRow (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (LitString "x")))
        `shouldEqual` Right unitT

    it "requires the ambient row to carry the key" do
      inferAt TRowEmpty (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (LitString "x")))
        `shouldEqual` Left (NoElementAt (EffectKey consoleEff) TRowEmpty)

    it "reads the signature from the effect the payload names" do
      -- the key `cache` selects the element; `Σ(State)` with `s := Int` is what
      -- says the operation resumes with an `Int`
      inferAt cacheRow (Perform unit cacheKey (OpName "get") [] primUnit)
        `shouldEqual` Right int

    it "refuses an operation the effect does not declare" do
      inferAt consoleRow (Perform unit (EffectKey consoleEff) (OpName "shout") [] primUnit)
        `shouldEqual` Left (UnknownOperation consoleEff (OpName "shout"))

    it "refuses a number of type arguments the operation does not bind" do
      -- `Console.log` binds none, so supplying one is an arity error
      inferAt consoleRow
        (Perform unit (EffectKey consoleEff) (OpName "log") [ int ] (Lit unit (LitString "x")))
        `shouldEqual` Left (OperationTypeArgCount (OpName "log") 0 1)

  describe "handlers" do
    it "removes the element the handler writes" do
      -- effect safety is not "no operation is performed": the row outside the
      -- handle carries nothing
      inferAt TRowEmpty (logging (fullLog oneLit)) `shouldEqual` Right int

    it "requires a clause for every operation of the effect" do
      inferAt TRowEmpty
        ( Handle unit (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (LitString "x")))
            { element: RowEffectEntry consoleEff []
            , cells: Nothing
            , returnClause: { binder: Ident "x", ty: unitT, body: oneLit }
            , opClauses: []
            }
            []
        )
        `shouldEqual` Left (MissingClause consoleEff (OpName "log"))

    it "gives the continuation the row outside the handle and the result of it" do
      -- a shallow handler would resume at the inner row and the inner result
      inferAt TRowEmpty
        ( logging
            ( FullClause
                { op: OpName "log"
                , tyBinders: []
                , argBinder: { name: Ident "s", ty: string }
                , contBinder: { name: Ident "k", ty: pureFn unitT string }
                , body: oneLit
                }
            )
        )
        `shouldEqual` Left (TypeMismatch (pureFn unitT int) (pureFn unitT string))

    it "lets a performance at another key pass through" do
      -- `Ev_k` matches on the key, and `counter` is not `cache`
      let
        counterRow = TRowExtend (RowLabelledEffectEntry (Symbol "counter") stateEff [ int ]) TRowEmpty
        counterKey = SymbolKey (Symbol "counter")
      inferAt counterRow
        ( Handle unit (Perform unit counterKey (OpName "get") [] primUnit)
            { element: RowLabelledEffectEntry (Symbol "cache") stateEff [ int ]
            , cells: Nothing
            , returnClause: { binder: Ident "x", ty: int, body: oneLit }
            , opClauses:
                [ FullClause
                    { op: OpName "get"
                    , tyBinders: []
                    , argBinder: { name: Ident "u", ty: unitT }
                    , contBinder: { name: Ident "k", ty: fn int counterRow int }
                    , body: oneLit
                    }
                , FullClause
                    { op: OpName "put"
                    , tyBinders: []
                    , argBinder: { name: Ident "v", ty: int }
                    , contBinder: { name: Ident "k", ty: fn unitT counterRow int }
                    , body: oneLit
                    }
                ]
            }
            []
        )
        `shouldEqual` Right int

  describe "clause forms" do
    it "checks a full clause's body at the answer type" do
      -- `β` is `Int` here, from the return clause; `Unit` is what `log` resumes
      -- with, and a full clause is not checked at that
      inferAt TRowEmpty (logging (fullLog primUnit))
        `shouldEqual` Left (TypeMismatch int unitT)

    it "checks a fast clause's body at the type the operation resumes with" do
      inferAt TRowEmpty (logging (fastLog primUnit)) `shouldEqual` Right int

    it "refuses a fast clause's body at the answer type instead" do
      inferAt TRowEmpty (logging (fastLog oneLit))
        `shouldEqual` Left (TypeMismatch unitT int)

    it "binds no continuation in a fast clause" do
      inferAt TRowEmpty (logging (fastLog (var "k")))
        `shouldEqual` Left (UnboundVar (Ident "k"))

    it "accepts a handler mixing the two forms" do
      -- the form is written per clause, so one effect's operations may differ
      inferAt TRowEmpty
        ( Handle unit (Perform unit cacheKey (OpName "get") [] primUnit)
            { element: RowLabelledEffectEntry (Symbol "cache") stateEff [ int ]
            , cells: Nothing
            , returnClause: { binder: Ident "x", ty: int, body: oneLit }
            , opClauses:
                [ FastClause
                    { op: OpName "get"
                    , tyBinders: []
                    , argBinder: { name: Ident "u", ty: unitT }
                    , body: oneLit
                    }
                , FullClause
                    { op: OpName "put"
                    , tyBinders: []
                    , argBinder: { name: Ident "v", ty: int }
                    , contBinder: { name: Ident "k", ty: pureFn unitT int }
                    , body: oneLit
                    }
                ]
            }
            []
        )
        `shouldEqual` Right int

    it "accepts a fast clause translating a polymorphic resume type into another effect" do
      -- `abort : forall a. Unit ->* a` admits no pure terminating body, but
      -- performing an operation that resumes at `a` has that type. A fast
      -- clause is therefore available wherever a capability, not a pure type,
      -- is the target
      inferAt fail2Row
        ( Handle unit (Perform unit (EffectKey failEff) (OpName "abort") [ int ] primUnit)
            { element: RowEffectEntry failEff []
            , cells: Nothing
            , returnClause: { binder: Ident "x", ty: int, body: oneLit }
            , opClauses:
                [ FastClause
                    { op: OpName "abort"
                    , tyBinders: [ { name: TyVar "b", kind: KType } ]
                    , argBinder: { name: Ident "u", ty: unitT }
                    , body:
                        Perform unit (EffectKey fail2Eff) (OpName "abort")
                          [ TVar (TyVar "b") ]
                          primUnit
                    }
                ]
            }
            []
        )
        `shouldEqual` Right int

  describe "regions of cells" do
    it "checks a fast clause against the cell the layout declares" do
      inferAt TRowEmpty
        (counting (Just oneCell) [ oneLit ] (var "x") (fastNext (ReadCell unit nKey)))
        `shouldEqual` Right int

    it "gives a writeCell the Unit type rather than the cell's" do
      -- a write is done for its effect on the region and hands back nothing of
      -- its own; reading back what was set takes a readCell
      inferAt TRowEmpty
        ( counting (Just oneCell) [ oneLit ] (var "x")
            ( fastNext
                (Let unit (Ident "w") unitT (WriteCell unit nKey oneLit) (ReadCell unit nKey))
            )
        )
        `shouldEqual` Right int

    it "refuses a writeCell bound at the cell's type" do
      inferAt TRowEmpty
        ( counting (Just oneCell) [ oneLit ] (var "x")
            ( fastNext
                (Let unit (Ident "w") int (WriteCell unit nKey oneLit) (ReadCell unit nKey))
            )
        )
        `shouldEqual` Left (TypeMismatch int unitT)

    it "refuses a readCell in the computation the handler handles" do
      -- the handled computation stands at `( ent | ρ )`, which carries no
      -- region, so the code a handler handles reaches no cell of its own (D36)
      inferAt TRowEmpty
        ( Handle unit (ReadCell unit nKey)
            { element: RowEffectEntry counterEff []
            , cells: Just oneCell
            , returnClause: { binder: Ident "x", ty: int, body: var "x" }
            , opClauses: [ fastNext oneLit ]
            }
            [ oneLit ]
        )
        `shouldEqual` Left (NoCellAt nKey (TRowExtend (RowEffectEntry counterEff []) TRowEmpty))

    it "refuses a readCell in the return clause" do
      -- the return clause stands at `ρ`, which is what makes an ordinary return
      -- hand back no state
      inferAt TRowEmpty
        (counting (Just oneCell) [ oneLit ] (ReadCell unit nKey) (fastNext oneLit))
        `shouldEqual` Left (NoCellAt nKey TRowEmpty)

    it "refuses a readCell for a key the layout does not declare" do
      inferAt TRowEmpty
        (counting (Just oneCell) [ oneLit ] (var "x") (fastNext (ReadCell unit sizeKey)))
        `shouldEqual` Left
          ( NoCellAt sizeKey
              (TRowExtend (RowRegionEntry (TVar regionVar) (TRowExtend (RowTypeEntry nKey int) TRowEmpty)) TRowEmpty)
          )

    it "refuses an initial value of the wrong type" do
      inferAt TRowEmpty
        (counting (Just oneCell) [ primUnit ] (var "x") (fastNext (ReadCell unit nKey)))
        `shouldEqual` Left (TypeMismatch int unitT)

    it "refuses a layout and a list of initial values of different lengths" do
      inferAt TRowEmpty
        (counting (Just oneCell) [] (var "x") (fastNext (ReadCell unit nKey)))
        `shouldEqual` Left (CellCount 1 0)

    it "refuses initial values where the handler owns no region" do
      inferAt TRowEmpty
        (counting Nothing [ oneLit ] (var "x") (fastNext oneLit))
        `shouldEqual` Left (CellCount 0 1)

    it "refuses a layout declaring one key twice" do
      -- kinding the layout is what rejects it: a row extension requires the key
      -- absent from the rest, which a repeat cannot discharge
      inferAt TRowEmpty
        ( counting
            (Just { var: regionVar, cells: [ { key: nKey, ty: int }, { key: nKey, ty: int } ] })
            [ oneLit, oneLit ]
            (var "x")
            (fastNext (ReadCell unit nKey))
        )
        `shouldEqual` Left (IllKindedType (NotSharp nKey (TRowExtend (RowTypeEntry nKey int) TRowEmpty)))

    it "refuses an answer type that mentions the region" do
      -- the answer is a closure carrying `ρ'` in its own arrow, so it mentions
      -- `r` — which is what `r ∉ ftv(β)` rejects. Everything else about the
      -- handler checks: the clause is the one place such a closure can be built
      let
        regionRow =
          TRowExtend (RowRegionEntry (TVar regionVar) (TRowExtend (RowTypeEntry nKey int) TRowEmpty))
            TRowEmpty
        answer = fn unitT regionRow int
      checkAt TRowEmpty answer
        ( Handle unit (Perform unit (EffectKey counterEff) (OpName "next") [] primUnit)
            { element: RowEffectEntry counterEff []
            , cells: Just oneCell
            , returnClause: { binder: Ident "x", ty: int, body: lam "u" unitT oneLit }
            , opClauses:
                [ FullClause
                    { op: OpName "next"
                    , tyBinders: []
                    , argBinder: { name: Ident "u", ty: unitT }
                    , contBinder: { name: Ident "k", ty: fn int regionRow answer }
                    , body: lam "u" unitT (ReadCell unit nKey)
                    }
                ]
            }
            [ oneLit ]
        )
        `shouldEqual` Left (RegionEscapes regionVar)

    it "checks the handler a var declaration desugars to" do
      -- the generated scheme carries `RegionKey ∉ e` beside the effect's own
      -- Lacks, and that is what discharges the region premise at a residual row
      -- which is a variable
      let
        e = TyVar "e"
        rowE = TVar e
        a = TyVar "a"
        tyA = TVar a
        thunkTy = fn unitT (TRowExtend (RowEffectEntry counterEff []) rowE) tyA
        -- the row the clauses stand at, which is what the widenings below name
        clauseRow =
          TRowExtend
            (RowRegionEntry (TVar regionVar) (TRowExtend (RowTypeEntry nKey int) TRowEmpty))
            rowE
        -- `add` is pure and curried, so each stage that consumes an argument is
        -- widened to the clause's row: containment is written, never implied
        added =
          App unit
            (OpenEff unit clauseRow (App unit (OpenEff unit clauseRow (var "add")) (var "v")))
            oneLit
        body =
          Let unit (Ident "add") (pureFn int (pureFn int int))
            (lam "p" int (lam "q" int (var "p")))
            ( Let unit (Ident "v") int (ReadCell unit nKey)
                (Let unit (Ident "w") unitT (WriteCell unit nKey added) (var "v"))
            )
        term =
          TyLam unit e (KRow RowEffect)
            $ TyLam unit a KType
            $ ConstraintLam unit (Lacks (EffectKey counterEff) rowE)
            $ ConstraintLam unit (Lacks RegionKey rowE)
            $ lam "thunk" thunkTy
            $ Handle unit (App unit (var "thunk") primUnit)
                { element: RowEffectEntry counterEff []
                , cells: Just oneCell
                , returnClause: { binder: Ident "x", ty: tyA, body: var "x" }
                , opClauses: [ fastNext body ]
                }
                [ oneLit ]
        scheme =
          TForall e (KRow RowEffect)
            ( TForall a KType
                ( TConstrained (Lacks (EffectKey counterEff) rowE)
                    (TConstrained (Lacks RegionKey rowE) (fn thunkTy rowE tyA))
                )
            )
      checkAt TRowEmpty scheme term `shouldEqual` Right unit

    it "refuses a handler with cells applied in a clause of another with cells" do
      let
        inner =
          Handle unit (Perform unit (EffectKey counterEff) (OpName "next") [] primUnit)
            { element: RowEffectEntry counterEff []
            , cells: Just { var: TyVar "s", cells: [ { key: nKey, ty: int } ] }
            , returnClause: { binder: Ident "y", ty: int, body: primUnit }
            , opClauses: [ fastNext (ReadCell unit nKey) ]
            }
            [ oneLit ]
        outer =
          Handle unit (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (LitString "x")))
            { element: RowEffectEntry consoleEff []
            , cells: Just { var: regionVar, cells: [ { key: sizeKey, ty: int } ] }
            , returnClause: { binder: Ident "x", ty: unitT, body: oneLit }
            , opClauses:
                [ FastClause
                    { op: OpName "log"
                    , tyBinders: []
                    , argBinder: { name: Ident "m", ty: string }
                    , body: inner
                    }
                ]
            }
            [ oneLit ]
      inferAt TRowEmpty outer `shouldEqual` Left
        ( NotEntailed
            ( Lacks RegionKey
                ( TRowExtend
                    (RowRegionEntry (TVar regionVar) (TRowExtend (RowTypeEntry sizeKey int) TRowEmpty))
                    TRowEmpty
                )
            )
        )

    it "refuses a cell binder already bound where the handler stands" do
      -- every bound variable of a Core term is unique within its context, and a
      -- region binder is checked against that: its layout is kinded outside the
      -- binder and then stands inside it
      inferAt TRowEmpty
        ( TyLam unit regionVar KType
            ( lam "u" unitT
                (counting (Just oneCell) [ oneLit ] (var "x") (fastNext (ReadCell unit nKey)))
            )
        )
        `shouldEqual` Left (RegionBinderShadows regionVar)

    it "keeps an outer variable apart from the region standing beside it" do
      -- the layout and the answer both mention `r`, which is bound outside the
      -- handler; the region binds `s`, and neither name is read for the other
      let
        r = TVar regionVar
        layout = { var: TyVar "s", cells: [ { key: nKey, ty: r } ] }
        term =
          TyLam unit regionVar KType
            ( lam "x" r
                ( Handle unit (Perform unit (EffectKey counterEff) (OpName "next") [] primUnit)
                    { element: RowEffectEntry counterEff []
                    , cells: Just layout
                    , returnClause: { binder: Ident "y", ty: int, body: var "x" }
                    , opClauses: [ fastNext (Let unit (Ident "z") r (ReadCell unit nKey) oneLit) ]
                    }
                    [ var "x" ]
                )
            )
      inferAt TRowEmpty term
        `shouldEqual` Right (TForall regionVar KType (fn r TRowEmpty r))

    it "refuses a handler naming a region as the element it handles" do
      -- `handles` reads an effect application out of the payload, and a region
      -- carries none
      inferAt TRowEmpty
        ( Handle unit oneLit
            { element: RowRegionEntry unitT TRowEmpty
            , cells: Nothing
            , returnClause: { binder: Ident "x", ty: int, body: var "x" }
            , opClauses: []
            }
            []
        )
        `shouldEqual` Left (WrongPayload RegionKey)

  describe "handlers of one key" do
    it "refuses two of them nested directly" do
      -- the inner one would stand at `( Console | ( Console ) )`
      let
        inner = Handle unit (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (LitString "x")))
          (consoleHandler unitT primUnit (pureFn unitT unitT))
          []
      inferAt TRowEmpty (Handle unit inner (consoleHandler unitT primUnit (pureFn unitT unitT)) [])
        `shouldEqual` Left (IllKindedType (NotSharp (EffectKey consoleEff) consoleRow))

    it "accepts a pure function handling the effect within itself" do
      -- no row carries `Console` twice; the two handlers meet only in the
      -- run-time stack, which `openEff` is what lets them do
      let
        handled = Handle unit (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (LitString "x")))
          (consoleHandler unitT primUnit (pureFn unitT unitT))
          []
        f = lam "u" unitT handled
        call = App unit (OpenEff unit consoleRow (var "f")) primUnit
      inferAt TRowEmpty
        ( Let unit (Ident "f") (pureFn unitT unitT) f
            (Handle unit call (consoleHandler unitT oneLit (fn unitT TRowEmpty int)) [])
        )
        `shouldEqual` Right int

  describe "an operation's own polymorphism" do
    it "aligns a clause's binders with those the declaration writes" do
      -- the declaration binds `a` and the clause binds `b`; a handler must
      -- respect the polymorphism, not the spelling
      inferAt TRowEmpty (aborting [ { name: TyVar "b", kind: KType } ] (fn (TVar (TyVar "b")) TRowEmpty int))
        `shouldEqual` Right int

    it "refuses a clause binding none where the operation binds one" do
      inferAt TRowEmpty (aborting [] (fn int TRowEmpty int))
        `shouldEqual` Left (ClauseTypeBinders (OpName "abort"))

    it "refuses a clause binding one at another kind" do
      inferAt TRowEmpty
        (aborting [ { name: TyVar "b", kind: KRow RowType } ] (fn (TVar (TyVar "b")) TRowEmpty int))
        `shouldEqual` Left (ClauseTypeBinders (OpName "abort"))

  describe "polymorphism" do
    it "checks a type abstraction against the type it is given" do
      -- the body of the abstraction is checked against the arrow the expected
      -- type writes, row and all
      let expected = TForall (TyVar "a") KType (fn int consoleRow unitT)
      checkAt TRowEmpty expected
        ( TyLam unit (TyVar "b") KType
            (lam "n" int (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (LitString "x"))))
        )
        `shouldEqual` Right unit

    it "refuses a binder introduced at another kind" do
      let expected = TForall (TyVar "a") KType (pureFn int int)
      checkAt TRowEmpty expected
        (TyLam unit (TyVar "b") (KRow RowType) (lam "n" int (var "n")))
        `shouldEqual` Left (BinderKindMismatch KType (KRow RowType))

  describe "join points" do
    it "types a jump from the definition of the join point it names" do
      inferAt TRowEmpty
        (LetJoin unit (JoinName "j") [ { name: Ident "n", ty: int } ] int (var "n") (Jump unit (JoinName "j") [ oneLit ]))
        `shouldEqual` Right int

    it "puts the root of a definition in tail position wherever the letjoin stands" do
      inferIn applied TRowEmpty
        ( App unit (var "f")
            ( LetJoin unit (JoinName "j") [ { name: Ident "n", ty: int } ] int
                (Jump unit (JoinName "j") [ var "n" ])
                oneLit
            )
        )
        `shouldEqual` Right int

    it "refuses a jump to a name no letjoin bound" do
      inferAt TRowEmpty (Jump unit (JoinName "j") [ oneLit ])
        `shouldEqual` Left (UnboundJoin (JoinName "j"))

    it "refuses a jump supplying the wrong number of arguments" do
      inferAt TRowEmpty
        ( LetJoin unit (JoinName "j") [ { name: Ident "n", ty: int } ] int (var "n")
            (Jump unit (JoinName "j") [ oneLit, oneLit ])
        )
        `shouldEqual` Left (JoinArity (JoinName "j") 1 2)

    it "refuses a jump outside tail position" do
      -- the argument of an application is not a tail position, and a jump is a
      -- transfer of control rather than something that returns a value
      inferIn applied TRowEmpty
        ( LetJoin unit (JoinName "j") [] int oneLit
            (App unit (var "f") (Jump unit (JoinName "j") []))
        )
        `shouldEqual` Left (JumpNotInTail (JoinName "j"))

    it "refuses a jump from under a lambda, the join context being discarded there" do
      -- a join point is a transfer within one function activation, so it does
      -- not cross a function boundary
      inferAt TRowEmpty
        ( LetJoin unit (JoinName "j") [] int oneLit
            (App unit (lam "u" unitT (Jump unit (JoinName "j") [])) primUnit)
        )
        `shouldEqual` Left (UnboundJoin (JoinName "j"))

  describe "recursive bindings" do
    it "refuses a right-hand side that is not a function value" do
      -- under strict evaluation `letrec x = x` has no meaning
      inferAt TRowEmpty
        (LetRec unit [ { name: Ident "x", ty: int, value: oneLit } ] (var "x"))
        `shouldEqual` Left (NotAFunctionValue (Ident "x"))

    it "accepts one that is" do
      inferAt TRowEmpty
        ( LetRec unit
            [ { name: Ident "loop", ty: pureFn int int, value: lam "n" int (var "n") } ]
            (var "loop")
        )
        `shouldEqual` Right (pureFn int int)

  describe "decision trees" do
    it "types the element of a record at a key" do
      -- a record carries one at every key of its row, so no branch establishes it
      let
        row = TRowExtend (RowTypeEntry nameKey int) TRowEmpty
        tree = Bind (Ident "y") (OccRecordField (OccScrutinee 0) nameKey) (Leaf (var "y"))
      inferIn (env { context = bindVar emptyContext (Ident "r") (record row) }) TRowEmpty
        (Case unit [ var "r" ] tree)
        `shouldEqual` Right int

    it "does not take the type of a dispatch from where a branch is written" do
      -- the first branch reaches no leaf, the second gives the type
      let
        tree = SwitchCtor (OccScrutinee 0)
          [ { ctor: value "Absurd"
            , tree: SwitchCtor (OccField (OccScrutinee 0) (value "Absurd") 0) [] Nothing
            }
          , { ctor: value "Plain", tree: Leaf oneLit }
          ]
          Nothing
      inferIn (env { context = bindVar emptyContext (Ident "w") (TCon (Qualified main (TyName "Wrap")) []) }) TRowEmpty
        (Case unit [ var "w" ] tree)
        `shouldEqual` Right int
    it "types the field of a constructor from the type of the occurrence" do
      let
        tree = SwitchCtor (OccScrutinee 0)
          [ { ctor: value "Nothing", tree: Leaf oneLit }
          , { ctor: value "Just"
            , tree: Bind (Ident "y") (OccField (OccScrutinee 0) (value "Just") 0) (Leaf (var "y"))
            }
          ]
          Nothing
      inferIn (env { context = bindVar emptyContext (Ident "m") (maybeOf int) }) TRowEmpty
        (Case unit [ var "m" ] tree)
        `shouldEqual` Right int

    it "refuses an occurrence no dispatch established" do
      -- what a constructor carries is known only under the dispatch that
      -- selected it, so the path reaches `Ω` through `switchCtor` and nowhere
      -- else
      let
        occurrence = OccField (OccScrutinee 0) (value "Just") 0
        tree = Bind (Ident "y") occurrence (Leaf (var "y"))
      inferIn (env { context = bindVar emptyContext (Ident "m") (maybeOf int) }) TRowEmpty
        (Case unit [ var "m" ] tree)
        `shouldEqual` Left (UnknownOccurrence occurrence)

    it "refuses a branch naming a constructor of another type" do
      let
        tree = SwitchCtor (OccScrutinee 0) [ { ctor: value "Plain", tree: Leaf oneLit } ] Nothing
      inferIn (env { context = bindVar emptyContext (Ident "m") (maybeOf int) }) TRowEmpty
        (Case unit [ var "m" ] tree)
        `shouldEqual` Left (NotAConstructorOf maybeTy (value "Plain"))

    it "refuses a dispatch naming one branch twice" do
      let
        branch = { ctor: value "Nothing", tree: Leaf oneLit }
        tree = SwitchCtor (OccScrutinee 0) [ branch, branch ] (Just (Leaf oneLit))
      inferIn (env { context = bindVar emptyContext (Ident "m") (maybeOf int) }) TRowEmpty
        (Case unit [ var "m" ] tree)
        `shouldEqual` Left DuplicateBranch

    it "refuses a literal dispatch over a type whose values are not literals" do
      let tree = SwitchLit (OccScrutinee 0) [] (Leaf oneLit)
      inferIn (env { context = bindVar emptyContext (Ident "m") (maybeOf int) }) TRowEmpty
        (Case unit [ var "m" ] tree)
        `shouldEqual` Left (NotALiteralType (maybeOf int))

    it "refuses a dispatch over an occurrence with no constructor at its head" do
      -- a scrutinee at a quantified type variable is the case: nothing says
      -- which constructors it has
      let tree = SwitchCtor (OccScrutinee 0) [] (Just (Leaf oneLit))
      inferIn (env { context = bindVar emptyContext (Ident "z") (TVar (TyVar "a")) }) TRowEmpty
        (Case unit [ var "z" ] tree)
        `shouldEqual` Left (UndispatchableOccurrence (OccScrutinee 0) (TVar (TyVar "a")))

    it "refuses a synthesized tree that reaches no leaf" do
      -- a type with no constructors exhausts vacuously, so the dispatch is
      -- locally total and has no leaf to take a type from. Checking the same
      -- tree against a type given from outside would succeed: this is a limit
      -- of synthesis rather than a rule of the system
      let tree = SwitchCtor (OccScrutinee 0) [] Nothing
      inferIn (env { context = bindVar emptyContext (Ident "v") (TCon (Qualified main (TyName "Void")) []) })
        TRowEmpty
        (Case unit [ var "v" ] tree)
        `shouldEqual` Left NoLeaf

    it "refuses a dispatch that is not locally total" do
      let
        tree = SwitchCtor (OccScrutinee 0) [ { ctor: value "Nothing", tree: Leaf oneLit } ] Nothing
      inferIn (env { context = bindVar emptyContext (Ident "m") (maybeOf int) }) TRowEmpty
        (Case unit [ var "m" ] tree)
        `shouldEqual` Left NotExhaustive

    it "refuses a constructor dispatch over an intrinsic type" do
      -- a type with no constructors would exhaust vacuously
      let tree = SwitchCtor (OccScrutinee 0) [] (Just (Leaf oneLit))
      inferIn (env { context = bindVar emptyContext (Ident "n") int }) TRowEmpty
        (Case unit [ var "n" ] tree)
        `shouldEqual` Left (NotADataType intTy)

    it "refines the occurrence in a default branch" do
      -- the default sees the residual variant, not the type the occurrence had
      let
        row = TRowExtend (RowTypeEntry nameKey int) (TRowExtend (RowTypeEntry sizeKey string) TRowEmpty)
        tree = SwitchKey (OccScrutinee 0)
          [ { key: nameKey, tree: Leaf (VariantInject unit nameKey oneLit) } ]
          (Just (Leaf (var "v")))
      inferIn (env { context = bindVar emptyContext (Ident "v") (variant row) }) TRowEmpty
        (Case unit [ var "v" ] tree)
        `shouldEqual` Left
          ( TypeMismatch (variant (TRowExtend (RowTypeEntry nameKey int) TRowEmpty))
              (variant row)
          )

    it "does not take the type of a guard from the branch written first" do
      -- the consequent reaches no leaf, and the alternative is what gives the
      -- type; a guard is no more ordered in this than a dispatch is
      let
        tree = SwitchCtor (OccScrutinee 0)
          [ { ctor: value "Absurd"
            , tree: Guard (Lit unit (LitBoolean true))
                (SwitchCtor (OccField (OccScrutinee 0) (value "Absurd") 0) [] Nothing)
                (Leaf oneLit)
            }
          , { ctor: value "Plain", tree: Leaf oneLit }
          ]
          Nothing
      inferIn (env { context = bindVar emptyContext (Ident "w") (TCon (Qualified main (TyName "Wrap")) []) }) TRowEmpty
        (Case unit [ var "w" ] tree)
        `shouldEqual` Right int

    it "requires a guard's condition to be a Boolean" do
      let tree = Guard oneLit (Leaf oneLit) (Leaf oneLit)
      inferIn (env { context = bindVar emptyContext (Ident "n") int }) TRowEmpty
        (Case unit [ var "n" ] tree)
        `shouldEqual` Left (TypeMismatch (TCon (Qualified (ModuleName "Prim") (TyName "Boolean")) []) int)
