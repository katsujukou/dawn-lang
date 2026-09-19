-- | Term typing.
-- |
-- | The cases the Implementation Plan singles out are here: an arrow's row
-- | against the ambient row, the value restriction, what a `perform` reads its
-- | signature from, and the local totality of a dispatch.
module Test.Dawn.Compiler.TypedCore.Check (spec) where

import Prelude

import Prim as P

import Dawn.Compiler.TypedCore (Decl(..), DecisionTree(..), EffName(..), Expr(..), Handler, Ident(..), JoinName(..), Kind(..), Literal(..), Module, ModuleName(..), Occurrence(..), OpName(..), Qualified(..), RowElemKind(..), RowEntry(..), RowKey(..), Symbol(..), TyName(..), TyVar(..), Type(..))
import Dawn.Compiler.TypedCore.Check (CheckError(..), Env, check, envOf, infer)
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
  Right ty -> Right ty

inferIn :: Env -> Type -> Expr Unit -> Either CheckError Type
inferIn e rho expr = case infer e rho expr of
  Left failure -> Left failure.error
  Right ty -> Right ty

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

-- | `handle (perform Fail.abort [Int] ()) with { handles Fail ; … }`, with the
-- | binders and the continuation type of the clause supplied.
aborting :: P.Array { name :: TyVar, kind :: Kind } -> Type -> Expr Unit
aborting tyBinders contType =
  Handle unit (Perform unit (EffectKey failEff) (OpName "abort") [ int ] primUnit)
    { element: RowEffectEntry failEff []
    , returnClause: { binder: Ident "x", ty: int, body: oneLit }
    , opClauses:
        [ { op: OpName "abort"
          , tyBinders
          , argBinder: { name: Ident "u", ty: unitT }
          , contBinder: { name: Ident "k", ty: contType }
          , body: oneLit
          }
        ]
    }

-- | `{ handles Console ; return (x : α) -> e ; log (s, k) -> 1 }`, with the
-- | return type, the return body, and the continuation type supplied.
consoleHandler :: Type -> Expr Unit -> Type -> Handler Unit
consoleHandler alpha returned contType =
  { element: RowEffectEntry consoleEff []
  , returnClause: { binder: Ident "x", ty: alpha, body: returned }
  , opClauses:
      [ { op: OpName "log"
        , tyBinders: []
        , argBinder: { name: Ident "s", ty: string }
        , contBinder: { name: Ident "k", ty: contType }
        , body: returned
        }
      ]
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
        ( RecordUpdate unit nameKey (Lit unit (LitString "s"))
            (RecordExtend unit nameKey oneLit emptyRecord)
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

  describe "handlers" do
    it "removes the element the handler writes" do
      -- effect safety is not "no operation is performed": the row outside the
      -- handle carries nothing
      inferAt TRowEmpty
        ( Handle unit (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (LitString "x")))
            { element: RowEffectEntry consoleEff []
            , returnClause: { binder: Ident "x", ty: unitT, body: oneLit }
            , opClauses:
                [ { op: OpName "log"
                  , tyBinders: []
                  , argBinder: { name: Ident "s", ty: string }
                  , contBinder: { name: Ident "k", ty: pureFn unitT int }
                  , body: oneLit
                  }
                ]
            }
        )
        `shouldEqual` Right int

    it "requires a clause for every operation of the effect" do
      inferAt TRowEmpty
        ( Handle unit (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (LitString "x")))
            { element: RowEffectEntry consoleEff []
            , returnClause: { binder: Ident "x", ty: unitT, body: oneLit }
            , opClauses: []
            }
        )
        `shouldEqual` Left (MissingClause consoleEff (OpName "log"))

    it "gives the continuation the row outside the handle and the result of it" do
      -- a shallow handler would resume at the inner row and the inner result
      inferAt TRowEmpty
        ( Handle unit (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (LitString "x")))
            { element: RowEffectEntry consoleEff []
            , returnClause: { binder: Ident "x", ty: unitT, body: oneLit }
            , opClauses:
                [ { op: OpName "log"
                  , tyBinders: []
                  , argBinder: { name: Ident "s", ty: string }
                  , contBinder: { name: Ident "k", ty: pureFn unitT string }
                  , body: oneLit
                  }
                ]
            }
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
            , returnClause: { binder: Ident "x", ty: int, body: oneLit }
            , opClauses:
                [ { op: OpName "get"
                  , tyBinders: []
                  , argBinder: { name: Ident "u", ty: unitT }
                  , contBinder: { name: Ident "k", ty: fn int counterRow int }
                  , body: oneLit
                  }
                , { op: OpName "put"
                  , tyBinders: []
                  , argBinder: { name: Ident "v", ty: int }
                  , contBinder: { name: Ident "k", ty: fn unitT counterRow int }
                  , body: oneLit
                  }
                ]
            }
        )
        `shouldEqual` Right int

  describe "handlers of one key" do
    it "refuses two of them nested directly" do
      -- the inner one would stand at `( Console | ( Console ) )`
      let
        inner = Handle unit (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (LitString "x")))
          (consoleHandler unitT primUnit (pureFn unitT unitT))
      inferAt TRowEmpty (Handle unit inner (consoleHandler unitT primUnit (pureFn unitT unitT)))
        `shouldEqual` Left (IllKindedType (NotSharp (EffectKey consoleEff) consoleRow))

    it "accepts a pure function handling the effect within itself" do
      -- no row carries `Console` twice; the two handlers meet only in the
      -- run-time stack, which `openEff` is what lets them do
      let
        handled = Handle unit (Perform unit (EffectKey consoleEff) (OpName "log") [] (Lit unit (LitString "x")))
          (consoleHandler unitT primUnit (pureFn unitT unitT))
        f = lam "u" unitT handled
        call = App unit (OpenEff unit consoleRow (var "f")) primUnit
      inferAt TRowEmpty
        ( Let unit (Ident "f") (pureFn unitT unitT) f
            (Handle unit call (consoleHandler unitT oneLit (fn unitT TRowEmpty int)))
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
