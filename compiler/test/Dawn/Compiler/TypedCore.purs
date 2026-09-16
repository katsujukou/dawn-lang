-- | The AST is exercised by building the worked examples of the specification.
-- | Whether they can be written at all is what this checks; their well-typedness
-- | is the Core type checker's business.
module Test.Dawn.Compiler.TypedCore (spec) where

import Prelude

import Prim as P

import Dawn.Compiler.TypedCore (AttrValue(..), Constraint(..), Decl(..), DecisionTree(..), EffName(..), EffectDecl, Expr(..), Ident(..), Kind(..), Label(..), Literal(..), Module, ModuleName(..), OpName(..), Occurrence(..), Qualified(..), RowElemKind(..), RowEntry(..), RowKey(..), TyName(..), TyVar(..), Type(..), declAnnotation, exprAnnotation, monoScheme, rowEntryKey)
import Data.Array (index)
import Data.Maybe (Maybe(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- Names used by the examples.

prim :: ModuleName
prim = ModuleName "Prim"

main_ :: ModuleName
main_ = ModuleName "Main"

example :: ModuleName
example = ModuleName "Example"

tInt :: Type
tInt = TCon (Qualified prim (TyName "Int")) []

tUnit :: Type
tUnit = TCon (Qualified prim (TyName "Unit")) []

-- | `τ1 -{ρ}-> τ2`, that is, `Prim.Function τ1 ρ τ2`. Core has no arrow syntax.
fn :: Type -> Type -> Type -> Type
fn arg row result =
  TApp (TApp (TApp (TCon (Qualified prim (TyName "Function")) []) arg) row) result

pureFn :: Type -> Type -> Type
pureFn arg result = fn arg TRowEmpty result

listOf :: Type -> Type
listOf a = TApp (TCon (Qualified main_ (TyName "List")) []) a

nil :: Qualified Ident
nil = Qualified main_ (Ident "Nil")

cons :: Qualified Ident
cons = Qualified main_ (Ident "Cons")

sumName :: Qualified Ident
sumName = Qualified main_ (Ident "sum")

intAdd :: Qualified Ident
intAdd = Qualified prim (Ident "intAdd")

-- | The vertical slice of the Examples document. The module carries 0 and its
-- | declarations 1, 2, and 3, so that annotations are observable.
verticalSlice :: Module P.Int
verticalSlice =
  { annotation: 0
  , name: main_
  , imports: []
  , exports: []
  , decls:
      [ DeclData 1
          { name: TyName "List"
          , kindVars: []
          , params: [ { name: TyVar "a", kind: KType } ]
          , constructors:
              [ { name: Ident "Nil", tag: 0, fields: [] }
              , { name: Ident "Cons", tag: 1, fields: [ TVar (TyVar "a"), listOf (TVar (TyVar "a")) ] }
              ]
          , isNewtype: false
          , attributes: []
          }
      , DeclRec 2
          [ { name: Ident "sum"
            , scheme: monoScheme (pureFn (listOf tInt) tInt)
            , value: sumBody
            , attributes: []
            }
          ]
      , DeclNonRec 3
          { name: Ident "result"
          , scheme: monoScheme tInt
          , value: resultBody
          , attributes: []
          }
      ]
  }

sumBody :: Expr P.Int
sumBody =
  Lam 0 (Ident "xs") (listOf tInt)
    $ Case 0 [ Var 0 (Ident "xs") ]
    $
      SwitchCtor (OccScrutinee 0)
        [ { ctor: nil, tree: Leaf (Lit 0 (LitInt 0)) }
        , { ctor: cons
          , tree:
              Bind (Ident "x") (OccField (OccScrutinee 0) cons 0)
                $ Bind (Ident "ys") (OccField (OccScrutinee 0) cons 1)
                $ Leaf
                $
                  App 0
                    (App 0 (Global 0 intAdd []) (Var 0 (Ident "x")))
                    (App 0 (Global 0 sumName []) (Var 0 (Ident "ys")))
          }
        ]
        Nothing

resultBody :: Expr P.Int
resultBody =
  App 0 (Global 0 sumName []) $
    consAt 1 (consAt 2 (consAt 3 (TyApp 0 (Global 0 nil []) tInt)))
  where
  consAt :: P.Int -> Expr P.Int -> Expr P.Int
  consAt n rest =
    App 0
      (App 0 (TyApp 0 (Global 0 cons []) tInt) (Lit 0 (LitInt n)))
      rest

-- | The `Partial` handler of the Examples document, annotated with the line each
-- | node stands on, so that a traversal over annotations is observable.
toMaybe :: Expr P.Int
toMaybe =
  TyLam 1 (TyVar "e") (KRow RowEffect)
    $ ConstraintLam 2 (Lacks (EffectKey partialEff) (TVar (TyVar "e")))
    $ TyLam 3 (TyVar "a") KType
    $ Lam 4 (Ident "thunk") thunkTy
    $
      Handle 5 (App 6 (Var 7 (Ident "thunk")) (Global 8 primUnit []))
        { effect: partialEff
        , returnClause:
            { binder: Ident "x"
            , ty: TVar (TyVar "a")
            , body: App 9 (TyApp 10 (Global 11 just []) (TVar (TyVar "a"))) (Var 12 (Ident "x"))
            }
        , opClauses:
            [ { op: OpName "abort"
              , tyBinders: [ { name: TyVar "b", kind: KType } ]
              , argBinder: { name: Ident "_", ty: tUnit }
              , contBinder:
                  { name: Ident "k"
                  , ty: fn (TVar (TyVar "b")) (TVar (TyVar "e")) (maybeOf (TVar (TyVar "a")))
                  }
              , body: TyApp 13 (Global 14 nothing []) (TVar (TyVar "a"))
              }
            ]
        }
  where
  thunkTy =
    fn tUnit (TRowExtend (RowEffectEntry partialEff []) (TVar (TyVar "e"))) (TVar (TyVar "a"))

partialEff :: Qualified EffName
partialEff = Qualified prim (EffName "Partial")

primUnit :: Qualified Ident
primUnit = Qualified prim (Ident "Unit")

just :: Qualified Ident
just = Qualified example (Ident "Just")

nothing :: Qualified Ident
nothing = Qualified example (Ident "Nothing")

maybeOf :: Type -> Type
maybeOf a = TApp (TCon (Qualified example (TyName "Maybe")) []) a

-- | `effect State s where get : Unit ->* s ; put : s ->* Unit`, which binds no
-- | kind variable, as no effect constructor does.
stateEffect :: EffectDecl
stateEffect =
  { name: EffName "State"
  , params: [ { name: TyVar "s", kind: KType } ]
  , operations:
      [ { name: OpName "get", tyBinders: [], argument: tUnit, resumesWith: TVar (TyVar "s") }
      , { name: OpName "put", tyBinders: [], argument: TVar (TyVar "s"), resumesWith: tUnit }
      ]
  , attributes: []
  }

-- | The annotation of an operation clause's body, reached through the handler
-- | record rather than through a constructor field.
clauseBodyAnnotation :: forall a. Expr a -> Maybe a
clauseBodyAnnotation = case _ of
  Handle _ _ h -> map (exprAnnotation <<< _.body) (index h.opClauses 0)
  _ -> Nothing

handlerOf :: forall a. Expr a -> Maybe (Expr a)
handlerOf = case _ of
  TyLam _ _ _ e -> handlerOf e
  ConstraintLam _ _ e -> handlerOf e
  Lam _ _ _ e -> handlerOf e
  e@(Handle _ _ _) -> Just e
  _ -> Nothing

spec :: Spec Unit
spec = describe "Dawn.Compiler.TypedCore" do
  describe "the vertical slice" do
    it "is a module of three declarations" do
      map declKind verticalSlice.decls `shouldEqual` [ "data", "rec", "nonrec" ]

    it "dispatches on the tag and binds the fields in the decision tree" do
      case verticalSlice.decls `index` 1 of
        Just (DeclRec _ [ binding ]) ->
          treeShape binding.value `shouldEqual`
            Just [ "switchCtor Main.Nil", "switchCtor Main.Cons" ]
        _ -> "expected a rec group of one binding" `shouldEqual` "…"

    it "exhausts the constructors, so no default branch is present" do
      case verticalSlice.decls `index` 1 of
        Just (DeclRec _ [ binding ]) -> hasDefault binding.value `shouldEqual` Just false
        _ -> "expected a rec group of one binding" `shouldEqual` "…"

  describe "annotations" do
    it "are read off any expression node" do
      exprAnnotation toMaybe `shouldEqual` 1

    it "are carried by a declaration and by the module itself" do
      verticalSlice.annotation `shouldEqual` 0
      map declAnnotation verticalSlice.decls `shouldEqual` [ 1, 2, 3 ]

    it "are mapped inside a handler's clauses, which sit behind a record" do
      clauseBodyAnnotation (handlerOf' toMaybe) `shouldEqual` Just 13
      clauseBodyAnnotation (handlerOf' (void toMaybe)) `shouldEqual` Just unit

  describe "effect declarations" do
    it "give an operation an argument and a resumption type, not a function type" do
      map _.argument stateEffect.operations `shouldEqual` [ tUnit, TVar (TyVar "s") ]
      map _.resumesWith stateEffect.operations `shouldEqual` [ TVar (TyVar "s"), tUnit ]

  describe "row keys" do
    it "come from the written label at Row Type" do
      rowEntryKey (RowField (Label "name") tInt) `shouldEqual` FieldKey (Label "name")

    it "come from the head constructor at Row Effect, which carries no label" do
      rowEntryKey (RowEffectEntry partialEff []) `shouldEqual` EffectKey partialEff

  describe "attributes" do
    it "carry a key and a structured value, and nothing the checker reads" do
      let attr = { key: "typeclass.instance", value: AttrObject [ { key: "priority", value: AttrInt 0 } ] }
      attr.value `shouldEqual` AttrObject [ { key: "priority", value: AttrInt 0 } ]

-- Helpers that summarise a structure as something comparable.

handlerOf' :: forall a. Expr a -> Expr a
handlerOf' e = case handlerOf e of
  Just h -> h
  Nothing -> e

declKind :: forall a. Decl a -> P.String
declKind = case _ of
  DeclData _ _ -> "data"
  DeclEffect _ _ -> "effect"
  DeclForeign _ _ -> "foreign"
  DeclNonRec _ _ -> "nonrec"
  DeclRec _ _ -> "rec"

treeShape :: forall a. Expr a -> Maybe (P.Array P.String)
treeShape = case _ of
  Lam _ _ _ (Case _ _ (SwitchCtor _ branches _)) ->
    Just (map (\b -> "switchCtor " <> showQualified b.ctor) branches)
  _ -> Nothing

hasDefault :: forall a. Expr a -> Maybe P.Boolean
hasDefault = case _ of
  Lam _ _ _ (Case _ _ (SwitchCtor _ _ def)) ->
    Just case def of
      Just _ -> true
      Nothing -> false
  _ -> Nothing

showQualified :: Qualified Ident -> P.String
showQualified (Qualified (ModuleName m) (Ident n)) = m <> "." <> n
