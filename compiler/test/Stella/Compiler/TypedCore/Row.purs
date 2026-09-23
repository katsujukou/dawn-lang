-- | Row normalization, type equality, and entailment.
-- |
-- | The cases marked "(step 2)" in the regression catalogue of the
-- | Implementation Plan are covered here, together with the worked normal forms
-- | of the Rows document. Each is a case in which a plausible implementation
-- | gives the wrong answer.
module Test.Stella.Compiler.TypedCore.Row (spec) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore (Constraint(..), DecomposeError(..), EffName(..), Kind(..), ModuleName(..), Qualified(..), RowElemKind(..), RowEntry(..), RowError(..), RowKey(..), RowPayload(..), Symbol(..), Tag(..), TyName(..), TyVar(..), Type(..), constraintEquiv, decompose, entails, nf, noFacts, rowEquiv, typeEquiv)
import Data.Either (Either(..))
import Data.Map as Map
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

prim :: ModuleName
prim = ModuleName "Prim"

tInt :: Type
tInt = TCon (Qualified prim (TyName "Int")) []

tString :: Type
tString = TCon (Qualified prim (TyName "String")) []

name :: Symbol
name = Symbol "name"

age :: Symbol
age = Symbol "age"

cache :: Symbol
cache = Symbol "cache"

counter :: Symbol
counter = Symbol "counter"

-- | One spelling, used as both a `Symbol` and a `Tag`.
spelled :: P.String
spelled = "X"

consoleEff :: Qualified EffName
consoleEff = Qualified prim (EffName "Console")

stateEff :: Qualified EffName
stateEff = Qualified prim (EffName "State")

readerEff :: Qualified EffName
readerEff = Qualified prim (EffName "Reader")

r :: TyVar
r = TyVar "r"

s :: TyVar
s = TyVar "s"

e :: TyVar
e = TyVar "e"

-- | `( l : τ | ρ )`
field :: Symbol -> Type -> Type -> Type
field l ty rest = TRowExtend (RowTypeEntry (SymbolKey l) ty) rest

-- | `( E τ̄ | ρ )`
effect :: Qualified EffName -> P.Array Type -> Type -> Type
effect eff args rest = TRowExtend (RowEffectEntry eff args) rest

-- | `( s : E τ̄ | ρ )`
labelledEffect :: Symbol -> Qualified EffName -> P.Array Type -> Type -> Type
labelledEffect s' eff args rest = TRowExtend (RowLabelledEffectEntry s' eff args) rest

-- | `( TagKey t : τ | ρ )`
variant :: Tag -> Type -> Type -> Type
variant t ty rest = TRowExtend (RowTypeEntry (TagKey t) ty) rest

-- | `( PositionKey n : τ | ρ )`
component :: P.Int -> Type -> Type -> Type
component n ty rest = TRowExtend (RowTypeEntry (PositionKey n) ty) rest

closed :: Symbol -> Type -> Type
closed l ty = field l ty TRowEmpty

spec :: Spec Unit
spec = describe "Stella.Compiler.TypedCore.Row" do
  describe "normalization" do
    it "collects known fields and leaves the tail open" do
      -- nf( ( name : String | r ) ⊎ ( age : Int ) )
      nf (TRowUnion (field name tString (TVar r)) (closed age tInt)) `shouldEqual`
        Right
          { known: Map.fromFoldable
              [ Tuple (SymbolKey name) (TypePayload tString)
              , Tuple (SymbolKey age) (TypePayload tInt)
              ]
          , tail: Set.singleton r
          }

    it "derives an effect key from the head constructor, with the arguments as payload" do
      -- nf( ( Console | e ) ⊎ ( State Int ) )
      nf (TRowUnion (effect consoleEff [] (TVar e)) (effect stateEff [ tInt ] TRowEmpty)) `shouldEqual`
        Right
          { known: Map.fromFoldable
              [ Tuple (EffectKey consoleEff) (EffectPayload consoleEff [])
              , Tuple (EffectKey stateEff) (EffectPayload stateEff [ tInt ])
              ]
          , tail: Set.singleton e
          }

    it "rejects a repeated key, which sharpness forbids" do
      nf (field name tString (closed name tInt)) `shouldEqual` Left (DuplicateKey (SymbolKey name))

    it "absorbs a repeated row variable, leaving `r # r` to reject it" do
      -- `r ⊎ r` normalizes; what rejects it is the disjointness side condition
      nf (TRowUnion (TVar r) (TVar r)) `shouldEqual`
        Right { known: Map.empty, tail: Set.singleton r }

  describe "keys" do
    it "separates a Symbol from a Tag of the same spelling" do
      -- `( SymbolKey X : Int, TagKey X : Int )`: one spelling, two keys
      nf (field (Symbol spelled) tInt (variant (Tag spelled) tInt TRowEmpty)) `shouldEqual`
        Right
          { known: Map.fromFoldable
              [ Tuple (SymbolKey (Symbol spelled)) (TypePayload tInt)
              , Tuple (TagKey (Tag spelled)) (TypePayload tInt)
              ]
          , tail: Set.empty
          }

    it "keys a tuple by position" do
      nf (component 0 tInt (component 1 tString TRowEmpty)) `shouldEqual`
        Right
          { known: Map.fromFoldable
              [ Tuple (PositionKey 0) (TypePayload tInt)
              , Tuple (PositionKey 1) (TypePayload tString)
              ]
          , tail: Set.empty
          }

    it "admits one effect twice where the keys are written" do
      -- `( cache : State Int, counter : State Int )`
      nf (labelledEffect cache stateEff [ tInt ] (labelledEffect counter stateEff [ tInt ] TRowEmpty))
        `shouldEqual`
          Right
            { known: Map.fromFoldable
                [ Tuple (SymbolKey cache) (EffectPayload stateEff [ tInt ])
                , Tuple (SymbolKey counter) (EffectPayload stateEff [ tInt ])
                ]
            , tail: Set.empty
            }

    it "rejects a written key twice, whatever the payloads" do
      nf (labelledEffect cache stateEff [ tInt ] (labelledEffect cache stateEff [ tString ] TRowEmpty))
        `shouldEqual` Left (DuplicateKey (SymbolKey cache))

    it "rejects one effect twice where no key is written" do
      -- Both elements derive `EffectKey State`
      nf (effect stateEff [ tInt ] (effect stateEff [ tString ] TRowEmpty))
        `shouldEqual` Left (DuplicateKey (EffectKey stateEff))

    it "compares the payload, which a written key leaves free" do
      -- The key selects the element; the payload decides the protocol, so two
      -- elements can agree on the key and still carry different effects
      rowEquiv
        (labelledEffect cache stateEff [ tInt ] TRowEmpty)
        (labelledEffect cache readerEff [ tInt ] TRowEmpty)
        `shouldEqual` Right false

  describe "equality" do
    it "ignores the order in which fields were written" do
      rowEquiv
        (TRowUnion (field name tString (TVar r)) (closed age tInt))
        (field age tInt (field name tString (TVar r)))
        `shouldEqual` Right true

    it "treats the tail as a set" do
      -- ⟨∅;{r,s}⟩ ≡ ⟨∅;{s,r}⟩
      rowEquiv (TRowUnion (TVar r) (TVar s)) (TRowUnion (TVar s) (TVar r))
        `shouldEqual` Right true

    it "does not identify distinct row variables" do
      -- ( name : String | r ) and ( name : String | s ) are different rows
      rowEquiv (field name tString (TVar r)) (field name tString (TVar s))
        `shouldEqual` Right false

    it "distinguishes a closed row from an open one" do
      rowEquiv (closed name tString) (field name tString (TVar r))
        `shouldEqual` Right false

    it "compares payloads" do
      rowEquiv (closed name tString) (closed name tInt) `shouldEqual` Right false

    it "identifies types that differ only in the names they bind" do
      typeEquiv
        (TForall r (KRow RowType) (field name tString (TVar r)))
        (TForall s (KRow RowType) (field name tString (TVar s)))
        `shouldEqual` Right true

    it "keeps a bound variable distinct from a free one of the same name" do
      typeEquiv
        (TForall r (KRow RowType) (TVar r))
        (TForall s (KRow RowType) (TVar r))
        `shouldEqual` Right false

    it "separates binders of different kinds" do
      typeEquiv
        (TForall r (KRow RowType) tInt)
        (TForall r (KRow RowEffect) tInt)
        `shouldEqual` Right false

    it "reports a comparison outside its domain rather than answering false" do
      -- Deciding `≡` presupposes `Γ ⊢ τ1 : κ` and `Γ ⊢ τ2 : κ`; answering
      -- `false` here would let a kinding lapse pass for an ordinary mismatch
      typeEquiv TRowEmpty tInt `shouldEqual` Left (NotARow tInt)

    it "compares a constraint structurally, so `#` is not symmetric here" do
      -- `r # s` and `s # r` entail each other, but definitional equality is
      -- structural: adapting one to the other is `Λ (_ : s # r). e [•]`
      constraintEquiv (Disjoint (TVar r) (TVar s)) (Disjoint (TVar s) (TVar r))
        `shouldEqual` Right false
      constraintEquiv (Disjoint (TVar r) (TVar s)) (Disjoint (TVar r) (TVar s))
        `shouldEqual` Right true

  describe "entailment" do
    it "holds of the empty row without any assumption" do
      entails noFacts (Lacks (SymbolKey name) TRowEmpty) `shouldEqual` Right true
      entails noFacts (Disjoint (TVar r) TRowEmpty) `shouldEqual` Right true

    it "fails on a known key, whatever is assumed" do
      entails noFacts (Lacks (SymbolKey name) (closed name tString)) `shouldEqual` Right false

    it "needs an assumption to see past an unknown tail" do
      entails noFacts (Lacks (SymbolKey name) (TVar r)) `shouldEqual` Right false
      case decompose [ Lacks (SymbolKey name) (TVar r) ] of
        Right facts -> entails facts (Lacks (SymbolKey name) (TVar r)) `shouldEqual` Right true
        Left err -> show err `shouldEqual` "no error"

    it "decomposes an assumption over a composite row" do
      -- `name ∉ ( age : Int | r )` yields the atomic fact `name ∉ r`
      case decompose [ Lacks (SymbolKey name) (field age tInt (TVar r)) ] of
        Right facts -> entails facts (Lacks (SymbolKey name) (TVar r)) `shouldEqual` Right true
        Left err -> show err `shouldEqual` "no error"

    it "derives the lacks facts a disjointness assumption implies" do
      -- `( name : String | r ) # s` yields `name ∉ s` and `r # s`
      case decompose [ Disjoint (field name tString (TVar r)) (TVar s) ] of
        Right facts -> do
          entails facts (Lacks (SymbolKey name) (TVar s)) `shouldEqual` Right true
          entails facts (Disjoint (TVar r) (TVar s)) `shouldEqual` Right true
        Left err -> show err `shouldEqual` "no error"

    it "closes `#` under symmetry, and nothing else" do
      case decompose [ Disjoint (TVar r) (TVar s) ] of
        Right facts -> do
          entails facts (Disjoint (TVar s) (TVar r)) `shouldEqual` Right true
          entails facts (Disjoint (TVar r) (TVar e)) `shouldEqual` Right false
        Left err -> show err `shouldEqual` "no error"

    it "does not derive `r # r` from nothing, which is what makes `r ⊎ r` ill-kinded" do
      entails noFacts (Disjoint (TVar r) (TVar r)) `shouldEqual` Right false
      case decompose [ Disjoint (TVar r) (TVar s) ] of
        Right facts -> entails facts (Disjoint (TVar r) (TVar r)) `shouldEqual` Right false
        Left err -> show err `shouldEqual` "no error"

    it "derives `r # r` where it is assumed, since an assumption entails itself" do
      -- `r # r` is satisfiable: it constrains `r` to the empty row
      case decompose [ Disjoint (TVar r) (TVar r) ] of
        Right facts -> entails facts (Disjoint (TVar r) (TVar r)) `shouldEqual` Right true
        Left err -> show err `shouldEqual` "no error"

    it "stops at `r # r` and does not pursue what it implies" do
      -- Entailment is sound for the set-theoretic reading of rows and
      -- intentionally incomplete: `r` being empty is a consequence the relation
      -- does not carry, and a solver that grew helpful here would lose that
      case decompose [ Disjoint (TVar r) (TVar r) ] of
        Right facts -> do
          entails facts (Lacks (SymbolKey name) (TVar r)) `shouldEqual` Right false
          entails facts (Disjoint (TVar r) (TVar s)) `shouldEqual` Right false
        Left err -> show err `shouldEqual` "no error"

    it "keeps assumptions about one variable together" do
      case decompose [ Lacks (SymbolKey name) (TVar r), Lacks (SymbolKey age) (TVar r) ] of
        Right facts -> do
          entails facts (Lacks (SymbolKey name) (TVar r)) `shouldEqual` Right true
          entails facts (Lacks (SymbolKey age) (TVar r)) `shouldEqual` Right true
        Left err -> show err `shouldEqual` "no error"

    it "reports an assumption that contradicts itself" do
      decompose [ Lacks (SymbolKey name) (closed name tString) ]
        `shouldEqual` Left (LacksContradiction (SymbolKey name))
      decompose [ Disjoint (closed name tString) (closed name tInt) ]
        `shouldEqual` Left (DisjointContradiction (SymbolKey name))

    it "decides an effect row by the same rules" do
      case decompose [ Lacks (EffectKey consoleEff) (TVar e) ] of
        Right facts -> do
          entails facts (Lacks (EffectKey consoleEff) (TVar e)) `shouldEqual` Right true
          entails facts (Lacks (EffectKey stateEff) (TVar e)) `shouldEqual` Right false
        Left err -> show err `shouldEqual` "no error"

