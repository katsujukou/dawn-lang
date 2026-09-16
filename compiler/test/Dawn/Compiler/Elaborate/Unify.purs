-- | Row unification.
-- |
-- | The three cases the Implementation Plan singles out are here: refinement of
-- | two flexible tails through a fresh one, the rigid/flexible asymmetry, and a
-- | constraint with two flexible tails on one side, which waits rather than
-- | fails.
module Test.Dawn.Compiler.Elaborate.Unify (spec) where

import Prelude

import Prim as P

import Dawn.Compiler.Elaborate.Row (xnf)
import Dawn.Compiler.Elaborate.Type (MetaVar, XConstraint(..), XRowEntry(..), XType(..))
import Dawn.Compiler.Elaborate.Unify (MetaBinding(..), MetaContext, MetaInfo, UnifyError(..), UnifyResult(..), emptyContext, freshMeta, lookupMeta, substitute, unifyRow)
import Dawn.Compiler.TypedCore (Constraint(..), Kind(..), KindVar(..), Label(..), ModuleName(..), Qualified(..), RowElemKind(..), RowKey(..), TyName(..), TyVar(..), Type(..))
import Dawn.Compiler.TypedCore.Entailment (AtomicFacts, decompose, noFacts)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..), fst, snd)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

prim :: ModuleName
prim = ModuleName "Prim"

tA :: XType
tA = XCon (Qualified prim (TyName "A")) []

tB :: XType
tB = XCon (Qualified prim (TyName "B")) []

a :: Label
a = Label "a"

b :: Label
b = Label "b"

rigidR :: TyVar
rigidR = TyVar "r"

-- | `( l : τ | ρ )`
field :: Label -> XType -> XType -> XType
field l ty rest = XRowExtend (XRowField l ty) rest

-- | A metavariable created where `r` is in scope, which is what the escape
-- | check compares a solution against.
rowTypeInfo :: MetaInfo
rowTypeInfo =
  { kind: KRow RowType
  , scope: { types: Set.singleton rigidR, kinds: Set.empty }
  , lacks: Set.empty
  , disjointFrom: Set.empty
  }

lacking :: P.Array RowKey -> MetaInfo
lacking keys = rowTypeInfo { lacks = Set.fromFoldable keys }

-- | `Γ*` with nothing assumed, which is what most of these cases unify under.
noAssumptions :: AtomicFacts
noAssumptions = noFacts

-- | `Γ*` built from the row constraints a case assumes.
assuming :: P.Array Constraint -> AtomicFacts
assuming cs = case decompose cs of
  Right facts -> facts
  Left _ -> noFacts

-- | Two fresh metavariables over an empty context.
twoMetas :: MetaInfo -> MetaInfo -> { r :: MetaVar, s :: MetaVar, ctx :: MetaContext }
twoMetas infoR infoS =
  let
    first = freshMeta infoR emptyContext
    second = freshMeta infoS (snd first)
  in
    { r: fst first, s: fst second, ctx: snd second }

solutionOf :: MetaContext -> MetaVar -> Maybe XType
solutionOf ctx m = case lookupMeta ctx m of
  Just (Assigned ty) -> Just (substitute ctx ty)
  _ -> Nothing

-- | The known keys of a solved row, which is what the refinement cases assert.
knownKeysOf :: MetaContext -> MetaVar -> Maybe (P.Array RowKey)
knownKeysOf ctx m = case solutionOf ctx m of
  Nothing -> Nothing
  Just ty -> case xnf ty of
    Left _ -> Nothing
    Right n -> Just (Set.toUnfoldable (Set.fromFoldable (Map.keys n.known)))

-- | The flexible tail of a solved row.
tailOf :: MetaContext -> MetaVar -> Maybe (P.Array MetaVar)
tailOf ctx m = case solutionOf ctx m of
  Nothing -> Nothing
  Just ty -> case xnf ty of
    Left _ -> Nothing
    Right n -> Just (Set.toUnfoldable n.flexible)

spec :: Spec Unit
spec = describe "Dawn.Compiler.Elaborate.Unify" do
  describe "two flexible tails" do
    it "refines both sides through one fresh tail" do
      -- { a : A | ?r } ≡ { b : B | ?s }
      --   ?r := ( b : B | ?t )   and   ?s := ( a : A | ?t )
      let
        m = twoMetas rowTypeInfo rowTypeInfo
        result = unifyRow noAssumptions m.ctx (field a tA (XMeta m.r)) (field b tB (XMeta m.s))
      case fst result of
        Solved ctx -> do
          knownKeysOf ctx m.r `shouldEqual` Just [ FieldKey b ]
          knownKeysOf ctx m.s `shouldEqual` Just [ FieldKey a ]
          -- the same fresh tail stands on both sides
          (tailOf ctx m.r == tailOf ctx m.s) `shouldEqual` true
          map Array.length (tailOf ctx m.r) `shouldEqual` Just 1
        other -> show other `shouldEqual` "Solved"

    it "carries the Lacks of both sides onto the fresh tail" do
      -- Lacks(?t) ⊇ dom(D1) ∪ dom(D2) ∪ Lacks(?r) ∪ Lacks(?s)
      let
        m = twoMetas (lacking [ FieldKey (Label "x") ]) rowTypeInfo
        result = unifyRow noAssumptions m.ctx (field a tA (XMeta m.r)) (field b tB (XMeta m.s))
      case fst result of
        Solved ctx ->
          case tailOf ctx m.r of
            Just [ t ] -> case lookupMeta ctx t of
              Just (Unsolved info) -> do
                Set.member (FieldKey (Label "x")) info.lacks `shouldEqual` true
                Set.member (FieldKey a) info.lacks `shouldEqual` true
                Set.member (FieldKey b) info.lacks `shouldEqual` true
              _ -> "the fresh tail is unsolved" `shouldEqual` "…"
            _ -> "one fresh tail" `shouldEqual` "…"
        other -> show other `shouldEqual` "Solved"

  describe "rigid and flexible tails" do
    it "lets a flexible tail absorb a rigid one" do
      -- ?s ≡ ( a : A | r ) succeeds: `r` is rigid but the other side can take it
      let
        m = twoMetas rowTypeInfo rowTypeInfo
        result = unifyRow noAssumptions m.ctx (XMeta m.s) (field a tA (XVar rigidR))
      case fst result of
        Solved ctx -> knownKeysOf ctx m.s `shouldEqual` Just [ FieldKey a ]
        other -> show other `shouldEqual` "Solved"

    it "does not let a rigid tail absorb a known field" do
      -- `forall (r : Row Type). r ≡ ( a : A )` fails: `r` is not assignable
      let result = unifyRow noAssumptions emptyContext (XVar rigidR) (field a tA XRowEmpty)
      case fst result of
        Mismatch (RigidTailRemains vars) -> Set.member rigidR vars `shouldEqual` true
        other -> show other `shouldEqual` "Mismatch (RigidTailRemains …)"

    it "does not identify two distinct rigid tails" do
      -- ( a : A | r ) ≡ ( a : A | s ) fails: they stand for different unknowns
      let
        other = TyVar "s"
        result = unifyRow noAssumptions emptyContext (field a tA (XVar rigidR)) (field a tA (XVar other))
      case fst result of
        Mismatch (RigidTailRemains vars) -> do
          Set.member rigidR vars `shouldEqual` true
          Set.member other vars `shouldEqual` true
        outcome -> show outcome `shouldEqual` "Mismatch (RigidTailRemains …)"

    it "cancels a rigid tail the two sides share" do
      -- ( a : A | r ) ≡ ( a : A | r )
      let
        row = field a tA (XVar rigidR)
        result = unifyRow noAssumptions emptyContext row row
      case fst result of
        Solved _ -> pure unit
        other -> show other `shouldEqual` "Solved"

  describe "waiting rather than failing" do
    it "is stuck when one side has two flexible tails" do
      -- ⟨∅;{?r,?s}⟩ ≡ ⟨{a↦A};∅⟩ has two solutions, so it waits
      let
        m = twoMetas rowTypeInfo rowTypeInfo
        result = unifyRow noAssumptions m.ctx (XRowUnion (XMeta m.r) (XMeta m.s)) (field a tA XRowEmpty)
      case fst result of
        Stuck waiting -> do
          Set.member m.r waiting `shouldEqual` true
          Set.member m.s waiting `shouldEqual` true
        other -> show other `shouldEqual` "Stuck"

    it "distinguishes waiting from a mismatch" do
      -- one flexible tail and a leftover on the determined side is a failure
      let
        m = twoMetas rowTypeInfo rowTypeInfo
        result = unifyRow noAssumptions m.ctx (field a tA XRowEmpty) (field b tB (XMeta m.s))
      case fst result of
        Mismatch _ -> pure unit
        other -> show other `shouldEqual` "Mismatch"

  describe "what a substitution must preserve" do
    it "refuses a solution carrying a key the metavariable lacks" do
      -- `a ∉ ?s` assumed, so `?s := ( a : A )` is refused
      let
        m = twoMetas rowTypeInfo (lacking [ FieldKey a ])
        result = unifyRow noAssumptions m.ctx (XMeta m.s) (field a tA XRowEmpty)
      case fst result of
        Mismatch (LacksViolated key) -> key `shouldEqual` FieldKey a
        other -> show other `shouldEqual` "Mismatch (LacksViolated …)"

    it "refuses a solution of the wrong row kind" do
      let
        effectInfo = rowTypeInfo { kind = KRow RowEffect }
        m = twoMetas rowTypeInfo effectInfo
        result = unifyRow noAssumptions m.ctx (XMeta m.s) (field a tA XRowEmpty)
      case fst result of
        Mismatch (KindMismatch _ expected actual) -> do
          expected `shouldEqual` KRow RowEffect
          actual `shouldEqual` KRow RowType
        other -> show other `shouldEqual` "Mismatch (KindMismatch …)"

    it "refuses a solution mentioning a variable bound inside the metavariable" do
      -- `?m` was created where only `r` is in scope, so a variable bound further
      -- in must not escape into it
      let
        inner = TyVar "inner"
        m = twoMetas rowTypeInfo rowTypeInfo
        result = unifyRow noAssumptions m.ctx (XMeta m.s) (field a tA (XVar inner))
      case fst result of
        Mismatch (EscapingVariable _ escaping) -> escaping `shouldEqual` inner
        other -> show other `shouldEqual` "Mismatch (EscapingVariable …)"

    it "refuses a rigid tail the context does not prove the Lacks of" do
      -- `a ∉ ?m` assumed of the metavariable, nothing assumed of `r`
      let
        m = twoMetas rowTypeInfo (lacking [ FieldKey a ])
        result = unifyRow noAssumptions m.ctx (XMeta m.s) (XVar rigidR)
      case fst result of
        Mismatch (LacksUnproven key t) -> do
          key `shouldEqual` FieldKey a
          t `shouldEqual` rigidR
        other -> show other `shouldEqual` "Mismatch (LacksUnproven …)"

    it "accepts that rigid tail once the context proves it" do
      let
        m = twoMetas rowTypeInfo (lacking [ FieldKey a ])
        facts = assuming [ Lacks (FieldKey a) (TVar rigidR) ]
        result = unifyRow facts m.ctx (XMeta m.s) (XVar rigidR)
      case fst result of
        Solved _ -> pure unit
        other -> show other `shouldEqual` "Solved"

    it "refuses a rigid tail it is assumed to be disjoint from" do
      -- `?t # r` recorded, so `?t := r` would build `r ⊎ r`
      let
        m = twoMetas rowTypeInfo (rowTypeInfo { disjointFrom = Set.singleton rigidR })
        result = unifyRow noAssumptions m.ctx (XMeta m.s) (XVar rigidR)
      case fst result of
        Mismatch (DisjointUnproven t u) -> do
          t `shouldEqual` rigidR
          u `shouldEqual` rigidR
        other -> show other `shouldEqual` "Mismatch (DisjointUnproven …)"

    it "refuses a known key the context cannot prove absent from a disjoint tail" do
      -- `?m # r` solved to `( a : A )` needs `a ∉ r`, which nothing gives
      let
        m = twoMetas rowTypeInfo (rowTypeInfo { disjointFrom = Set.singleton rigidR })
        result = unifyRow noAssumptions m.ctx (XMeta m.s) (field a tA XRowEmpty)
      case fst result of
        Mismatch (LacksUnproven key u) -> do
          key `shouldEqual` FieldKey a
          u `shouldEqual` rigidR
        other -> show other `shouldEqual` "Mismatch (LacksUnproven …)"

    it "accepts that known key once the context proves it absent" do
      let
        m = twoMetas rowTypeInfo (rowTypeInfo { disjointFrom = Set.singleton rigidR })
        facts = assuming [ Lacks (FieldKey a) (TVar rigidR) ]
        result = unifyRow facts m.ctx (XMeta m.s) (field a tA XRowEmpty)
      case fst result of
        Solved _ -> pure unit
        other -> show other `shouldEqual` "Solved"

    it "refuses a refinement whose fresh tail would leave a variable out of scope" do
      -- `?s` was created outside `r`, `?q` inside it; the fresh tail would have
      -- to be disjoint from `r` while standing where `?s` stands
      let
        outer = rowTypeInfo { scope = { types: Set.empty, kinds: Set.empty } }
        inner = rowTypeInfo
        m = twoMetas outer inner
        result = unifyRow noAssumptions m.ctx (XRowUnion (XMeta m.r) (XVar rigidR)) (XMeta m.s)
      case fst result of
        Mismatch (FreshTailOutOfScope escaping) -> escaping `shouldEqual` rigidR
        other -> show other `shouldEqual` "Mismatch (FreshTailOutOfScope …)"

    it "refuses a solution mentioning a kind variable out of scope" do
      -- `[Γ]` covers kind variables too, which reach a type through the kind
      -- arguments of a constructor
      let
        k = KindVar "k"
        m = twoMetas rowTypeInfo rowTypeInfo
        proxied = XCon (Qualified prim (TyName "Proxy")) [ KVar k ]
        result = unifyRow noAssumptions m.ctx (XMeta m.s) (field a proxied XRowEmpty)
      case fst result of
        Mismatch (EscapingKindVariable _ escaping) -> escaping `shouldEqual` k
        other -> show other `shouldEqual` "Mismatch (EscapingKindVariable …)"

    it "accepts that kind variable when the metavariable was created under it" do
      let
        k = KindVar "k"
        info = rowTypeInfo { scope = { types: Set.singleton rigidR, kinds: Set.singleton k } }
        m = twoMetas rowTypeInfo info
        proxied = XCon (Qualified prim (TyName "Proxy")) [ KVar k ]
        result = unifyRow noAssumptions m.ctx (XMeta m.s) (field a proxied XRowEmpty)
      case fst result of
        Solved _ -> pure unit
        other -> show other `shouldEqual` "Solved"

    it "substitutes inside a constraint, not only under it" do
      -- a hole left in `XLacks`'s row would survive zonking and fail `toCore`
      let
        m = twoMetas rowTypeInfo rowTypeInfo
        result = unifyRow noAssumptions m.ctx (XMeta m.s) XRowEmpty
        constrained = XConstrained (XLacks (FieldKey a) (XMeta m.s)) (XVar rigidR)
      case fst result of
        Solved ctx ->
          substitute ctx constrained
            `shouldEqual` XConstrained (XLacks (FieldKey a) XRowEmpty) (XVar rigidR)
        other -> show other `shouldEqual` "Solved"

    it "does not solve two bare metavariables of different row kinds" do
      -- neither side has an element to give its row element kind away
      let
        m = twoMetas rowTypeInfo (rowTypeInfo { kind = KRow RowEffect })
        result = unifyRow noAssumptions m.ctx (XMeta m.r) (XMeta m.s)
      case fst result of
        Mismatch (KindMismatch _ _ _) -> pure unit
        other -> show other `shouldEqual` "Mismatch (KindMismatch …)"

    it "emits an equation for each key the two sides share" do
      -- the payloads are not unified here; they are handed back to the caller
      let
        m = twoMetas rowTypeInfo rowTypeInfo
        result = unifyRow noAssumptions m.ctx (field a tA (XMeta m.r)) (field a tB (XMeta m.s))
      snd result `shouldEqual` [ Tuple tA tB ]
