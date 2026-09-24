-- | Row unification.
-- |
-- | The three cases the Implementation Plan singles out are here: refinement of
-- | two flexible tails through a fresh one, the rigid/flexible asymmetry, and a
-- | constraint with two flexible tails on one side, which waits rather than
-- | fails.
module Test.Stella.Compiler.Elaborate.Unify (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Kind (KindMetaVar(..), XKind(..))
import Stella.Compiler.Elaborate.Row (xnf)
import Stella.Compiler.Elaborate.Type (MetaVar(..), Scope, XConstraint(..), XRowEntry(..), XType(..), emptyScope)
import Stella.Compiler.Elaborate.Unify (KindMetaBinding(..), KindMetaInfo, MetaBinding(..), MetaContext, MetaInfo, UnifyError(..), UnifyResult(..), emptyContext, freshKindMeta, freshMeta, lookupKindMeta, lookupMeta, substitute, substituteKind, unifyKind, unifyRow)
import Stella.Compiler.TypedCore (Constraint(..), EffName(..), KindVar(..), ModuleName(..), Qualified(..), RowElemKind(..), RowKey(..), Symbol(..), TyName(..), TyVar(..), Type(..))
import Stella.Compiler.TypedCore.Entailment (AtomicFacts, decompose, noFacts)
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

a :: Symbol
a = Symbol "a"

b :: Symbol
b = Symbol "b"

cache :: Symbol
cache = Symbol "cache"

stateEff :: Qualified EffName
stateEff = Qualified prim (EffName "State")

readerEff :: Qualified EffName
readerEff = Qualified prim (EffName "Reader")

rigidR :: TyVar
rigidR = TyVar "r"

-- | `( l : τ | ρ )`
field :: Symbol -> XType -> XType -> XType
field l ty rest = XRowExtend (XRowTypeEntry (SymbolKey l) ty) rest

-- | `( region r ι | ρ )`
regionOf :: XType -> XType -> XType -> XType
regionOf var cells rest = XRowExtend (XRowRegionEntry var cells) rest

-- | `( s : E τ̄ | ρ )`
labelledEffect :: Symbol -> Qualified EffName -> P.Array XType -> XType -> XType
labelledEffect s eff args rest = XRowExtend (XRowLabelledEffectEntry s eff args) rest

-- | A metavariable created where `r` is in scope, which is what the escape
-- | check compares a solution against.
rowTypeInfo :: MetaInfo
rowTypeInfo =
  { kind: XKRow RowType
  , scope: { types: Set.singleton rigidR, kinds: Set.empty }
  , lacks: Set.empty
  , disjointFrom: Set.empty
  }

effectRowInfo :: MetaInfo
effectRowInfo = rowTypeInfo { kind = XKRow RowEffect }

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

-- | A kind metavariable created where no kind variable is in scope.
closedKindInfo :: KindMetaInfo
closedKindInfo = { scope: Set.empty }

-- | Two fresh kind metavariables over an empty context.
twoKindMetas :: KindMetaInfo -> KindMetaInfo -> { j :: KindMetaVar, k :: KindMetaVar, ctx :: MetaContext }
twoKindMetas infoJ infoK =
  let
    first = freshKindMeta infoJ emptyContext
    second = freshKindMeta infoK (snd first)
  in
    { j: fst first, k: fst second, ctx: snd second }

kindSolutionOf :: MetaContext -> KindMetaVar -> Maybe XKind
kindSolutionOf ctx m = case lookupKindMeta ctx m of
  Just (KindAssigned kind) -> Just (substituteKind ctx kind)
  _ -> Nothing

scopeOfMeta :: MetaContext -> MetaVar -> Maybe Scope
scopeOfMeta ctx m = case lookupMeta ctx m of
  Just (Unsolved info) -> Just info.scope
  _ -> Nothing

spec :: Spec Unit
spec = describe "Stella.Compiler.Elaborate.Unify" do
  describe "kind unification" do
    it "accepts two identical kinds" do
      case unifyKind emptyContext XKType XKType of
        Right _ -> pure unit
        Left err -> show err `shouldEqual` "Right"

    it "rejects two kinds no substitution equates" do
      case unifyKind emptyContext XKType (XKRow RowType) of
        Left (KindNotEqual left right) -> do
          left `shouldEqual` XKType
          right `shouldEqual` XKRow RowType
        other -> show other `shouldEqual` "Left (KindNotEqual …)"

    it "rejects Effect against Type" do
      -- `Effect` is a kind and not a quantifiable one (D24), and it equals
      -- nothing but itself here either
      case unifyKind emptyContext XKEffect XKType of
        Left (KindNotEqual _ _) -> pure unit
        other -> show other `shouldEqual` "Left (KindNotEqual …)"

    it "assigns a metavariable, whichever side it stands on" do
      let m = twoKindMetas closedKindInfo closedKindInfo
      case unifyKind m.ctx (XKMeta m.j) XKType of
        Right ctx -> kindSolutionOf ctx m.j `shouldEqual` Just XKType
        Left err -> show err `shouldEqual` "Right"
      case unifyKind m.ctx (XKRow RowEffect) (XKMeta m.k) of
        Right ctx -> kindSolutionOf ctx m.k `shouldEqual` Just (XKRow RowEffect)
        Left err -> show err `shouldEqual` "Right"

    it "identifies two metavariables" do
      let m = twoKindMetas closedKindInfo closedKindInfo
      case unifyKind m.ctx (XKMeta m.j) (XKMeta m.k) of
        Right ctx -> case unifyKind ctx (XKMeta m.k) XKType of
          Right ctx' -> kindSolutionOf ctx' m.j `shouldEqual` Just XKType
          Left err -> show err `shouldEqual` "Right"
        Left err -> show err `shouldEqual` "Right"

    it "solves both sides of an arrow" do
      -- ?j -> Type  ≡  Row Type -> ?k
      let
        m = twoKindMetas closedKindInfo closedKindInfo
        left = XKFun (XKMeta m.j) XKType
        right = XKFun (XKRow RowType) (XKMeta m.k)
      case unifyKind m.ctx left right of
        Right ctx -> do
          kindSolutionOf ctx m.j `shouldEqual` Just (XKRow RowType)
          kindSolutionOf ctx m.k `shouldEqual` Just XKType
        Left err -> show err `shouldEqual` "Right"

    it "looks through what is already solved" do
      let m = twoKindMetas closedKindInfo closedKindInfo
      case unifyKind m.ctx (XKMeta m.j) XKType of
        Right ctx -> case unifyKind ctx (XKMeta m.j) (XKRow RowType) of
          Left (KindNotEqual _ _) -> pure unit
          other -> show other `shouldEqual` "Left (KindNotEqual …)"
        Left err -> show err `shouldEqual` "Right"

    it "refuses a solution that would make a metavariable refer to itself" do
      let m = twoKindMetas closedKindInfo closedKindInfo
      case unifyKind m.ctx (XKMeta m.j) (XKFun (XKMeta m.j) XKType) of
        Left (KindOccursCheck escaping _) -> escaping `shouldEqual` m.j
        other -> show other `shouldEqual` "Left (KindOccursCheck …)"

    it "refuses a kind variable the metavariable was not created under" do
      let
        k = KindVar "k"
        m = twoKindMetas closedKindInfo closedKindInfo
      case unifyKind m.ctx (XKMeta m.j) (XKVar k) of
        Left (KindEscapingVariable _ escaping) -> escaping `shouldEqual` k
        other -> show other `shouldEqual` "Left (KindEscapingVariable …)"

    it "accepts that kind variable when the metavariable was created under it" do
      let
        k = KindVar "k"
        m = twoKindMetas { scope: Set.singleton k } closedKindInfo
      case unifyKind m.ctx (XKMeta m.j) (XKVar k) of
        Right ctx -> kindSolutionOf ctx m.j `shouldEqual` Just (XKVar k)
        Left err -> show err `shouldEqual` "Right"

    it "reports a kind metavariable the context does not hold" do
      case unifyKind emptyContext (XKMeta (KindMetaVar 0)) XKType of
        Left (KindMetaUnbound _) -> pure unit
        other -> show other `shouldEqual` "Left (KindMetaUnbound …)"

    it "reports it against itself too, where reflexivity would otherwise pass" do
      case unifyKind emptyContext (XKMeta (KindMetaVar 0)) (XKMeta (KindMetaVar 0)) of
        Left (KindMetaUnbound _) -> pure unit
        other -> show other `shouldEqual` "Left (KindMetaUnbound …)"

  describe "the row kind of a metavariable" do
    it "solves an unknown row kind against the one the other side carries" do
      -- neither bare metavariable gives its row element kind away, so the two
      -- kinds meet at the refinement rather than at an element
      let
        kindMeta = freshKindMeta closedKindInfo emptyContext
        unknownKind = rowTypeInfo { kind = XKMeta (fst kindMeta) }
        first = freshMeta unknownKind (snd kindMeta)
        second = freshMeta rowTypeInfo (snd first)
        ctx = snd second
        result = unifyRow noAssumptions ctx (XMeta (fst first)) (XMeta (fst second))
      case fst result of
        Solved ctx' -> kindSolutionOf ctx' (fst kindMeta) `shouldEqual` Just (XKRow RowType)
        other -> show other `shouldEqual` "Solved …"

  describe "a flexible tail the context does not hold unsolved" do
    it "reports one standing against itself" do
      -- the two occurrences cancel each other, so nothing later in the case
      -- analysis would look at either
      case fst (unifyRow noAssumptions emptyContext (XMeta (MetaVar 0)) (XMeta (MetaVar 0))) of
        Mismatch (MetaUnbound _) -> pure unit
        other -> show other `shouldEqual` "Mismatch (MetaUnbound …)"

    it "reports one standing against a metavariable the context holds" do
      let m = twoMetas rowTypeInfo rowTypeInfo
      case fst (unifyRow noAssumptions m.ctx (XMeta m.r) (XMeta (MetaVar 99))) of
        Mismatch (MetaUnbound unbound) -> unbound `shouldEqual` MetaVar 99
        other -> show other `shouldEqual` "Mismatch (MetaUnbound …)"

  describe "the scope of a metavariable inside a solution" do
    it "narrows a type metavariable the solution mentions" do
      -- `?r` was created under nothing, so what `?p` may later be solved to is
      -- what `?r` may mention and no more
      let
        outer = rowTypeInfo { scope = emptyScope }
        payload = rowTypeInfo { scope = { types: Set.singleton rigidR, kinds: Set.singleton (KindVar "k") } }
        first = freshMeta outer emptyContext
        second = freshMeta payload (snd first)
        ctx = snd second
        result = unifyRow noAssumptions ctx (XMeta (fst first)) (field a (XMeta (fst second)) XRowEmpty)
      case fst result of
        Solved ctx' -> scopeOfMeta ctx' (fst second) `shouldEqual` Just emptyScope
        other -> show other `shouldEqual` "Solved …"

    it "narrows a kind metavariable a type solution mentions" do
      -- the escape check reads the rigid variables a solution mentions now, and
      -- an unsolved kind inside it mentions none until it is solved
      let
        k = KindVar "k"
        kindMeta = freshKindMeta { scope: Set.singleton k } emptyContext
        outer = rowTypeInfo { scope = emptyScope }
        first = freshMeta outer (snd kindMeta)
        proxied = XCon (Qualified prim (TyName "Proxy")) [ XKMeta (fst kindMeta) ]
        result = unifyRow noAssumptions (snd first) (XMeta (fst first)) (field a proxied XRowEmpty)
      case fst result of
        Solved ctx -> case unifyKind ctx (XKMeta (fst kindMeta)) (XKVar k) of
          Left (KindEscapingVariable _ escaping) -> escaping `shouldEqual` k
          other -> show other `shouldEqual` "Left (KindEscapingVariable …)"
        other -> show other `shouldEqual` "Solved …"

    it "refuses where the narrowed metavariable's own kind would escape" do
      -- `?p` stands at a rigid kind variable, and narrowing `?p` to what `?r`
      -- may mention puts that variable outside the scope `?p` keeps it in
      let
        k = KindVar "k"
        outer = rowTypeInfo { scope = emptyScope }
        payload = rowTypeInfo
          { kind = XKVar k
          , scope = { types: Set.empty, kinds: Set.singleton k }
          }
        first = freshMeta outer emptyContext
        second = freshMeta payload (snd first)
        result = unifyRow noAssumptions (snd second) (XMeta (fst first)) (field a (XMeta (fst second)) XRowEmpty)
      case fst result of
        Mismatch (EscapingKindVariable _ escaping) -> escaping `shouldEqual` k
        other -> show other `shouldEqual` "Mismatch (EscapingKindVariable …)"

    it "refuses where the narrowed metavariable's disjointness would escape" do
      let
        outer = rowTypeInfo { scope = emptyScope }
        payload = rowTypeInfo { disjointFrom = Set.singleton rigidR }
        first = freshMeta outer emptyContext
        second = freshMeta payload (snd first)
        result = unifyRow noAssumptions (snd second) (XMeta (fst first)) (field a (XMeta (fst second)) XRowEmpty)
      case fst result of
        Mismatch (EscapingVariable _ escaping) -> escaping `shouldEqual` rigidR
        other -> show other `shouldEqual` "Mismatch (EscapingVariable …)"

    it "narrows a kind metavariable standing in the narrowed metavariable's kind" do
      let
        k = KindVar "k"
        kindMeta = freshKindMeta { scope: Set.singleton k } emptyContext
        outer = rowTypeInfo { scope = emptyScope }
        payload = rowTypeInfo { kind = XKMeta (fst kindMeta), scope = emptyScope }
        first = freshMeta outer (snd kindMeta)
        second = freshMeta payload (snd first)
        result = unifyRow noAssumptions (snd second) (XMeta (fst first)) (field a (XMeta (fst second)) XRowEmpty)
      case fst result of
        Solved ctx -> case unifyKind ctx (XKMeta (fst kindMeta)) (XKVar k) of
          Left (KindEscapingVariable _ escaping) -> escaping `shouldEqual` k
          other -> show other `shouldEqual` "Left (KindEscapingVariable …)"
        other -> show other `shouldEqual` "Solved …"

    it "refuses where a solved kind the metavariable stands at would escape" do
      -- `?p` stands at `?k`, and `?k` is already solved to a rigid kind
      -- variable, so what `?p` holds is that variable however it reads
      let
        k = KindVar "k"
        kindMeta = freshKindMeta { scope: Set.singleton k } emptyContext
        outer = rowTypeInfo { scope = emptyScope }
        payload = rowTypeInfo
          { kind = XKMeta (fst kindMeta)
          , scope = { types: Set.empty, kinds: Set.singleton k }
          }
      case unifyKind (snd kindMeta) (XKMeta (fst kindMeta)) (XKVar k) of
        Right solvedKind ->
          let
            first = freshMeta outer solvedKind
            second = freshMeta payload (snd first)
            result = unifyRow noAssumptions (snd second) (XMeta (fst first)) (field a (XMeta (fst second)) XRowEmpty)
          in
            case fst result of
              Mismatch (EscapingKindVariable _ escaping) -> escaping `shouldEqual` k
              other -> show other `shouldEqual` "Mismatch (EscapingKindVariable …)"
        Left err -> show err `shouldEqual` "Right"

    it "narrows a kind metavariable a kind solution mentions" do
      let
        k = KindVar "k"
        m = twoKindMetas closedKindInfo { scope: Set.singleton k }
      case unifyKind m.ctx (XKMeta m.j) (XKFun (XKMeta m.k) XKType) of
        Right ctx -> case unifyKind ctx (XKMeta m.k) (XKVar k) of
          Left (KindEscapingVariable _ escaping) -> escaping `shouldEqual` k
          other -> show other `shouldEqual` "Left (KindEscapingVariable …)"
        Left err -> show err `shouldEqual` "Right"

  describe "two flexible tails" do
    it "refines both sides through one fresh tail" do
      -- { a : A | ?r } ≡ { b : B | ?s }
      --   ?r := ( b : B | ?t )   and   ?s := ( a : A | ?t )
      let
        m = twoMetas rowTypeInfo rowTypeInfo
        result = unifyRow noAssumptions m.ctx (field a tA (XMeta m.r)) (field b tB (XMeta m.s))
      case fst result of
        Solved ctx -> do
          knownKeysOf ctx m.r `shouldEqual` Just [ SymbolKey b ]
          knownKeysOf ctx m.s `shouldEqual` Just [ SymbolKey a ]
          -- the same fresh tail stands on both sides
          (tailOf ctx m.r == tailOf ctx m.s) `shouldEqual` true
          map Array.length (tailOf ctx m.r) `shouldEqual` Just 1
        other -> show other `shouldEqual` "Solved"

    it "carries the Lacks of both sides onto the fresh tail" do
      -- Lacks(?t) ⊇ dom(D1) ∪ dom(D2) ∪ Lacks(?r) ∪ Lacks(?s)
      let
        m = twoMetas (lacking [ SymbolKey (Symbol "x") ]) rowTypeInfo
        result = unifyRow noAssumptions m.ctx (field a tA (XMeta m.r)) (field b tB (XMeta m.s))
      case fst result of
        Solved ctx ->
          case tailOf ctx m.r of
            Just [ t ] -> case lookupMeta ctx t of
              Just (Unsolved info) -> do
                Set.member (SymbolKey (Symbol "x")) info.lacks `shouldEqual` true
                Set.member (SymbolKey a) info.lacks `shouldEqual` true
                Set.member (SymbolKey b) info.lacks `shouldEqual` true
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
        Solved ctx -> knownKeysOf ctx m.s `shouldEqual` Just [ SymbolKey a ]
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
        m = twoMetas rowTypeInfo (lacking [ SymbolKey a ])
        result = unifyRow noAssumptions m.ctx (XMeta m.s) (field a tA XRowEmpty)
      case fst result of
        Mismatch (LacksViolated key) -> key `shouldEqual` SymbolKey a
        other -> show other `shouldEqual` "Mismatch (LacksViolated …)"

    it "refuses a solution of the wrong row kind" do
      let
        effectInfo = rowTypeInfo { kind = XKRow RowEffect }
        m = twoMetas rowTypeInfo effectInfo
        result = unifyRow noAssumptions m.ctx (XMeta m.s) (field a tA XRowEmpty)
      case fst result of
        Mismatch (KindMismatch _ expected actual) -> do
          expected `shouldEqual` XKRow RowEffect
          actual `shouldEqual` XKRow RowType
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
        m = twoMetas rowTypeInfo (lacking [ SymbolKey a ])
        result = unifyRow noAssumptions m.ctx (XMeta m.s) (XVar rigidR)
      case fst result of
        Mismatch (LacksUnproven key t) -> do
          key `shouldEqual` SymbolKey a
          t `shouldEqual` rigidR
        other -> show other `shouldEqual` "Mismatch (LacksUnproven …)"

    it "accepts that rigid tail once the context proves it" do
      let
        m = twoMetas rowTypeInfo (lacking [ SymbolKey a ])
        facts = assuming [ Lacks (SymbolKey a) (TVar rigidR) ]
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
          key `shouldEqual` SymbolKey a
          u `shouldEqual` rigidR
        other -> show other `shouldEqual` "Mismatch (LacksUnproven …)"

    it "accepts that known key once the context proves it absent" do
      let
        m = twoMetas rowTypeInfo (rowTypeInfo { disjointFrom = Set.singleton rigidR })
        facts = assuming [ Lacks (SymbolKey a) (TVar rigidR) ]
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
        proxied = XCon (Qualified prim (TyName "Proxy")) [ XKVar k ]
        result = unifyRow noAssumptions m.ctx (XMeta m.s) (field a proxied XRowEmpty)
      case fst result of
        Mismatch (EscapingKindVariable _ escaping) -> escaping `shouldEqual` k
        other -> show other `shouldEqual` "Mismatch (EscapingKindVariable …)"

    it "accepts that kind variable when the metavariable was created under it" do
      let
        k = KindVar "k"
        info = rowTypeInfo { scope = { types: Set.singleton rigidR, kinds: Set.singleton k } }
        m = twoMetas rowTypeInfo info
        proxied = XCon (Qualified prim (TyName "Proxy")) [ XKVar k ]
        result = unifyRow noAssumptions m.ctx (XMeta m.s) (field a proxied XRowEmpty)
      case fst result of
        Solved _ -> pure unit
        other -> show other `shouldEqual` "Solved"

    it "substitutes inside a constraint, not only under it" do
      -- a hole left in `XLacks`'s row would survive zonking and fail `toCore`
      let
        m = twoMetas rowTypeInfo rowTypeInfo
        result = unifyRow noAssumptions m.ctx (XMeta m.s) XRowEmpty
        constrained = XConstrained (XLacks (SymbolKey a) (XMeta m.s)) (XVar rigidR)
      case fst result of
        Solved ctx ->
          substitute ctx constrained
            `shouldEqual` XConstrained (XLacks (SymbolKey a) XRowEmpty) (XVar rigidR)
        other -> show other `shouldEqual` "Solved"

    it "does not solve two bare metavariables of different row kinds" do
      -- neither side has an element to give its row element kind away
      let
        m = twoMetas rowTypeInfo (rowTypeInfo { kind = XKRow RowEffect })
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

    it "equates the arguments of two elements sharing a key and an effect" do
      let
        m = twoMetas effectRowInfo effectRowInfo
        result = unifyRow noAssumptions m.ctx
          (labelledEffect cache stateEff [ tA ] (XMeta m.r))
          (labelledEffect cache stateEff [ tB ] (XMeta m.s))
      snd result `shouldEqual` [ Tuple tA tB ]

    it "fails where a shared key stands over different effects" do
      -- A written key does not determine the payload, so two elements can agree
      -- on the key and still name different protocols
      let
        m = twoMetas effectRowInfo effectRowInfo
        result = unifyRow noAssumptions m.ctx
          (labelledEffect cache stateEff [ tA ] (XMeta m.r))
          (labelledEffect cache readerEff [ tA ] (XMeta m.s))
      case fst result of
        Mismatch (PayloadMismatch key _ _) -> key `shouldEqual` SymbolKey cache
        other -> show other `shouldEqual` "Mismatch (PayloadMismatch …)"

    it "fails where a shared key and effect stand over different arities" do
      -- Arity belongs to the payload, so the shorter argument vector is a
      -- mismatch rather than a prefix of the longer one
      let
        m = twoMetas effectRowInfo effectRowInfo
        result = unifyRow noAssumptions m.ctx
          (labelledEffect cache stateEff [ tA ] (XMeta m.r))
          (labelledEffect cache stateEff [ tA, tB ] (XMeta m.s))
      case fst result of
        Mismatch (PayloadMismatch key _ _) -> key `shouldEqual` SymbolKey cache
        other -> show other `shouldEqual` "Mismatch (PayloadMismatch …)"

    it "equates both the variable and the layout of two regions sharing the key" do
      let
        m = twoMetas effectRowInfo effectRowInfo
        result = unifyRow noAssumptions m.ctx
          (regionOf tA (field a tA XRowEmpty) (XMeta m.r))
          (regionOf tB (field a tB XRowEmpty) (XMeta m.s))
      snd result `shouldEqual`
        [ Tuple tA tB, Tuple (field a tA XRowEmpty) (field a tB XRowEmpty) ]

    it "leaves two regions whose layouts differ to the layout equation" do
      -- The key does not decide the layout, so the two are handed back as an
      -- equation and fail where that equation is solved, not here
      let
        m = twoMetas effectRowInfo effectRowInfo
        left = field a tA XRowEmpty
        right = field b tA XRowEmpty
        result = unifyRow noAssumptions m.ctx
          (regionOf tA left (XMeta m.r))
          (regionOf tA right (XMeta m.s))
      snd result `shouldEqual` [ Tuple tA tA, Tuple left right ]
      case fst (unifyRow noAssumptions m.ctx left right) of
        Mismatch (RowMismatch _ _) -> pure unit
        other -> show other `shouldEqual` "Mismatch (RowMismatch …)"
