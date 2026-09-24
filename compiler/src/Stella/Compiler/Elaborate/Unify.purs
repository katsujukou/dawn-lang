-- | Unification over Core⁺, at kinds and at rows.
-- |
-- | Solving `ρ1 ≡ ρ2` operates on the normal form, and the procedure is
-- | identical at `Row Type` and `Row Effect`: every key is rigid, so the domain
-- | of a normal form does not depend on how metavariables are solved.
-- |
-- | Three outcomes are distinguished. `Solved` records a substitution,
-- | `Mismatch` is a failure to report, and `Stuck` is neither: it names the
-- | metavariables whose solution would let the constraint be retried.
-- |
-- | **`Stuck` arises at one place**, the case where a side carries more than one
-- | flexible tail and no solution is unique yet. Every metavariable it names is
-- | one the context holds unsolved, so each can be woken by an assignment; a
-- | metavariable that is absent or already solved is a caller error and is
-- | reported as one.
-- |
-- | Kind unification has no third outcome and says so in its type: kind equality
-- | is syntactic (D2), so a kind metavariable is assigned or the two kinds
-- | differ, and there is nothing to wait for.
module Stella.Compiler.Elaborate.Unify
  ( MetaInfo
  , MetaBinding(..)
  , KindRequirement(..)
  , KindMetaInfo
  , KindMetaBinding(..)
  , MetaContext
  , UnifyError(..)
  , UnifyResult(..)
  , emptyContext
  , freshMeta
  , freshKindMeta
  , lookupMeta
  , lookupKindMeta
  , substitute
  , substituteKind
  , requireQuantifiable
  , requireProducesType
  , unifyKind
  , unifyRow
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Kind (KindMetaVar(..), XKind(..), kindMetasOf, kindVarsOf, occursInKind)
import Stella.Compiler.Elaborate.Row (XRowError, XRowNormalForm, payloadEquations, rebuild, xnf)
import Stella.Compiler.Elaborate.Type (MetaVar(..), Scope, XConstraint(..), XRowEntry(..), XType(..), kindMetasOfType, metasOf, occursIn, outOfScope)
import Stella.Compiler.TypedCore (Constraint(..), KindVar, RowElemKind(..), RowKey, TyVar, Type(..))
import Stella.Compiler.TypedCore.Entailment (AtomicFacts, entails)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM, foldr)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), snd)

-- | What `Ψ` records of an unsolved metavariable, that is, `?α : κ [Γ]`.
-- |
-- | `scope` is the `[Γ]`: the type and kind variables that were in scope where
-- | the metavariable was created. A solution mentioning any other lets a
-- | variable bound further in escape.
-- |
-- | `lacks` and `disjointFrom` carry the row constraints assumed of it, which a
-- | substitution must preserve: a solution that dropped them would produce Core
-- | that is not well-kinded.
type MetaInfo =
  { kind :: XKind
  , scope :: Scope
  , lacks :: Set RowKey
  , disjointFrom :: Set TyVar
  }

data MetaBinding
  = Unsolved MetaInfo
  | Assigned XType

-- | What a site that created a kind metavariable requires of whatever solves it.
-- |
-- | Kind equality decides nothing about these: `?k ≡ Effect` is a kind equation
-- | that solves, and it is wrong only where `?k` stands somewhere a quantifiable
-- | kind is called for (D24). So a requirement is carried by the metavariable and
-- | re-applied at every assignment, rather than being a condition on equality.
data KindRequirement
  -- | `Γ ⊢ κ qkind`: the kind may stand where a type variable is introduced, and
  -- | in a `[[κ̄]]`.
  = Quantifiable
  -- | `result(κ) = Type`: the kind produces `Type` once fully applied, which is
  -- | what the right-hand side of a quantifiable arrow must do.
  | ProducesType

-- | What `Ψ` records of an unsolved kind metavariable, that is, `?k [Γ]`.
-- |
-- | A kind variable enters `Γ` only while a declaration whose scheme binds it is
-- | being checked (D3), so a solution mentioning one the metavariable was not
-- | created under keeps that variable alive past its declaration.
type KindMetaInfo =
  { scope :: Set KindVar
  , requirements :: Set KindRequirement
  }

data KindMetaBinding
  = KindUnsolved KindMetaInfo
  | KindAssigned XKind

type MetaContext =
  { bindings :: Map MetaVar MetaBinding
  , kindBindings :: Map KindMetaVar KindMetaBinding
  , next :: P.Int
  , nextKind :: P.Int
  }

data UnifyError
  -- | The two sides cannot be made equal by any substitution.
  = RowMismatch XRowNormalForm XRowNormalForm
  -- | A rigid tail on a side that has nothing left to absorb it.
  | RigidTailRemains (Set TyVar)
  -- | Assigning would make a metavariable refer to itself.
  | OccursCheck MetaVar XType
  -- | A solution would carry a key the metavariable is assumed to lack.
  | LacksViolated RowKey
  -- | Two entries share a key but carry payloads no substitution equates.
  | PayloadMismatch RowKey XRowEntry XRowEntry
  -- | A solution puts a rigid tail where the context does not prove the Lacks
  -- | the metavariable carries.
  | LacksUnproven RowKey TyVar
  -- | A solution puts a rigid tail where the context does not prove a
  -- | disjointness the metavariable carries.
  | DisjointUnproven TyVar TyVar
  -- | A rigid variable that would outlive its binder through a metavariable:
  -- | mentioned by a solution the metavariable was not created under, or left in
  -- | what that metavariable holds once a narrowing has put it out of scope.
  | EscapingVariable MetaVar TyVar
  -- | The same, for a kind variable.
  | EscapingKindVariable MetaVar KindVar
  -- | A fresh tail would have to mention a rigid variable that is not in scope
  -- | on both sides, so the refinement has no representable solution.
  | FreshTailOutOfScope TyVar
  -- | The kind of a solution does not match the kind of the metavariable. The
  -- | whole of each kind is reported, the metavariable being what names the
  -- | failure, rather than the sub-kinds at which the two first differed.
  | KindMismatch MetaVar XKind XKind
  -- | Two kinds no substitution equates.
  | KindNotEqual XKind XKind
  -- | Assigning would make a kind metavariable refer to itself.
  | KindOccursCheck KindMetaVar XKind
  -- | A kind solution mentions a kind variable that was not in scope where the
  -- | metavariable was created.
  | KindEscapingVariable KindMetaVar KindVar
  -- | A kind required to be quantifiable that is not (D24).
  | KindNotQuantifiable XKind
  -- | A kind required to produce `Type` once fully applied that does not.
  | KindDoesNotProduceType XKind
  -- | A kind metavariable the context does not hold, which is a caller error.
  | KindMetaUnbound KindMetaVar
  -- | A metavariable the context does not hold, and one it holds solved. Both
  -- | are caller errors rather than unification failures, and neither may be
  -- | reported as `Stuck`: a dependency that is absent, or already solved, is
  -- | one no assignment can wake.
  | MetaUnbound MetaVar
  | MetaAlreadyAssigned MetaVar
  | NotARow XRowError

data UnifyResult
  = Solved MetaContext
  | Stuck (Set MetaVar)
  | Mismatch UnifyError

emptyContext :: MetaContext
emptyContext =
  { bindings: Map.empty
  , kindBindings: Map.empty
  , next: 0
  , nextKind: 0
  }

freshMeta :: MetaInfo -> MetaContext -> Tuple MetaVar MetaContext
freshMeta info ctx =
  Tuple m ctx
    { bindings = Map.insert m (Unsolved info) ctx.bindings
    , next = ctx.next + 1
    }
  where
  m = MetaVar ctx.next

freshKindMeta :: KindMetaInfo -> MetaContext -> Tuple KindMetaVar MetaContext
freshKindMeta info ctx =
  Tuple k ctx
    { kindBindings = Map.insert k (KindUnsolved info) ctx.kindBindings
    , nextKind = ctx.nextKind + 1
    }
  where
  k = KindMetaVar ctx.nextKind

lookupMeta :: MetaContext -> MetaVar -> Maybe MetaBinding
lookupMeta ctx m = Map.lookup m ctx.bindings

lookupKindMeta :: MetaContext -> KindMetaVar -> Maybe KindMetaBinding
lookupKindMeta ctx k = Map.lookup k ctx.kindBindings

-- | Apply what is already solved. Normalizing without this would leave an
-- | assigned metavariable in the flexible tail, where the case analysis would
-- | treat it as an unknown.
substitute :: MetaContext -> XType -> XType
substitute ctx = go
  where
  go = case _ of
    XMeta m -> case Map.lookup m ctx.bindings of
      Just (Assigned ty) -> go ty
      _ -> XMeta m
    XCon n kinds -> XCon n (map (substituteKind ctx) kinds)
    XApp f a -> XApp (go f) (go a)
    XForall a k body -> XForall a (substituteKind ctx k) (go body)
    XConstrained c body -> XConstrained (goConstraint c) (go body)
    XRowExtend entry rest -> XRowExtend (goEntry entry) (go rest)
    XRowUnion l r -> XRowUnion (go l) (go r)
    ty -> ty

  goEntry = case _ of
    XRowTypeEntry k ty -> XRowTypeEntry k (go ty)
    XRowEffectEntry e args -> XRowEffectEntry e (map go args)
    XRowLabelledEffectEntry s e args -> XRowLabelledEffectEntry s e (map go args)
    XRowRegionEntry var cells -> XRowRegionEntry (go var) (go cells)

  -- A constraint carries rows of its own, and a hole left in one of them would
  -- survive zonking and fail `toCore`.
  goConstraint = case _ of
    XLacks key row -> XLacks key (go row)
    XDisjoint l r -> XDisjoint (go l) (go r)

-- | Apply what is already solved at the kind level.
substituteKind :: MetaContext -> XKind -> XKind
substituteKind ctx = go
  where
  go = case _ of
    XKMeta m -> case Map.lookup m ctx.kindBindings of
      Just (KindAssigned kind) -> go kind
      _ -> XKMeta m
    XKFun a b -> XKFun (go a) (go b)
    kind -> kind

-- | `κ1 ≡ κ2`.
-- |
-- | There is no computation at the kind level and no subsumption, so this is
-- | first-order unification with an occurs check. Every outcome is decided here:
-- | a kind metavariable is assigned, or the two kinds differ.
unifyKind :: MetaContext -> XKind -> XKind -> Either UnifyError MetaContext
unifyKind ctx kind1 kind2 = go ctx kind1 kind2
  where
  go c a b = case substituteKind c a, substituteKind c b of
    -- One metavariable against itself holds whatever it is, but only where the
    -- context has it: an unknown one is a caller error on either side.
    XKMeta m, XKMeta n | m == n ->
      if Map.member m c.kindBindings then Right c else Left (KindMetaUnbound m)
    XKMeta m, solution -> assignKind c m solution
    solution, XKMeta n -> assignKind c n solution
    XKVar x, XKVar y | x == y -> Right c
    XKType, XKType -> Right c
    XKEffect, XKEffect -> Right c
    XKRow e, XKRow f | e == f -> Right c
    XKFun a1 a2, XKFun b1 b2 -> do
      c1 <- go c a1 b1
      go c1 a2 b2
    left, right -> Left (KindNotEqual left right)

-- | Every kind substitution performs an occurs check and a scope check, as a
-- | type substitution does, and then holds the solution to what the
-- | metavariable requires of it.
assignKind :: MetaContext -> KindMetaVar -> XKind -> Either UnifyError MetaContext
assignKind ctx m given = case Map.lookup m ctx.kindBindings of
  Just (KindUnsolved info) ->
    let
      solution = substituteKind ctx given
    in
      if occursInKind m solution then
        Left (KindOccursCheck m solution)
      else case Set.findMin (Set.difference (kindVarsOf solution) info.scope) of
        Just escaping ->
          Left (KindEscapingVariable m escaping)
        Nothing -> do
          -- A requirement reaching an unsolved kind attaches itself there, so
          -- assigning one metavariable to another moves the requirements across
          -- and the two sets merge.
          required <- foldM (applyRequirement solution) ctx
            (Set.toUnfoldable info.requirements :: P.Array KindRequirement)
          narrowed <- foldM (narrowKindTo info.scope) required
            (Set.toUnfoldable (kindMetasOf solution) :: P.Array KindMetaVar)
          pure narrowed { kindBindings = Map.insert m (KindAssigned solution) narrowed.kindBindings }

  _ ->
    Left (KindMetaUnbound m)

applyRequirement :: XKind -> MetaContext -> KindRequirement -> Either UnifyError MetaContext
applyRequirement kind ctx = case _ of
  Quantifiable -> requireQuantifiable ctx kind
  ProducesType -> requireProducesType ctx kind

-- | `Γ ⊢ κ qkind`, as an obligation rather than as a judgement.
-- |
-- | Where the kind is unsolved there is nothing to decide yet, so the
-- | requirement is attached to the metavariable and decided when it is
-- | assigned. An arrow is quantifiable only where it produces `Type`, so both
-- | sides carry the requirement and the right-hand one carries a second.
-- |
-- | **A rigid kind variable is admitted unconditionally, and that it is bound is
-- | the caller's to establish.** This takes no `Γ`: every kind variable of a
-- | well-formed kind is bound by the scheme of the declaration being checked
-- | (D3), so the judgement `k ∈ Γ` belongs where the kind is built. A caller
-- | that skips it leaves an unbound kind variable for the Core kind checker to
-- | find rather than reporting it where it was written.
requireQuantifiable :: MetaContext -> XKind -> Either UnifyError MetaContext
requireQuantifiable ctx kind = case substituteKind ctx kind of
  XKType -> Right ctx
  XKRow _ -> Right ctx
  XKVar _ -> Right ctx
  XKMeta m -> attachRequirement Quantifiable m ctx
  XKEffect -> Left (KindNotQuantifiable XKEffect)
  XKFun a b -> do
    ctx1 <- requireQuantifiable ctx a
    ctx2 <- requireQuantifiable ctx1 b
    requireProducesType ctx2 b

-- | `result(κ) = Type`.
-- |
-- | A rigid kind variable fails: a scheme says nothing about what instantiates
-- | it, and a row kind is among the possibilities.
requireProducesType :: MetaContext -> XKind -> Either UnifyError MetaContext
requireProducesType ctx kind = case substituteKind ctx kind of
  XKType -> Right ctx
  XKFun _ b -> requireProducesType ctx b
  XKMeta m -> attachRequirement ProducesType m ctx
  other -> Left (KindDoesNotProduceType other)

attachRequirement :: KindRequirement -> KindMetaVar -> MetaContext -> Either UnifyError MetaContext
attachRequirement requirement m ctx = case Map.lookup m ctx.kindBindings of
  Just (KindUnsolved info) ->
    Right ctx
      { kindBindings = Map.insert m
          (KindUnsolved (info { requirements = Set.insert requirement info.requirements }))
          ctx.kindBindings
      }

  -- Substituting leaves no assigned metavariable in the position this reaches.
  _ ->
    Left (KindMetaUnbound m)

-- | `solve(ρ1 ≡ ρ2)`.
-- |
-- | Payload equations are returned rather than solved: equating `F1(k)` with
-- | `F2(k)` is type unification, which is a separate judgement. The caller
-- | discharges them. A payload the two sides cannot share at all is decided
-- | here, since no substitution repairs it.
unifyRow :: AtomicFacts -> MetaContext -> XType -> XType -> Tuple UnifyResult (P.Array (Tuple XType XType))
unifyRow facts ctx row1 row2 =
  case xnf (substitute ctx row1), xnf (substitute ctx row2) of
    Left err, _ -> Tuple (Mismatch (NotARow err)) []
    _, Left err -> Tuple (Mismatch (NotARow err)) []
    Right n1, Right n2 -> case unsolvedTails ctx (Set.union n1.flexible n2.flexible) of
      Just err -> Tuple (Mismatch err) []
      Nothing -> solve facts ctx n1 n2

-- | Every flexible tail is a metavariable the context holds unsolved.
-- |
-- | Deciding this before the case analysis is what keeps a `Stuck` honest. Two
-- | occurrences of one tail cancel each other, and a tail nothing holds would
-- | otherwise pass through that cancellation into a `Solved`, or stand in the
-- | dependency set of a `Stuck` that no assignment can ever wake.
unsolvedTails :: MetaContext -> Set MetaVar -> Maybe UnifyError
unsolvedTails ctx metas =
  Array.head (Array.mapMaybe unsolved (Set.toUnfoldable metas :: P.Array MetaVar))
  where
  unsolved m = case Map.lookup m ctx.bindings of
    Just (Unsolved _) -> Nothing
    Just (Assigned _) -> Just (MetaAlreadyAssigned m)
    Nothing -> Just (MetaUnbound m)

solve :: AtomicFacts -> MetaContext -> XRowNormalForm -> XRowNormalForm -> Tuple UnifyResult (P.Array (Tuple XType XType))
solve facts ctx n1 n2 =
  case traverse payloadsAt (Set.toUnfoldable shared :: P.Array RowKey) of
    Left err ->
      Tuple (Mismatch err) []
    Right equations ->
      Tuple (step4 facts ctx d1 d2 r1 r2 m1 m2 n1 n2) (Array.concat equations)
  where
  -- 1. match the payloads of shared keys
  shared = Set.intersection (domain n1) (domain n2)

  payloadsAt key = case Map.lookup key n1.known, Map.lookup key n2.known of
    Just e1, Just e2 -> case payloadEquations e1 e2 of
      Just equations -> Right equations
      Nothing -> Left (PayloadMismatch key e1 e2)
    _, _ -> Right []

  d1 = Map.filterKeys (\k -> not (Set.member k shared)) n1.known
  d2 = Map.filterKeys (\k -> not (Set.member k shared)) n2.known

  -- 2. cancel shared tails, on both the rigid and the flexible side
  r1 = Set.difference n1.rigid n2.rigid
  r2 = Set.difference n2.rigid n1.rigid
  m1 = Set.difference n1.flexible n2.flexible
  m2 = Set.difference n2.flexible n1.flexible

-- | 4. case analysis on the number of flexible tails.
step4
  :: AtomicFacts
  -> MetaContext
  -> Map RowKey XRowEntry
  -> Map RowKey XRowEntry
  -> Set TyVar
  -> Set TyVar
  -> Set MetaVar
  -> Set MetaVar
  -> XRowNormalForm
  -> XRowNormalForm
  -> UnifyResult
step4 facts ctx d1 d2 r1 r2 m1 m2 n1 n2 =
  case Set.toUnfoldable m1 :: P.Array MetaVar, Set.toUnfoldable m2 :: P.Array MetaVar of
    -- (a) both sides are determined
    [], [] ->
      if Map.isEmpty d1 && Map.isEmpty d2 && Set.isEmpty r1 && Set.isEmpty r2 then
        Solved ctx
      else if not (Set.isEmpty r1) || not (Set.isEmpty r2) then
        Mismatch (RigidTailRemains (Set.union r1 r2))
      else
        Mismatch (RowMismatch n1 n2)

    -- (b) one side is determined, so the other's remainder must be empty
    [], [ s ] ->
      assign facts ctx s { known: d1, rigid: r1, flexible: Set.empty } d2 r2

    [ r ], [] ->
      assign facts ctx r { known: d2, rigid: r2, flexible: Set.empty } d1 r1

    -- (c) both tails are flexible: refine them together through a fresh one
    [ r ], [ s ] ->
      refine facts ctx r s d1 d2 r1 r2

    -- (d) more than one flexible tail on a side: no unique solution yet
    _, _ ->
      Stuck (Set.union m1 m2)

-- | Case (b). The side with no flexible tail has nothing left to absorb what
-- | remains on the other, so a leftover there is a mismatch. A rigid tail
-- | **can** be absorbed by the flexible side, which is the point of the split.
assign
  :: AtomicFacts
  -> MetaContext
  -> MetaVar
  -> XRowNormalForm
  -> Map RowKey XRowEntry
  -> Set TyVar
  -> UnifyResult
assign facts ctx m solution leftoverKnown leftoverRigid =
  if not (Map.isEmpty leftoverKnown) then
    Mismatch (RowMismatch solution { known: leftoverKnown, rigid: leftoverRigid, flexible: Set.empty })
  else if not (Set.isEmpty leftoverRigid) then
    Mismatch (RigidTailRemains leftoverRigid)
  else
    assignMeta facts ctx m (rebuild solution)

-- | Case (c). A substitution on one side alone either fails an occurs check or
-- | produces an unequal pair, so a fresh tail is introduced and **both** sides
-- | are refined through it.
refine
  :: AtomicFacts
  -> MetaContext
  -> MetaVar
  -> MetaVar
  -> Map RowKey XRowEntry
  -> Map RowKey XRowEntry
  -> Set TyVar
  -> Set TyVar
  -> UnifyResult
refine facts ctx r s d1 d2 r1 r2 =
  case lookupMeta ctx r, lookupMeta ctx s of
    Just (Unsolved infoR), Just (Unsolved infoS) ->
      -- Two bare metavariables have no element to give their row element kind
      -- away, so the kinds are unified here rather than at the assignment.
      case unifyKind ctx infoR.kind infoS.kind of
        Left _ ->
          Mismatch (KindMismatch s infoS.kind infoR.kind)

        Right ctxK ->
          let
            -- The fresh tail stands where both stood, so it may mention only
            -- what both had in scope.
            sharedScope =
              { types: Set.intersection infoR.scope.types infoS.scope.types
              , kinds: Set.intersection infoR.scope.kinds infoS.scope.kinds
              }

            -- Lacks(?t) ⊇ dom(D1) ∪ dom(D2) ∪ Lacks(?r) ∪ Lacks(?s), and
            -- ?t # R1, R2.
            requiredRigids = Set.unions [ infoR.disjointFrom, infoS.disjointFrom, r1, r2 ]

            freshInfo =
              { kind: substituteKind ctxK infoR.kind
              , scope: sharedScope
              , lacks: Set.unions
                  [ Set.fromFoldable (Map.keys d1)
                  , Set.fromFoldable (Map.keys d2)
                  , infoR.lacks
                  , infoS.lacks
                  ]
              , disjointFrom: requiredRigids
              }
          in
            -- The constraints the fresh tail must carry mention rigid
            -- variables of their own. A solver state that recorded one outside
            -- the tail's scope would keep that variable alive past its binder,
            -- so a refinement that cannot be written down is refused here.
            case Set.findMin (Set.difference requiredRigids sharedScope.types) of
              Just escaping ->
                Mismatch (FreshTailOutOfScope escaping)
              Nothing ->
                let
                  Tuple t ctx' = freshMeta freshInfo ctxK
                in
                  case assignMeta facts ctx' r (rebuild { known: d2, rigid: r2, flexible: Set.singleton t }) of
                    Solved ctx'' ->
                      assignMeta facts ctx'' s (rebuild { known: d1, rigid: r1, flexible: Set.singleton t })
                    other ->
                      other

    Just (Assigned _), _ -> Mismatch (MetaAlreadyAssigned r)
    Nothing, _ -> Mismatch (MetaUnbound r)
    _, Just (Assigned _) -> Mismatch (MetaAlreadyAssigned s)
    _, Nothing -> Mismatch (MetaUnbound s)

-- | Every substitution performs an occurs check, verifies the kind, and checks
-- | that the constraints assumed of the metavariable survive.
assignMeta :: AtomicFacts -> MetaContext -> MetaVar -> XType -> UnifyResult
assignMeta facts ctx m solution =
  case lookupMeta ctx m of
    Just (Unsolved info) ->
      if occursIn m solution then
        Mismatch (OccursCheck m solution)
      else case escapes info.scope solution of
        Just escaping ->
          Mismatch (escaping m)
        Nothing -> case kindAgrees ctx m info solution of
          Left err ->
            Mismatch err
          Right ctxK ->
            case obligationUnmet facts info solution of
              Just err ->
                Mismatch err
              Nothing ->
                case propagateLacks ctxK info solution >>= \ctx' -> narrowScopes ctx' info.scope solution of
                  Left err ->
                    Mismatch err
                  Right ctx' ->
                    Solved ctx' { bindings = Map.insert m (Assigned solution) ctx'.bindings }

    Just (Assigned _) ->
      Mismatch (MetaAlreadyAssigned m)

    Nothing ->
      Mismatch (MetaUnbound m)

-- | The kind a solution commits to, unified against the kind of the
-- | metavariable. A solution whose elements give no row element kind away
-- | commits to nothing, and there is nothing to unify.
kindAgrees :: MetaContext -> MetaVar -> MetaInfo -> XType -> Either UnifyError MetaContext
kindAgrees ctx m info solution = case rowKindOf solution of
  Nothing ->
    Right ctx
  Just k -> case unifyKind ctx info.kind k of
    Left _ -> Left (KindMismatch m info.kind k)
    Right ctxK -> Right ctxK

-- | Narrow every metavariable the solution mentions to the scope of the
-- | metavariable being solved, in both classes.
-- |
-- | `escapes` decides the rigid variables a solution mentions **now**, and a
-- | metavariable standing in one mentions none until it is solved. Without this
-- | narrowing, `?α` created outside a binder and solved to a type mentioning
-- | `?β` would admit whatever `?β` was later solved to, binder and all.
-- |
-- | **A narrowed metavariable carries metadata of its own, and that travels
-- | wherever the metavariable does.** Its kind names rigid kind variables and
-- | may hold kind metavariables, and its disjointness names rigid type
-- | variables; each is refused or narrowed in turn, so narrowing the scope alone
-- | would leave the metavariable holding what its new scope excludes. Refusing
-- | is why this reports rather than returning a context.
narrowScopes :: MetaContext -> Scope -> XType -> Either UnifyError MetaContext
narrowScopes ctx scope solution = do
  narrowed <- foldM narrowType ctx types
  foldM (narrowKindTo scope.kinds) narrowed kinds
  where
  -- Substituting first leaves only unsolved metavariables to narrow, so the
  -- fold reaches what a solution stands on rather than what it was written with.
  substituted = substitute ctx solution
  types = Set.toUnfoldable (metasOf substituted) :: P.Array MetaVar
  kinds = Set.toUnfoldable (kindMetasOfType substituted) :: P.Array KindMetaVar

  narrowType acc t = case Map.lookup t acc.bindings of
    Just (Unsolved tInfo) ->
      let
        within =
          { types: Set.intersection tInfo.scope.types scope.types
          , kinds: Set.intersection tInfo.scope.kinds scope.kinds
          }

        -- A kind the metavariable stands at may itself be solved, and a rigid
        -- variable reaches the metadata through that solution as readily as it
        -- is written there. Substituting is what brings either into view.
        kind = substituteKind acc tInfo.kind
      in
        case Set.findMin (Set.difference (kindVarsOf kind) within.kinds) of
          Just escaping ->
            Left (EscapingKindVariable t escaping)
          Nothing -> case Set.findMin (Set.difference tInfo.disjointFrom within.types) of
            Just escaping ->
              Left (EscapingVariable t escaping)
            Nothing -> do
              acc' <- foldM (narrowKindTo within.kinds) acc
                (Set.toUnfoldable (kindMetasOf kind) :: P.Array KindMetaVar)
              pure acc'
                { bindings = Map.insert t
                    (Unsolved (tInfo { kind = kind, scope = within }))
                    acc'.bindings
                }

    Just (Assigned _) ->
      Left (MetaAlreadyAssigned t)

    Nothing ->
      Left (MetaUnbound t)

-- | Narrow one kind metavariable against a scope, in the three states the
-- | context can hold it in.
-- |
-- | A solved one is closed rather than skipped: its solution is where a rigid
-- | variable outside the new scope would otherwise sit.
narrowKindTo :: Set KindVar -> MetaContext -> KindMetaVar -> Either UnifyError MetaContext
narrowKindTo scope ctx k = case Map.lookup k ctx.kindBindings of
  Just (KindUnsolved kInfo) ->
    Right ctx
      { kindBindings = Map.insert k
          (KindUnsolved (kInfo { scope = Set.intersection kInfo.scope scope }))
          ctx.kindBindings
      }

  Just (KindAssigned _) ->
    let
      -- Substituting resolves the chain entire, so what remains to narrow is
      -- unsolved and the recursion goes no deeper than that.
      solution = substituteKind ctx (XKMeta k)
    in
      case Set.findMin (Set.difference (kindVarsOf solution) scope) of
        Just escaping ->
          Left (KindEscapingVariable k escaping)
        Nothing ->
          foldM (narrowKindTo scope) ctx
            (Set.toUnfoldable (kindMetasOf solution) :: P.Array KindMetaVar)

  Nothing ->
    Left (KindMetaUnbound k)

-- | Whether a solution mentions anything its metavariable was not created
-- | under, in either class of variable.
escapes :: Scope -> XType -> Maybe (MetaVar -> UnifyError)
escapes scope solution =
  case Set.findMin escaped.types of
    Just a -> Just (\m -> EscapingVariable m a)
    Nothing -> map (\k m -> EscapingKindVariable m k) (Set.findMin escaped.kinds)
  where
  escaped = outOfScope scope solution

-- | The constraints assumed of a metavariable, checked against its solution.
-- |
-- | The known part is decided here: a key the metavariable lacks may not appear
-- | among the solution's elements. The **rigid** part of the tail is decided by
-- | `Γ*`, since `a ∉ ?m` solved to `r` holds exactly when the context gives
-- | `a ∉ r`. The flexible part is not decided but propagated, below.
obligationUnmet :: AtomicFacts -> MetaInfo -> XType -> Maybe UnifyError
obligationUnmet facts info solution = case xnf solution of
  Left _ ->
    Nothing
  Right n ->
    case Set.findMin (Set.intersection info.lacks (Set.fromFoldable (Map.keys n.known))) of
      Just key ->
        Just (LacksViolated key)
      Nothing ->
        case Array.head (Array.filter (not <<< lacksHolds) rigidLacks) of
          Just (Tuple key t) ->
            Just (LacksUnproven key t)
          Nothing ->
            case Array.head (Array.filter (not <<< keyAbsentFrom) knownAgainstDisjoint) of
              Just (Tuple key u) ->
                Just (LacksUnproven key u)
              Nothing ->
                map (\(Tuple t u) -> DisjointUnproven t u)
                  (Array.head (Array.filter (not <<< disjointHolds) rigidPairs))
    where
    rigidTail = Set.toUnfoldable n.rigid :: P.Array TyVar
    disjointRigids = Set.toUnfoldable info.disjointFrom :: P.Array TyVar
    knownKeys = Set.toUnfoldable (Set.fromFoldable (Map.keys n.known)) :: P.Array RowKey

    rigidLacks = do
      key <- Set.toUnfoldable info.lacks :: P.Array RowKey
      t <- rigidTail
      pure (Tuple key t)

    -- `?m # r` solved to a row carrying `a` needs `a ∉ r`: disjointness binds
    -- the known part of a solution as much as it binds the tail.
    knownAgainstDisjoint = do
      key <- knownKeys
      u <- disjointRigids
      pure (Tuple key u)

    rigidPairs = do
      t <- rigidTail
      u <- disjointRigids
      pure (Tuple t u)

    lacksHolds (Tuple key t) = entails facts (Lacks key (TVar t)) == Right true
    keyAbsentFrom (Tuple key u) = entails facts (Lacks key (TVar u)) == Right true
    disjointHolds (Tuple t u) = entails facts (Disjoint (TVar t) (TVar u)) == Right true

-- | The row element kind a solution commits to, which its known elements give
-- | away: an element carrying a type belongs to `Row Type`, one carrying an
-- | effect to `Row Effect`. A row of variables alone commits to neither, and
-- | there is nothing to check.
rowKindOf :: XType -> Maybe XKind
rowKindOf ty = case xnf ty of
  Left _ -> Nothing
  Right n -> map entryKind (Array.head (Map.toUnfoldable n.known # map snd :: P.Array XRowEntry))

entryKind :: XRowEntry -> XKind
entryKind = case _ of
  XRowTypeEntry _ _ -> XKRow RowType
  XRowEffectEntry _ _ -> XKRow RowEffect
  XRowLabelledEffectEntry _ _ _ -> XKRow RowEffect
  XRowRegionEntry _ _ -> XKRow RowEffect

-- | What `?r` lacks, the flexible tail of its solution must lack too.
propagateLacks :: MetaContext -> MetaInfo -> XType -> Either UnifyError MetaContext
propagateLacks ctx info solution = case xnf solution of
  Left err ->
    Left (NotARow err)
  Right n ->
    Right (foldr addLacks ctx (Set.toUnfoldable n.flexible :: P.Array MetaVar))
  where
  addLacks t acc = case Map.lookup t acc.bindings of
    Just (Unsolved tInfo) ->
      acc
        { bindings = Map.insert t
            (Unsolved (tInfo { lacks = Set.union tInfo.lacks info.lacks }))
            acc.bindings
        }
    _ -> acc

domain :: XRowNormalForm -> Set RowKey
domain n = Set.fromFoldable (Map.keys n.known)

derive instance Eq MetaBinding
derive instance Generic MetaBinding _

instance Show MetaBinding where
  show x = genericShow x

derive instance Eq KindRequirement
derive instance Ord KindRequirement
derive instance Generic KindRequirement _

instance Show KindRequirement where
  show = genericShow

derive instance Eq KindMetaBinding
derive instance Generic KindMetaBinding _

instance Show KindMetaBinding where
  show x = genericShow x

derive instance Eq UnifyError
derive instance Generic UnifyError _

instance Show UnifyError where
  show x = genericShow x

derive instance Eq UnifyResult
derive instance Generic UnifyResult _

instance Show UnifyResult where
  show x = genericShow x
