-- | Row unification over Core⁺.
-- |
-- | Solving `ρ1 ≡ ρ2` operates on the normal form, and the procedure is
-- | identical at `Row Type` and `Row Effect`: effect keys are rigid, so the
-- | domain of a normal form does not depend on how metavariables are solved.
-- |
-- | Three outcomes are distinguished. `Solved` records a substitution,
-- | `Mismatch` is a failure to report, and `Stuck` is neither: it names the
-- | metavariables whose solution would let the constraint be retried.
module Dawn.Compiler.Elaborate.Unify
  ( MetaInfo
  , MetaBinding(..)
  , MetaContext
  , UnifyError(..)
  , UnifyResult(..)
  , emptyContext
  , freshMeta
  , lookupMeta
  , substitute
  , unifyRow
  ) where

import Prelude

import Prim as P

import Dawn.Compiler.Elaborate.Row (XRowError, XRowNormalForm, payloadTypes, rebuild, xnf)
import Dawn.Compiler.Elaborate.Type (MetaVar(..), Scope, XConstraint(..), XRowEntry(..), XType(..), occursIn, outOfScope)
import Dawn.Compiler.TypedCore (Constraint(..), Kind(..), KindVar, RowElemKind(..), RowKey, TyVar, Type(..))
import Dawn.Compiler.TypedCore.Entailment (AtomicFacts, entails)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldr)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
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
  { kind :: Kind
  , scope :: Scope
  , lacks :: Set RowKey
  , disjointFrom :: Set TyVar
  }

data MetaBinding
  = Unsolved MetaInfo
  | Assigned XType

type MetaContext =
  { bindings :: Map MetaVar MetaBinding
  , next :: P.Int
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
  -- | A solution puts a rigid tail where the context does not prove the Lacks
  -- | the metavariable carries.
  | LacksUnproven RowKey TyVar
  -- | A solution puts a rigid tail where the context does not prove a
  -- | disjointness the metavariable carries.
  | DisjointUnproven TyVar TyVar
  -- | A solution mentions a rigid variable that was not in scope where the
  -- | metavariable was created.
  | EscapingVariable MetaVar TyVar
  -- | The same, for a kind variable.
  | EscapingKindVariable MetaVar KindVar
  -- | A fresh tail would have to mention a rigid variable that is not in scope
  -- | on both sides, so the refinement has no representable solution.
  | FreshTailOutOfScope TyVar
  -- | The kind of a solution does not match the kind of the metavariable.
  | KindMismatch MetaVar Kind Kind
  | NotARow XRowError

data UnifyResult
  = Solved MetaContext
  | Stuck (Set MetaVar)
  | Mismatch UnifyError

emptyContext :: MetaContext
emptyContext = { bindings: Map.empty, next: 0 }

freshMeta :: MetaInfo -> MetaContext -> Tuple MetaVar MetaContext
freshMeta info ctx =
  Tuple m ctx
    { bindings = Map.insert m (Unsolved info) ctx.bindings
    , next = ctx.next + 1
    }
  where
  m = MetaVar ctx.next

lookupMeta :: MetaContext -> MetaVar -> Maybe MetaBinding
lookupMeta ctx m = Map.lookup m ctx.bindings

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
    XApp f a -> XApp (go f) (go a)
    XForall a k body -> XForall a k (go body)
    XConstrained c body -> XConstrained (goConstraint c) (go body)
    XRowExtend entry rest -> XRowExtend (goEntry entry) (go rest)
    XRowUnion l r -> XRowUnion (go l) (go r)
    ty -> ty

  goEntry = case _ of
    XRowField l ty -> XRowField l (go ty)
    XRowEffectEntry e args -> XRowEffectEntry e (map go args)

  -- A constraint carries rows of its own, and a hole left in one of them would
  -- survive zonking and fail `toCore`.
  goConstraint = case _ of
    XLacks key row -> XLacks key (go row)
    XDisjoint l r -> XDisjoint (go l) (go r)

-- | `solve(ρ1 ≡ ρ2)`.
-- |
-- | Payload equations are returned rather than solved: equating `F1(l)` with
-- | `F2(l)` is type unification, which is a separate judgement. The caller
-- | discharges them.
unifyRow :: AtomicFacts -> MetaContext -> XType -> XType -> Tuple UnifyResult (P.Array (Tuple XType XType))
unifyRow facts ctx row1 row2 =
  case xnf (substitute ctx row1), xnf (substitute ctx row2) of
    Left err, _ -> Tuple (Mismatch (NotARow err)) []
    _, Left err -> Tuple (Mismatch (NotARow err)) []
    Right n1, Right n2 -> solve facts ctx n1 n2

solve :: AtomicFacts -> MetaContext -> XRowNormalForm -> XRowNormalForm -> Tuple UnifyResult (P.Array (Tuple XType XType))
solve facts ctx n1 n2 =
  Tuple (step4 facts ctx d1 d2 r1 r2 m1 m2 n1 n2) equations
  where
  -- 1. match the payloads of shared keys
  shared = Set.intersection (domain n1) (domain n2)
  equations = Array.concatMap payloadEquations (Set.toUnfoldable shared)

  payloadEquations key = case Map.lookup key n1.known, Map.lookup key n2.known of
    Just e1, Just e2 -> Array.zip (payloadTypes e1) (payloadTypes e2)
    _, _ -> []

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
    Just (Unsolved infoR), Just (Unsolved infoS)
      -- Two bare metavariables have no element to give their row element kind
      -- away, so the kinds are compared here rather than at the assignment.
      | infoR.kind /= infoS.kind ->
          Mismatch (KindMismatch s infoS.kind infoR.kind)

      | otherwise ->
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
              { kind: infoR.kind
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
                  Tuple t ctx' = freshMeta freshInfo ctx
                in
                  case assignMeta facts ctx' r (rebuild { known: d2, rigid: r2, flexible: Set.singleton t }) of
                    Solved ctx'' ->
                      assignMeta facts ctx'' s (rebuild { known: d1, rigid: r1, flexible: Set.singleton t })
                    other ->
                      other

    _, _ ->
      Stuck (Set.fromFoldable [ r, s ])

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
        Nothing -> case rowKindOf solution of
          Just k | k /= info.kind ->
            Mismatch (KindMismatch m info.kind k)
          _ ->
            case obligationUnmet facts info solution of
              Just err ->
                Mismatch err
              Nothing ->
                case propagateLacks ctx info solution of
                  Mismatch err -> Mismatch err
                  Stuck ms -> Stuck ms
                  Solved ctx' ->
                    Solved ctx' { bindings = Map.insert m (Assigned solution) ctx'.bindings }

    -- Assigning to something already solved, or to an unknown metavariable, is
    -- a caller error rather than a unification failure.
    _ ->
      Stuck (Set.singleton m)

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
-- | away: a field element belongs to `Row Type`, an effect element to
-- | `Row Effect`. A row of variables alone commits to neither, and there is
-- | nothing to check.
rowKindOf :: XType -> Maybe Kind
rowKindOf ty = case xnf ty of
  Left _ -> Nothing
  Right n -> map entryKind (Array.head (Map.toUnfoldable n.known # map snd :: P.Array XRowEntry))

entryKind :: XRowEntry -> Kind
entryKind = case _ of
  XRowField _ _ -> KRow RowType
  XRowEffectEntry _ _ -> KRow RowEffect

-- | What `?r` lacks, the flexible tail of its solution must lack too.
propagateLacks :: MetaContext -> MetaInfo -> XType -> UnifyResult
propagateLacks ctx info solution = case xnf solution of
  Left err ->
    Mismatch (NotARow err)
  Right n ->
    Solved (foldr addLacks ctx (Set.toUnfoldable n.flexible :: P.Array MetaVar))
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

derive instance Eq UnifyError
derive instance Generic UnifyError _

instance Show UnifyError where
  show x = genericShow x

derive instance Eq UnifyResult
derive instance Generic UnifyResult _

instance Show UnifyResult where
  show x = genericShow x
