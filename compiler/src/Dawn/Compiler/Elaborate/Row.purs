-- | Row normal forms over Core⁺.
-- |
-- | The tail is split in two. A rigid variable stands for an unknown the solver
-- | may not touch; a flexible one may be assigned. Keeping them apart in the
-- | type is what stops a case analysis from reading "the tail is not empty" as
-- | "the tail can absorb this", which is the error the Implementation Plan
-- | singles out.
-- |
-- | `known` holds entries rather than payloads, so a key and what it carries
-- | cannot drift apart when a normal form is written back as a row.
module Dawn.Compiler.Elaborate.Row
  ( XRowNormalForm
  , XRowError(..)
  , emptyXNormalForm
  , xnf
  , payloadTypes
  , rebuild
  ) where

import Prelude

import Prim as P

import Dawn.Compiler.Elaborate.Type (MetaVar, XRowEntry(..), XType(..), xRowEntryKey)
import Dawn.Compiler.TypedCore (RowKey, TyVar)
import Data.Either (Either(..))
import Data.Foldable (foldr)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)

-- | `⟨ F ; T ⟩` with `T` separated into the part that cannot be solved and the
-- | part that can.
type XRowNormalForm =
  { known :: Map RowKey XRowEntry
  , rigid :: Set TyVar
  , flexible :: Set MetaVar
  }

data XRowError
  = XDuplicateKey RowKey
  | XNotARow XType

emptyXNormalForm :: XRowNormalForm
emptyXNormalForm = { known: Map.empty, rigid: Set.empty, flexible: Set.empty }

-- | What an entry carries, which is what unification equates when two rows
-- | share a key.
payloadTypes :: XRowEntry -> P.Array XType
payloadTypes = case _ of
  XRowField _ ty -> [ ty ]
  XRowEffectEntry _ args -> args

-- | `nf` over Core⁺.
-- |
-- | A metavariable normalizes into the flexible tail without being looked
-- | through: a solved one is substituted away before normalizing, so reaching
-- | `XMeta` here means it is still unsolved.
-- |
-- | As in Core, the caller establishes that what it passes is a row of one row
-- | element kind. `XNotARow` and `XDuplicateKey` are defensive.
xnf :: XType -> Either XRowError XRowNormalForm
xnf = case _ of
  XRowEmpty ->
    Right emptyXNormalForm

  XVar a ->
    Right (emptyXNormalForm { rigid = Set.singleton a })

  XMeta m ->
    Right (emptyXNormalForm { flexible = Set.singleton m })

  XRowExtend entry rest -> do
    n <- xnf rest
    let key = xRowEntryKey entry
    case Map.lookup key n.known of
      Just _ -> Left (XDuplicateKey key)
      Nothing -> Right (n { known = Map.insert key entry n.known })

  XRowUnion left right -> do
    l <- xnf left
    r <- xnf right
    union l r

  ty ->
    Left (XNotARow ty)

union :: XRowNormalForm -> XRowNormalForm -> Either XRowError XRowNormalForm
union l r =
  case Set.findMin (Set.intersection (domain l) (domain r)) of
    Just shared ->
      Left (XDuplicateKey shared)
    Nothing ->
      Right
        { known: Map.union l.known r.known
        , rigid: Set.union l.rigid r.rigid
        , flexible: Set.union l.flexible r.flexible
        }

domain :: XRowNormalForm -> Set RowKey
domain n = Set.fromFoldable (Map.keys n.known)

-- | A normal form written back as a row, which is how a solution is recorded:
-- | `?s := D ⊎ R ⊎ ?t` is built here.
rebuild :: XRowNormalForm -> XType
rebuild n =
  foldr XRowUnion (foldr XRowUnion knownRow rigidRows) flexibleRows
  where
  knownRow =
    foldr XRowExtend XRowEmpty
      (Map.values n.known)

  rigidRows = map XVar (Set.toUnfoldable n.rigid) :: P.Array XType
  flexibleRows = map XMeta (Set.toUnfoldable n.flexible) :: P.Array XType

derive instance Eq XRowError
derive instance Generic XRowError _

instance Show XRowError where
  show x = genericShow x
