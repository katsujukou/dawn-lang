-- | Row normal forms.
-- |
-- | A row is a keyed, unordered, duplicate-free collection, so its normal form
-- | is a finite map from keys to payloads together with a set of row variables
-- | standing for the unknown tail. Normalization never closes a row variable,
-- | which is what makes row equality decidable on open rows.
-- |
-- | Keys are rigid — a label is a literal (D13) and an effect key is the head
-- | constructor (D16) — so no key changes while a row is normalized.
module Dawn.Compiler.TypedCore.Row
  ( RowPayload(..)
  , RowNormalForm
  , RowError(..)
  , emptyNormalForm
  , nf
  , entryPayload
  ) where

import Prelude

import Prim as P

import Dawn.Compiler.TypedCore.Name (TyVar)
import Dawn.Compiler.TypedCore.Type (RowEntry(..), RowKey, Type(..), rowEntryKey)
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)

-- | What a row element carries once its key is taken away: a type at
-- | `Row Type`, an argument vector at `Row Effect`.
data RowPayload
  = FieldPayload Type
  | EffectPayload (P.Array Type)

-- | `⟨ F ; T ⟩`.
-- |
-- | `known` is `F` and `tail` is `T`. A row is closed exactly when `tail` is
-- | empty.
type RowNormalForm =
  { known :: Map RowKey RowPayload
  , tail :: Set TyVar
  }

-- | Normalization fails only on input the kinding rules already reject.
data RowError
  -- | The same key twice, which sharpness forbids (D4).
  = DuplicateKey RowKey
  -- | A type that is not a row at all.
  | NotARow Type

emptyNormalForm :: RowNormalForm
emptyNormalForm = { known: Map.empty, tail: Set.empty }

entryPayload :: RowEntry -> RowPayload
entryPayload = case _ of
  RowField _ ty -> FieldPayload ty
  RowEffectEntry _ args -> EffectPayload args

-- | `nf`.
-- |
-- | **The caller establishes `Γ ⊢ ρ : Row ε` first.** `NotARow` and
-- | `DuplicateKey` are defensive checks, not a replacement for kinding: a type
-- | variable alone does not carry its kind, so `nf` cannot decide on its own
-- | that what it is given is a row. Kind-check the tail of a row extension and
-- | both sides of a union before normalizing or deciding entailment.
-- |
-- | A duplicate is reported rather than silently resolved, because
-- | normalization is part of the trusted core and must not turn an ill-kinded
-- | row into a well-formed one.
-- |
-- | A repeated row *variable*, as in `r ⊎ r`, is absorbed by the union of sets
-- | and is not an error here. What decides it is the union's side condition
-- | `r # r`, which an ordinary context does not derive.
nf :: Type -> Either RowError RowNormalForm
nf = case _ of
  TRowEmpty ->
    Right emptyNormalForm

  TVar a ->
    Right { known: Map.empty, tail: Set.singleton a }

  TRowExtend entry rest -> do
    { known, tail } <- nf rest
    let key = rowEntryKey entry
    case Map.lookup key known of
      Just _ -> Left (DuplicateKey key)
      Nothing ->
        Right { known: Map.insert key (entryPayload entry) known, tail }

  TRowUnion left right -> do
    l <- nf left
    r <- nf right
    union l r

  ty ->
    Left (NotARow ty)

union :: RowNormalForm -> RowNormalForm -> Either RowError RowNormalForm
union l r =
  case Set.findMin (Set.intersection (keysOf l) (keysOf r)) of
    Just shared -> Left (DuplicateKey shared)
    Nothing ->
      Right
        { known: Map.union l.known r.known
        , tail: Set.union l.tail r.tail
        }
  where
  keysOf n = Set.fromFoldable (Map.keys n.known)

derive instance Eq RowPayload
derive instance Ord RowPayload
derive instance Generic RowPayload _

instance Show RowPayload where
  show x = genericShow x

derive instance Eq RowError
derive instance Generic RowError _

instance Show RowError where
  show x = genericShow x
