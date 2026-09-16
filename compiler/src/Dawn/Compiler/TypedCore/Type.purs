-- | Types, rows, and row constraints of Typed Core.
-- |
-- | The type grammar has application but no abstraction, so Core lies between
-- | System F and System Fω (D1) and type equality is syntactic apart from row
-- | normalization.
module Dawn.Compiler.TypedCore.Type
  ( Type(..)
  , RowEntry(..)
  , RowKey(..)
  , Constraint(..)
  , TyBinder
  , TypeScheme
  , rowEntryKey
  ) where

import Prelude

-- `Prim` is imported qualified, which replaces its implicit open import. Core's
-- own `Type` and `Constraint` would otherwise shadow the `Prim` names of those
-- spellings.
import Prim as P

import Dawn.Compiler.TypedCore.Kind (Kind, Scheme)
import Dawn.Compiler.TypedCore.Name (EffName, Label, Qualified, TyName, TyVar)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- | A type, written `τ`, `σ`, or `ρ`.
-- |
-- | Rows are types: `TRowEmpty`, `TRowExtend`, and `TRowUnion` are the three row
-- | operators Core has (D6). A function type is an application of the type
-- | constructor `Prim.Function`; Core has no arrow syntax.
data Type
  = TVar TyVar
  -- | A type constructor with its kind scheme instantiated, `T [[κ̄]]`. The
  -- | array is empty where the scheme is.
  | TCon (Qualified TyName) (P.Array Kind)
  | TApp Type Type
  | TForall TyVar Kind Type
  -- | Constraint abstraction, `C => τ`, erased at run time.
  | TConstrained Constraint Type
  -- | The empty row, `()`.
  | TRowEmpty
  -- | Row extension, `( ent | ρ )`. Well-kindedness requires the entry's key to
  -- | be absent from the tail, which is what makes rows sharp (D4).
  | TRowExtend RowEntry Type
  -- | Row union, `ρ1 ⊎ ρ2`, well-kinded only where the two are disjoint.
  | TRowUnion Type Type

-- | An element of a row.
-- |
-- | A `Row Type` element carries the label that is written; a `Row Effect`
-- | element carries no label, since its key is the constructor at its head.
data RowEntry
  = RowField Label Type
  | RowEffectEntry (Qualified EffName) (P.Array Type)

-- | The key of a row element. Keys are rigid — independent of metavariable
-- | solving — which is what makes row equality decidable (D13, D16).
data RowKey
  = FieldKey Label
  | EffectKey (Qualified EffName)

rowEntryKey :: RowEntry -> RowKey
rowEntryKey = case _ of
  RowField l _ -> FieldKey l
  RowEffectEntry e _ -> EffectKey e

-- | A row constraint. Core has exactly two, and neither carries run-time
-- | content: the checker re-derives entailment rather than accepting a proof
-- | term (D5).
data Constraint
  -- | `l ∉ ρ`
  = Lacks RowKey Type
  -- | `ρ1 # ρ2`
  | Disjoint Type Type

-- | A type variable together with the kind it is introduced at. Every such site
-- | requires a quantifiable kind (D24).
type TyBinder =
  { name :: TyVar
  , kind :: Kind
  }

-- | The declared type of a value, foreign, or data constructor, `forall k̄. σ`.
type TypeScheme = Scheme Type

-- | Structural equality of the syntax. This is not the type equality `≡` of the
-- | specification, which compares rows by their normal form.
derive instance Eq Type
derive instance Ord Type
derive instance Generic Type _

instance Show Type where
  show x = genericShow x

derive instance Eq RowEntry
derive instance Ord RowEntry
derive instance Generic RowEntry _

instance Show RowEntry where
  show x = genericShow x

derive instance Eq RowKey
derive instance Ord RowKey
derive instance Generic RowKey _

instance Show RowKey where
  show = genericShow

derive instance Eq Constraint
derive instance Ord Constraint
derive instance Generic Constraint _

instance Show Constraint where
  show x = genericShow x
