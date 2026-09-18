-- | Types, rows, and row constraints of Typed Core.
-- |
-- | The type grammar has application but no abstraction, so Core lies between
-- | System F and System Fω (D1) and type equality is syntactic apart from row
-- | normalization.
module Dawn.Compiler.TypedCore.Type
  ( Type(..)
  , RowEntry(..)
  , RowKey(..)
  , RowPayload(..)
  , Constraint(..)
  , TyBinder
  , TypeScheme
  , rowEntryKey
  , rowEntryPayload
  ) where

import Prelude

-- `Prim` is imported qualified, which replaces its implicit open import. Core's
-- own `Type` and `Constraint` would otherwise shadow the `Prim` names of those
-- spellings.
import Prim as P

import Dawn.Compiler.TypedCore.Kind (Kind, Scheme)
import Dawn.Compiler.TypedCore.Name (EffName, Qualified, Symbol, Tag, TyName, TyVar)
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
-- | Every element is a key together with a payload. At `Row Type` the key is
-- | written; at `Row Effect` it is derived from the effect at the head of the
-- | payload unless a `Symbol` is written for it.
data RowEntry
  -- | `k : τ` — an element of a `Row Type`. The key is written, and any
  -- | structural key may stand there; which one a structure conventionally
  -- | uses is settled by the surface, not by kinding.
  = RowTypeEntry RowKey Type
  -- | `E τ̄` — an element of a `Row Effect` whose key is derived from the
  -- | effect at the head of its payload.
  | RowEffectEntry (Qualified EffName) (P.Array Type)
  -- | `SymbolKey s : E τ̄` — the same, with a key written for it. This is what
  -- | lets one effect appear twice in a row.
  | RowLabelledEffectEntry Symbol (Qualified EffName) (P.Array Type)

-- | The key of a row element. Keys are rigid — independent of metavariable
-- | solving — which is what makes row equality decidable (D13, D16).
-- | Three of these are **structural**, decided by the syntax that writes them,
-- | and one is **nominal**, decided by a declaration in `Σ`. The row theory
-- | tells them apart nowhere: to normalization, equality, and entailment all
-- | four are rigid keys that compare for equality. Only well-formedness looks,
-- | since only an `EffectKey` sends the checker to `Σ`.
data RowKey
  = SymbolKey Symbol
  | TagKey Tag
  -- | A tuple component, 0-origin. Elaborating a tuple derives it from where
  -- | the component stands (D13).
  | PositionKey P.Int
  | EffectKey (Qualified EffName)

-- | What an element carries once its key is taken away.
-- |
-- | At `Row Type` that is the type; at `Row Effect` it is an application of a
-- | declared effect constructor, and **the payload is what decides the
-- | protocol** — a `perform` reads its operation's signature from `E`, never
-- | from the key.
data RowPayload
  = TypePayload Type
  | EffectPayload (Qualified EffName) (P.Array Type)

rowEntryKey :: RowEntry -> RowKey
rowEntryKey = case _ of
  RowTypeEntry k _ -> k
  RowEffectEntry e _ -> EffectKey e
  RowLabelledEffectEntry s _ _ -> SymbolKey s

rowEntryPayload :: RowEntry -> RowPayload
rowEntryPayload = case _ of
  RowTypeEntry _ ty -> TypePayload ty
  RowEffectEntry e args -> EffectPayload e args
  RowLabelledEffectEntry _ e args -> EffectPayload e args

-- | A row constraint. Core has exactly two, and neither carries run-time
-- | content: the checker re-derives entailment rather than accepting a proof
-- | term (D5).
data Constraint
  -- | `k ∉ ρ`
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

derive instance Eq RowPayload
derive instance Ord RowPayload
derive instance Generic RowPayload _

instance Show RowPayload where
  show x = genericShow x

derive instance Eq Constraint
derive instance Ord Constraint
derive instance Generic Constraint _

instance Show Constraint where
  show x = genericShow x
