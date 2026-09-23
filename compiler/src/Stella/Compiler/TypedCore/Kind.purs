-- | Kinds of Typed Core.
-- |
-- | Kinds and types are separate syntactic classes (D2), and kinds are
-- | stratified into three layers (D24): row element kinds, general kinds, and
-- | the quantifiable subset.
module Stella.Compiler.TypedCore.Kind
  ( RowElemKind(..)
  , Kind(..)
  , Scheme
  , KindScheme
  , monoScheme
  , kindVarsOf
  , resultKind
  , substituteKind
  ) where

import Prelude

import Stella.Compiler.TypedCore.Name (KindVar)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- | The kinds a row may have elements of, written `ε`.
-- |
-- | `Row` is applied to one of these and to nothing else, which is what keeps
-- | degenerate row kinds such as `Row (Type -> Type)` out of the grammar.
data RowElemKind
  = RowType
  | RowEffect

-- | A kind, written `κ`.
-- |
-- | `KEffect` is the result kind of an effect constructor. It is a kind but not
-- | a quantifiable one, so `forall (e : Effect)` is underivable (D24).
data Kind
  = KVar KindVar
  | KType
  | KEffect
  | KRow RowElemKind
  | KFun Kind Kind

-- | A prenex kind scheme over `a`. The binder disappears when `kindVars` is
-- | empty, which is the case for most declarations.
type Scheme a =
  { kindVars :: Array KindVar
  , body :: a
  }

-- | The scheme of a type constructor, `T : forall k̄. κ`.
type KindScheme = Scheme Kind

-- | The scheme of something that binds no kind variable.
monoScheme :: forall a. a -> Scheme a
monoScheme body = { kindVars: [], body }

-- | The kind variables a kind mentions.
-- |
-- | Kind schemes are prenex (D3), so a kind has no binder of its own and every
-- | variable here is free.
kindVarsOf :: Kind -> Set KindVar
kindVarsOf = case _ of
  KVar k -> Set.singleton k
  KType -> Set.empty
  KEffect -> Set.empty
  KRow _ -> Set.empty
  KFun a b -> kindVarsOf a <> kindVarsOf b

-- | What a kind produces once it is fully applied.
-- |
-- | Only row syntax may produce a row, so this is `Type` for every type
-- | constructor and for every arrow inside a quantifiable kind, and `Effect`
-- | for an effect constructor.
resultKind :: Kind -> Kind
resultKind = case _ of
  KFun _ b -> resultKind b
  k -> k

-- | Instantiate kind variables. Kind schemes are prenex and instantiation is
-- | explicit, so this is a substitution over a kind and nothing more: there is
-- | no binder to avoid capturing.
substituteKind :: Map KindVar Kind -> Kind -> Kind
substituteKind sub = go
  where
  go = case _ of
    KVar k -> fromMaybe (KVar k) (Map.lookup k sub)
    KType -> KType
    KEffect -> KEffect
    KRow e -> KRow e
    KFun a b -> KFun (go a) (go b)

derive instance Eq RowElemKind
derive instance Ord RowElemKind
derive instance Generic RowElemKind _

instance Show RowElemKind where
  show = genericShow

derive instance Eq Kind
derive instance Ord Kind
derive instance Generic Kind _

instance Show Kind where
  show x = genericShow x
