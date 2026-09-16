-- | Names of Typed Core.
-- |
-- | Name resolution and hygiene are complete by the time a term reaches Core,
-- | so these types carry neither scope information nor expansion traces.
module Dawn.Compiler.TypedCore.Name
  ( ModuleName(..)
  , Ident(..)
  , TyName(..)
  , TyVar(..)
  , KindVar(..)
  , Label(..)
  , EffName(..)
  , OpName(..)
  , JoinName(..)
  , Qualified(..)
  , qualifier
  , unqualified
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- | A fully qualified module name, written with its segments joined by dots.
newtype ModuleName = ModuleName String

-- | A value-level identifier.
-- |
-- | Data constructors live in this namespace: a constructor is an ordinary
-- | global name whose type, tag, and arity the declaration table records.
newtype Ident = Ident String

-- | A type constructor name.
newtype TyName = TyName String

-- | A type variable.
newtype TyVar = TyVar String

-- | A kind variable. Kind schemes are prenex, so a kind variable is bound only
-- | by a declaration (D3).
newtype KindVar = KindVar String

-- | A row key that is written: a record field name or a variant tag.
-- |
-- | A label is not a name. Effect rows have no label component; their key is
-- | the effect constructor at the head of the element (D16).
newtype Label = Label String

-- | An effect constructor name, which is the key of a `Row Effect` element.
newtype EffName = EffName String

-- | An effect operation name, unique within its effect declaration.
newtype OpName = OpName String

-- | A join point name. Join points are not first class and do not cross a
-- | function boundary.
newtype JoinName = JoinName String

-- | A name owned by a module. Every Core name that refers to a declaration is
-- | qualified; local names introduced by binders are not.
data Qualified a = Qualified ModuleName a

qualifier :: forall a. Qualified a -> ModuleName
qualifier (Qualified m _) = m

unqualified :: forall a. Qualified a -> a
unqualified (Qualified _ a) = a

derive instance Eq ModuleName
derive instance Ord ModuleName
derive newtype instance Show ModuleName

derive instance Eq Ident
derive instance Ord Ident
derive newtype instance Show Ident

derive instance Eq TyName
derive instance Ord TyName
derive newtype instance Show TyName

derive instance Eq TyVar
derive instance Ord TyVar
derive newtype instance Show TyVar

derive instance Eq KindVar
derive instance Ord KindVar
derive newtype instance Show KindVar

derive instance Eq Label
derive instance Ord Label
derive newtype instance Show Label

derive instance Eq EffName
derive instance Ord EffName
derive newtype instance Show EffName

derive instance Eq OpName
derive instance Ord OpName
derive newtype instance Show OpName

derive instance Eq JoinName
derive instance Ord JoinName
derive newtype instance Show JoinName

derive instance Eq a => Eq (Qualified a)
derive instance Ord a => Ord (Qualified a)
derive instance Functor Qualified
derive instance Generic (Qualified a) _

instance Show a => Show (Qualified a) where
  show = genericShow
