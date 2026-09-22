-- | Representation types.
-- |
-- | A `Rep` says which class of value flows through a binding. It is not a type
-- | in the sense of Core: it has no rows, no quantifiers, no constraints, and no
-- | effect row.
-- |
-- | **A `Rep` is descriptive.** It records what the Core type already said and
-- | obliges a backend to nothing: there is no coercion form and nothing converts
-- | between representation types. A backend keeping one uniform representation
-- | ignores it; one choosing an unboxed integer or a struct per data type reads
-- | it and inserts whatever its own choice calls for.
-- |
-- | `Val` means unknown, and is sound wherever a type is not to hand.
module Dawn.Compiler.MidIR.Rep
  ( Rep(..)
  , repOf
  ) where

import Prelude

import Prim as P

import Dawn.Compiler.TypedCore.Name (Qualified, TyName)
import Dawn.Compiler.TypedCore.Prim (booleanTy, charTy, functionTy, intTy, numberTy, recordTy, stringTy, variantTy)
import Dawn.Compiler.TypedCore.Signature (CanonicalClass(..), Signature, TyConInfo(..), lookupTyCon)
import Dawn.Compiler.TypedCore.Type (Type(..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)

data Rep
  = RepInt
  | RepNumber
  | RepChar
  | RepString
  | RepBoolean
  -- | Anything callable: a closure, a partial application, a continuation.
  -- | What unites them is that applying one is the only thing to do with it.
  | RepClos
  | RepRec
  | RepVariant
  -- | A value of a declared data type, which the type constructor names so that
  -- | a backend choosing a layout per type can find its constructors.
  | RepData (Qualified TyName)
  -- | A value only a foreign observes. Nothing takes one apart.
  | RepOpaque
  -- | Unknown: the Core type is a variable, or none was to hand.
  | RepVal

-- | `rep`, total on well-kinded types of kind `Type`.
-- |
-- | A `forall` and a constraint arrow contribute nothing, the abstractions they
-- | type being erased, so a value of such a type is a value of its body.
-- | Applying a type variable leaves the head unknown.
repOf :: Signature -> Type -> Rep
repOf sig = case _ of
  TForall _ _ body -> repOf sig body
  TConstrained _ body -> repOf sig body
  ty -> case headOf ty of
    Just name
      | name == intTy -> RepInt
      | name == numberTy -> RepNumber
      | name == charTy -> RepChar
      | name == stringTy -> RepString
      | name == booleanTy -> RepBoolean
      | name == functionTy -> RepClos
      | name == recordTy -> RepRec
      | name == variantTy -> RepVariant
      | otherwise -> case lookupTyCon sig name of
          Just (DataTyCon _ _) -> RepData name
          Just (IntrinsicTyCon _ CanonicalOpaque) -> RepOpaque
          Just (IntrinsicTyCon _ CanonicalLiteral) -> RepVal
          Just (IntrinsicTyCon _ CanonicalFunction) -> RepClos
          Just (IntrinsicTyCon _ CanonicalRecord) -> RepRec
          Just (IntrinsicTyCon _ CanonicalVariant) -> RepVariant
          Nothing -> RepVal
    Nothing -> RepVal

-- | The type constructor at the head of an application spine, where there is
-- | one. A head that is a type variable, a row, or a quantifier has none.
headOf :: Type -> Maybe (Qualified TyName)
headOf = case _ of
  TCon name _ -> Just name
  TApp f _ -> headOf f
  _ -> Nothing

derive instance Eq Rep
derive instance Ord Rep
derive instance Generic Rep _

instance Show Rep where
  show x = genericShow x
