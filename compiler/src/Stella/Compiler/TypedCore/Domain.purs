-- | The value domains of literals, and the identity of a literal within one.
-- |
-- | Every domain is fixed (D27, D37): an `Int` is a 32-bit signed integer, a
-- | `Number` is IEEE 754 binary64, a `Char` is a Unicode scalar value, a `String`
-- | is a sequence of those, and a `Boolean` is one of two values.
-- |
-- | Three of the five are the host's own types. This module carries what they do
-- | not: `ScalarValue` and `ScalarString`, the types a `Char` and a `String`
-- | literal hold, and the relation that decides when two `Number` literals are
-- | one.
-- |
-- | **A domain belongs to Core rather than to a target**, since two backends
-- | disagreeing on one would give a Core term two meanings
-- | ([Prim and Base](../../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)).
module Stella.Compiler.TypedCore.Domain
  ( ScalarValue
  , scalarValue
  , codePointOf
  , ScalarString
  , scalarString
  , scalarStringOf
  , textOf
  , scalarLength
  , scalarAt
  , sameNumber
  , compareNumber
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Enum (fromEnum, toEnum)
import Data.Maybe (Maybe(..))
import Data.String.CodePoints (CodePoint, fromCodePointArray, toCodePointArray)

-- | A Unicode scalar value: `0x0` to `0x10FFFF`, less the surrogates `0xD800`
-- | to `0xDFFF`.
-- |
-- | **A `Char` literal holds one of these rather than a code unit** (D27). A
-- | code unit holds no astral character whole and admits an unpaired surrogate,
-- | which no Stella `String` carries. The constructor is not exported, so a
-- | value of this type is a scalar value and nothing downstream checks it again.
newtype ScalarValue = ScalarValue CodePoint

-- | The scalar value a code stands for, where it stands for one: `toEnum` is
-- | what admits the range and the surrogates are what this refuses.
scalarValue :: P.Int -> Maybe ScalarValue
scalarValue code
  | surrogate code = Nothing
  | otherwise = map ScalarValue (toEnum code)

codePointOf :: ScalarValue -> P.Int
codePointOf (ScalarValue point) = fromEnum point

-- | A sequence of Unicode scalar values: text holding no unpaired surrogate.
-- |
-- | **A `String` literal carries one of these** (D27), for the reason a `Char`
-- | carries a `ScalarValue`: the host's string type admits an unpaired surrogate,
-- | and a Stella `String` does not. The constructor is not exported, so the
-- | invariant holds of every value of this type.
-- |
-- | Concatenation preserves it — neither half of a pair can stand alone in text
-- | that holds no unpaired surrogate — so the monoid is derived.
newtype ScalarString = ScalarString P.String

-- | The text a string stands for, where every code point in it is a scalar
-- | value.
scalarString :: P.String -> Maybe ScalarString
scalarString text
  | Array.any (surrogate <<< fromEnum) (toCodePointArray text) = Nothing
  | otherwise = Just (ScalarString text)

-- | The text a sequence of scalar values spells, which every such sequence
-- | spells: nothing built this way can carry an unpaired surrogate, so this needs
-- | no failure case and a reader of a file has one less unreachable branch.
scalarStringOf :: P.Array ScalarValue -> ScalarString
scalarStringOf values =
  ScalarString (fromCodePointArray (map (\(ScalarValue point) -> point) values))

textOf :: ScalarString -> P.String
textOf (ScalarString text) = text

-- | How many scalar values a string holds, which is what its length is (D27). A
-- | count of code units is the host's and is not this.
scalarLength :: ScalarString -> P.Int
scalarLength (ScalarString text) = Array.length (toCodePointArray text)

-- | The scalar value at an index, counting scalar values from zero. The only way
-- | this has none is an index outside the string: every element of one is a scalar
-- | value, which is what the type carries.
scalarAt :: P.Int -> ScalarString -> Maybe ScalarValue
scalarAt i (ScalarString text) =
  map ScalarValue (Array.index (toCodePointArray text) i)

surrogate :: P.Int -> P.Boolean
surrogate code = code >= 0xD800 && code <= 0xDFFF

-- | Literal identity on `Number`: equality of the bit pattern, with all NaNs
-- | taken as one (D37). So `0.0` and `-0.0` are different literals, and a NaN is
-- | one literal however it arose.
-- |
-- | IEEE equality decides nothing usable here — it identifies the two zeros and
-- | separates a NaN from itself — while `switchLit` requires its literals to be
-- | distinct. Neither case needs a bit pattern to decide: a NaN is the one value
-- | unequal to itself, and `1.0 / (-0.0)` is negative where `1.0 / 0.0` is not.
sameNumber :: P.Number -> P.Number -> P.Boolean
sameNumber x y
  | isNotANumber x = isNotANumber y
  | isNotANumber y = false
  | x == 0.0 && y == 0.0 = negativeZero x == negativeZero y
  | otherwise = x == y

-- | A total order agreeing with `sameNumber`, which is what lets the two stand
-- | together on one type: a NaN is above every number, and `-0.0` below `0.0`.
compareNumber :: P.Number -> P.Number -> Ordering
compareNumber x y
  | isNotANumber x = if isNotANumber y then EQ else GT
  | isNotANumber y = LT
  | x == 0.0 && y == 0.0 = case negativeZero x, negativeZero y of
      true, false -> LT
      false, true -> GT
      _, _ -> EQ
  | otherwise = compare x y

isNotANumber :: P.Number -> P.Boolean
isNotANumber x = x /= x

negativeZero :: P.Number -> P.Boolean
negativeZero x = 1.0 / x < 0.0

derive instance Eq ScalarValue
derive instance Ord ScalarValue
derive newtype instance Show ScalarValue

derive instance Eq ScalarString
derive instance Ord ScalarString
derive newtype instance Show ScalarString
derive newtype instance Semigroup ScalarString
derive newtype instance Monoid ScalarString
