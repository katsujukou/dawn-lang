-- | The value domains of literals, and identity within one (D27, D37).
-- |
-- | Three of the five domains are the host's own types and need no test: an
-- | `Int` is a 32-bit signed integer, a `Number` is IEEE 754 binary64, and a
-- | `Boolean` is one of two values. What is written here is the part the language
-- | fixes and the host does not — which codes are scalar values, which text is a
-- | sequence of them, and when two `Number` literals are one.
module Test.Stella.Compiler.TypedCore.Domain (spec) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore (Literal(..), codePointOf, scalarString, scalarStringOf, scalarValue, textOf)
import Stella.Compiler.TypedCore.Domain (scalarsOf)
import Data.Char as Char
import Data.Maybe (Maybe(..), isNothing)
import Data.String.CodeUnits as CodeUnits
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | A NaN, without a library to take one from: it is the one value unequal to
-- | itself, and dividing zero by zero produces one.
notANumber :: P.Number
notANumber = 0.0 / 0.0

-- | A literal of a scalar value, where the code is one.
charLit :: P.Int -> Maybe Literal
charLit code = map LitChar (scalarValue code)

-- | A literal of text, where every code point in it is a scalar value.
stringLit :: P.String -> Maybe Literal
stringLit text = map LitString (scalarString text)

-- | Text holding one unpaired surrogate, which is what a host's string type
-- | admits and a Stella `String` does not. A code unit is the only way to write
-- | one: a scalar value cannot be a surrogate.
loneSurrogate :: Maybe P.String
loneSurrogate = map CodeUnits.singleton (Char.fromCharCode 0xD800)

spec :: Spec Unit
spec = describe "Stella.Compiler.TypedCore.Domain" do
  describe "scalar values" do
    it "admits a code the whole range holds, astral planes included" do
      -- a scalar value is not a code unit: an astral character is one value
      map codePointOf (scalarValue 0x1F600) `shouldEqual` Just 0x1F600
      map codePointOf (scalarValue 0x0) `shouldEqual` Just 0x0
      map codePointOf (scalarValue 0x10FFFF) `shouldEqual` Just 0x10FFFF

    it "refuses a surrogate, which no Stella String carries" do
      isNothing (scalarValue 0xD800) `shouldEqual` true
      isNothing (scalarValue 0xDBFF) `shouldEqual` true
      isNothing (scalarValue 0xDC00) `shouldEqual` true
      isNothing (scalarValue 0xDFFF) `shouldEqual` true

    it "admits the codes either side of the surrogates" do
      map codePointOf (scalarValue 0xD7FF) `shouldEqual` Just 0xD7FF
      map codePointOf (scalarValue 0xE000) `shouldEqual` Just 0xE000

    it "refuses a code outside the range" do
      isNothing (scalarValue (-1)) `shouldEqual` true
      isNothing (scalarValue 0x110000) `shouldEqual` true

  describe "strings of scalar values" do
    it "admits text a Stella String may hold" do
      map textOf (scalarString "hello") `shouldEqual` Just "hello"
      -- an astral character is a pair of code units in the host's string and one
      -- scalar value in this one
      map textOf (scalarString "😀") `shouldEqual` Just "😀"
      map textOf (scalarString "") `shouldEqual` Just ""

    it "gives back the scalar values it holds, an astral character as one" do
      map (map codePointOf <<< scalarsOf) (scalarString "a😀")
        `shouldEqual` Just [ 0x61, 0x1F600 ]
      -- the inverse of `scalarStringOf`, so text survives the round trip
      map (textOf <<< scalarStringOf <<< scalarsOf) (scalarString "a😀b")
        `shouldEqual` Just "a😀b"

    it "refuses text carrying an unpaired surrogate" do
      -- D27: a Stella String is a sequence of scalar values, so the host's
      -- string type admits text this one does not
      map (isNothing <<< scalarString) loneSurrogate `shouldEqual` Just true

    it "carries the refusal into a literal" do
      (loneSurrogate >>= stringLit) `shouldEqual` Nothing
      isNothing (stringLit "ok") `shouldEqual` false

  describe "literal identity" do
    it "tells the two zeros apart" do
      -- IEEE equality identifies them, and `switchLit` would then have one
      -- branch where the module wrote two
      (LitNumber 0.0 == LitNumber (-0.0)) `shouldEqual` false
      compare (LitNumber (-0.0)) (LitNumber 0.0) `shouldEqual` LT

    it "takes every NaN as one literal" do
      -- IEEE equality separates a NaN from itself, which would leave a dispatch
      -- with two branches on one literal
      (LitNumber notANumber == LitNumber notANumber) `shouldEqual` true
      compare (LitNumber notANumber) (LitNumber notANumber) `shouldEqual` EQ

    it "orders a NaN above every number" do
      compare (LitNumber notANumber) (LitNumber 1.0) `shouldEqual` GT
      compare (LitNumber 1.0) (LitNumber notANumber) `shouldEqual` LT

    it "is ordinary equality elsewhere" do
      (LitNumber 1.5 == LitNumber 1.5) `shouldEqual` true
      (LitNumber 1.5 == LitNumber 2.5) `shouldEqual` false
      (LitInt 1 == LitInt 1) `shouldEqual` true
      (stringLit "a" == stringLit "a") `shouldEqual` true
      (charLit 0x61 == charLit 0x61) `shouldEqual` true
      (charLit 0x61 == charLit 0x62) `shouldEqual` false

    it "holds no literal of one domain equal to one of another" do
      (LitInt 1 == LitBoolean true) `shouldEqual` false
      (LitNumber 1.0 == LitInt 1) `shouldEqual` false
