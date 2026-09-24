-- | The operations of `stella-base-0.1`, as this interpreter carries them out.
-- |
-- | What each one means is the ABI's
-- | ([Prim and Base](../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)),
-- | so these cases are that document read back: arithmetic wraps and faults on
-- | nothing, a length counts scalar values, and an index outside a string faults.
module Test.Steam.Ops (spec) where

import Prelude

import Prim as P

import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Steam.Op (Fault(..), Refusal(..), carryOut)
import Steam.Value (Value(..))
import Stella.Compiler.Primitive (PrimOp(..))
import Stella.Compiler.TypedCore.Domain (ScalarString, codePointOf, scalarString)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- | The largest and smallest `Int`, which is where wrapping shows.
maxInt :: P.Int
maxInt = 2147483647

minInt :: P.Int
minInt = -2147483648

-- | Two scalar values and an astral one, which a count of code units would get
-- | wrong.
text :: Maybe ScalarString
text = scalarString "a😀"

-- | What an operation produced, as far as a test needs it.
data Held
  = AnInt P.Int
  | AChar P.Int
  | Elsewhere

held :: Either Refusal Value -> Either Refusal Held
held = map case _ of
  VInt n -> AnInt n
  VChar c -> AChar (codePointOf c)
  _ -> Elsewhere

spec :: Spec Unit
spec = describe "Steam.Op" do

  describe "arithmetic" do
    it "adds and subtracts" do
      held (carryOut IntAdd [ VInt 2, VInt 3 ]) `shouldEqual` Right (AnInt 5)
      held (carryOut IntSub [ VInt 2, VInt 3 ]) `shouldEqual` Right (AnInt (-1))

    it "wraps at 32 bits, and faults on nothing" do
      -- what every backend owes, whatever its host does on overflow
      held (carryOut IntAdd [ VInt maxInt, VInt 1 ]) `shouldEqual` Right (AnInt minInt)
      held (carryOut IntSub [ VInt minInt, VInt 1 ]) `shouldEqual` Right (AnInt maxInt)

  describe "strings" do
    it "counts scalar values rather than code units" do
      case text of
        Nothing -> fail "the fixture is a scalar string"
        Just s -> held (carryOut StringLength [ VString s ]) `shouldEqual` Right (AnInt 2)

    it "indexes by scalar value, astral characters among them" do
      case text of
        Nothing -> fail "the fixture is a scalar string"
        Just s -> do
          held (carryOut StringCodePointAt [ VInt 0, VString s ])
            `shouldEqual` Right (AChar 0x61)
          held (carryOut StringCodePointAt [ VInt 1, VString s ])
            `shouldEqual` Right (AChar 0x1F600)

    it "faults outside the string" do
      case text of
        Nothing -> fail "the fixture is a scalar string"
        Just s -> do
          held (carryOut StringCodePointAt [ VInt 2, VString s ])
            `shouldEqual` Left (Faulted (IndexOutsideString 2 2))
          held (carryOut StringCodePointAt [ VInt (-1), VString s ])
            `shouldEqual` Left (Faulted (IndexOutsideString (-1) 2))

  describe "what is not an operation's to decide" do
    it "refuses operands it does not take" do
      held (carryOut IntAdd [ VInt 1 ]) `shouldEqual` Left WrongOperands
      held (carryOut IntAdd [ VInt 1, VBoolean true ]) `shouldEqual` Left WrongOperands

    it "names the one entry it does not carry out" do
      held (carryOut ArrayUnsafeIndex [ VInt 0, VInt 0 ])
        `shouldEqual` Left (NotImplemented ArrayUnsafeIndex)

derive instance Eq Held
derive instance Generic Held _

instance Show Held where
  show = genericShow
