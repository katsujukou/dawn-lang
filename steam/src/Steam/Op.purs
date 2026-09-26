-- | Carrying out an operation of `stella-base-0.1`
-- | ([Prim and Base](../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)).
-- |
-- | An **operation** is a `Base` ABI entry a machine carries out itself rather than
-- | through a foreign implementation. What each one means, and which of them may
-- | fault, is the ABI's and is one meaning for every backend; this module is where
-- | this interpreter implements what is written there.
module Steam.Op
  ( Refusal(..)
  , carryOut
  , implemented
  ) where

import Prelude

import Prim as P

import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Steam.Fault (Fault(..))
import Steam.Value (Value(..))
import Stella.Compiler.Primitive (PrimOp(..))
import Stella.Compiler.TypedCore.Domain (scalarAt, scalarLength)

-- | Why an operation produced no value.
data Refusal
  = Faulted Fault
  -- | Operands the entry does not take. Their classes and their number are settled
  -- | before a `.dmo` exists, so this is a defect above the interpreter rather than
  -- | a failure of the program.
  | WrongOperands
  -- | An operation outside what this interpreter carries out. A module naming one
  -- | is refused where it is loaded, so this is what a `.dmo` that got past that
  -- | would produce.
  | NotImplemented PrimOp

-- | The operations this interpreter carries out. A module naming any other is one
-- | it cannot load.
implemented :: P.Array PrimOp
implemented = [ IntAdd, IntSub, StringLength, StringCodePointAt ]

-- | What an operation computes from the arguments it is given.
carryOut :: PrimOp -> P.Array Value -> Either Refusal Value
carryOut op args = case op, args of
  -- **32-bit wrapping arithmetic**, which every backend owes whatever its host
  -- does: neither of these faults.
  IntAdd, [ VInt a, VInt b ] -> Right (VInt (a + b))
  IntSub, [ VInt a, VInt b ] -> Right (VInt (a - b))

  -- the number of Unicode scalar values, which is what the length of a `String`
  -- is (D27)
  StringLength, [ VString s ] -> Right (VInt (scalarLength s))

  -- the scalar value at a **scalar index**, counting from zero
  StringCodePointAt, [ VInt i, VString s ] -> case scalarAt i s of
    Just scalar -> Right (VChar scalar)
    Nothing -> Left (Faulted (IndexOutsideString i (scalarLength s)))

  ArrayUnsafeIndex, _ -> Left (NotImplemented ArrayUnsafeIndex)

  _, _ -> Left WrongOperands

derive instance Eq Refusal
derive instance Generic Refusal _

instance Show Refusal where
  show = genericShow
