-- | A `Number` as the two 32-bit halves a `.dmo` carries.
-- |
-- | A `Number` is IEEE 754 binary64 (D37), and the container writes a constant as
-- | eight bytes of it, least significant byte first. Nothing but a bit pattern
-- | carries one exactly: a decimal rendering loses the sign of a zero, which
-- | literal identity reads.
-- |
-- | **A NaN is written as `quietNaN` and no other pattern.** Every NaN is one
-- | literal, so a payload would be a distinction the language does not make, and
-- | one encoding of that literal is what leaves one module one file
-- | ([Encoding](../../../../docs/technical-references/05-Backend/02-Encoding.md)).
module Stella.Compiler.Bytecode.Float
  ( Halves
  , halvesOfNumber
  , numberOfHalves
  , quietNaN
  ) where

import Prim as P

-- | The high and low 32 bits of a binary64, each as a signed 32-bit integer.
type Halves =
  { hi :: P.Int
  , lo :: P.Int
  }

foreign import halvesOfNumber :: P.Number -> Halves

foreign import numberOfHalves :: P.Int -> P.Int -> P.Number

-- | The one quiet NaN a `.dmo` carries, `0x7FF8000000000000`.
quietNaN :: Halves
quietNaN = { hi: 0x7FF80000, lo: 0x00000000 }
