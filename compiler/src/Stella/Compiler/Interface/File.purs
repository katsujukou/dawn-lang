-- | The bytes of a `.dmi`
-- | ([Interface](../../../../docs/technical-references/05-Backend/03-Interface.md)).
-- |
-- | A header and one table: the magic, the version of the format, the flags, the
-- | module's own name, and the arity of each value it exports that has one. The
-- | primitives are the `.dmo`'s ([Encoding](../../../../docs/technical-references/05-Backend/02-Encoding.md)),
-- | and what this adds is the order of the entries.
-- |
-- | **No string table, no ABI version, no sections.** No name occurs twice, so a
-- | table would buy an indirection; nothing here has a meaning an ABI version
-- | fixes; and there is nothing to skip or reorder, so a reader refuses a byte
-- | after the table rather than reading a later format as though it had ended.
-- |
-- | **The entries ascend strictly by name, compared by scalar value.** That is the
-- | format's order and not a host's — `Ord String` compares code units, which puts
-- | an astral character below `U+E000` where a scalar value puts it above — so both
-- | directions read the comparison below and two encoders write one file.
module Stella.Compiler.Interface.File
  ( encode
  , decode
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Bytecode.Bytes (Bytes, DecodeError(..), EncodeError(..), R, atEndR, expect, runR, structuralR, throwR, utf8, utf8R, uvar, uvarR, vecR)
import Stella.Compiler.Interface (Dmi)
import Stella.Compiler.TypedCore.Domain (textOf)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Enum (fromEnum)
import Data.Foldable (traverse_)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String.CodePoints (toCodePointArray)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))

-- | `"DMI\0"`, the four bytes a `.dmi` begins with.
magic :: Bytes
magic = [ 0x44, 0x4D, 0x49, 0x00 ]

-- | The version of the format this module reads and writes.
formatVersion :: P.Int
formatVersion = 0

-- | What an entry holds, once the name is text and the arity a count.
type Entry =
  { name :: P.String
  , arity :: P.Int
  }

-- | **What this writes, a decoder returns.** An arity below one is refused rather
-- | than written, absence being what a value without one has, and a name no reader
-- | could read is refused as it is for a `.dmo`.
encode :: Dmi -> Either EncodeError Bytes
encode dmi = do
  name <- text (case dmi.name of ModuleName m -> m)
  entries <- traverse entry (Map.toUnfoldable dmi.arities :: P.Array (Tuple Ident P.Int))
  emitted <- traverse write (Array.sortBy order entries)
  pure
    ( magic
        <> uvar formatVersion
        <> uvar 0
        <> name
        <> uvar (Array.length emitted)
        <> Array.concat emitted
    )
  where
  entry (Tuple ident arity) = case ident of
    Ident name
      | arity < 1 -> Left (ArityBelowOne ident arity)
      | otherwise -> Right { name, arity }

  write e = do
    name <- text e.name
    pure (name <> uvar e.arity)

  order a b = compareScalars a.name b.name

-- | A length-prefixed run of UTF-8.
text :: P.String -> Either EncodeError Bytes
text s = do
  bytes <- utf8 s
  pure (uvar (Array.length bytes) <> bytes)

decode :: Bytes -> Either DecodeError Dmi
decode bytes = runR bytes dmiR

dmiR :: R Dmi
dmiR = do
  traverse_ (\b -> expect b BadMagic) magic
  format <- uvarR
  when (format /= formatVersion) (throwR (UnsupportedFormatVersion format))
  flags <- uvarR
  when (flags /= 0) (throwR (UnknownFlags flags))
  name <- textR
  entries <- vecR entryR
  ascending entries
  done <- atEndR
  when (not done) (throwR TrailingBytes)
  pure
    { name: ModuleName name
    , arities: Map.fromFoldable (map (\e -> Tuple (Ident e.name) e.arity) entries)
    }

textR :: R P.String
textR = do
  n <- structuralR
  map textOf (utf8R n)

entryR :: R Entry
entryR = do
  name <- textR
  arity <- structuralR
  when (arity < 1) (throwR (ArityNotPositive arity))
  pure { name, arity }

-- | The entries ascend strictly, which is also what refuses a name twice: a
-- | repeat does not ascend.
ascending :: P.Array Entry -> R Unit
ascending entries = traverse_ pair (Array.zip entries (Array.drop 1 entries))
  where
  pair (Tuple a b) = case compareScalars a.name b.name of
    LT -> pure unit
    _ -> throwR EntriesOutOfOrder

-- | Two names by their scalar values, which is the order of their UTF-8 bytes,
-- | that encoding being order-preserving.
compareScalars :: P.String -> P.String -> Ordering
compareScalars a b = go 0 (codes a) (codes b)
  where
  codes = map fromEnum <<< toCodePointArray

  go i x y = case Array.index x i, Array.index y i of
    Nothing, Nothing -> EQ
    Nothing, _ -> LT
    _, Nothing -> GT
    Just p, Just q -> case compare p q of
      EQ -> go (i + 1) x y
      other -> other
