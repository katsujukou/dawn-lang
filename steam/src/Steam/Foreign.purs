-- | The host's foreign function table
-- | ([Abstract Machine](../../../docs/technical-references/07-Runtime/01-Abstract-Machine.md)).
-- |
-- | **The table is the host's to build and the interpreter's to read.** Resolving a
-- | module name to a module specifier, and an unqualified name to an export of it,
-- | is the host's, as is whatever it takes to reach that export; what arrives here
-- | is a table already assembled, and nothing below looks for anything.
-- |
-- | **A module's foreigns are resolved where that module is loaded**, so this is
-- | read once per declaration and never while a program runs
-- | ([Load](Load.purs)).
-- |
-- | What the table does not hold is an effect summary. Whether an entry returns an
-- | `IO` is the value's own form, and whether it has an observational effect
-- | travels to an optimizer through the interface file rather than to a machine
-- | that optimizes nothing (D41).
module Steam.Foreign
  ( ForeignTable(..)
  , ForeignEntry
  , emptyTable
  , insert
  , lookup
  ) where

import Prim as P

import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe)
import Steam.Value (ForeignBody)
import Stella.Compiler.TypedCore.Name (Ident, Qualified)

-- | Every foreign the host supplies, under the qualified name a declaration of it
-- | writes.
newtype ForeignTable = ForeignTable (Map (Qualified Ident) ForeignEntry)

-- | An implementation and the number of arguments it takes.
-- |
-- | The arity stands beside the body because an adapter is uncurried — a saturated
-- | call hands it every argument at once — and because it is the one thing a loader
-- | can check the host's side against: a `.dmo` says nothing about a foreign's
-- | type, so nothing else about the two sides can be compared.
type ForeignEntry =
  { arity :: P.Int
  , body :: ForeignBody
  }

-- | The table a host that supplies nothing hands over. A module declaring a foreign
-- | of its own does not load against this one.
emptyTable :: ForeignTable
emptyTable = ForeignTable Map.empty

insert :: Qualified Ident -> ForeignEntry -> ForeignTable -> ForeignTable
insert name entry (ForeignTable table) = ForeignTable (Map.insert name entry table)

lookup :: Qualified Ident -> ForeignTable -> Maybe ForeignEntry
lookup name (ForeignTable table) = Map.lookup name table
