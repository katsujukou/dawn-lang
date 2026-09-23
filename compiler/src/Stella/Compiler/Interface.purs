-- | The interface of a module: what a module downstream of it reads
-- | ([Interface](../../../docs/technical-references/05-Backend/03-Interface.md)).
-- |
-- | What it holds is the **definitional arity** of each value the module exports
-- | that has one, which is what lets a saturated call to an imported value be a
-- | `callk`. A type does not determine that arity, so nothing else carries it;
-- | where it is absent the call is a `callu`, correct for every callee.
-- |
-- | **The arities are a map**, so a name occurs once by construction rather than
-- | by a rule a writer must keep, and an export list naming a value twice yields
-- | one entry.
-- |
-- | Format 0 holds no types: a compiler obtains `Σ` as it does today and reads
-- | this beside it, so an interface is a sidecar rather than the whole interface
-- | separate compilation will rest on.
-- |
-- | **What translation reads is `Imports`, not an array of interfaces.** An
-- | interface in memory need not have come through a reader — a `Dmi` is a record of
-- | a name and a map — and an arity translation cannot trust is worse than no arity
-- | at all, so `importsOf` checks the arities as a reader of the bytes checks them
-- | and `Imports` is the only thing that reaches a translation. What is read out of
-- | one is read through an import list, so an interface of a module a term cannot
-- | name says nothing about that term.
-- |
-- | **This module holds no bytes.** Translation reads an interface, and a stage
-- | upstream of a backend must not depend on one; the file is
-- | [Interface.File](Interface/File.purs).
module Stella.Compiler.Interface
  ( Dmi
  , interfaceOf
  , Imports
  , InterfaceError(..)
  , noImports
  , importsOf
  , importedArities
  ) where

import Prelude

import Prim as P

import Stella.Compiler.MiddleEnd.IR as MIR
import Stella.Compiler.TypedCore.Name (Ident, ModuleName, Qualified(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

-- | A module's name, and the definitional arity of each value it exports that
-- | has one. An arity is at least one: a value with none is absent, and absence
-- | is not zero.
type Dmi =
  { name :: ModuleName
  , arities :: Map Ident P.Int
  }

-- | The interface of a module, read off the module a lowering is handed.
-- |
-- | A global installed as a **function** has a definitional arity, which is the
-- | number of parameters of the function table entry it names; one evaluated at
-- | initialization has none. So the arity is read where the `.dmo`'s own entry
-- | was decided and nothing computes it twice.
-- |
-- | A global installed as a function of **no** parameters has no definitional
-- | arity either: a count of leading lambdas that is zero is what absence is.
interfaceOf :: MIR.Module -> Dmi
interfaceOf m =
  { name: m.name
  , arities: Map.fromFoldable (Array.mapMaybe entry m.exports)
  }
  where
  installed = Map.fromFoldable (map (\g -> Tuple g.ref g.init) m.globals)
  functions = Map.fromFoldable (map (\f -> Tuple f.id f) m.functions)

  -- an interface speaks for its own module, so an export of another's name
  -- contributes nothing to it
  entry ref = case ref of
    Qualified moduleName name
      | moduleName /= m.name -> Nothing
      | otherwise -> case Map.lookup ref installed of
          Just (MIR.GFunc id) -> case Map.lookup id functions of
            Just f
              | Array.length f.params > 0 -> Just (Tuple name (Array.length f.params))
            _ -> Nothing
          _ -> Nothing

-- | The arities of the imports of one translation, under the qualified names a
-- | term carries, **checked**: every arity is at least one, and one module has one
-- | interface. Only [importsOf](#v:importsOf) builds one.
newtype Imports = Imports (Map (Qualified Ident) P.Int)

-- | What a translation is handed where it imports nothing, which is also what an
-- | interface it was not given amounts to: every call to an imported value is a
-- | `callu`.
noImports :: Imports
noImports = Imports Map.empty

-- | What an interface may hold that no translation may act on.
data InterfaceError
  -- | An arity below one, under the module and the name it stands in. A
  -- | definitional arity counts leading lambdas, so a value with none is absent
  -- | from an interface rather than present at zero; translation splits an
  -- | application spine at the arity it is given, and at zero it would split a
  -- | saturated call into a `callk` of no arguments.
  = NotAnArity ModuleName Ident P.Int
  -- | Two interfaces of one module. Which arity each of that module's names has
  -- | would then depend on the order the two were read in.
  | ModuleTwice ModuleName

derive instance Eq InterfaceError
derive instance Generic InterfaceError _

instance Show InterfaceError where
  show = genericShow

-- | The interfaces of every import, as one environment, or what makes them no
-- | environment.
importsOf :: P.Array Dmi -> Either InterfaceError Imports
importsOf interfaces =
  map (Imports <<< _.arities) (foldM one { seen: Set.empty, arities: Map.empty } interfaces)
  where
  one acc dmi
    | Set.member dmi.name acc.seen = Left (ModuleTwice dmi.name)
    | otherwise = do
        arities <- foldM (entry dmi.name) acc.arities (entriesOf dmi)
        pure { seen: Set.insert dmi.name acc.seen, arities }

  entriesOf dmi = Map.toUnfoldable dmi.arities :: P.Array (Tuple Ident P.Int)

  entry moduleName acc (Tuple name arity)
    | arity < 1 = Left (NotAnArity moduleName name arity)
    | otherwise = Right (Map.insert (Qualified moduleName name) arity acc)

-- | The arities the environment holds for the modules named, and for no others.
-- |
-- | Each interface speaks for one module and a module has one interface, so what is
-- | looked up under a qualified name is the arity the declaring module published.
-- | **The names are a module's own import list**: an interface of a module its terms
-- | cannot name — the module itself among them, whose globals this translation reads
-- | off their right-hand sides — would sharpen a call it is not about.
importedArities :: P.Array ModuleName -> Imports -> Map (Qualified Ident) P.Int
importedArities moduleNames (Imports arities) = Map.filterKeys imported arities
  where
  declared = Set.fromFoldable moduleNames

  imported (Qualified moduleName _) = Set.member moduleName declared
