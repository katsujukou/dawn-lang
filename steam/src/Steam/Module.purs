-- | A module as loading leaves it
-- | ([Abstract Machine](../../../docs/technical-references/07-Runtime/01-Abstract-Machine.md)).
-- |
-- | **Every index a file writes is resolved here.** A `.dmo` names a constructor
-- | by an index into its own `CTORREFS` and a key by an index into its own
-- | `KEYS`, and those indices are that file's own; what a running program
-- | compares is the identity the registry assigned. So each table below stands in
-- | the order the file wrote it, holding what the file's index resolves to.
-- |
-- | **A join point is resolved here as well.** A file holds a name so that the
-- | structure survives the format, and what a running function reaches a `Join` by
-- | is the table built below — never a search of the function's join list.
module Steam.Module
  ( Loaded
  , CtorRef
  , Prepared
  , LoadError(..)
  , prepare
  ) where

import Prelude

import Prim as P

import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Show.Generic (genericShow)
import Steam.Value (CtorId, KeyId, ModuleId)
import Stella.Compiler.Bytecode.Instr (Function, Join, JoinName, Node)
import Stella.Compiler.Bytecode.Module (Constant)

type Loaded =
  { id :: ModuleId
  -- | The literal pool, which `LOADK` and dispatch on a literal read.
  , constants :: P.Array Constant
  -- | One entry per `KEYS` index, as the key it resolves to.
  , keys :: P.Array KeyId
  -- | One entry per `CTORREFS` index: the constructors this module's code names,
  -- | its own and those of the modules it imports.
  , ctors :: P.Array CtorRef
  , functions :: P.Array Prepared
  }

-- | A constructor a module's code names, with the arity its declaration states.
-- | A constructor is applied all at once or through a partial application, so an
-- | application of any other length is a module no lowering produces.
type CtorRef =
  { id :: CtorId
  , arity :: P.Int
  }

-- | A function as loading leaves it: the body to enter, and the join points a
-- | transfer inside it reaches, under the names its transfers carry.
type Prepared =
  { nparams :: P.Int
  , body :: Node
  , joins :: Map JoinName Join
  }

-- | What a module may hold that cannot be loaded.
data LoadError
  -- | Two join points of one function under one name. Which one a transfer means
  -- | would otherwise depend on the order they were written in.
  = JoinNameTwice JoinName

-- | What loading makes of a function.
prepare :: Function -> Either LoadError Prepared
prepare function = do
  joins <- foldM one Map.empty function.joins
  pure { nparams: function.nparams, body: function.body, joins }
  where
  one acc join
    | Map.member join.name acc = Left (JoinNameTwice join.name)
    | otherwise = Right (Map.insert join.name join acc)

derive instance Eq LoadError
derive instance Generic LoadError _

instance Show LoadError where
  show = genericShow
