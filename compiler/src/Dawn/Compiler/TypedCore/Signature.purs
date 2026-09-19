-- | The global signature `Σ`.
-- |
-- | `Σ` is an unordered table of declarations, assembled from a module and from
-- | the interfaces of the modules it imports and fixed throughout the checking
-- | of that module. The rules only look things up in it, never extend or shrink
-- | it, which is why the judgements leave it implicit.
-- |
-- | Every name in it is fully qualified. `Σ` is also what separates the two row
-- | key kinds: a structural key needs nothing from it, while an `EffectKey` is
-- | the identity of a declaration recorded here.
module Dawn.Compiler.TypedCore.Signature
  ( Signature
  , EffectInfo
  , emptySignature
  , lookupTyCon
  , lookupEffect
  , effectParamKinds
  ) where

import Prelude

import Prim as P

import Dawn.Compiler.TypedCore.Decl (OpDecl)
import Dawn.Compiler.TypedCore.Kind (Kind, KindScheme)
import Dawn.Compiler.TypedCore.Name (EffName, OpName, Qualified, TyName)
import Dawn.Compiler.TypedCore.Type (TyBinder)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe)

type Signature =
  { types :: Map (Qualified TyName) KindScheme
  , effects :: Map (Qualified EffName) EffectInfo
  }

-- | An effect declaration as the rules read it.
-- |
-- | An effect constructor carries no kind scheme: its kind is `κ̄ -> Effect`,
-- | fixed by `params`, so an element of a `Row Effect` is written `E τ̄` and
-- | needs no instantiation.
type EffectInfo =
  { params :: P.Array TyBinder
  , operations :: Map OpName OpDecl
  }

emptySignature :: Signature
emptySignature = { types: Map.empty, effects: Map.empty }

lookupTyCon :: Signature -> Qualified TyName -> Maybe KindScheme
lookupTyCon sig name = Map.lookup name sig.types

lookupEffect :: Signature -> Qualified EffName -> Maybe EffectInfo
lookupEffect sig name = Map.lookup name sig.effects

-- | `κ̄` of `E : κ̄ -> Effect`, which is what an element's payload is checked
-- | against.
effectParamKinds :: EffectInfo -> P.Array Kind
effectParamKinds info = map _.kind info.params
