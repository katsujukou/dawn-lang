-- | The local context `Γ`.
-- |
-- | `Γ` grows at a binder and shrinks on leaving it, and later entries may refer
-- | to earlier ones. Nothing in it crosses a module boundary and nothing in it
-- | carries a kind scheme, which is the whole of the difference between it and
-- | the global signature `Σ`.
-- |
-- | The row constraints it assumes are kept decomposed, since entailment reads
-- | atomic facts about row variables rather than the assumptions as written.
module Stella.Compiler.TypedCore.Context
  ( Context
  , emptyContext
  , bindKindVars
  , bindTyVar
  , lookupTyVar
  , bindVar
  , lookupVar
  , kindVarInScope
  , assume
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore.Entailment (AtomicFacts, DecomposeError, addAssumption, noFacts)
import Stella.Compiler.TypedCore.Kind (Kind)
import Stella.Compiler.TypedCore.Name (Ident, KindVar, TyVar)
import Stella.Compiler.TypedCore.Type (Constraint, Type)
import Data.Either (Either)
import Data.Foldable (foldr)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe)
import Data.Set (Set)
import Data.Set as Set

type Context =
  { kindVars :: Set KindVar
  , tyVars :: Map TyVar Kind
  , vars :: Map Ident Type
  , facts :: AtomicFacts
  }

emptyContext :: Context
emptyContext = { kindVars: Set.empty, tyVars: Map.empty, vars: Map.empty, facts: noFacts }

-- | Bind the kind variables of a declaration's scheme. A kind variable enters
-- | `Γ` here and nowhere else: neither grammar has a kind quantifier (D3).
bindKindVars :: Context -> P.Array KindVar -> Context
bindKindVars ctx vars =
  ctx { kindVars = foldr Set.insert ctx.kindVars vars }

bindTyVar :: Context -> TyVar -> Kind -> Context
bindTyVar ctx name kind =
  ctx { tyVars = Map.insert name kind ctx.tyVars }

lookupTyVar :: Context -> TyVar -> Maybe Kind
lookupTyVar ctx name = Map.lookup name ctx.tyVars

bindVar :: Context -> Ident -> Type -> Context
bindVar ctx name ty =
  ctx { vars = Map.insert name ty ctx.vars }

lookupVar :: Context -> Ident -> Maybe Type
lookupVar ctx name = Map.lookup name ctx.vars

kindVarInScope :: Context -> KindVar -> P.Boolean
kindVarInScope ctx name = Set.member name ctx.kindVars

-- | Assume a row constraint.
-- |
-- | An assumption that contradicts itself is rejected here rather than carried,
-- | so what `Γ*` holds is always satisfiable.
assume :: Context -> Constraint -> Either DecomposeError Context
assume ctx constraint =
  ctx { facts = _ } <$> addAssumption ctx.facts constraint
