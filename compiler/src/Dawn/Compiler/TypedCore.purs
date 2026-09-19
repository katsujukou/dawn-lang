-- | Typed Core.
-- |
-- | Core defines the semantics of the language: it makes type abstraction and
-- | application, evidence arguments, record and variant operations, the
-- | decision structure of pattern matching, and effect operations and handlers
-- | explicit. Surface features elaborate into it, and an independent type
-- | checker validates every term elaboration produces.
-- |
-- | This module re-exports the syntax together with the decisions the trusted
-- | core makes over it — row normalization, kinding, type equality, and
-- | entailment — which the specification lists as one trusted set.
-- |
-- | The forms that arise only during reduction — `match θ dt`, `openEffC`, and
-- | `rec_i` — belong to the evaluator and are not produced by elaboration, so
-- | they are absent here.
module Dawn.Compiler.TypedCore
  ( module Dawn.Compiler.TypedCore.Name
  , module Dawn.Compiler.TypedCore.Kind
  , module Dawn.Compiler.TypedCore.Type
  , module Dawn.Compiler.TypedCore.Term
  , module Dawn.Compiler.TypedCore.Decl
  , module Dawn.Compiler.TypedCore.Prim
  , module Dawn.Compiler.TypedCore.Signature
  , module Dawn.Compiler.TypedCore.Context
  , module Dawn.Compiler.TypedCore.Row
  , module Dawn.Compiler.TypedCore.Kinding
  , module Dawn.Compiler.TypedCore.Declare
  , module Dawn.Compiler.TypedCore.Equality
  , module Dawn.Compiler.TypedCore.Entailment
  ) where

-- Re-exporting `Type` and `Constraint` shadows the `Prim` names of those
-- spellings, so `Prim` is imported qualified here as well.
import Prim as P

import Dawn.Compiler.TypedCore.Context (Context, assume, bindKindVars, bindTyVar, emptyContext, kindVarInScope, lookupTyVar)
import Dawn.Compiler.TypedCore.Declare (DeclError(..), DeclFailure, checkTyConEntries, collectTypes, declare, initialSignature)
import Dawn.Compiler.TypedCore.Decl (AttrField, AttrValue(..), Attribute, CtorDecl, DataDecl, Decl(..), declAnnotation, EffectDecl, Export(..), ForeignDecl, Module, OpDecl, ValueBinding)
import Dawn.Compiler.TypedCore.Entailment (AtomicFacts, DecomposeError(..), addAssumption, decompose, entails, noFacts)
import Dawn.Compiler.TypedCore.Equality (constraintEquiv, rowEquiv, typeEquiv)
import Dawn.Compiler.TypedCore.Kind (Kind(..), KindScheme, RowElemKind(..), Scheme, kindVarsOf, monoScheme, substituteKind)
import Dawn.Compiler.TypedCore.Kinding (KindError(..), Synthesized(..), checkKind, kindOf, producesType, quantifiableKind, rowElemKindOf, wellFormedConstraint, wellFormedKey, wellFormedKind)
import Dawn.Compiler.TypedCore.Name (EffName(..), Ident(..), JoinName(..), KindVar(..), ModuleName(..), OpName(..), Qualified(..), Symbol(..), Tag(..), TyName(..), TyVar(..), qualifier, unqualified)
import Dawn.Compiler.TypedCore.Prim (asFunction, booleanTy, charTy, fn, functionTy, intTy, ioTy, litType, numberTy, primModule, primSignature, pureFn, recordTy, stringTy, unitCtor, unitTy, variantTy)
import Dawn.Compiler.TypedCore.Row (RowError(..), RowNormalForm, emptyNormalForm, nf)
import Dawn.Compiler.TypedCore.Signature (CanonicalClass(..), CtorInfo, EffectInfo, Signature, TyConInfo(..), ValueInfo, effectParamKinds, emptySignature, lookupCtor, lookupEffect, lookupOperation, lookupTyCon, lookupValue, tyConKind)
import Dawn.Compiler.TypedCore.Term (Binding, CtorBranch, DecisionTree(..), Expr(..), Handler, KeyBranch, LitBranch, Literal(..), OpClause, Occurrence(..), Param, ReturnClause, exprAnnotation)
import Dawn.Compiler.TypedCore.Type (Constraint(..), RowEntry(..), RowKey(..), RowPayload(..), TyBinder, Type(..), TypeScheme, rowEntryKey, rowEntryPayload)
