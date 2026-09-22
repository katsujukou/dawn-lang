-- | Mid IR.
-- |
-- | The backend-independent stage between Typed Core and a target. It is an
-- | A-normal form: every intermediate result is named by a binding, every
-- | argument is an atom, and every control construct stands in tail position.
-- | It has no nested function, and no types — what survives of those is a `Rep`
-- | on each binding.
-- |
-- | This module re-exports the representation together with the translation that
-- | produces it, which is the boundary a lowering reads.
module Dawn.Compiler.MidIR
  ( module Dawn.Compiler.MidIR.Rep
  , module Dawn.Compiler.MidIR.Term
  , module Dawn.Compiler.MidIR.Translate
  , module Dawn.Compiler.MidIR.Verify
  ) where

-- Re-exporting `Function` shadows the `Prim` name of that spelling, so `Prim` is
-- imported qualified here as well.
import Prim as P

import Dawn.Compiler.MidIR.Rep (Rep(..), repOf)
import Dawn.Compiler.MidIR.Term (Atom(..), Binder, Callee(..), ClauseForm(..), ClauseRef, Comp(..), CtorBranch, CtorEntry, Debug, EffectEntry, Expr(..), ForeignEntry, FuncId(..), Function, FunctionDebug, GlobalEntry, GlobalInit(..), Handler, JoinId(..), KeyBranch, LitBranch, Local(..), Module, OpClauseRef, RecBinding, emptyDebug)
import Dawn.Compiler.MidIR.Translate (TranslateError(..), freeVars, translate)
import Dawn.Compiler.MidIR.Verify (VerifyError(..), verify)
