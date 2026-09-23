-- | Bytecode and the `.dmo` module object.
-- |
-- | One lowering of Mid IR, beside any backend including JS and WebAssembly.
-- | Its target is a virtual machine Stella owns.
-- |
-- | Code is linear within a straight run of instructions and structured above
-- | it: a transfer names its destination and a decision tree stays a tree, so
-- | nothing downstream runs a relooper (D32).
module Stella.Compiler.Bytecode
  ( module Stella.Compiler.Bytecode.Instr
  , module Stella.Compiler.Bytecode.Module
  , module Stella.Compiler.Bytecode.Lower
  ) where

-- Re-exporting `Function` shadows the `Prim` name of that spelling, so `Prim` is
-- imported qualified here as well.
import Prim as P

import Stella.Compiler.Bytecode.Instr (CalleeIx(..), ConstIx(..), CtorCase, CtorIx(..), ForeignIx(..), FuncIx(..), Function, GlobalIx(..), HandlerIx(..), Instr(..), Join, JoinName(..), KeyCase, KeyIx(..), LitCase, Node, OpIx(..), PrimIx(..), Reg(..), Tail(..))
import Stella.Compiler.Bytecode.Lower (LowerError(..), lower)
import Stella.Compiler.Bytecode.Module (CalleeEntry(..), ClauseEntry, Constant(..), CtorEntry, Debug, Dmo, EffectEntry, ForeignEntry, FunctionDebug, GlobalEntry, GlobalInit(..), HandlerEntry, Key(..), abiVersion, formatVersion)
