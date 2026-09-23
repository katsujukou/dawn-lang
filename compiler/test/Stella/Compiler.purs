module Test.Stella.Compiler where

import Prelude

import Effect (Effect)
import Test.Stella.Compiler.TypedCore as TypedCore
import Test.Stella.Compiler.Primitive as Primitive
import Test.Stella.Compiler.Bytecode.Effects as BytecodeEffects
import Test.Stella.Compiler.Bytecode.Lower as BytecodeLower
import Test.Stella.Compiler.MidIR.Regression as MidRegression
import Test.Stella.Compiler.MidIR.Translate as MidTranslate
import Test.Stella.Compiler.MidIR.Effects as MidEffects
import Test.Stella.Compiler.MidIR.Verify as MidVerify
import Test.Stella.Compiler.TypedCore.Annotation as Annotation
import Test.Stella.Compiler.TypedCore.Check as Check
import Test.Stella.Compiler.TypedCore.Declare as Declare
import Test.Stella.Compiler.TypedCore.Domain as Domain
import Test.Stella.Compiler.TypedCore.Kinding as Kinding
import Test.Stella.Compiler.TypedCore.Row as Row
import Test.Stella.Compiler.Elaborate.Unify as Unify
import Test.Stella.Compiler.TypedCore.RowProperties as RowProperties
import Test.Stella.Compiler.TypedCore.EffectSlice as EffectSlice
import Test.Stella.Compiler.TypedCore.HandlerSlice as HandlerSlice
import Test.Stella.Compiler.TypedCore.VerticalSlice as VerticalSlice
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  TypedCore.spec
  Row.spec
  Kinding.spec
  Declare.spec
  Domain.spec
  Check.spec
  Annotation.spec
  MidTranslate.spec
  MidRegression.spec
  MidVerify.spec
  MidEffects.spec
  Primitive.spec
  BytecodeLower.spec
  BytecodeEffects.spec
  VerticalSlice.spec
  EffectSlice.spec
  HandlerSlice.spec
  RowProperties.spec
  Unify.spec
