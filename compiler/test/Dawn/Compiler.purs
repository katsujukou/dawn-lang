module Test.Dawn.Compiler where

import Prelude

import Effect (Effect)
import Test.Dawn.Compiler.TypedCore as TypedCore
import Test.Dawn.Compiler.TypedCore.Annotation as Annotation
import Test.Dawn.Compiler.TypedCore.Check as Check
import Test.Dawn.Compiler.TypedCore.Declare as Declare
import Test.Dawn.Compiler.TypedCore.Kinding as Kinding
import Test.Dawn.Compiler.TypedCore.Row as Row
import Test.Dawn.Compiler.Elaborate.Unify as Unify
import Test.Dawn.Compiler.TypedCore.RowProperties as RowProperties
import Test.Dawn.Compiler.TypedCore.EffectSlice as EffectSlice
import Test.Dawn.Compiler.TypedCore.VerticalSlice as VerticalSlice
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  TypedCore.spec
  Row.spec
  Kinding.spec
  Declare.spec
  Check.spec
  Annotation.spec
  VerticalSlice.spec
  EffectSlice.spec
  RowProperties.spec
  Unify.spec
