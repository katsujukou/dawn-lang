module Test.Dawn.Compiler where

import Prelude

import Effect (Effect)
import Test.Dawn.Compiler.TypedCore as TypedCore
import Test.Dawn.Compiler.TypedCore.Kinding as Kinding
import Test.Dawn.Compiler.TypedCore.Row as Row
import Test.Dawn.Compiler.Elaborate.Unify as Unify
import Test.Dawn.Compiler.TypedCore.RowProperties as RowProperties
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  TypedCore.spec
  Row.spec
  Kinding.spec
  RowProperties.spec
  Unify.spec
