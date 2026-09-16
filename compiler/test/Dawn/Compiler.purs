module Test.Dawn.Compiler where

import Prelude

import Effect (Effect)
import Test.Dawn.Compiler.TypedCore as TypedCore
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  TypedCore.spec
