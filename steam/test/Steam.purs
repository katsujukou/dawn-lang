module Test.Steam where

import Prelude

import Effect (Effect)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Steam.Calls as Calls
import Test.Steam.Eval as Eval
import Test.Steam.Load as Load
import Test.Steam.Ops as Ops
import Test.Steam.Value as Value

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  Value.spec
  Eval.spec
  Calls.spec
  Ops.spec
  Load.spec
