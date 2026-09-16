module Dawn.CLI where

import Prelude

import Effect (Effect)
import Effect.Console as Console

main :: Effect Unit
main = do
  Console.log "🌅 The Dawn-lang compiler toolchain CLI"