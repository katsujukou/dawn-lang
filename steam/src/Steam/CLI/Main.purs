module Steam.CLI.Main where

import Prelude

import Effect (Effect)
import Effect.Console as Console

main :: Effect Unit
main = do
  Console.log "STEAM - The Stella Abstract Machine"