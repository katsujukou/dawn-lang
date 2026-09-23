module Steam.CLI.Program where

import Prelude

import Effect.Console (logShow)
import Run (EFFECT, Run, liftEffect)
import Run.Except (EXCEPT)
import Steam.CLI.Error (ErrorType)
import Steam.CLI.Options (Options)
import Stella.CLI.Effect.Log (LOG)
import Stella.CLI.Effect.Log as Log
import Type.Row (type (+))

type SteamEffects = (LOG + EXCEPT ErrorType + EFFECT + ())

program :: Options -> Run SteamEffects Unit
program opts = do
  Log.info "STEAM - Stella Abstract Machine"
  liftEffect $ logShow opts
