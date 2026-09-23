module Steam.CLI.JS where

import Prelude

import ArgParse.Basic (ArgError(..), ArgErrorMsg(..))
import ArgParse.Basic as ArgParser
import Data.Array as Array
import Data.Either (Either(..))
import Effect (Effect)
import Effect.Console as Console
import Node.Process as Process
import Run (Run, EFFECT, runBaseEffect)
import Run.Except (EXCEPT)
import Run.Except as Except
import Steam.CLI.Error (ErrorType)
import Steam.CLI.Options as Options
import Steam.CLI.Program (program)
import Stella.CLI.Effect.Log (LOG, defaultLoggerConfig)
import Stella.CLI.Effect.Log as Log
import Type.Row (type (+))

runNode :: forall a. Run (LOG + EXCEPT ErrorType + EFFECT + ()) a -> Effect (Either String a)
runNode m = m
  # Log.interpret (Log.terminalHandler (defaultLoggerConfig { minLevel = Log.Info }))
  # Except.runExcept
  # runBaseEffect

main :: Effect Unit
main = do
  args <- Array.drop 2 <$> Process.argv
  case Options.parse args of
    -- Asking for help is not a failure, and a shell that checks the exit
    -- status should not be told it was one.
    Left err@(ArgError _ ShowHelp) -> asked err
    Left err@(ArgError _ (ShowInfo _)) -> asked err
    Left err -> do
      Console.error (ArgParser.printArgError err)
      Process.exit' 1
    Right opts -> run opts
  where
  asked err = Console.log (ArgParser.printArgError err)

  run opts = runNode (program opts) >>= case _ of
    Right _ -> pure unit
    Left e -> Console.error e