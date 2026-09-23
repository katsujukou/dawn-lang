module Steam.CLI.Options where

import Prelude

import ArgParse.Basic (ArgParser)
import ArgParse.Basic as ArgParser
import Data.Either (Either)
import Stella.CLI.Effect.Log (LogLevel(..))
import Stella.CLI.Options (loglevel)

type Options =
  { logLevel :: LogLevel
  }

options :: ArgParser Options
options =
  ArgParser.fromRecord
    { logLevel:
        ArgParser.argument [ "--log-level" ]
          "Suppress log messages of level lower than"
          # loglevel
          # ArgParser.default Info
    }
    <* ArgParser.flagHelp
    <* ArgParser.flagInfo [ "--version", "-v" ] "Show the current version" "v0.1.0"

parse :: Array String -> Either ArgParser.ArgError Options
parse = ArgParser.parseArgs
  "steam"
  "The Stella Abstract Machine"
  options