module Steam.CLI.Options where

import Prelude

import ArgParse.Basic (ArgParser)
import ArgParse.Basic as ArgParser
import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Stella.CLI.Effect.Log (LogLevel(..))
import Stella.CLI.Options (loglevel, moduleName)
import Stella.Compiler.TypedCore (ModuleName(..))

type RunOptions =
  { entry :: ModuleName
  }

data Command
  = Eval {}
  | Run RunOptions

derive instance Eq Command
derive instance Generic Command _
instance Show Command where
  show = genericShow

type Options =
  { logLevel :: LogLevel
  , command :: Command
  }

options :: ArgParser Options
options =
  ArgParser.fromRecord
    { logLevel:
        ArgParser.argument [ "--log-level" ]
          "Suppress log messages of level lower than"
          # loglevel
          # ArgParser.default Info
    , command:
        ArgParser.choose "command"
          [ ArgParser.command [ "run" ]
              "Load whole program and execute main once."
              ((Run <$> runOptions) <* ArgParser.flagHelp)
          , ArgParser.command [ "eval" ]
              "Evaluates a single module or declaration.\n\
              \Intended for use as a REPL backend."
              ((Eval {}) <$ ArgParser.flagHelp)
          ]
    }
    <* ArgParser.flagHelp
  where
  runOptions = ArgParser.fromRecord
    { entry:
        ArgParser.argument [ "--entry", "-e" ]
          "Entry module name which should contain `main :: IO Unit`"
          # moduleName
          # ArgParser.default (ModuleName "Main")
    }

parse :: Array String -> Either ArgParser.ArgError Options
parse = ArgParser.parseArgs
  "steam"
  "The Stella Abstract Machine"
  options