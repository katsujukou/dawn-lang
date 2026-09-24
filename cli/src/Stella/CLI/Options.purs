module Stella.CLI.Options where

import Prelude

import ArgParse.Basic (ArgParser)
import ArgParse.Basic as ArgParser
import Data.Either (note)
import Data.Maybe (Maybe(..))
import Stella.CLI.Effect.Log (LogLevel(..))
import Stella.Compiler.TypedCore (ModuleName(..))

loglevel :: ArgParser String -> ArgParser LogLevel
loglevel = ArgParser.unformat "LOG_LEVEL" parseLogLevel
  where
  parseLogLevel = note "Invaid LogLevel. Acceptable: debug | info | warn | error"
    <<< case _ of
      "Debug" -> Just Debug
      "debug" -> Just Debug
      "Info" -> Just Info
      "info" -> Just Info
      "Warn" -> Just Warn
      "warn" -> Just Warn
      "Error" -> Just Error
      "error" -> Just Error
      _ -> Nothing

moduleName :: ArgParser String -> ArgParser ModuleName
moduleName = (ModuleName <$> _)