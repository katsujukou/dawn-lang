-- | The `.dmi`, and what it buys: a saturated call to an imported value.
-- |
-- | Two modules stand behind these cases. `Lib` exports a function of two
-- | arguments and a value that is not a function; `Main` calls the first,
-- | saturated. **With the interface of `Lib` the call is a `callk` and without it
-- | the same call is a `callu`**, which is the whole of what the file is for.
-- |
-- | The cases after that are the format's: what an interface holds, that the
-- | entries ascend by scalar value rather than by the host's order, and what each
-- | direction refuses.
module Test.Stella.Compiler.Interface (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Bytecode.Bytes (Bytes, DecodeError(..), EncodeError(..))
import Stella.Compiler.Interface (Dmi, InterfaceError(..), importedArities, importsOf, interfaceOf, noImports)
import Stella.Compiler.Interface.File as File
import Stella.Compiler.MidIR as M
import Stella.Compiler.TypedCore (Decl(..), Export(..), Expr(..), Ident(..), Literal(..), Module, ModuleName(..), Qualified(..), Type(..), monoScheme)
import Stella.Compiler.TypedCore.Declare (declare, declareAnnotated)
import Stella.Compiler.TypedCore.Prim (intTy, primSignature, pureFn)
import Stella.Compiler.TypedCore.Signature (Signature)
import Data.Array as Array
import Data.Char as Char
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String.CodeUnits as CodeUnits
import Data.Tuple (Tuple(..))
import Test.Stella.Compiler.TypedCore.VerticalSlice (intModule)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- Names -------------------------------------------------------------------------

libModuleName :: ModuleName
libModuleName = ModuleName "Lib"

mainModuleName :: ModuleName
mainModuleName = ModuleName "Main"

intModuleName :: ModuleName
intModuleName = ModuleName "Base.Int"

intAdd :: Qualified Ident
intAdd = Qualified intModuleName (Ident "add")

add2 :: Qualified Ident
add2 = Qualified libModuleName (Ident "add2")

int :: Type
int = TCon intTy []

-- The modules -------------------------------------------------------------------

-- | `Lib` exports a function of two arguments and a value that is not a
-- | function, and keeps one function to itself.
libModule :: Module P.Int
libModule =
  { annotation: 0
  , name: libModuleName
  , imports: [ intModuleName ]
  , exports: [ ExportValue (Ident "add2"), ExportValue (Ident "one") ]
  , decls:
      [ DeclNonRec 1
          { name: Ident "add2"
          , scheme: monoScheme (pureFn int (pureFn int int))
          , value:
              Lam 0 (Ident "a") int
                ( Lam 0 (Ident "b") int
                    ( App 0 (App 0 (Global 0 intAdd []) (Var 0 (Ident "a")))
                        (Var 0 (Ident "b"))
                    )
                )
          , attributes: []
          }
      , DeclNonRec 2
          { name: Ident "one"
          , scheme: monoScheme int
          , value: Lit 0 (LitInt 1)
          , attributes: []
          }
      , DeclNonRec 3
          { name: Ident "hidden"
          , scheme: monoScheme (pureFn int int)
          , value: Lam 0 (Ident "x") int (Var 0 (Ident "x"))
          , attributes: []
          }
      ]
  }

-- | `Main` calls the exported function of two arguments with two.
mainModule :: Module P.Int
mainModule =
  { annotation: 0
  , name: mainModuleName
  , imports: [ libModuleName ]
  , exports: []
  , decls:
      [ DeclNonRec 1
          { name: Ident "result"
          , scheme: monoScheme int
          , value:
              App 0 (App 0 (Global 0 add2 []) (Lit 0 (LitInt 1))) (Lit 0 (LitInt 2))
          , attributes: []
          }
      ]
  }

mainAlias :: Qualified Ident
mainAlias = Qualified mainModuleName (Ident "alias")

-- | `Main` with the call going through a value that holds the function rather
-- | than naming it. `alias` is evaluated when the module is initialized, so it has
-- | no definitional arity and a call to it is a `callu`; an interface claiming an
-- | arity for it claims one for a right-hand side that has none.
aliasModule :: Module P.Int
aliasModule =
  { annotation: 0
  , name: mainModuleName
  , imports: [ libModuleName ]
  , exports: []
  , decls:
      [ DeclNonRec 1
          { name: Ident "alias"
          , scheme: monoScheme (pureFn int (pureFn int int))
          , value: Global 0 add2 []
          , attributes: []
          }
      , DeclNonRec 2
          { name: Ident "result"
          , scheme: monoScheme int
          , value:
              App 0 (App 0 (Global 0 mainAlias []) (Lit 0 (LitInt 1)))
                (Lit 0 (LitInt 2))
          , attributes: []
          }
      ]
  }

-- Running the pipeline ------------------------------------------------------------

-- | `Lib` declared and translated, with the signature `Main` is checked against.
library :: Either P.String { signature :: Signature, mid :: M.Module }
library = case declare primSignature intModule of
  Left _ -> Left "Base.Int did not declare"
  Right s1 -> case declareAnnotated s1 libModule of
    Left _ -> Left "Lib did not declare"
    Right declared -> case M.translate noImports libModule declared of
      Left err -> Left (show err)
      Right out -> Right { signature: declared.signature, mid: out.module }

-- | The body of the function the last declaration of a version of `Main` becomes,
-- | translated against the interfaces given.
bodyOf :: P.Array Dmi -> Module P.Int -> Either P.String M.Expr
bodyOf interfaces m = do
  lib <- library
  case importsOf interfaces of
    Left err -> Left (show err)
    Right imports -> case declareAnnotated lib.signature m of
      Left _ -> Left "Main did not declare"
      Right declared -> case M.translate imports m declared of
        Left err -> Left (show err)
        Right out -> case Array.last out.module.functions of
          Nothing -> Left "Main holds no function"
          Just f -> Right f.body

libInterface :: Either P.String Dmi
libInterface = map (interfaceOf <<< _.mid) library

-- Fixtures of the format ----------------------------------------------------------

-- | An interface of one module and one entry.
oneEntry :: P.String -> P.Int -> Dmi
oneEntry name arity =
  { name: mainModuleName
  , arities: Map.singleton (Ident name) arity
  }

-- | Two names whose order by scalar value is the reverse of their order by code
-- | unit: an astral character is a pair beginning `0xD83D`, which a host compares
-- | below `U+E000`, and a scalar value puts above it.
astral :: P.String
astral = "😀"

privateUse :: Maybe P.String
privateUse = map CodeUnits.singleton (Char.fromCharCode 0xE000)

loneSurrogate :: Maybe P.String
loneSurrogate = map CodeUnits.singleton (Char.fromCharCode 0xD800)

-- | The arities of an environment built from the interfaces given, every module
-- | among them named, which is how an environment is compared here: `Imports`
-- | itself is opaque.
aritiesOf :: P.Array Dmi -> Either InterfaceError (Map (Qualified Ident) P.Int)
aritiesOf interfaces = importedArities (map _.name interfaces) <$> importsOf interfaces

bytesOf :: Dmi -> Bytes
bytesOf dmi = case File.encode dmi of
  Left _ -> []
  Right bytes -> bytes

-- | Where a run of bytes stands in another, which is how the order of two entries
-- | is read off a file.
indexOfBytes :: Bytes -> Bytes -> Maybe P.Int
indexOfBytes needle haystack = go 0
  where
  go i
    | i + Array.length needle > Array.length haystack = Nothing
    | Array.slice i (i + Array.length needle) haystack == needle = Just i
    | otherwise = go (i + 1)

spec :: Spec Unit
spec = describe "Stella.Compiler.Interface" do

  describe "what it buys" do
    it "makes a saturated call to an imported value a known call" do
      case libInterface of
        Left err -> fail err
        Right dmi -> bodyOf [ dmi ] mainModule `shouldEqual` Right
          (M.ETail (M.CCallKnown add2 [ M.ALit (LitInt 1), M.ALit (LitInt 2) ]))

    it "leaves the same call unknown without the interface" do
      -- absent an arity the call is a `callu`, which is correct for every callee:
      -- what the file buys is sharpness
      bodyOf [] mainModule `shouldEqual` Right
        ( M.ETail
            ( M.CCallUnknown (M.AGlobal add2)
                [ M.ALit (LitInt 1), M.ALit (LitInt 2) ]
            )
        )

    it "leaves a call unknown where the interface is of a module this one does not import" do
      -- an interface naming the module being translated claims an arity for a
      -- right-hand side whose arity is read off the term, and a term may name only
      -- a module its own module imports, so neither source sharpens this call
      let selfNamed = { name: mainModuleName, arities: Map.singleton (Ident "alias") 2 }
      bodyOf [ selfNamed ] aliasModule `shouldEqual` Right
        ( M.ETail
            ( M.CCallUnknown (M.AGlobal mainAlias)
                [ M.ALit (LitInt 1), M.ALit (LitInt 2) ]
            )
        )
      bodyOf [] aliasModule `shouldEqual` bodyOf [ selfNamed ] aliasModule

  describe "what an interface holds" do
    it "the arity of an exported value whose right-hand side is a lambda" do
      -- `one` is evaluated at initialization and has no definitional arity;
      -- `hidden` is a function this module keeps to itself
      map _.arities libInterface `shouldEqual`
        Right (Map.fromFoldable [ Tuple (Ident "add2") 2 ])

    it "the module's own name" do
      map _.name libInterface `shouldEqual` Right libModuleName

  describe "the environment a translation reads" do
    it "carries the arities of the modules named, under the qualified names" do
      case libInterface of
        Left err -> fail err
        Right dmi -> do
          (importedArities [ libModuleName ] <$> importsOf [ dmi ])
            `shouldEqual` Right (Map.singleton add2 2)
          -- an interface of a module a term cannot name says nothing about it
          (importedArities [] <$> importsOf [ dmi ])
            `shouldEqual` Right Map.empty

    it "refuses an arity of zero, and one below it" do
      -- an interface in memory need not have come through a reader, and
      -- translation splits an application spine at the arity it is given: at zero
      -- a saturated call would become a known call of no arguments
      aritiesOf [ oneEntry "f" 0 ]
        `shouldEqual` Left (NotAnArity mainModuleName (Ident "f") 0)
      aritiesOf [ oneEntry "f" (-1) ]
        `shouldEqual` Left (NotAnArity mainModuleName (Ident "f") (-1))

    it "refuses two interfaces of one module" do
      -- which arity each of that module's names has would otherwise depend on the
      -- order the two were read in
      aritiesOf [ oneEntry "f" 1, oneEntry "g" 1 ]
        `shouldEqual` Left (ModuleTwice mainModuleName)

  describe "the bytes" do
    it "begin with the magic, the format version, and the flags" do
      Array.take 6 (bytesOf (oneEntry "f" 1))
        `shouldEqual` [ 0x44, 0x4D, 0x49, 0x00, 0x00, 0x00 ]

    it "carry an interface through and back" do
      case libInterface of
        Left err -> fail err
        Right dmi -> File.decode (bytesOf dmi) `shouldEqual` Right dmi

    it "order the entries by scalar value and not by the host's order" do
      -- `Ord String` compares code units, which puts the astral name first; the
      -- format compares scalar values, which puts `U+E000` first
      case privateUse of
        Nothing -> fail "a code unit is the only way to write one"
        Just name -> do
          let
            two =
              { name: mainModuleName
              , arities: Map.fromFoldable
                  [ Tuple (Ident astral) 1, Tuple (Ident name) 2 ]
              }
            bytes = bytesOf two
          (indexOfBytes [ 0xEE, 0x80, 0x80 ] bytes < indexOfBytes [ 0xF0, 0x9F, 0x98, 0x80 ] bytes)
            `shouldEqual` true
          File.decode bytes `shouldEqual` Right two

  describe "what a reader refuses" do
    it "other magic" do
      File.decode [ 0x44, 0x4D, 0x4F, 0x00 ] `shouldEqual` Left BadMagic

    it "a format version it does not implement" do
      File.decode (mutated 4 0x01 (bytesOf (oneEntry "f" 1)))
        `shouldEqual` Left (UnsupportedFormatVersion 1)

    it "a flag it does not know" do
      File.decode (mutated 5 0x01 (bytesOf (oneEntry "f" 1)))
        `shouldEqual` Left (UnknownFlags 1)

    it "an entry whose arity is not positive" do
      -- `"Main"`, then one entry of the one-byte name `f` at arity 0
      File.decode (header <> [ 0x01, 0x01, 0x66, 0x00 ])
        `shouldEqual` Left (ArityNotPositive 0)

    it "entries that do not ascend, a repeated name among them" do
      File.decode (header <> [ 0x02, 0x01, 0x62, 0x01, 0x01, 0x61, 0x02 ])
        `shouldEqual` Left EntriesOutOfOrder
      File.decode (header <> [ 0x02, 0x01, 0x61, 0x01, 0x01, 0x61, 0x02 ])
        `shouldEqual` Left EntriesOutOfOrder

    it "a byte after the table" do
      -- a longer file is a later format, not this one with something ignorable
      -- at the end
      File.decode (bytesOf (oneEntry "f" 1) <> [ 0x00 ])
        `shouldEqual` Left TrailingBytes

  describe "what an encoder refuses" do
    it "an arity below one, absence being what a value without one has" do
      File.encode (oneEntry "f" 0)
        `shouldEqual` Left (ArityBelowOne (Ident "f") 0)

    it "a name carrying an unpaired surrogate" do
      case loneSurrogate of
        Nothing -> fail "a code unit is the only way to write one"
        Just name ->
          File.encode (oneEntry name 1) `shouldEqual` Left (NotScalarText name)

-- | The header of a file of module `Main`, up to the count of the entries.
header :: Bytes
header = [ 0x44, 0x4D, 0x49, 0x00, 0x00, 0x00, 0x04, 0x4D, 0x61, 0x69, 0x6E ]

-- | The bytes with one of them replaced.
mutated :: P.Int -> P.Int -> Bytes -> Bytes
mutated at value bytes = fromMaybe bytes (Array.updateAt at value bytes)
