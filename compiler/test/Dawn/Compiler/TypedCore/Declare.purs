-- | Declarations and the signature a module contributes.
-- |
-- | The cases the Implementation Plan singles out are here: D23 on both sides
-- | of an arrow, the shape a `newtype` claims, and the dependency order of
-- | value declarations.
module Test.Dawn.Compiler.TypedCore.Declare (spec) where

import Prelude

import Prim as P

import Dawn.Compiler.TypedCore (Constraint(..), CtorDecl, Decl(..), EffName(..), Export(..), Expr(..), Ident(..), Kind(..), KindVar(..), Literal(..), Module, ModuleName(..), OpName(..), Qualified(..), RowElemKind(..), RowEntry(..), RowKey(..), Symbol(..), TyName(..), TyVar(..), Type(..), TypeScheme, monoScheme)
import Dawn.Compiler.TypedCore.Declare (DeclError(..), checkTyConEntries, declare, initialSignature)
import Dawn.Compiler.TypedCore.Kinding (KindError(..), Synthesized(..))
import Dawn.Compiler.TypedCore.Prim (fn, intTy, ioTy, primSignature, pureFn, recordTy, stringTy, unitTy)
import Dawn.Compiler.TypedCore.Signature (CanonicalClass(..), Signature, TyConInfo(..), emptySignature, lookupCtor)
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

main :: ModuleName
main = ModuleName "Main"

value :: P.String -> Qualified Ident
value name = Qualified main (Ident name)

tyCon :: P.String -> Qualified TyName
tyCon name = Qualified main (TyName name)

consoleEff :: Qualified EffName
consoleEff = Qualified main (EffName "Console")

string :: Type
string = TCon stringTy []

int :: Type
int = TCon intTy []

unitTy' :: Type
unitTy' = TCon unitTy []

io :: Type -> Type
io ty = TApp (TCon ioTy []) ty

-- | `effect Console where log : String ->* Unit`, which the foreign cases need
-- | in order to write an effectful arrow at all.
consoleDecl :: Decl Unit
consoleDecl = DeclEffect unit
  { name: EffName "Console"
  , params: []
  , operations:
      [ { name: OpName "log", tyBinders: [], argument: string, resumesWith: unitTy' } ]
  , attributes: []
  }

-- | `( Console )`
consoleRow :: Type
consoleRow = TRowExtend (RowEffectEntry consoleEff []) TRowEmpty

moduleOf :: P.Array (Decl Unit) -> Module Unit
moduleOf decls =
  { annotation: unit, name: main, imports: [], exports: [], decls }

exporting :: P.Array Export -> P.Array (Decl Unit) -> Module Unit
exporting exports decls = (moduleOf decls) { exports = exports }

-- | The verdict on a module, with the signature it would contribute dropped.
verdict :: Module Unit -> Either DeclError Unit
verdict m = case declare primSignature m of
  Left failure -> Left failure.error
  Right _ -> Right unit

-- | The scheme `Σ` records for a data constructor.
ctorScheme :: Module Unit -> Qualified Ident -> Maybe TypeScheme
ctorScheme m name = case declare primSignature m of
  Left _ -> Nothing
  Right sig -> map _.scheme (lookupCtor sig name)

-- | `newtype N = …`, whose shape the checker verifies.
newtypeOf :: P.Array CtorDecl -> Decl Unit
newtypeOf constructors = DeclData unit
  { name: TyName "N"
  , kindVars: []
  , params: []
  , constructors
  , isNewtype: true
  , attributes: []
  }

foreignDecl :: P.String -> TypeScheme -> Decl Unit
foreignDecl name scheme = DeclForeign unit { name: Ident name, scheme, attributes: [] }

nonrec :: P.String -> TypeScheme -> Expr Unit -> Decl Unit
nonrec name scheme expr = DeclNonRec unit
  { name: Ident name, scheme, value: expr, attributes: [] }

globalRef :: P.String -> Expr Unit
globalRef name = Global unit (value name) []

-- | A kind variable no scheme binds.
ghost :: KindVar
ghost = KindVar "ghost"

entry :: Kind -> P.Array KindVar -> TyConInfo
entry body kindVars = IntrinsicTyCon { kindVars, body } CanonicalOpaque

-- | `Σ_Prim` with one entry of the kind no declaration produces.
withEntry :: TyConInfo -> Signature
withEntry info =
  primSignature { types = Map.insert (tyCon "Weird") info primSignature.types }

spec :: Spec Unit
spec = describe "TypedCore.Declare" do
  describe "the signature a compiler builds" do
    it "accepts the entries of Prim" do
      checkTyConEntries primSignature `shouldEqual` Right unit

    it "assembles the signature a module is checked under" do
      map (\sig -> Map.member (tyCon "Weird") sig.types) (initialSignature [])
        `shouldEqual` Right false

    it "checks the table where it is assembled" do
      map (const unit) (initialSignature [ withEntry (entry (KVar ghost) []) ])
        `shouldEqual` Left (TyConEntryError (tyCon "Weird") (UnboundKindVar ghost))

    it "refuses an entry that produces a row at some instantiation" do
      -- `forall k. k` passes every use site that instantiates it at `Type`
      let k = KindVar "k"
      checkTyConEntries (withEntry (entry (KVar k) [ k ]))
        `shouldEqual` Left (TyConEntryError (tyCon "Weird") (ResultNotType (KVar k)))

    it "refuses an entry whose kind variable nothing binds" do
      -- the result is `Type`, so checking only the result admits it
      checkTyConEntries (withEntry (entry (KFun (KVar ghost) KType) []))
        `shouldEqual` Left (TyConEntryError (tyCon "Weird") (UnboundKindVar ghost))

    it "refuses an entry taking an argument that cannot be quantified" do
      checkTyConEntries (withEntry (entry (KFun KEffect KType) []))
        `shouldEqual` Left (TyConEntryError (tyCon "Weird") (NotQuantifiable KEffect))

    it "absorbs an entry arriving through two import paths" do
      -- a name belongs to the module that declares it, so the two are one entry
      let part = withEntry (entry KType [])
      map (\sig -> Map.member (tyCon "Weird") sig.types) (initialSignature [ part, part ])
        `shouldEqual` Right true

    it "refuses two different entries under one name" do
      let
        parts = [ withEntry (entry KType []), withEntry (entry (KFun KType KType) []) ]
      map (const unit) (initialSignature parts)
        `shouldEqual` Left (ConflictingTyCon (tyCon "Weird"))

    it "keeps constructors and values in one namespace across parts" do
      let
        ctorPart = emptySignature
          { ctors = Map.singleton (value "T")
              { owner: tyCon "T", tag: 0, fields: [], scheme: monoScheme int }
          }
        valuePart = emptySignature
          { values = Map.singleton (value "T") { scheme: monoScheme int, isForeign: false } }
      map (const unit) (initialSignature [ ctorPart, valuePart ])
        `shouldEqual` Left (ConflictingValue (value "T"))

  describe "data declarations" do
    it "derives the type of a constructor" do
      let
        m = moduleOf
          [ DeclData unit
              { name: TyName "Box"
              , kindVars: []
              , params: [ { name: TyVar "a", kind: KType } ]
              , constructors: [ { name: Ident "Box", tag: 0, fields: [ TVar (TyVar "a") ] } ]
              , isNewtype: false
              , attributes: []
              }
          ]
      ctorScheme m (value "Box")
        `shouldEqual` Just
          ( monoScheme
              ( TForall (TyVar "a") KType
                  (pureFn (TVar (TyVar "a")) (TApp (TCon (tyCon "Box") []) (TVar (TyVar "a"))))
              )
          )

    it "carries the kind scheme into the constructor's type" do
      -- `Proxy : forall k. forall (a : k). Proxy [[k]] a`
      let
        k = KindVar "k"
        m = moduleOf
          [ DeclData unit
              { name: TyName "Proxy"
              , kindVars: [ k ]
              , params: [ { name: TyVar "a", kind: KVar k } ]
              , constructors: [ { name: Ident "Proxy", tag: 0, fields: [] } ]
              , isNewtype: false
              , attributes: []
              }
          ]
      ctorScheme m (value "Proxy")
        `shouldEqual` Just
          { kindVars: [ k ]
          , body:
              TForall (TyVar "a") (KVar k)
                (TApp (TCon (tyCon "Proxy") [ KVar k ]) (TVar (TyVar "a")))
          }

    it "refuses a field that is not a type" do
      let
        m = moduleOf
          [ DeclData unit
              { name: TyName "Bad"
              , kindVars: []
              , params: []
              , constructors: [ { name: Ident "Bad", tag: 0, fields: [ TRowEmpty ] } ]
              , isNewtype: false
              , attributes: []
              }
          ]
      verdict m `shouldEqual` Left (IllKinded (ExpectedKind TRowEmpty KType AnyRow))

    it "refuses a tag used twice" do
      let
        m = moduleOf
          [ DeclData unit
              { name: TyName "Two"
              , kindVars: []
              , params: []
              , constructors:
                  [ { name: Ident "A", tag: 0, fields: [] }
                  , { name: Ident "B", tag: 0, fields: [] }
                  ]
              , isNewtype: false
              , attributes: []
              }
          ]
      verdict m `shouldEqual` Left (DuplicateTag (tyCon "Two") 0)

    it "accepts a newtype of one constructor with one field" do
      verdict (moduleOf [ newtypeOf [ { name: Ident "N", tag: 0, fields: [ int ] } ] ])
        `shouldEqual` Right unit

    it "refuses a newtype with two constructors" do
      verdict
        ( moduleOf
            [ newtypeOf
                [ { name: Ident "N", tag: 0, fields: [ int ] }
                , { name: Ident "M", tag: 1, fields: [ int ] }
                ]
            ]
        )
        `shouldEqual` Left (NewtypeShape (tyCon "N"))

    it "refuses a newtype whose constructor has two fields" do
      verdict (moduleOf [ newtypeOf [ { name: Ident "N", tag: 0, fields: [ int, int ] } ] ])
        `shouldEqual` Left (NewtypeShape (tyCon "N"))

  describe "effect declarations" do
    it "checks an operation signature" do
      verdict (moduleOf [ consoleDecl ]) `shouldEqual` Right unit

    it "refuses a parameter at a kind that is not quantifiable" do
      let
        m = moduleOf
          [ DeclEffect unit
              { name: EffName "Bad"
              , params: [ { name: TyVar "e", kind: KEffect } ]
              , operations: []
              , attributes: []
              }
          ]
      verdict m `shouldEqual` Left (IllKinded (NotQuantifiable KEffect))

    it "refuses one operation name twice" do
      let
        op = { name: OpName "log", tyBinders: [], argument: string, resumesWith: unitTy' }
        m = moduleOf
          [ DeclEffect unit
              { name: EffName "Console", params: [], operations: [ op, op ], attributes: [] }
          ]
      verdict m `shouldEqual` Left (DuplicateOperation consoleEff (OpName "log"))

  describe "foreign declarations" do
    it "accepts the shape every leaf takes" do
      verdict (moduleOf [ foreignDecl "primLog" (monoScheme (pureFn string (io unitTy'))) ])
        `shouldEqual` Right unit

    it "refuses an effectful result arrow" do
      -- the type would remove the effect from the row while the output never
      -- reaches a handler's clause
      verdict (moduleOf [ consoleDecl, foreignDecl "log" (monoScheme (fn string consoleRow unitTy')) ])
        `shouldEqual` Left (EffectfulForeign (value "log") consoleRow)

    it "refuses an effectful argument arrow" do
      -- the calling convention of the lowering would leak across the boundary
      let
        e = TyVar "e"
        a = TyVar "a"
        scheme = monoScheme
          ( TForall e (KRow RowEffect)
              (TForall a KType (pureFn (fn (TVar a) (TVar e) (TVar a)) (TVar a)))
          )
      verdict (moduleOf [ foreignDecl "mapImpl" scheme ])
        `shouldEqual` Left (EffectfulForeign (value "mapImpl") (TVar e))

    it "refuses an effectful arrow in the payload of a row" do
      -- a callback reaches the boundary through a record as readily as through
      -- an argument
      let
        row = TRowExtend (RowTypeEntry (SymbolKey (Symbol "cb")) (fn int consoleRow int)) TRowEmpty
        scheme = monoScheme (pureFn (TApp (TCon recordTy []) row) unitTy')
      verdict (moduleOf [ consoleDecl, foreignDecl "use" scheme ])
        `shouldEqual` Left (EffectfulForeign (value "use") consoleRow)

    it "does not traverse a constraint, which carries no value across" do
      -- a constraint is an erased proposition, so neither handler bypass nor a
      -- leaking calling convention can arise inside one
      let
        row = TRowExtend (RowTypeEntry (SymbolKey (Symbol "x")) (fn int consoleRow int)) TRowEmpty
        scheme = monoScheme (TConstrained (Lacks (SymbolKey (Symbol "cb")) row) (pureFn int int))
      verdict (moduleOf [ consoleDecl, foreignDecl "f" scheme ])
        `shouldEqual` Right unit

  describe "value declarations" do
    it "accepts a reference to a foreign declared later" do
      let
        m = moduleOf
          [ nonrec "x" (monoScheme (io unitTy')) (globalRef "primLog")
          , foreignDecl "primLog" (monoScheme (pureFn string (io unitTy')))
          ]
      verdict m `shouldEqual` Right unit

    it "refuses a reference to a later value declaration" do
      let
        m = moduleOf
          [ nonrec "x" (monoScheme int) (globalRef "y")
          , nonrec "y" (monoScheme int) (Lit unit (LitInt 1))
          ]
      verdict m `shouldEqual` Left (ForwardReference (value "y"))

    it "refuses a nonrec referring to itself" do
      let m = moduleOf [ nonrec "x" (monoScheme int) (globalRef "x") ]
      verdict m `shouldEqual` Left (ForwardReference (value "x"))

    it "accepts a rec group whose members refer to each other" do
      let
        m = moduleOf
          [ DeclRec unit
              [ { name: Ident "f", scheme: monoScheme int, value: globalRef "g", attributes: [] }
              , { name: Ident "g", scheme: monoScheme int, value: globalRef "f", attributes: [] }
              ]
          ]
      verdict m `shouldEqual` Right unit

    it "accepts a rec group whose members have different kind schemes" do
      -- every scheme is registered before any right-hand side is checked
      let
        k = KindVar "k"
        m = moduleOf
          [ DeclRec unit
              [ { name: Ident "f"
                , scheme: { kindVars: [ k ], body: TForall (TyVar "a") (KVar k) int }
                , value: globalRef "g"
                , attributes: []
                }
              , { name: Ident "g", scheme: monoScheme int, value: globalRef "f", attributes: [] }
              ]
          ]
      verdict m `shouldEqual` Right unit

  describe "module well-formedness" do
    it "refuses a module named Prim" do
      let m = (moduleOf []) { name = ModuleName "Prim" }
      verdict m `shouldEqual` Left (ReservedModuleName (ModuleName "Prim"))

    it "refuses one type name twice" do
      let
        decl = DeclData unit
          { name: TyName "T"
          , kindVars: []
          , params: []
          , constructors: []
          , isNewtype: false
          , attributes: []
          }
      verdict (moduleOf [ decl, decl ]) `shouldEqual` Left (DuplicateTyCon (tyCon "T"))

    it "refuses a constructor and a value of one name" do
      -- a constructor is an ordinary global name, so the two share a namespace
      let
        m = moduleOf
          [ DeclData unit
              { name: TyName "T"
              , kindVars: []
              , params: []
              , constructors: [ { name: Ident "T", tag: 0, fields: [] } ]
              , isNewtype: false
              , attributes: []
              }
          , nonrec "T" (monoScheme int) (Lit unit (LitInt 1))
          ]
      verdict m `shouldEqual` Left (DuplicateName (value "T"))

    it "refuses an export of a name the module does not declare" do
      verdict (exporting [ ExportValue (Ident "absent") ] [])
        `shouldEqual` Left (MissingExport (ExportValue (Ident "absent")))
