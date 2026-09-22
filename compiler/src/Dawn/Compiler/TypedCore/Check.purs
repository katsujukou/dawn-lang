-- | Term typing, `Γ; Δ ⊢ e : τ ! ρ`.
-- |
-- | `ρ` is the range of effects evaluating a term may produce. Pure constructs
-- | are typeable under any `ρ`; one that produces effects requires agreement
-- | with it. Containment is never inserted (D8), so an arrow's row equals the
-- | ambient row at an application and `openEff` is what widens one.
-- |
-- | The judgement is not directed and the checker is: a type is synthesized
-- | where the term determines one and checked where an enclosing annotation
-- | supplies it. Conversion is by equality, there being no subtyping.
module Dawn.Compiler.TypedCore.Check
  ( CheckError(..)
  , CheckFailure
  , Env
  , JoinInfo
  , envOf
  , infer
  , check
  , isValueForm
  , isFunVal
  ) where

import Prelude

import Prim as P

import Dawn.Compiler.TypedCore.Context (Context, assume, bindTyVar, bindVar, lookupVar)
import Dawn.Compiler.TypedCore.Entailment (DecomposeError, entails)
import Dawn.Compiler.TypedCore.Equality (constraintEquiv, typeEquiv)
import Dawn.Compiler.TypedCore.Kind (Kind(..), RowElemKind(..))
import Dawn.Compiler.TypedCore.Kinding (KindError, checkKind, quantifiableKind, wellFormedConstraint, wellFormedKey)
import Dawn.Compiler.TypedCore.Name (EffName, Ident, JoinName, OpName, Qualified, TyName, TyVar)
import Dawn.Compiler.TypedCore.Prim (asFunction, booleanTy, fn, litType, recordTy, variantTy)
import Dawn.Compiler.TypedCore.Row (RowError, RowNormalForm, fromNormalForm, nf)
import Dawn.Compiler.TypedCore.Signature (CanonicalClass(..), CtorInfo, EffectInfo, Signature, TyConInfo(..), lookupCtor, lookupEffect, lookupOperation, lookupTyCon, lookupValue)
import Dawn.Compiler.TypedCore.Term (Binding, DecisionTree(..), Expr(..), Handler, OpClause(..), Occurrence(..), Param, exprAnnotation, opClauseOp)
import Dawn.Compiler.TypedCore.Type (Constraint(..), RowEntry(..), RowKey, RowPayload(..), TyBinder, Type(..), TypeScheme, rowEntryKey, rowEntryPayload, substituteKindsInType, substituteType)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl, traverse_)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), snd)

-- | A join point, `j : (τ̄) -> τ ! ρ`. Its result type is written at the
-- | `letjoin`, so a `jump` has one whichever body the checker reaches first.
type JoinInfo =
  { params :: P.Array Type
  , result :: Type
  , row :: Type
  }

-- | `Σ`, `Γ`, and `Δ`, together with whether the term stands in tail position.
-- |
-- | `Δ` is discarded at a `λ`, a `Λ`, and a `handle`: a join point is a transfer
-- | of control within one function activation and crosses no function boundary.
type Env =
  { signature :: Signature
  , context :: Context
  , joins :: Map JoinName JoinInfo
  , tail :: P.Boolean
  }

-- | An error together with the term it is reported at. A decision tree and a
-- | handler carry no span of their own, so an error inside one is located at the
-- | `case` or `handle` containing it.
type CheckFailure a =
  { at :: a
  , error :: CheckError
  }

data CheckError
  = UnboundVar Ident
  | UndeclaredGlobal (Qualified Ident)
  -- | `M.x [[κ̄']]` supplying a number of kinds the scheme does not bind, as
  -- | expected and actual.
  | GlobalKindArgCount (Qualified Ident) P.Int P.Int
  -- | `Γ ⊢ τ1 ≡ τ2` fails, as expected and actual.
  | TypeMismatch Type Type
  -- | Two rows that are not equal, as expected and actual. An arrow's row meets
  -- | the ambient row here.
  | RowMismatch Type Type
  | NotAFunction Type
  | NotAForall Type
  | NotConstrained Type
  | NotARecord Type
  | NotAVariant Type
  -- | A row has no element at the key a term names.
  | NoElementAt RowKey Type
  -- | The payload of a declared effect where a type was wanted, or the reverse.
  | WrongPayload RowKey
  -- | A normal form pairing a payload with a key no element can carry.
  | MalformedRow Type
  | NotEntailed Constraint
  -- | The body of a `Λ` that is not a value form. The value restriction is what
  -- | makes `Λ` and its elimination erasable.
  | NotAValueForm
  -- | The right-hand side of a recursive binding that is not a function value
  -- | (D14). Under strict evaluation such a binding has no meaning.
  | NotAFunctionValue Ident
  | UnboundJoin JoinName
  | JoinArity JoinName P.Int P.Int
  -- | A `jump` outside tail position, which no transfer of control implements.
  | JumpNotInTail JoinName
  | UnknownOperation (Qualified EffName) OpName
  -- | `perform k.op [σ̄]` supplying a number of types the operation does not
  -- | bind, as expected and actual.
  | OperationTypeArgCount OpName P.Int P.Int
  -- | A handler clause for an operation the effect does not declare, or an
  -- | operation of it that no clause handles.
  | MissingClause (Qualified EffName) OpName
  -- | A clause whose own type binders are not those the operation declares. A
  -- | handler must respect an operation's polymorphism.
  | ClauseTypeBinders OpName
  -- | A binder introduced at a kind other than the one expected of it.
  | BinderKindMismatch Kind Kind
  -- | `Γ ⊢ C1 ≡ C2` fails, as expected and actual.
  | ConstraintMismatch Constraint Constraint
  -- | An effect the signature does not declare, where a handler names one.
  | EffectNotDeclared (Qualified EffName)
  | UnknownOccurrence Occurrence
  -- | `switchCtor` over an intrinsic type. It has no constructors to take
  -- | apart, so a dispatch over one would exhaust vacuously.
  | NotADataType (Qualified TyName)
  | NotAConstructorOf (Qualified TyName) (Qualified Ident)
  -- | A dispatch naming one branch twice.
  | DuplicateBranch
  -- | A dispatch that is not locally total, leaving a value with no
  -- | destination.
  | NotExhaustive
  -- | `switchLit` over a type whose values are not literals.
  | NotALiteralType Type
  -- | A `switch*` over an occurrence whose type it cannot dispatch on.
  | UndispatchableOccurrence Occurrence Type
  -- | A tree with no leaf, which leaves the dispatch with no type.
  | NoLeaf
  -- | A type written in a term whose kind the rules do not derive.
  | IllKindedType KindError
  | NotARowType RowError
  | UndecidedConstraint DecomposeError

-- | The environment a top-level right-hand side is checked in. The join point
-- | context is empty, a join point crossing no declaration boundary.
envOf :: Signature -> Context -> Env
envOf signature context =
  { signature, context, joins: Map.empty, tail: true }

-- | `Γ;Δ ⊢ e : τ ! ρ`, synthesizing the type.
infer :: forall a. Env -> Type -> Expr a -> Either (CheckFailure a) Type
infer env rho expr = case expr of
  Var at name -> case lookupVar env.context name of
    Just ty -> Right ty
    Nothing -> Left { at, error: UnboundVar name }

  Global at name kinds -> do
    scheme <- globalScheme at env.signature name
    instantiateKinds at env name kinds scheme

  Lit _ literal -> Right (litType literal)

  -- A `λ` does not write the row of its arrow. A synthesized one takes the
  -- ambient row, which is what application requires of it; every other position
  -- that reaches a `λ` has a type to check it against.
  Lam at name ty body -> do
    kinded at (checkKind env.signature env.context ty KType)
    result <- infer (lambdaEnv env name ty) rho body
    Right (fn ty rho result)

  App at f x -> do
    fnType <- infer (notTail env) rho f
    parts <- functionParts at fnType
    sameRow at rho parts.row
    check (notTail env) rho parts.argument x
    Right parts.result

  TyLam at name kind body -> do
    kinded at (quantifiableKind env.context kind)
    valueForm at env body
    let inner = (abstracted env) { context = bindTyVar env.context name kind }
    result <- infer inner TRowEmpty body
    Right (TForall name kind result)

  TyApp at e ty -> do
    quantified <- infer (notTail env) rho e
    case quantified of
      TForall name kind body -> do
        kinded at (checkKind env.signature env.context ty kind)
        Right (substituteType (Map.singleton name ty) body)
      other -> Left { at, error: NotAForall other }

  ConstraintLam at constraint body -> do
    kinded at (wellFormedConstraint env.signature env.context constraint)
    valueForm at env body
    inner <- assuming at env constraint
    result <- infer (abstracted inner) TRowEmpty body
    Right (TConstrained constraint result)

  ConstraintApp at e -> do
    constrained <- infer (notTail env) rho e
    case constrained of
      TConstrained constraint body -> do
        require at env constraint
        Right body
      other -> Left { at, error: NotConstrained other }

  Let at name ty value body -> do
    kinded at (checkKind env.signature env.context ty KType)
    check (notTail env) rho ty value
    infer (bound env name ty) rho body

  LetRec at bindings body -> do
    inner <- recursiveEnv at env bindings
    infer inner rho body

  Case at scrutinees dt -> do
    occurrences <- scrutineeTypes env rho scrutinees
    tree at env rho Nothing occurrences dt

  LetJoin at name params result value body -> do
    traverse_ (\param -> kinded at (checkKind env.signature env.context param.ty KType)) params
    kinded at (checkKind env.signature env.context result KType)
    checkJoinBody env name params result rho value
    check (joining env name params result rho) rho result body
    Right result

  Jump at name args -> do
    info <- joinInfo at env name
    when (not env.tail) (Left { at, error: JumpNotInTail name })
    sameRow at rho info.row
    checkArguments at env rho name info.params args
    Right info.result

  RecordEmpty _ -> Right (record TRowEmpty)

  RecordExtend at key value rest -> do
    kinded at (wellFormedKey env.signature key RowType)
    valueType <- infer (notTail env) rho value
    row <- recordRow at env rho rest
    require at env (Lacks key row)
    Right (record (TRowExtend (RowTypeEntry key valueType) row))

  RecordSelect at key e -> do
    kinded at (wellFormedKey env.signature key RowType)
    row <- recordRow at env rho e
    payloadAt at key row

  RecordRestrict at key e -> do
    kinded at (wellFormedKey env.signature key RowType)
    row <- recordRow at env rho e
    normal <- normalize at row
    _ <- payloadAt at key row
    rest <- rowOfNormalForm at row (normal { known = Map.delete key normal.known })
    Right (record rest)

  RecordUpdate at key value rest -> do
    kinded at (wellFormedKey env.signature key RowType)
    row <- recordRow at env rho rest
    normal <- normalize at row
    _ <- payloadAt at key row
    valueType <- infer (notTail env) rho value
    updated <- rowOfNormalForm at row (normal { known = Map.insert key (TypePayload valueType) normal.known })
    Right (record updated)

  RecordMerge at left right -> do
    leftRow <- recordRow at env rho left
    rightRow <- recordRow at env rho right
    require at env (Disjoint leftRow rightRow)
    Right (record (TRowUnion leftRow rightRow))

  -- The residual row of an injection is not written in the term. A synthesized
  -- one is the variant of that key alone, and `weaken` is what widens it.
  VariantInject at key value -> do
    kinded at (wellFormedKey env.signature key RowType)
    valueType <- infer (notTail env) rho value
    Right (variant (TRowExtend (RowTypeEntry key valueType) TRowEmpty))

  VariantWeaken at key ty e -> do
    kinded at (wellFormedKey env.signature key RowType)
    kinded at (checkKind env.signature env.context ty KType)
    row <- variantRow at env rho e
    require at env (Lacks key row)
    Right (variant (TRowExtend (RowTypeEntry key ty) row))

  VariantAbsurd at ty e -> do
    kinded at (checkKind env.signature env.context ty KType)
    row <- variantRow at env rho e
    sameRow at TRowEmpty row
    Right ty

  -- The key selects the element and the payload selects the protocol: the
  -- operation's signature comes from the effect the payload names, never from
  -- the key.
  Perform at key op tyArgs arg -> do
    normal <- normalize at rho
    case Map.lookup key normal.known of
      Nothing -> Left { at, error: NoElementAt key rho }
      Just (TypePayload _) -> Left { at, error: WrongPayload key }
      Just (EffectPayload name args) -> do
        { params, signature } <- operationOf at env name op
        substitution <- operationSubstitution at env op params args signature.tyBinders tyArgs
        check (notTail env) rho (substituteType substitution signature.argument) arg
        Right (substituteType substitution signature.resumesWith)

  Handle at body handler -> handled at env rho Nothing body handler

  OpenEff at row e -> do
    kinded at (checkKind env.signature env.context row (KRow RowEffect))
    fnType <- infer (notTail env) rho e
    parts <- functionParts at fnType
    require at env (Disjoint parts.row row)
    Right (fn parts.argument (TRowUnion parts.row row) parts.result)

-- | `Γ;Δ ⊢ e : τ ! ρ` against a type an enclosing annotation supplies.
check :: forall a. Env -> Type -> Type -> Expr a -> Either (CheckFailure a) Unit
check env rho expected expr = case expr of
  Lam at name ty body -> do
    parts <- functionParts at expected
    kinded at (checkKind env.signature env.context ty KType)
    equalTypes at parts.argument ty
    check (lambdaEnv env name ty) parts.row parts.result body

  VariantInject at key value -> do
    kinded at (wellFormedKey env.signature key RowType)
    row <- variantOf at expected
    payload <- payloadAt at key row
    check (notTail env) rho payload value

  Let at name ty value body -> do
    kinded at (checkKind env.signature env.context ty KType)
    check (notTail env) rho ty value
    check (bound env name ty) rho expected body

  LetRec at bindings body -> do
    inner <- recursiveEnv at env bindings
    check inner rho expected body

  Case at scrutinees dt -> do
    occurrences <- scrutineeTypes env rho scrutinees
    _ <- tree at env rho (Just expected) occurrences dt
    Right unit

  LetJoin at name params result value body -> do
    traverse_ (\param -> kinded at (checkKind env.signature env.context param.ty KType)) params
    kinded at (checkKind env.signature env.context result KType)
    equalTypes at expected result
    checkJoinBody env name params result rho value
    check (joining env name params result rho) rho result body

  TyLam at name kind body -> case expected of
    TForall expectedName expectedKind inner -> do
      kinded at (quantifiableKind env.context kind)
      when (kind /= expectedKind) (Left { at, error: BinderKindMismatch expectedKind kind })
      valueForm at env body
      let aligned = substituteType (Map.singleton expectedName (TVar name)) inner
      check ((abstracted env) { context = bindTyVar env.context name kind }) TRowEmpty aligned body
    other -> Left { at, error: NotAForall other }

  ConstraintLam at constraint body -> case expected of
    TConstrained expectedConstraint inner -> do
      kinded at (wellFormedConstraint env.signature env.context constraint)
      sameConstraint at expectedConstraint constraint
      valueForm at env body
      assumed <- assuming at env constraint
      check (abstracted assumed) TRowEmpty inner body
    other -> Left { at, error: NotConstrained other }

  Handle at body handler -> do
    _ <- handled at env rho (Just expected) body handler
    Right unit

  other -> do
    actual <- infer env rho other
    equalTypes (exprAnnotation other) expected actual

-- | `handle e with h`.
-- |
-- | Inside the `handle` the row grows by the element the handler writes, and
-- | that element is what the `handle` removes. The key selects it; the payload
-- | names the effect whose operations the clauses exhaust.
handled
  :: forall a
   . a
  -> Env
  -> Type
  -> Maybe Type
  -> Expr a
  -> Handler a
  -> Either (CheckFailure a) Type
handled at env rho expected body handler = do
  let inner = TRowExtend handler.element rho
  kinded at (checkKind env.signature env.context inner (KRow RowEffect))
  let alpha = handler.returnClause.ty
  kinded at (checkKind env.signature env.context alpha KType)
  check (abstracted env) inner alpha body
  beta <- returnType at env rho expected alpha handler
  payload <- effectPayloadOf at handler.element
  info <- effectInfoOf at env payload.name
  checkClauses at env rho beta payload info handler.opClauses
  Right beta

returnType
  :: forall a
   . a
  -> Env
  -> Type
  -> Maybe Type
  -> Type
  -> Handler a
  -> Either (CheckFailure a) Type
returnType _ env rho expected alpha handler = case expected of
  Just ty -> do
    check returning rho ty handler.returnClause.body
    Right ty
  Nothing -> infer returning rho handler.returnClause.body
  where
  returning = abstracted (bound env handler.returnClause.binder alpha)

effectPayloadOf
  :: forall a
   . a
  -> RowEntry
  -> Either (CheckFailure a) { name :: Qualified EffName, args :: P.Array Type }
effectPayloadOf at element = case rowEntryPayload element of
  EffectPayload name args -> Right { name, args }
  TypePayload _ -> Left { at, error: WrongPayload (rowEntryKey element) }

effectInfoOf :: forall a. a -> Env -> Qualified EffName -> Either (CheckFailure a) EffectInfo
effectInfoOf at env name = case lookupEffect env.signature name of
  Just info -> Right info
  Nothing -> Left { at, error: EffectNotDeclared name }

-- | The clauses exhaust the operations of the effect, each once.
checkClauses
  :: forall a
   . a
  -> Env
  -> Type
  -> Type
  -> { name :: Qualified EffName, args :: P.Array Type }
  -> EffectInfo
  -> P.Array (OpClause a)
  -> Either (CheckFailure a) Unit
checkClauses at env rho beta payload info clauses = do
  distinct at (map opClauseOp clauses)
  traverse_ declared (Array.fromFoldable (Map.keys info.operations))
  traverse_ (checkClause at env rho beta payload info) clauses
  where
  declared op =
    when (not (Array.elem op (map opClauseOp clauses)))
      (Left { at, error: MissingClause payload.name op })

-- | One clause, with the operation's own type binders α-aligned to those the
-- | declaration writes.
-- |
-- | The two forms share the operation, its type binders, and its argument, and
-- | differ in the tail (D28). A `FullClause` binds a continuation `τ' -{ρ}-> β`
-- | — resuming returns under the same handler, which is what makes handlers
-- | deep (D15) — and its body is checked at `β`. A `FastClause` binds none, and
-- | its body is checked at `τ'`, the type the operation resumes with; `β` takes
-- | no part in checking it.
checkClause
  :: forall a
   . a
  -> Env
  -> Type
  -> Type
  -> { name :: Qualified EffName, args :: P.Array Type }
  -> EffectInfo
  -> OpClause a
  -> Either (CheckFailure a) Unit
checkClause at env rho beta payload info clause = do
  decl <- case Map.lookup shared.op info.operations of
    Just decl -> Right decl
    Nothing -> Left { at, error: MissingClause payload.name shared.op }
  when (Array.length decl.tyBinders /= Array.length shared.tyBinders)
    (Left { at, error: ClauseTypeBinders shared.op })
  traverse_ (\(Tuple declared written) -> when (declared.kind /= written.kind) (Left { at, error: ClauseTypeBinders shared.op }))
    (Array.zip decl.tyBinders shared.tyBinders)
  let
    substitution =
      Map.union
        (Map.fromFoldable (Array.zip (map _.name decl.tyBinders) (map (TVar <<< _.name) shared.tyBinders)))
        (Map.fromFoldable (Array.zip (map _.name info.params) payload.args))
    resumesWith = substituteType substitution decl.resumesWith
    inner = clauseEnv env shared.tyBinders shared.argBinder
  equalTypes at (substituteType substitution decl.argument) shared.argBinder.ty
  case clause of
    FullClause c -> do
      equalTypes at (fn resumesWith rho beta) c.contBinder.ty
      check (bound inner c.contBinder.name c.contBinder.ty) rho beta c.body
    FastClause c ->
      check inner rho resumesWith c.body
  where
  shared = case clause of
    FullClause c -> { op: c.op, tyBinders: c.tyBinders, argBinder: c.argBinder }
    FastClause c -> { op: c.op, tyBinders: c.tyBinders, argBinder: c.argBinder }

-- | `Γ` a clause body is checked in: the operation's own type binders, then its
-- | argument. A continuation is bound on top of this where the form has one.
clauseEnv :: Env -> P.Array TyBinder -> Param -> Env
clauseEnv env tyBinders argBinder =
  bound quantified argBinder.name argBinder.ty
  where
  quantified =
    foldl (\acc binder -> acc { context = bindTyVar acc.context binder.name binder.kind })
      (abstracted env)
      tyBinders

sameConstraint :: forall a. a -> Constraint -> Constraint -> Either (CheckFailure a) Unit
sameConstraint at expected actual = case constraintEquiv expected actual of
  Left err -> Left { at, error: NotARowType err }
  Right true -> Right unit
  Right false -> Left { at, error: ConstraintMismatch expected actual }

-- | `Γ;Δ;Ω ⊢ dt : τ ! ρ`.
-- |
-- | The type is supplied where an annotation reaches the tree and taken from the
-- | first leaf otherwise; every other leaf is checked against it, so which it is
-- | makes no difference to what is accepted beyond a tree having no leaf at all.
tree
  :: forall a
   . a
  -> Env
  -> Type
  -> Maybe Type
  -> Map Occurrence Type
  -> DecisionTree a
  -> Either (CheckFailure a) Type
tree at env rho expected occurrences dt = case dt of
  Leaf e -> case expected of
    Just ty -> do
      check env rho ty e
      Right ty
    Nothing -> infer env rho e

  Bind name occurrence inner -> do
    ty <- occurrenceType at occurrences occurrence
    tree at (bound env name ty) rho expected occurrences inner

  SwitchCtor occurrence branches fallback -> do
    scrutinee <- occurrenceType at occurrences occurrence
    spine <- constructorSpine at env occurrence scrutinee
    distinct at (map _.ctor branches)
    items <- traverse (ctorItem at env occurrences occurrence spine) branches
    exhaustive at spine.constructors (map _.ctor branches) fallback
    subTrees at env rho expected (items <> fallbackItem occurrences fallback)

  SwitchLit occurrence branches fallback -> do
    scrutinee <- occurrenceType at occurrences occurrence
    literalType at env scrutinee
    distinct at (map _.lit branches)
    traverse_ (\branch -> equalTypes at scrutinee (litType branch.lit)) branches
    subTrees at env rho expected
      (map (\branch -> Tuple occurrences branch.tree) branches <> [ Tuple occurrences fallback ])

  SwitchKey occurrence branches fallback -> do
    scrutinee <- occurrenceType at occurrences occurrence
    row <- variantOf at scrutinee
    normal <- normalize at row
    distinct at (map _.key branches)
    items <- traverse (keyItem at occurrences occurrence row normal) branches
    residual <- residualVariant at row normal (map _.key branches)
    keysExhaustive at normal (map _.key branches) fallback
    subTrees at env rho expected
      (items <> fallbackItem (Map.insert occurrence residual occurrences) fallback)

  Guard condition consequent alternative -> do
    check (notTail env) rho (TCon booleanTy []) condition
    subTrees at env rho expected
      [ Tuple occurrences consequent, Tuple occurrences alternative ]

-- The rules, one helper each --------------------------------------------------

globalScheme :: forall a. a -> Signature -> Qualified Ident -> Either (CheckFailure a) TypeScheme
globalScheme at sig name = case lookupValue sig name, lookupCtor sig name of
  Just info, _ -> Right info.scheme
  _, Just info -> Right info.scheme
  _, _ -> Left { at, error: UndeclaredGlobal name }

-- | `M.x [[κ̄']]`. The kinds are written in the term, so this verifies their
-- | number and their layer and substitutes; it neither guesses nor searches.
instantiateKinds
  :: forall a
   . a
  -> Env
  -> Qualified Ident
  -> P.Array Kind
  -> TypeScheme
  -> Either (CheckFailure a) Type
instantiateKinds at env name kinds scheme = do
  let expected = Array.length scheme.kindVars
  let actual = Array.length kinds
  when (expected /= actual) (Left { at, error: GlobalKindArgCount name expected actual })
  traverse_ (\kind -> kinded at (quantifiableKind env.context kind)) kinds
  Right (substituteKindsInType (Map.fromFoldable (Array.zip scheme.kindVars kinds)) scheme.body)

-- | Every scheme of a recursive group is registered before any right-hand side
-- | is checked, and each of those is a function value.
recursiveEnv :: forall a. a -> Env -> P.Array (Binding a) -> Either (CheckFailure a) Env
recursiveEnv at env bindings = do
  let inner = foldl (\acc binding -> bound acc binding.name binding.ty) env bindings
  traverse_ (checkBinding inner) bindings
  Right inner
  where
  checkBinding inner binding = do
    kinded at (checkKind env.signature env.context binding.ty KType)
    when (not (isFunVal binding.value))
      (Left { at, error: NotAFunctionValue binding.name })
    check inner TRowEmpty binding.ty binding.value

checkJoinBody
  :: forall a
   . Env
  -> JoinName
  -> P.Array Param
  -> Type
  -> Type
  -> Expr a
  -> Either (CheckFailure a) Unit
checkJoinBody env name params result rho value =
  check inner rho result value
  where
  -- The root of a join definition is in tail position whatever position the
  -- `letjoin` itself stands in.
  inner =
    foldl (\acc param -> bound acc param.name param.ty)
      ((joining env name params result rho) { tail = true })
      params

checkArguments
  :: forall a
   . a
  -> Env
  -> Type
  -> JoinName
  -> P.Array Type
  -> P.Array (Expr a)
  -> Either (CheckFailure a) Unit
checkArguments at env rho name params args = do
  let expected = Array.length params
  let actual = Array.length args
  when (expected /= actual) (Left { at, error: JoinArity name expected actual })
  traverse_ (\(Tuple ty arg) -> check (notTail env) rho ty arg) (Array.zip params args)

scrutineeTypes
  :: forall a
   . Env
  -> Type
  -> P.Array (Expr a)
  -> Either (CheckFailure a) (Map Occurrence Type)
scrutineeTypes env rho scrutinees = do
  types <- traverse (infer (notTail env) rho) scrutinees
  Right (Map.fromFoldable (Array.mapWithIndex (\i ty -> Tuple (OccScrutinee i) ty) types))

-- | `Ω ⊢ o : τ`.
-- |
-- | A dispatch puts what it takes apart into `Ω`, so what a constructor or a
-- | variant carries is typeable only under the branch that established it. The
-- | element of a record at a key needs no branch: a record has one at every key
-- | of its row, so that path is read off the type of what it projects from.
occurrenceType :: forall a. a -> Map Occurrence Type -> Occurrence -> Either (CheckFailure a) Type
occurrenceType at occurrences occurrence = case Map.lookup occurrence occurrences of
  Just ty -> Right ty
  Nothing -> case occurrence of
    OccRecordField base key -> do
      baseType <- occurrenceType at occurrences base
      row <- recordOf at baseType
      payloadAt at key row
    _ -> Left { at, error: UnknownOccurrence occurrence }

-- | `T σ̄` together with the constructors of `T`, which a `switchCtor` takes
-- | apart. An intrinsic type has none and is not dispatched on this way.
constructorSpine
  :: forall a
   . a
  -> Env
  -> Occurrence
  -> Type
  -> Either (CheckFailure a) { name :: Qualified TyName, kinds :: P.Array Kind, args :: P.Array Type, constructors :: P.Array (Qualified Ident) }
constructorSpine at env occurrence ty = case spineOf ty [] of
  Just { name, kinds, args } -> case lookupTyCon env.signature name of
    Just (DataTyCon _ constructors) -> Right { name, kinds, args, constructors }
    Just (IntrinsicTyCon _ _) -> Left { at, error: NotADataType name }
    Nothing -> Left { at, error: NotADataType name }
  Nothing -> Left { at, error: UndispatchableOccurrence occurrence ty }

spineOf :: Type -> P.Array Type -> Maybe { name :: Qualified TyName, kinds :: P.Array Kind, args :: P.Array Type }
spineOf ty acc = case ty of
  TCon name kinds -> Just { name, kinds, args: acc }
  TApp f x -> spineOf f (Array.cons x acc)
  _ -> Nothing

-- | Every sub-tree of a dispatch, at one type.
-- |
-- | The first is checked against what an enclosing annotation gave, or
-- | synthesized where there was none, and the rest against that.
subTrees
  :: forall a
   . a
  -> Env
  -> Type
  -> Maybe Type
  -> P.Array (Tuple (Map Occurrence Type) (DecisionTree a))
  -> Either (CheckFailure a) Type
subTrees at env rho expected items = do
  ty <- case expected of
    Just given -> Right given
    Nothing -> case Array.find (hasLeaf <<< snd) items of
      Just (Tuple occurrences dt) -> tree at env rho Nothing occurrences dt
      Nothing -> Left { at, error: NoLeaf }
  traverse_ (\(Tuple occurrences dt) -> tree at env rho (Just ty) occurrences dt) items
  Right ty

-- | Whether a tree reaches a leaf. A sub-tree that reaches none gives the
-- | dispatch no type, and the written order of branches carries no meaning, so
-- | the type is taken from one that does.
hasLeaf :: forall a. DecisionTree a -> P.Boolean
hasLeaf = case _ of
  Leaf _ -> true
  Bind _ _ inner -> hasLeaf inner
  SwitchCtor _ branches fallback ->
    Array.any (hasLeaf <<< _.tree) branches || Array.any hasLeaf (Array.fromFoldable fallback)
  SwitchLit _ branches fallback ->
    Array.any (hasLeaf <<< _.tree) branches || hasLeaf fallback
  SwitchKey _ branches fallback ->
    Array.any (hasLeaf <<< _.tree) branches || Array.any hasLeaf (Array.fromFoldable fallback)
  Guard _ consequent alternative -> hasLeaf consequent || hasLeaf alternative

fallbackItem
  :: forall a
   . Map Occurrence Type
  -> Maybe (DecisionTree a)
  -> P.Array (Tuple (Map Occurrence Type) (DecisionTree a))
fallbackItem occurrences = case _ of
  Nothing -> []
  Just dt -> [ Tuple occurrences dt ]

-- | The fields of a constructor enter `Ω` as `o ! Ctor . j`, with the type
-- | parameters of the declaration instantiated from the type of the occurrence.
ctorItem
  :: forall a
   . a
  -> Env
  -> Map Occurrence Type
  -> Occurrence
  -> { name :: Qualified TyName, kinds :: P.Array Kind, args :: P.Array Type, constructors :: P.Array (Qualified Ident) }
  -> { ctor :: Qualified Ident, tree :: DecisionTree a }
  -> Either (CheckFailure a) (Tuple (Map Occurrence Type) (DecisionTree a))
ctorItem at env occurrences occurrence spine branch = do
  when (not (Array.elem branch.ctor spine.constructors))
    (Left { at, error: NotAConstructorOf spine.name branch.ctor })
  info <- constructorInfo at env branch.ctor
  let fields = map (instantiateField spine info) info.fields
  Right (Tuple (foldl addField occurrences (Array.mapWithIndex Tuple fields)) branch.tree)
  where
  addField acc (Tuple index ty) =
    Map.insert (OccField occurrence branch.ctor index) ty acc

instantiateField
  :: { name :: Qualified TyName, kinds :: P.Array Kind, args :: P.Array Type, constructors :: P.Array (Qualified Ident) }
  -> CtorInfo
  -> Type
  -> Type
instantiateField spine info =
  substituteType (Map.fromFoldable (Array.zip (map _.name info.params) spine.args))
    <<< substituteKindsInType (Map.fromFoldable (Array.zip info.scheme.kindVars spine.kinds))

constructorInfo :: forall a. a -> Env -> Qualified Ident -> Either (CheckFailure a) CtorInfo
constructorInfo at env name = case lookupCtor env.signature name of
  Just info -> Right info
  Nothing -> Left { at, error: UndeclaredGlobal name }

literalType :: forall a. a -> Env -> Type -> Either (CheckFailure a) Unit
literalType at env ty = case spineOf ty [] of
  Just { name, args: [] } -> case lookupTyCon env.signature name of
    Just (IntrinsicTyCon _ CanonicalLiteral) -> Right unit
    _ -> Left { at, error: NotALiteralType ty }
  _ -> Left { at, error: NotALiteralType ty }

-- | The payload a variant carries at a key enters `Ω` as `o ? k`.
keyItem
  :: forall a
   . a
  -> Map Occurrence Type
  -> Occurrence
  -> Type
  -> RowNormalForm
  -> { key :: RowKey, tree :: DecisionTree a }
  -> Either (CheckFailure a) (Tuple (Map Occurrence Type) (DecisionTree a))
keyItem at occurrences occurrence row normal branch =
  case Map.lookup branch.key normal.known of
    Nothing -> Left { at, error: NoElementAt branch.key row }
    Just (EffectPayload _ _) -> Left { at, error: WrongPayload branch.key }
    Just (TypePayload payload) ->
      Right
        ( Tuple (Map.insert (OccVariantPayload occurrence branch.key) payload occurrences)
            branch.tree
        )

-- | The type an occurrence takes in a default branch: the variant of the row
-- | with the enumerated keys removed, not the type it had.
residualVariant
  :: forall a
   . a
  -> Type
  -> RowNormalForm
  -> P.Array RowKey
  -> Either (CheckFailure a) Type
residualVariant at row normal keys = do
  rest <- rowOfNormalForm at row (normal { known = foldl (flip Map.delete) normal.known keys })
  Right (variant rest)

exhaustive
  :: forall a
   . a
  -> P.Array (Qualified Ident)
  -> P.Array (Qualified Ident)
  -> Maybe (DecisionTree a)
  -> Either (CheckFailure a) Unit
exhaustive at constructors branches fallback = case fallback of
  Just _ -> Right unit
  Nothing ->
    when (not (Array.all (\ctor -> Array.elem ctor branches) constructors))
      (Left { at, error: NotExhaustive })

-- | Absent a default, a `switchKey` has an empty unknown tail and enumerates
-- | every known key: a value carrying anything else would have no destination.
keysExhaustive
  :: forall a
   . a
  -> RowNormalForm
  -> P.Array RowKey
  -> Maybe (DecisionTree a)
  -> Either (CheckFailure a) Unit
keysExhaustive at normal branches fallback = case fallback of
  Just _ -> Right unit
  Nothing -> do
    when (not (Set.isEmpty normal.tail)) (Left { at, error: NotExhaustive })
    when (not (Array.all (\key -> Array.elem key branches) (Map.keys normal.known # Array.fromFoldable)))
      (Left { at, error: NotExhaustive })

distinct :: forall a b. Ord b => a -> P.Array b -> Either (CheckFailure a) Unit
distinct at items =
  when (Array.length items /= Set.size (Set.fromFoldable items))
    (Left { at, error: DuplicateBranch })

-- Effects ---------------------------------------------------------------------

-- | `ā`, the type parameters of the effect, together with the signature the
-- | operation is declared with.
operationOf
  :: forall a
   . a
  -> Env
  -> Qualified EffName
  -> OpName
  -> Either (CheckFailure a) { params :: P.Array TyVar, signature :: OpSignature }
operationOf at env name op = case lookupEffect env.signature name of
  Nothing -> Left { at, error: UnknownOperation name op }
  Just info -> case lookupOperation env.signature name op of
    Nothing -> Left { at, error: UnknownOperation name op }
    Just decl -> Right
      { params: map _.name info.params
      , signature:
          { tyBinders: decl.tyBinders, argument: decl.argument, resumesWith: decl.resumesWith }
      }

type OpSignature =
  { tyBinders :: P.Array { name :: TyVar, kind :: Kind }
  , argument :: Type
  , resumesWith :: Type
  }

-- | `[ā := τ̄]` from the payload, and `[b̄ := σ̄]` from the term.
operationSubstitution
  :: forall a
   . a
  -> Env
  -> OpName
  -> P.Array TyVar
  -> P.Array Type
  -> P.Array { name :: TyVar, kind :: Kind }
  -> P.Array Type
  -> Either (CheckFailure a) (Map TyVar Type)
operationSubstitution at env op params args binders tyArgs = do
  let expected = Array.length binders
  let actual = Array.length tyArgs
  when (expected /= actual) (Left { at, error: OperationTypeArgCount op expected actual })
  traverse_ (\(Tuple binder ty) -> kinded at (checkKind env.signature env.context ty binder.kind))
    (Array.zip binders tyArgs)
  Right
    ( Map.union
        (Map.fromFoldable (Array.zip (map _.name binders) tyArgs))
        (Map.fromFoldable (Array.zip params args))
    )

-- Value forms -----------------------------------------------------------------

-- | `v`.
-- |
-- | A constructor spine is a value form saturated or not: a constructor has no
-- | body to reduce, so an unsaturated one is a value that behaves as a function.
isValueForm :: forall a. Signature -> Expr a -> P.Boolean
isValueForm sig = case _ of
  Lit _ _ -> true
  Lam _ _ _ _ -> true
  TyLam _ _ _ body -> isValueForm sig body
  ConstraintLam _ _ body -> isValueForm sig body
  RecordEmpty _ -> true
  RecordExtend _ _ value rest -> isValueForm sig value && isValueForm sig rest
  VariantInject _ _ value -> isValueForm sig value
  other -> isCtorSpine sig other

isCtorSpine :: forall a. Signature -> Expr a -> P.Boolean
isCtorSpine sig = case _ of
  Global _ name _ -> isJust (lookupCtor sig name)
  App _ f x -> isCtorSpine sig f && isValueForm sig x
  TyApp _ e _ -> isCtorSpine sig e
  ConstraintApp _ e -> isCtorSpine sig e
  _ -> false

-- | `FunVal`, the right-hand side a recursive binding admits (D14).
isFunVal :: forall a. Expr a -> P.Boolean
isFunVal = case _ of
  Lam _ _ _ _ -> true
  TyLam _ _ _ body -> isFunVal body
  ConstraintLam _ _ body -> isFunVal body
  _ -> false

valueForm :: forall a. a -> Env -> Expr a -> Either (CheckFailure a) Unit
valueForm at env body =
  when (not (isValueForm env.signature body)) (Left { at, error: NotAValueForm })

-- Environments ----------------------------------------------------------------

bound :: Env -> Ident -> Type -> Env
bound env name ty = env { context = bindVar env.context name ty }

-- | A `λ` discards the join point context and its body stands in tail position.
lambdaEnv :: Env -> Ident -> Type -> Env
lambdaEnv env name ty =
  (abstracted env) { context = bindVar env.context name ty }

abstracted :: Env -> Env
abstracted env = env { joins = Map.empty, tail = true }

notTail :: Env -> Env
notTail env = env { tail = false }

joining :: Env -> JoinName -> P.Array Param -> Type -> Type -> Env
joining env name params result rho =
  env { joins = Map.insert name { params: map _.ty params, result, row: rho } env.joins }

joinInfo :: forall a. a -> Env -> JoinName -> Either (CheckFailure a) JoinInfo
joinInfo at env name = case Map.lookup name env.joins of
  Just info -> Right info
  Nothing -> Left { at, error: UnboundJoin name }

assuming :: forall a. a -> Env -> Constraint -> Either (CheckFailure a) Env
assuming at env constraint = case assume env.context constraint of
  Left err -> Left { at, error: UndecidedConstraint err }
  Right context -> Right env { context = context }

-- Decisions the rules delegate ------------------------------------------------

require :: forall a. a -> Env -> Constraint -> Either (CheckFailure a) Unit
require at env constraint = case entails env.context.facts constraint of
  Left err -> Left { at, error: UndecidedConstraint err }
  Right true -> Right unit
  Right false -> Left { at, error: NotEntailed constraint }

equalTypes :: forall a. a -> Type -> Type -> Either (CheckFailure a) Unit
equalTypes at expected actual = case typeEquiv expected actual of
  Left err -> Left { at, error: NotARowType err }
  Right true -> Right unit
  Right false -> Left { at, error: TypeMismatch expected actual }

sameRow :: forall a. a -> Type -> Type -> Either (CheckFailure a) Unit
sameRow at expected actual = case typeEquiv expected actual of
  Left err -> Left { at, error: NotARowType err }
  Right true -> Right unit
  Right false -> Left { at, error: RowMismatch expected actual }

normalize :: forall a. a -> Type -> Either (CheckFailure a) RowNormalForm
normalize at row = case nf row of
  Left err -> Left { at, error: NotARowType err }
  Right normal -> Right normal

rowOfNormalForm :: forall a. a -> Type -> RowNormalForm -> Either (CheckFailure a) Type
rowOfNormalForm at row normal = case fromNormalForm normal of
  Just ty -> Right ty
  Nothing -> Left { at, error: MalformedRow row }

kinded :: forall a b. a -> Either KindError b -> Either (CheckFailure a) b
kinded at = case _ of
  Left err -> Left { at, error: IllKindedType err }
  Right value -> Right value

functionParts :: forall a. a -> Type -> Either (CheckFailure a) { argument :: Type, row :: Type, result :: Type }
functionParts at ty = case asFunction ty of
  Just parts -> Right parts
  Nothing -> Left { at, error: NotAFunction ty }

record :: Type -> Type
record row = TApp (TCon recordTy []) row

variant :: Type -> Type
variant row = TApp (TCon variantTy []) row

recordOf :: forall a. a -> Type -> Either (CheckFailure a) Type
recordOf at ty = case ty of
  TApp (TCon name []) row | name == recordTy -> Right row
  _ -> Left { at, error: NotARecord ty }

variantOf :: forall a. a -> Type -> Either (CheckFailure a) Type
variantOf at ty = case ty of
  TApp (TCon name []) row | name == variantTy -> Right row
  _ -> Left { at, error: NotAVariant ty }

recordRow :: forall a. a -> Env -> Type -> Expr a -> Either (CheckFailure a) Type
recordRow at env rho e = do
  ty <- infer (notTail env) rho e
  recordOf at ty

variantRow :: forall a. a -> Env -> Type -> Expr a -> Either (CheckFailure a) Type
variantRow at env rho e = do
  ty <- infer (notTail env) rho e
  variantOf at ty

payloadAt :: forall a. a -> RowKey -> Type -> Either (CheckFailure a) Type
payloadAt at key row = do
  normal <- normalize at row
  case Map.lookup key normal.known of
    Just (TypePayload ty) -> Right ty
    Just (EffectPayload _ _) -> Left { at, error: WrongPayload key }
    Nothing -> Left { at, error: NoElementAt key row }

derive instance Eq CheckError
derive instance Generic CheckError _

instance Show CheckError where
  show x = genericShow x
