# Effects

## Effect rows

An effect row has kind `Row Effect` and shares the row theory of [Rows](04-Rows.md).

```text
Console : Effect
Partial : Effect
State   : Type -> Effect
Exn     : Type -> Effect
```

`IO` is not among them: `IO` is an ordinary monad, not an effect (D20).

**Elements of an effect row carry no label.** The key is the effect constructor at the head of the element.

```text
()                          pure
( Console )                 Console alone; the key is Console
( State Int | e )           contains State Int, with an unknown remainder
( Console, State Int | e )  two known effects and an unknown tail
```

There is no need to write `( console : Console | e )`. This is not an abbreviation: an effect row has no label component to begin with.

Effect rows are sharp (D4), so no effect constructor occurs twice.

## Effects on the arrow

```text
Function : Type -> Row Effect -> Type -> Type
```

`τ1 -{ρ}-> τ2` is a function that takes a `τ1`, may perform effects within `ρ`, and returns a `τ2`.

Making effects a type constructor `Eff ρ τ` would give effectful functions the type `τ1 -> Eff ρ τ2`, distinguishing them from ordinary functions. The FFI boundary, exceptions, and asynchrony would then divide along "is it in the monad or not", and that division would appear throughout every API. On the arrow, a pure function is simply the case `ρ = ()`, and no division arises (D7).

## Declaring effects

```text
effect E (ā : κ̄) where
  op1 : forall (b̄ : κ̄'). σ1 ->* τ1
  ...
```

**An operation signature is not a function type.** To the left of `->*` are the arguments; to the right is the type the continuation resumes with. There is no functional relationship between them (D21).

`->` is unsuitable because in Dawn it asserts an empty effect row.

```text
τ1 -> τ2   ≡   Function τ1 () τ2
```

An operation is by definition the one thing that is not pure, so `log : String -> Unit` would, read by Dawn's own rules, say the opposite of what is meant. In Haskell or Eff no contradiction arises, because `->` there says nothing about effects; once the effect row sits on the arrow (D7), the notation is no longer available.

### Rules for `->*`

1. Exactly **one** `->*` appears in an operation signature. Neither zero nor two.
2. It has the **same precedence as `->` and is right-associative**.
3. It must lie on the spine. `(a ->* b) -> c` is not admitted.

All three are checked by walking the declared type.

```purescript
effect Console where
  log     :: String ->* Unit
  writeAt :: Int -> String ->* Unit              -- two arguments
  readAll :: Unit ->* String                     -- no arguments

effect Partial where
  abort :: forall b. Unit ->* b
```

`a -> b -> c ->* d -> e` takes three arguments `a`, `b`, `c` and resumes with `d -> e`. That the continuation resumes with a function is **visible in the notation**, which it is not when only `->` is available.

### `->*` marks the arrow that carries the effect

In the generated type of an operation, the arrow at the position of `->*` is the one that carries the effect row.

```purescript
writeAt :: Int -> String ->* Unit                        -- declaration
writeAt :: Int -> String -> Unit / {| Console, ... |}    -- generated type
```

Since `/` attaches to the last arrow, the two correspond directly, and **partial application is pure**.

```purescript
let writeAt0 = writeAt 0      -- pure; nothing happens
writeAt0 "foo"                -- control reaches the handler's clause
```

`->*` is not an ad hoc symbol; it names a structure that D7 and currying already imply.

### Core operations take one argument

A Core operation takes a single argument. Multi-argument operations are realized by the surface packing arguments into a record and generating a curried function.

```text
-- surface: writeAt :: Int -> String ->* Unit
-- Σ:       writeAt : { line : Int, text : String } ->* Unit
-- generated function:
writeAt = λ(line : Int). λ(text : String).
            perform Console.writeAt (extend line line (extend text text {}))
```

Core requires no change, and destructuring in handler clauses is likewise surface sugar.

## `perform` and `handle`

```text
e ::= ...
    | perform E.op [τ̄] e              invoke an operation
    | handle e with h                 apply a handler
    | openEff [ρ'] e                  effect widening, erased

h ::= { return (x : τ) -> e_r
      ; E.op1 [b̄1] (x1 : σ1, k1 : τ1 -{ρ}-> β) -> e1
      ; ...
      ; E.opn [b̄n] (xn : σn, kn : τn -{ρ}-> β) -> en }
```

- `perform E.op [τ̄] e` invokes operation `op` of effect constructor `E`. It requires the ambient effect row to contain `E` as a key, that is, to have the form `( E τ̄ | _ )`.
- `handle e with h` removes the element keyed `E` from `e`'s effect row and processes it with the clauses of `h`. Handlers are **deep** (D15): after a resumption, control is under the same handler.
- `openEff [ρ'] e` turns `e : τ1 -{ρ}-> τ2` into `τ1 -{ρ ⊎ ρ'}-> τ2`. Effect containment is an explicit term rather than subtyping (D8). At run time it is the identity and disappears during lowering.

**A handler must cover every operation of `E`.** Since `handle` removes `E` from the row, an operation without a clause would leave its `perform` with nowhere to go. This is the same requirement as local totality of a decision tree ([Terms and Matching](06-Terms-and-Matching.md)). Handling only part of an effect is done by writing pass-through clauses for the rest; a partial handler that leaves `E` in the row is not available in v0.1.

### `perform` does not require a handler to exist

What `perform E.op` requires is that **the ambient effect row contain `E`**, not that a handler be installed. The type system tracks an obligation, not the presence of a handler.

Handlers are installed as a dynamic nesting on the call stack, so whether one exists cannot be asked statically at the `perform` site. What can be asked is which effects a computation may perform, and that is the effect row.

**The absence of a handler anywhere is not in itself a type error.** An unhandled effect is an obligation recorded in a type.

```text
f : Unit -{( E )}-> Unit          -- performs E.op internally
```

This is well typed. A library exporting only such functions compiles and ships; installing a handler is the caller's responsibility. If `f` is never called, the obligation is never passed on.

A type error arises exactly where the obligation **cannot propagate further**. There are three such boundaries, all of them existing rules.

| Boundary | Rule |
| --- | --- |
| Function application: the arrow's row must equal the ambient row | [Typing Rules](07-Typing-Rules.md) |
| A top-level declaration's right-hand side, checked at ambient `()` | [Modules](09-Modules.md) |
| The entry point `main : IO Unit`, which admits no effect row | [Modules](09-Modules.md) |

Along a call chain reachable from `main`, the effect row propagates upward through types. Since `main` has type `IO Unit`, a `handle` must have removed the effect somewhere along the chain, or one of the boundaries rejects the program. This is a consequence of types propagating, not of reachability analysis.

D8 contributes here: because rows do not widen automatically, an obligation cannot slip through silently, and the diagnostic points at the function that failed to declare the effect.

## Partiality

A non-exhaustive pattern match produces a `partial` effect (D10).

`Partial` is an ordinary effect declaration in the standard library, not a builtin.

```text
effect Partial where
  abort : forall (b : Type). Unit ->* b
```

`fail τ` is not a separate constructor but **derived notation**.

```text
fail τ   ≡   perform Partial.abort [τ] unit
```

A partial function therefore carries `( Partial | e )` in its type. The effect of PureScript's `Partial` class is obtained without a class mechanism and without a dedicated language feature. A handler converting abortion into an exception or a `Maybe` is an ordinary handler.

## Surface syntax

### Set notation

The common spread rules are in [Rows](04-Rows.md); this section covers what is specific to effect rows.

**The brackets are `{|` and `|}`.** Elements are effect types, written without labels.

```purescript
log :: String -> Unit / {| Console |}
```

```text
{||}                           ⟹  ()
{| Console |}                  ⟹  ( Console )
{| ...e |}                     ⟹  e
{| Console, ...e |}            ⟹  ( Console ) ⊎ e
{| Console, State Int, ...e |} ⟹  ( Console, State Int ) ⊎ e
```

**`/` attaches to the last arrow, not to the function type as a whole.**

```purescript
log    :: String -> Unit / {| Console |}
       -- String -{ ( Console ) }-> Unit

logAt  :: Int -> String -> Unit / {| Console |}
       -- Int -{ () }-> ( String -{ ( Console ) }-> Unit )
```

`logAt 0` is pure. Partial application performs nothing, which is the correct reading in a curried language. A function type written without `/` is pure.

### Direct style

Effect sequencing is direct style, and **`perform` does not appear in surface syntax** (D17). Operations are written as ordinary function calls; effects appear in the type but not in the syntax.

```purescript
effect State s where
  get :: Unit ->* s
  put :: s ->* Unit

tick :: Unit -> Int / {| State Int, ... |}
tick _ =
  let n = get ()
  put (n + 1)
  n
```

`get ()` and `put (n + 1)` are ordinary applications; the elaborator turns them into `perform State.get [] unit` and `perform State.put [] (…)`. From the author's side, calling an effectful function looks no different from calling a pure one.

Requiring `do` and `bind` for effects would restore at the level of syntax exactly the division that D7 removed from types: whether one passes a pure function or a `do` block to `map` would become a visible distinction, and D7's benefit would be lost.

Because any subexpression may perform an effect, the evaluation order fixed in [Semantics](08-Semantics.md) is **observable from surface syntax**, not merely an internal convention of Core. Strict evaluation together with effect rows on arrows already implies this, independently of the choice of sequencing syntax.

### `handle` does appear in surface syntax

Hiding `perform` while exposing `handle` is not arbitrary. The criterion is **use site versus binder**.

| | Surface | Reason |
| --- | --- | --- |
| `perform` | hidden | A use site. It occurs everywhere in ordinary code and must blend in with ordinary calls (D7) |
| `handle` | **exposed** | A binder. It changes the body's effect row, from `( E τ̄ \| ρ )` to `ρ`, and each clause binds a continuation `k` |

Changing an effect row and binding `k` are the work of a binder, like `let`, `λ`, or `case`. Hiding a binder would make it impossible to see where a scope changes.

**Application code nevertheless contains no `handle`.** Thanks to the thunk encoding below, a reusable interpreter is an ordinary function.

```purescript
runConsoleIO (\_ -> body)      -- an ordinary application
```

`handle` appears only inside the definition of an interpreter, of which a library has few.

The details of surface syntax are left to parser design: whether to spell it `handle e with { … }`, whether to place the handler first, and whether sugar such as `with runConsoleIO do …` hides the thunk's `\_ ->`. A syntax macro may provide the spelling. What is fixed here is only that **`handle` exists as a Core construct**.

### Coexistence with classical monads

Direct style does not exclude monads as data structures, such as `Maybe` or a parser. The condition for coexistence is that `bind` be effect-polymorphic, which Core can express.

```text
bind : forall m. … => forall a b. forall (e : Row Effect).
       m a -> ( a -{e}-> m b ) -{e}-> m b
```

Because the continuation `a -{e}-> m b` carries the effect row, a monadic binding and an effectful call may be mixed in the same block. The first arrow is pure, so `bind m1` is a pure partial application, consistent with the currying rule above.

The concrete syntax — whether to use `<-`, and how to spell `do` — is **not decided**. Just as `class` and `instance` need not be primitive keywords, `do` should be a syntax macro supplied by the standard library. The compiler need not know about `do`.

## The end of interpretation

### `IO` is not an effect

Every other effect has a finite declared signature; `IO` admits none.

```text
effect Console where log : String ->* Unit
effect State s  where get : Unit ->* s ; put : s ->* Unit
effect Partial  where abort : forall b. Unit ->* b
effect IO       where ???
```

What `IO` would mean is "anything", which is not an algebraic effect but an escape hatch in the shape of one.

As a symptom, logical containment appears between effects: the operations of `Console` are a subset of what `IO` can do, so `Console ⊂ IO`. Because row keys are constructor names (D16), `( Console, IO )` is two independent keys and cannot express that relationship.

Removing `IO` from the effect world dissolves the question. Effects are mutually independent, which is what sharp rows assume.

### `IO` is an ordinary monad

```text
IO : Type -> Type
```

`IO a` is a **value** denoting a computation that returns an `a` when executed. It is an opaque primitive type, and `Prim` supplies only the minimum.

```text
foreign IO.pure : forall a. a -> IO a
foreign IO.bind : forall a b. IO a -> (a -> IO b) -> IO b
```

**`IO.bind`'s continuation is a pure arrow**, unlike the effect-polymorphic `bind` of classical monads above, for two reasons.

First, every arrow in a `foreign` type has an empty effect row (D23), so `( a -{f}-> IO b )` cannot be declared at all.

Second, the semantics would not hold. Deferring `k` until the `IO` is executed would run the residual effect `f` **after leaving the dynamic context of the handler that installed it**, while the result type `IO a` does not carry `f`. The type would fail to describe what execution requires.

### Interpreters that sequence native actions take a closed row

The consequence does not extend to every handler that returns `IO`. A closed row is required only when a **native `IO` action is sequenced before the continuation using `IO.bind`**.

With ambient row `e` and `k : τ -{e}-> IO a`:

```text
k v                     : IO a ! e      resume synchronously, return that IO
IO.pure x               : IO a ! e      abandon the continuation
IO.bind act (\_ -> k v) : ill typed     ← IO.bind's second argument must be pure
```

Only the third fails, because `\_ -> k v` has effect `e`. The requirement is therefore a **library discipline** for terminal interpreters, not a typing restriction on `IO`-returning handlers in general.

```text
Std.runConsoleIO
  : forall (a : Type). ( Unit -{ ( Console ) }-> a ) -> IO a
```

With no `⊎ e`, the clause's `k : Unit -{()}-> IO a` is a pure arrow and composes with the pure `IO.bind`.

Expressiveness is unaffected. Handlers nest, and only the one stage that sequences native actions needs a closed row; in the standard library that stage is the outermost interpreter.

```purescript
-- inner handlers stay effect-polymorphic
runState :: forall a s. (Unit -> a / {| State s, ... |}) -> Tuple a s / {| ... |}

-- only the terminal one is closed
runConsoleIO :: forall a. (Unit -> a / {| Console |}) -> IO a

main = runConsoleIO (\_ -> runState (\_ -> body))
```

A `Monad` instance is placed on `IO.bind` by the standard library. To Core, `IO` is an ordinary type constructor with no special status.

### Uninterpreted effects are not executed

> The runtime can do two things: **compute a pure value**, and **execute an `IO`**. Every effect must be interpreted into `()` or into `IO`; an effect interpreted into neither is never executed.

The type of the entry point enforces this.

```purescript
main :: IO Unit
```

A computation with unhandled effects does not have type `IO Unit` and so cannot reach `main`. The question of what becomes of an uninterpreted effect closes by **never arising**.

What closes here is that such effects are *not executed*, not that code carrying them cannot be written. A function with effects is well typed on its own and can be shipped as a library; installing a handler is the caller's responsibility.

### The type of a handler

An interpreter takes a computation carrying effects and returns an `IO`. Written naively, the effect row appears to fall to the left of an arrow.

```text
forall a. a / {| Console |} -> IO a        -- not expressible
```

Under call-by-value, however, `Unit -{ρ}-> a` **is** a computation of type `a` with effects `ρ`, so thunking suffices; the effect row sits **on** the left-hand arrow rather than to its left.

```purescript
runConsoleIO :: forall a. (Unit -> a / {| Console |}) -> IO a
```

**A `Handler` need not be a separate inhabitant from `->`.** The function type stays `Function` alone.

The target of interpretation need not be `IO`: a handler may interpret `Partial` into `Maybe`, which is the pure side. All that is required is that by the time control reaches `main`, the row is `()` or the result is `IO`.

### `IO` appears in exactly one place

Operations are **declared without implementations**. Writing `effect Console where log :: String ->* Unit` makes `log : String -> Unit / {| Console |}` available, elaborated to `perform Console.log`. There is nothing to define.

`IO` appears only inside an interpreter's clauses.

```purescript
effect Console where
  log :: String ->* Unit

foreign primLog :: String -> IO Unit

runConsoleIO :: forall a. (Unit -> a / {| Console |}) -> IO a
runConsoleIO thunk =
  handle (thunk ()) with
    { return x            -> IO.pure x
    ; Console.log (s, k)  -> IO.bind (primLog s) (\_ -> k ())
    }
```

The clause's result type is already `IO a`, so `IO.bind` composes there naturally. **No lift of the form `IO a -> a / {| Console |}` is needed.**

### Where the trust boundary lies

The type of `primLog`, `String -> IO Unit`, says only that some IO occurs. That it performs only console IO is not guaranteed by the type; an implementation that deleted files would still type check.

This is a trust boundary that **should be accepted**. That is what FFI is, and [Modules](09-Modules.md) already declares it.

What matters is its **location**: at the `foreign` declaration, and nowhere else. An interpreter such as `runConsoleIO` is ordinary safe Dawn code and is not a trust boundary. The boundaries do not multiply.

### Do not introduce a lift

The structure collapses if a lift is provided.

```purescript
liftConsoleIO :: forall a. IO a -> a / {| Console |}     -- must not exist
```

For it to typecheck, `Console` would need the operation

```text
effect Console where liftIO : forall a. IO a ->* a
```

`log : String ->* Unit` is a meaningful signature; `liftIO : IO a ->* a` says nothing. It is precisely the "effect with no operation signature" that D20 excludes, wearing the name `Console` — `IO :: Effect` again, one step removed.

The meaning of an effect is given by its operation signatures. **No operation may admit an arbitrary `IO`.** An `effect Unsafe where liftIO : forall a. IO a ->* a` is tempting for prototyping, but it is a hole through which D20's discipline drains, and should be marked unsafe if provided at all.

### Confining `IO` is a discipline

Making `IO` a monad gives functions that perform real IO the type `a -> IO b`, which is exactly the monadic division D7 avoids.

It holds together only if `IO` stays inside interpreters and `main`. That requires every real-world capability to be a named effect.

```purescript
effect Console    where log :: String ->* Unit
effect FileSystem where readFile :: Path ->* String ; writeFile :: Path -> String ->* Unit
effect Clock      where now :: Unit ->* Instant
effect Random     where nextInt :: Unit ->* Int
```

Ordinary code says "uses `Console` and `FileSystem`", not "does IO". `IO` is written only by interpreters and by `main`.

D7 is lost the moment ordinary code starts writing `-> IO a`. This is therefore a matter of **policy** rather than of types, and the shape of the standard library must support it. Conversely, so long as the discipline holds, the effect system is used as it is meant to be.
