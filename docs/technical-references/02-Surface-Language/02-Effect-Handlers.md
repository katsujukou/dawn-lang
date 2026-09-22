# Effect Handlers

Core fixes `handle` and the two clause forms and leaves the spelling to the surface ([Effects](../03-Typed-Core/03-Effects.md)). This document settles that spelling, and settles when the elaborator supplies a handler the author did not write.

Nothing here reaches Core. A handler declaration desugars to an ordinary function, and an inserted handler is an ordinary application; what elaboration produces is application, `openEff`, and `handle`, each of which the Core type checker validates as it validates any other term (D29).

## Handler declarations

A **handler declaration** binds a name to an interpreter.

```purescript
handler runConsole :: Console ~> ( LiftIO ) where
  fast log msg = liftIO (Js.Console.log msg)
```

It desugars to a value declaration whose right-hand side is a `handle` under a thunk.

```text
Js.Effect.Console.runConsole
  : forall (e : Row Effect). forall (a : Type).
    Console ∉ e => LiftIO ∉ e =>
    ( Unit -{ ( Console, LiftIO | e ) }-> a ) -{ ( LiftIO | e ) }-> a
  = Λ (e : Row Effect). Λ (a : Type).
      Λ (_ : Console ∉ e). Λ (_ : LiftIO ∉ e).
        λ (thunk : Unit -{ ( Console, LiftIO | e ) }-> a).
          handle ( thunk Prim.Unit ) with
            { handles Console
            ; return (x : a) -> x
            ; fast log (msg : String) ->
                perform LiftIO.liftIO [Unit]
                  ( ( openEff [( LiftIO | e )] Js.Console.log ) msg )
            }
```

`handler` is a declaration form and not a new kind of entity. The name it binds is an ordinary global, exported by an ordinary export list, applied at an ordinary call site.

### `~>` is a shorthand for one shape

`E ~> ρ` reads "handles `E`, performs `ρ`", and abbreviates the shape every capability translation takes: effect-polymorphic in a residual row, and leaving the answer type alone.

```text
handler h :: E ~> ( t1, …, tn ) where …

  ⟹  h : forall (e : Row Effect). forall (a : Type).
           E ∉ e => t1 ∉ e => … => tn ∉ e =>
           ( Unit -{ ( E, t1, …, tn | e ) }-> a ) -{ ( t1, …, tn | e ) }-> a
```

The left of `~>` is **one element**, because a `handle` names one key. The right is a **row fragment**, which may hold several elements or none; the empty target is written `()`.

```purescript
-- effect Verbosity where level :: Unit ->* Int
handler quiet :: Verbosity ~> () where
  fast level _ = 0
```

**The source element appears in the source row together with the target.** A handler declared `Console ~> ( LiftIO )` accepts a computation already performing `LiftIO` and returns one still performing it, which is the shape a hand-written adapter takes as well ([Prim and Base](../06-Modules/02-Prim-and-Base.md)).

The narrower shape, taking `( Console | e )`, is a different function and it does not compose: it cannot stand where its target is already in the row, `LiftIO ∉ e` failing there. That is not a corner. It is the position every handler after the first stands in once two of them lower into one target, and the position the insertion below puts them in, since a computation is brought to a row carrying every target before any handler is applied.

### The general form

A handler whose answer type differs from the computation's, or whose residual row must be closed, writes its signature in full instead of using `~>`.

```purescript
handler runConsoleIO :: forall a. (Unit -> a / {| Console |}) -> IO a where
  return x = Base.IO.pure x
  full log s k = Base.IO.bind (Js.Console.log s) (\_ -> k ())
```

Both properties belong to terminal interpreters, and both follow from what the clauses do rather than from a rule of this form. Sequencing a native action before the continuation requires a closed row, `Base.IO.bind` taking a pure arrow ([Effects](../03-Typed-Core/03-Effects.md)); supplying `IO a` where the computation gives `a` requires a `return` clause, and only a `full` clause can carry the answer onward.

A handler interpreting an effect into a pure type is the same case.

```purescript
handler toMaybe :: forall a. (Unit -> a / {| Partial, ... |}) -> Maybe a / {| ... |} where
  return x = Just x
  full abort _ k = Nothing
```

### Clause forms

```text
clause ::= [ 'full' | 'fast' ] op binder* '=' expr
         | 'return' binder '=' expr
```

A **`full` clause** binds the continuation after the operation's arguments; its body is the answer. A **`fast` clause** binds the arguments alone; its body has the type the operation resumes with (D28).

```purescript
full log s k = Base.IO.bind (Js.Console.log s) (\_ -> k ())
fast log msg = liftIO (Js.Console.log msg)
```

**An unmarked clause is `full`.** Core writes the marker on every clause, so the desugaring settles which form an unmarked one means, and it means the unrestricted one. Nothing in Core falls back on a default.

An operation declared with several arguments binds them one by one, the record Core packs them into being surface sugar ([Effects](../03-Typed-Core/03-Effects.md)).

```purescript
-- writeAt :: Int -> String ->* Unit
fast writeAt line text = liftIO (Js.Console.writeAt line text)
```

The `return` clause is optional. A handler without one returns the computation's own value, which is the identity `return (x : α) -> x` in Core.

### Parameters

A handler declaration may take ordinary value parameters, written before the `::`.

```purescript
handler runWithLimit (limit :: Int) :: Fuel ~> () where …
```

They become arguments of the generated function, ahead of the thunk, and require nothing of Core.

## Applying a handler

A handler is applied like any other function, to a thunk.

```purescript
runConsole (\_ -> program)
```

`handle` therefore appears only inside a handler declaration, of which a library has few, and application code contains none.

**The thunk is what defers the computation.** An argument reaches a value before the function it is applied to, and before anything the callee does (D35), so a handler taking the computation itself would receive one that had already run — outside the `handle` meant to enclose it, with its operations reaching whatever handler was installed there instead. The `λ` is what puts that evaluation inside. This is why every application the desugaring and the insertion below produce has a value in argument position: a thunk, a variable, or `Prim.Unit`, never a computation.

## Implicit handlers

The `implicit` modifier marks a handler the elaborator may supply where the author did not write one.

```purescript
implicit
handler runConsole :: Console ~> ( LiftIO ) where
  fast log msg = liftIO (Js.Console.log msg)
```

An implicit handler is subject to four conditions, each checked where it is declared.

| Condition | Reason |
| --- | --- |
| Written with `~>` | The row transformation must be readable from the declaration, since the search runs over rows |
| Every clause is `fast` | An inserted handler translates one capability into another. A `full` clause could abandon or duplicate the computation at a site the author did not write, and control flow should not appear where nothing is written |
| No `return` clause | The answer type must be unchanged; see below |
| No value parameters | The elaborator has no argument to supply |

The last two are the ones a reader is most likely to want relaxed, and they are not alike. **The parameter restriction is liftable**: a parameter could be a synthesis goal, resolved by the same hook type classes use ([Elaboration](01-Elaboration.md)), and that mechanism exists already. Whether it is wanted is a separate question, since a parameter chosen at the call site — an initial state, a fuel bound — is one the caller means to write, and an implicit handler is exactly the case where nothing is written.

**The `return` restriction is not liftable in this form.** Were an implicit handler allowed to change the answer, insertion would be driven by a mismatch of types rather than by a difference of rows, and the search would no longer be finite or directed: the elaborator would look for a composition of answer-type transformations reconciling two types, which is implicit coercion rather than capability translation. That the keys to remove are determined by the row difference is what makes the search below terminate.

## Insertion

### Where it fires

**Inference never inserts.** An expression is first given its own least effect row, so principal rows and the diagnostics D8 provides are preserved. Insertion is attempted only at a checking position, where an expected row is supplied by an annotation or by an enclosing signature.

### The judgement

```text
Ξ ; Γ ⊢ e : α ! ρ1  ⇝  e' : α ! ρ2
```

`Ξ` is the environment of implicit handlers the module's imports make visible. `Γ`, `Δ`, `Ω`, and `Ψ` are taken by the contexts of Core and of Core⁺, so the environment takes a letter of its own.

**`Ξ` is checked where it is assembled**, which is where the module's imports are resolved rather than where any one declaration is. Acyclicity is a property of the environment and not of a declaration: two modules declaring `A ~> ( B )` and `B ~> ( A )` are each coherent on their own, and the cycle exists only for a module importing both. Checking it at assembly is early enough that no use site sees it, and late enough to see it at all.

The judgement holds when a **plan** exists, and the elaborator inserts a plan only when it is unique.

### The plan

Let `nf(ρ1) = ⟨ F1 ; T1 ⟩` and `nf(ρ2) = ⟨ F2 ; T2 ⟩`.

```text
1. the handlers, by worklist
     worklist ← dom(F1) ∖ dom(F2)      processed ← ∅      plan ← ∅
     while the worklist is not empty:
       take a key k from it      processed ← processed ∪ { k }
       among the implicit handlers of Ξ whose source key is k:
         none      → failure, naming k
         several   → ambiguity, naming them and the modules they come from
         one, H    → plan ← plan ∪ { H }
                      worklist ← worklist ∪
                        ( keys(target(H)) ∖ dom(F2) ∖ processed )

2. ordering
     H is required inside H' when source(H') ∈ keys(target(H))
     ≺ is the transitive closure of that relation on plan

3. uniqueness
     the plan is unique exactly when ≺ is a total order on plan —
     equivalently, when plan has exactly one topological order
     otherwise → ambiguity, naming the handlers ≺ leaves unordered

4. the row the computation must reach
     W = the compatible union of F2 and every target(H), H ∈ plan —
       a key contributed more than once carries one payload, or failure
     F1 and W agree likewise on dom(F1) ∩ dom(W), or failure
     widen e once by the elements of W whose keys are not in dom(F1)

5. the result
     apply the handlers outward in the order ≺ gives
     the row so obtained must equal ρ2 by ordinary row equality
```

Step 4 adds only what is missing. **A computation already performing a target is left alone**, since widening it again by that element is not well-kinded, sharpness admitting no key twice; and a key that only `ρ2` carries is added, since no handler would otherwise put it there.

**`W` is a union of finite maps and is therefore partial.** `F2` and the targets may each contribute the same key — two handlers ordered one inside the other may both name `cache`, and `F2` may name it too — and a key so contributed must carry one payload throughout. Where it does not, no row is being described and the failure belongs there rather than at the final equality. The same holds between `F1` and `W`: a widening adds elements and reconciles no payload.

Step 1 is a worklist rather than a set comprehension because the target of the handler for `k` can be consulted only once that handler is known to be the one there is, which is a property of `k` and not of the set. **It terminates** because `Ξ` is finite and each target is a finite fragment, so finitely many keys can ever enter the worklist, and `processed` keeps any of them from entering twice. The set of row keys is not itself finite, and the argument does not need it to be.

Step 2 takes the transitive closure rather than the direct edges alone. A chain of three is ordered by `A ≺ B` and `B ≺ C` alone, whose union is not a total order until `A ≺ C` is added.

Requiring a total order is where the design declines to be clever. Two handlers the relation does not order are two nestings of the same term, and whether they mean the same thing is not something the elaborator can settle: a `fast` clause performs an operation of the residual row, and what becomes of the computation then belongs to whichever handler is installed for that row (D28). Rather than classify handlers by whether they resume, which no declaration records, insertion requires that the term be determined.

**The consequence is worth stating plainly.** A single key is always totally ordered, so the common case goes through. A chain does too, its transitive closure being total.

```text
{ Console, ...e }  ⟹  { Logging, ...e }  ⟹  { LiftIO, ...e }
```

Two capabilities lowering independently into one target do not.

```purescript
implicit handler lowerConsole :: Console ~> ( LiftIO ) where …
implicit handler lowerFile    :: File    ~> ( LiftIO ) where …

program :: a / {| Console, File |}

-- checked against a / {| LiftIO |}: the relation orders neither handler
-- against the other, so this is an ambiguity rather than an insertion
```

Such a site writes the composition itself, which is an ordinary nesting of two applications and says which order it means. Lifting the restriction is [an open question](../07-Open-Questions/01-Open-Questions.md).

### `IO` is not a node

Every node of the graph is an effect, so the terminal step — interpreting the last capability into `IO` — lies outside it by construction (D20). That step changes the answer type and takes a closed residual row, which the conditions above exclude twice over. A program therefore always writes its terminal interpreter, and only the translations between capabilities are supplied.

### Keys, not constructors

A row element is keyed, and `handles Console` fixes the key `EffectKey Console` (D16). Core has no key polymorphism, so a handler for one key is not a handler for another, and an implicit handler is registered in `Ξ` under **its key** rather than under its effect constructor.

**Implicit insertion therefore reaches unlabelled instances only.** A labelled instance `( logger : Console )` is keyed `SymbolKey logger`, and lowering it needs a handler declared for that key. What the surface writes to declare one is part of the spelling of labelled instances, which is not settled ([Rows](../03-Typed-Core/02-Rows.md)).

## Scheduling

The search shares the machinery of [Elaboration](01-Elaboration.md) and adds none.

**Ordinary unification is attempted first.** `ρ1 ≡ ρ2` is solved under `transact`, so that an attempt which fails leaves `Ψ`, the constraint set, and the queues as it found them. Insertion is attempted only where that attempt **definitely fails** — a leftover known key or rigid tail in case (a) or (b) of row unification — and never where it merely succeeds by instantiating a metavariable. A row solvable by unification needs no handler.

**Shared tails cancel before anything waits.** Row unification removes the tails the two sides have in common before its case analysis, and the plan is read after the same cancellation. A goal is `Stuck` only where a **flexible tail survives that cancellation**, since assigning one adds keys and can still change `dom(F1)` or `dom(F2)`. It then joins the queue every other goal joins and is resumed when one of the metavariables it awaits is assigned.

The distinction is not a fine point: the ordinary case has a flexible tail on both sides.

```text
a ! ( Console | ?e )   checked against   a ! ( LiftIO | ?e )
```

Cancelling `?e` leaves `{ Console }` against `{ LiftIO }` with no tail on either side, so the key difference is settled and the plan is read off it. Treating an unsolved metavariable as a reason to wait would stall the very shape the mechanism exists for.

**A rigid tail is never a reason to wait.** A row variable bound by a `forall` contributes no key to the normal form, and nothing in the goal being solved can assign it one; a residual row open in that sense is as determined as a closed one.

Distinguishing "no handler for this key" from "not enough information yet" is the same three-way split synthesis goals use, for the same reason.

## Diagnostics

A row problem is reported as a row problem, naming what is missing rather than what was searched.

- A key with no implicit handler names the key and the row it stands in
- A key with several names the candidates and the modules they come from
- An ambiguous order names the handlers that the dependency relation leaves unordered, and says that writing the composition settles it
- A cycle is reported against the import environment that closes it, naming the modules whose declarations form it

## What reaches Core

A handler takes a thunk and returns a computation, so handlers do not compose by application alone: **the result of one is thunked again before the next receives it.** Keeping the two apart makes the rule total. With `W'` the elements step 4 widens by, and `H1 … Hn` the plan in the order `≺` gives, innermost first:

```text
q0      = openEff [ W' ] ( λ (_ : Unit). e )      a thunk
di      = Hi ⟨ instantiation ⟩ q(i-1)             a computation
qi      = λ (_ : Unit). di                        a thunk again

e'      = q0 Prim.Unit        when n = 0
e'      = dn                  when n > 0
```

**The plan may be empty.** Where `ρ2` differs from `ρ1` only by keys no handler removes — a capability the expected row carries and the computation does not — step 4 widens and there is nothing to apply, so the thunk is forced at once. Writing `e'` as a nest of applications leaves that case with no term; writing it as `q0 Prim.Unit` gives it one.

Only `q0` is widened. Each later thunk stands at the row the handler below it produced, which already carries every target, so nothing further is owed.

```text
-- program : a ! ( Console | e ),  checked against a ! ( LiftIO | e )
Js.Effect.Console.runConsole [e] [a] [•] [•]
  ( openEff [( LiftIO )] ( λ (_ : Unit). program ) )
```

The widening takes the thunk from `Unit -{ ( Console | e ) }-> a` to the
`Unit -{ ( Console, LiftIO | e ) }-> a` the handler asks for.

The handler is an ordinary global, the thunk an ordinary lambda, the widening an ordinary `openEff`. **No subsumption enters Core**, so D8 holds of an inserted handler exactly as it holds of a written one, and the Core type checker rejects an elaborator that gets any of it wrong.
