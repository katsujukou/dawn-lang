# Implementation Plan

Once this specification is settled, the target of Phase A is determined.

1. **Define the Core AST** ([Kinds and Types](../03-Typed-Core/01-Kinds-and-Types.md), [Terms and Matching](../03-Typed-Core/04-Terms-and-Matching.md), [Modules](../06-Modules/01-Modules.md))
2. **Row normalization `nf`, the entailment decision `Γ ⊨ C`, and row unification** ([Rows](../03-Typed-Core/02-Rows.md), [Elaboration](../02-Surface-Language/01-Elaboration.md)) — the first target for unit tests and property tests
3. **The Core type checker** ([Core Type Checker](../03-Typed-Core/07-Core-Type-Checker.md))
4. **Hand-write the Core module of the vertical slice** ([Examples](../03-Typed-Core/08-Examples.md)) and run it through step 3 — the type checker's first end-to-end test
5. **Lowering to Mid IR**: the erasures of [Semantics](../03-Typed-Core/06-Semantics.md), and the mapping of decision trees and join points
6. **The JavaScript backend**
7. **Parser, name resolution, type inference, and elaboration**, built on top of steps 1 through 4

Steps 2 and 4 precede step 7 because the type checker can run before the parser exists. Being able to write Core by hand is also what demonstrates in practice that Core type checking is self-contained.

## Notes on step 2

Row unification is where subtle errors concentrate, and two properties deserve explicit regression tests.

**Two-sided refinement.** A constraint such as `{ a : A | ?r } ≡ { b : B | ?s }` cannot be solved by substituting into one side; it requires a fresh variable substituted into both. A one-sided substitution either produces an incorrect solution or fails an occurs check and rejects a solvable constraint.

**The rigid/flexible distinction.** A rigid row variable is not assignable but can be absorbed by a flexible tail on the other side. Case analysis that only checks whether a tail is empty gets this wrong.

## Notes on step 5

Two constraints must be respected even though the constructs they concern belong to Phase E.

**Do not assume one-shot continuations** in Mid IR's representation ([Semantics](../03-Typed-Core/06-Semantics.md)). Mid IR is designed in Phase A while effect lowering belongs to Phase E, so the assumption would be baked in before the decision is made.

**Represent partially applied constructors** ([Semantics](../03-Typed-Core/06-Semantics.md)). A constructor application with fewer arguments than its arity is a value and may be passed around. Mid IR should retain constructor application in a form that lowers either to curried functions or to a partial-application object.

## Notes on step 6

The set of FFI the backend must implement is `dawn-base-0.1`, the first version of the `Base` ABI surface ([Open Questions](../07-Open-Questions/01-Open-Questions.md)). The longer it is deferred, the more the standard library settles into a shape that depends on FFI, so it should be fixed while writing this backend.

## Testing the properties instead of proving them

[Semantics](../03-Typed-Core/06-Semantics.md) states progress, preservation, effect safety, and erasure without proof. Proving them for a calculus with rows, effect rows, and handlers is a substantial undertaking, and most of the confidence it would buy is available more cheaply: **each property can be turned into a property test.**

This requires a Core evaluator, which step 4 needs regardless. Type checking a hand-written module confirms that it is well typed; running it is what confirms that it computes.

**Preservation** is the most directly testable. Generate a well-typed Core term, reduce one step, and re-run the type checker.

```text
assume Σ ⊨ G
for each generated e with ·;· ⊢ e : τ ! ρ:
    while e is not a value and fuel remains:
        c = step(G, e)
        if c is a fault:  stop; the run ends, and nothing is asserted
        assert ·;· ⊢ c : τ ! ρ
        e = c
```

A step to a fault ends the run rather than failing the test: a fault carries no type, so there is nothing to re-check.

Both the type and the ambient row are checked for equality. A generator that produces `G` must satisfy `Σ ⊨ G`; supplying an ill-typed global definition or a non-conforming `δ_f` invalidates the property rather than testing it.

The type checker is already required for step 3, so the assertion costs nothing to write. What takes work is the generator: producing well-typed terms rather than arbitrary ones. Generating type-directed — choosing a type first, then building a term of it — is the practical approach, and it doubles as a source of test cases for the checker itself.

**Progress** falls out of the same loop: if `e` is not a value and `step` returns nothing, the property has failed.

**Erasure** is a differential test. Run a term under the typed relation and its erasure under the erased relation, and compare the sequences of observable steps; a typed step that only consumes a coercion corresponds to no erased step.

**Effect safety** deserves separate treatment, because it is the property that ordinary tests are least likely to reveal: a violation does not crash, it silently performs an effect.

The test is **not** to reject every `perform`. A term well typed at ambient row `()` may perform operations internally, so long as each is enclosed by a handler for its key; rejecting them outright would fail correct programs. What the evaluator maintains instead is a stack of installed handler keys, and it asserts that **every `perform` it executes finds a handler on that stack**. Reaching a `perform` with no matching handler is the failure.

Generating terms that call effectful functions and wrap them in handlers is what exercises the property; what is being checked is that the wrapping is genuinely exhaustive.

Extending the generator to `foreign` declarations is worthwhile once the FFI surface exists, since D23 together with condition (3) of `Σ ⊨ G` is what keeps effect safety from being violated at that boundary. D23 alone constrains only the declared type.

**Machine-checked or paper proofs are deferred.** They become worth revisiting if the work is to be published, or if one subsystem keeps producing subtle bugs that property testing does not catch.

**Conformance of the global environment** is a premise of every property above, not something they establish. A test harness supplies `G` and must therefore guarantee `Σ ⊨ G` itself: global definitions are well-typed values, and each `δ_f` returns either a value of the instantiated result type — the one the spine judgement gives — or a permitted fault, performs nothing observable to Core, and terminates.

For generated `foreign` declarations this is easy, since the harness writes `δ_f` and can make it a pure total function that never faults. For real backends it is a conformance obligation, and a backend test suite should check it directly rather than relying on the property tests above to expose a violation.

## A catalogue of regression tests

Each entry below is a case in which a plausible implementation gives the wrong answer. They are worth writing as tests before the corresponding code rather than after, since property testing reaches most of them only by chance: several require a specific combination of features to arise at all.

The heading of each group names the step of the plan that the group belongs to.

### Row normalization and unification (step 2)

| Input | Required outcome |
| --- | --- |
| `{ a : A \| ?r } ≡ { b : B \| ?s }` | Solved with a fresh `?t`: `?r := ( b : B \| ?t )` and `?s := ( a : A \| ?t )`. Substituting into one side alone either yields an unequal pair or fails an occurs check on the symmetric attempt |
| `forall (r : Row Type). Record r ≡ Record ( name : String )` | Fails. A rigid tail cannot absorb a known field |
| `?s ≡ ( a : A \| r )` with `r` rigid | Succeeds. A rigid tail **can** be absorbed by a flexible one on the other side |
| `( name : String \| r ) ≡ ( name : String \| s )`, `r` and `s` distinct rigid variables | Fails. Distinct row variables are not identified |
| `⟨∅;{r,s}⟩ ≡ ⟨∅;{s,r}⟩` | Succeeds. The tail is a set |
| `⟨∅;{?r,?s}⟩ ≡ ⟨{a↦A};∅⟩` | Stuck, not failure. Two solutions exist, so the constraint waits |
| A solved `?r := D ⊎ ?t` where `k ∉ ?r` was assumed | The Lacks constraint propagates to `?t`, and `k ∉ dom(D)` is checked. Omitting this produces Core that is not well-kinded |
| `r ⊎ r` | Ill-kinded. The disjointness side condition rejects it before normalization |

### Kinds and constraints (step 3)

| Input | Required outcome |
| --- | --- |
| `forall (e : Effect). …` | Rejected. `Effect` is not a quantifiable kind |
| `forall (f : Type -> Effect). …` | Rejected, for the same reason |
| `Proxy [[Effect]]` | Rejected. Instantiation also requires a quantifiable kind |
| `forall (f : Type -> Type). …` | **Accepted.** Higher-kinded types must survive the restriction |
| `forall (r : Row Effect). …` | Accepted |
| `Row (Type -> Type)` | Ill-formed. `Row` takes only a row element kind |
| `#Ok ∉ ( Console )` | Rejected. A tag is not a key of a `Row Effect`; a `SymbolKey` would be admitted, since it may key a labelled instance |
| `ρ1 # ρ2` with `ρ1 : Row Type` and `ρ2 : Row Effect` | Rejected. Both sides share one row element kind |
| `Proxy [[Type]] [Int]` and `Proxy [[Row Type]] [( x : Int )]` | Both accepted. Type and data constructors carry independent kind schemes |
| `forall (f : Row Type -> Type). …` | Accepted. A row may be consumed |
| `forall (f : Row Type -> Row Type). …` | Rejected. Only row syntax produces a row, which is what keeps `nf` total on well-kinded rows |
| `forall (f : Type -> k). …` | Rejected. `k` may be instantiated with a row kind |
| A `Σ` entry `MkRow : Type -> Row Type`, used as `Record (MkRow Int)` | Rejected at the occurrence. Kinding does not trust the table for this |
| `(name ∉ r) => Record ( name : String \| r )` | **Accepted.** The constraint is assumed while the body is kinded; without it the row is not sharp |
| `(name ∉ ( name : String )) => Int` | Rejected. `Γ, C` requires `C` to be satisfiable |

### Row keys (step 3)

| Input | Required outcome |
| --- | --- |
| `( SymbolKey X : Int, TagKey X : Int )` | **Accepted.** The two are different keys; sharing a spelling does not make them collide |
| `( cache : State Int, counter : State Int )` | **Accepted.** One effect, two elements, distinguished by their keys |
| `( cache : State Int, cache : State String )` | Rejected. The same key twice, whatever the payloads |
| `( State Int, State String )` | Rejected. Both derive `EffectKey State` |
| `( PositionKey (-1) : Int )` | Rejected. The grammar gives `PositionKey` a `Nat`, and the AST holds an `Int`, so the bound is a kinding side condition |
| `( EffectKey State : Int )` | Rejected. `Γ ⊢ k key Type` admits the structural keys only |
| A handler keyed `cache` enclosing `perform counter.get` | The `perform` passes through. `Ev_k` matches on the key, and `counter` is not `cache` |
| `perform cache.get` where the row has `cache ↦ State Int` | The operation's type comes from `Σ(State)`, not from `cache`. A checker that looked the key up in `Σ` would fail here and pass on the unlabelled form |
| `handle (handle e with h) with h` at one key | Rejected. The inner one would stand at `( k \| ( k \| ρ ) )`, which is not sharp |
| A pure function handling `E` within itself, called through `openEff [( E )]` under an outer handler of `E` | **Accepted.** No row carries `E` twice; the two handlers meet only in the run-time stack |

### Decision trees and handlers (step 3)

| Input | Required outcome |
| --- | --- |
| `switchCtor` with no default, not exhausting the constructors | Rejected |
| `switchLit` with no default | Rejected. A default is mandatory |
| `switchKey` over a closed variant enumerating only some keys, no default | Rejected. A value would be left with no destination |
| `switchKey` over a row with an unknown tail, no default | Rejected |
| `switchCtor` with a default whose body is ill-typed | Rejected. The default branch is typed like any other |
| `switchKey` default | The occurrence is refined to the residual `Variant r'`, not left at the original type |
| A handler omitting an operation of `E` | Rejected. `handle` removes the keyed element, so an operation without a clause has nowhere to go |
| A handler clause that does not respect an operation's own `forall b̄` | Rejected |
| An interpreter sequencing a native action before resuming a continuation, the residual row not being closed | Rejected. That continuation is `a -{ρ}-> IO r`, which the pure arrow of `Base.IO.bind` does not take. Abandoning the continuation, or resuming it first, is admitted |
| A pure global applied where the ambient row is not empty, as `Base.Int.add n 1` is under `( State Int | e )` | Rejected without `openEff`. An application requires the arrow to carry the ambient row and containment is never inserted (D8); currying makes it one `openEff` per argument consumed |
| A data constructor applied in a handler clause, the row outside the handle not being empty | Rejected for the same reason. Constructor arrows are pure by declaration, so one is widened like any other pure global. An instantiation such as `Prelude.Nothing [a]` needs no widening, applying nothing |
| `handle (perform E.op v) with h` at ambient row `()` | **Accepted.** Effect safety is not "no operation is performed" |
| A `λ` whose body jumps to a join point bound outside it | Rejected. The join point context is discarded at a lambda |
| A `letjoin` in argument position whose definition jumps to itself | Accepted. The root of a definition is in tail position wherever the `letjoin` stands |
| `switchCtor` whose first branch reaches no leaf and whose second does | Accepted, at the type the second gives. The written order of branches carries no meaning |
| `bind x = o . k` with no dispatch having established `o . k` | Accepted. A record has an element at every key of its row |
| A handler clause whose continuation is typed at the inner row | Rejected. It is `τ' -{ρ}-> β`, the row outside the handle and the result of it (D15) |
| A clause binding `forall b` where the operation declares `forall a` | Accepted. The binders are aligned, a handler respecting the polymorphism rather than the spelling |
| A clause binding a different number of them, or one at another kind | Rejected |
| `guard` whose consequent reaches no leaf and whose alternative does | Accepted, at the type the alternative gives |

### FFI and declarations (step 3)

| Input | Required outcome |
| --- | --- |
| `foreign log : String -{( Console )}-> Unit` | Rejected. An effectful result arrow would let the effect bypass a handler |
| `foreign mapImpl : ( a -{e}-> b ) -> …` | Rejected. An effectful argument arrow would leak the calling convention across the boundary |
| `foreign Js.Console.log : String -> IO Unit` | Accepted. This is the shape every real-world leaf takes |
| `foreign use : Record ( cb : Int -{( Console )}-> Int ) -> Unit` | Rejected. An arrow reaches the boundary through the payload of a row as readily as through an argument |
| A `foreign` whose only effectful arrow stands inside a constraint | Accepted. A constraint is an erased proposition and carries no value across the boundary |
| An effect with an operation `liftIO : forall a. IO a ->* a` | **Accepted.** `perform` carries the opaque `IO` to the handler without executing it. What it costs is the granularity of the capability, not soundness |
| `newtype` on a type with two constructors, or with one constructor of two fields | Rejected. The backend erases the representation on the strength of this flag |
| A `nonrec` whose right-hand side refers to a `foreign` declared later in the text | Initializes. Constructors and foreign implementations enter the environment before any value declaration is evaluated |
| A `nonrec` referring to a later `nonrec` | Rejected. Value declarations are in dependency order |
| A top-level `rec` group whose members have different kind schemes | Accepted. Every scheme is registered before any right-hand side is checked |
| A `Σ` entry `T : forall k. k` | Rejected where the signature is built. Every use site instantiating it at `Type` would pass, so an occurrence check alone lets it in |
| A `Σ` entry `T : k -> Type` with nothing binding `k`, or `T : Effect -> Type` | Rejected there too. The whole scheme is checked under the kind variables it binds, not only its result |
| One entry reaching a name through two import paths | Accepted. A name belongs to the module that declares it, so the two are one entry |
| Two different entries under one name | Rejected where the parts are merged, rather than resolved by preferring either |
| A data constructor and a value of one name | Rejected. A constructor is an ordinary global name, so the two share a namespace |

### Reduction (step 4, once an evaluator exists)

| Input | Required outcome |
| --- | --- |
| `let x = (openEff [( E )] f) 0 in perform E.op Prim.Unit` with `f : Int -> Int` | Steps to `let x = openEffC [( E )] (f 0) in …`. Discarding the coercion leaves the two parts of the `let` with no common ambient row |
| `id [Int -> Int] f 0` with `foreign id : forall a. a -> a` | `δ_id(f)` runs and returns `f`, and `0` is applied to the result. Testing the substituted type instead absorbs `0` and calls `δ_id(f, 0)` |
| `foreign clock : IO Time`, an arity-zero foreign | Steps to `δ_clock()`. The spine is saturated as soon as it is formed |
| `M.f v` for a unary foreign | Steps. The final value argument must fire the implementation |
| `Base.IO.pure [Int]` | Steps. A polymorphic foreign accumulates the type argument on its spine |
| `letjoin j (x : Int) : Int = e1 in let y = (λz.z) 1 in jump j y` | The body reduces before the jump fires |
| `letrec { f = λx. … } in e` | Unfolds only in elimination position. No term steps to itself |
| `switchKey` on a value wrapped in `weaken` | Dispatches on the key actually injected. `weaken` is a value form and is looked through |
| `bind x = o in guard (p x) …` | The substitution happens before descending, so the guard's condition has no free `x` |
| That call, once it is evaluated | The innermost handler of the key is chosen: `Ev_k` lets no `handle` of that key stand between it and the hole |
| A saturated foreign whose `δ_f` faults | Steps to `fault φ`, which propagates out of every context including `handle`. It is not caught by a handler and is not the `Partial` effect |
| A term at ambient row `()` reaching a `perform` with no enclosing handler | Does not arise. This is what effect safety asserts |

### Erasure (step 5)

| Input | Required outcome |
| --- | --- |
| A term and its erasure | The same sequence of observable steps, modulo steps that only introduce or discharge a coercion |
| A term whose reduction faults | The erased term faults identically |
| The number of run-time arguments a backend passes to `δ_f` | Determined by the arrow count of the **declared** type, not by the instantiated result type |
