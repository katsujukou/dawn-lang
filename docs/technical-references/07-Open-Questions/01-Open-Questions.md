# Open Questions

Questions that v0.1 leaves open, with what is already known about each.

## Required for v1.0

**Close the soundness gap for multi-shot continuations.** The v0.1 JavaScript and Wasm backends do not satisfy the reference semantics; a second resumption raises a run-time error ([Semantics](../03-Typed-Core/06-Semantics.md)). This is a soundness gap that v0.1 accepts deliberately and that v1.0 must close.

Three routes are available. Implement full CPS conversion on JavaScript. Wait for a cloning primitive to enter the Wasm stack-switching proposal. Or make the reference semantics target-parameterized, which conflicts with the backend independence of Mid IR.

Until then, multiple resumptions that are **syntactically evident** — a clause mentioning `k` more than once, or passing `k` elsewhere — should warn at compile time.

## The type system

**Type-level functions and their termination, which is to say whether to move to Fω.** Adding a lambda over `Row ε` makes `Map f ρ` expressible, but conditions preserving the confluence and termination of row normalization must be settled first (D6).

This also changes the class of the calculus. Introducing a type-level lambda makes Core System Fω (D1) and brings type-level β-reduction into type equality, so that "equality is syntactic apart from row normalization" no longer holds and both equality and row unification need redesigning.

**How much higher-rank polymorphism to infer.** Core can express `forall` at any rank. The restriction belongs to inference and is outside the scope of these documents. Note that this is independent of D3: kinds are rank-1 while types are unrestricted.

**Kind-polymorphic functions.** D3 places no kind quantifier in the type of a value.

```purescript
reflect :: forall k (a :: k). Proxy a -> String     -- not expressible
```

Kind-polymorphic **data types** such as `Proxy` are expressible; a kind-polymorphic **function** would require adding `forall (k : Kind). τ` to the type language. Since v0.1 has no type-level generic programming, the need does not yet arise.

It arises when `Map` or label polymorphism is introduced in Phase D, and should be judged together with reconsidering D2. Withdrawing D2 and unifying kinds with types, as PureScript 0.14+ does, would dissolve this question and the duplication of the rank question at once.

**Kind-polymorphic effect constructors.** An effect constructor carries no kind scheme ([Kinds](../03-Typed-Core/01-Kinds-and-Types.md)), so `effect E forall k. (a : k)` cannot be declared and a `Row Effect` element needs no instantiation.

Restoring it costs more than adding a row to that table. The element becomes `E [[κ̄]] τ̄`, and a row's normal form then carries a kind vector beside its argument vector. Row equality and unification compare payloads, so both would compare kinds as well. Entailment is unaffected: it decides by the keys of a normal form and the atomic facts of `Γ*`, and never examines a payload, however rich the payload becomes. Whether an effect parameterized over a kind other than `Type` is ever wanted is the question; no use has arisen. The addition is backward compatible, since an empty scheme writes nothing.

**The value domains of `Int` and `Number`.** [Prim and Base](../06-Modules/02-Prim-and-Base.md) fixes the type of each literal, and fixes what `String` and `Char` range over; what `Int` and `Number` range over is open.

What Core requires is only that literal identity be decidable, since `switchLit` demands distinct literals. What is unsettled is the range of `Int`, and the representation of `Number` together with how NaN and signed zero behave under that identity.

These belong in Core rather than in the runtime ABI, because two backends disagreeing on them would give one Core term two meanings — which is exactly what the backend independence of Mid IR exists to prevent. Until they are settled, an implementation's incidental choices are not the specification.

`String` is settled as a sequence of Unicode scalar values and `Char` as one of them, which leaves each backend free in its representation and fixes what a `Base.String` operation returns. What remains belongs to the ABI specification rather than to Core: which entries `Base.String` holds, and where the operations counting UTF-16 code units or UTF-8 bytes live.

**Label polymorphism and a `Symbol` kind.** D13 restricts labels to literals, so the kind grammar has nothing corresponding to `Symbol` and labels are not types.

**The principal use of `Symbol` is already served.** Reflecting type-level labels to run-time strings — PureScript's `IsSymbol` and `reflectSymbol` — is the work of a metaprogram using `normalizeRow` ([Elaboration](../02-Surface-Language/01-Elaboration.md)), so a JSON encoder derived from a closed record row is unaffected.

What remains missing is **label-polymorphic functions**: a library function that takes which field to operate on as an argument.

```purescript
over :: Proxy l -> (a -> b) -> { l :: a, ...r } -> { l :: b, ...r }   -- not expressible
```

Direct access is unaffected, since `rec.name` becomes `select name rec`, so only libraries are affected.

**The condition for introducing it.** Adding `Symbol` to the kinds entails re-validating row normalization: once symbols are types, the `s` of a `SymbolKey s` may be a type variable, row keys cease to be rigid, and the decidability of `nf` collapses.

The condition is the one already imposed on effect row elements: **keep label variables out of Core's row-extension position, confining them to constraints and the elaboration layer.** This is how PureScript handles label variables through `Cons` and `RowToList` while keeping them out of `RCons`. So long as the condition holds, adding `Symbol` is compatible with D4 and D16.

**Type equality and GADTs.** D1 does not adopt FC coercions. This should be revisited when GADTs, type-level equality proofs, or something equivalent to `Coercible` for newtypes becomes necessary.

**Relaxing the value restriction.** If restricting the body of a `Λ` to a value form becomes a burden on elaboration, it may be relaxed to requiring only an empty effect row, in which case the erasability of `Λ` needs separate justification.

D17 has increased the weight of this item: under direct style the right-hand side of a surface `let` may perform effects, so the value restriction continuously underwrites the fact that let-generalization does not generalize a non-value right-hand side. Any relaxation should be evaluated against that frequency.

**The operational cost of D8.** Should explicit insertion of `openEff` make elaboration unduly complex, the fallback is a decidable effect subsumption judgement `ρ ≤ ρ'`, decidable by inclusion of normal forms, which would keep type equality syntactic. Note that retreating would lose the diagnostic precision D8 provides ([Effects](../03-Typed-Core/03-Effects.md)).

**Whether `split` is needed.** The inverse of `merge`, `Record (r ⊎ s) -> Tuple (Record r) (Record s)`, cannot be executed unless the labels of `r` are known. Whether it is needed should be validated in Phase D.

## Effects

**Declaring non-conformance.** Under D18 the v0.1 JavaScript and Wasm backends remain non-conforming and provisionally tolerated.

D28 settles part of this. A clause is `full` or `fast`, and a `fast` clause constructs no continuation, so implementing one demands no multi-shot continuation and the construct that can demand one is `full` alone ([Semantics](../03-Typed-Core/06-Semantics.md)). A program containing `fast` clauses is not thereby one-shot: duplication arises wherever a `full` handler on the residual row applies its continuation more than once.

What remains is **how to declare and check the extent of non-conformance among `full` clauses**. Detecting a second resumption at run time suffices for now, but a program able to state that a handler requires multi-shot could fail at build time on a backend that does not conform. Answering it means a third level beside `full` and `fast`, separating a `full` clause that resumes at most once from one that genuinely branches the computation. Whatever shape it takes stays backward compatible, a `full` clause reading as unrestricted.

The other is **confirming the Wasm stack-switching proposal**. The tables in [Semantics](../03-Typed-Core/06-Semantics.md) assume that its continuations are one-shot and linear and that no cloning primitive is in the MVP. This is secondhand and should be verified against primary sources before Phase E.

**Effect-polymorphism of handlers that sequence native actions.** By D23 and the purity of `Base.IO.bind`, a handler that sequences a native action **before the continuation** must take a closed row ([Effects](../03-Typed-Core/03-Effects.md)). This is not true of `IO`-returning handlers in general: one that merely resumes synchronously, or merely abandons the continuation, may remain effect-polymorphic.

In the standard library this constraint falls on terminal interpreters, producing a non-uniformity in which only the terminal stage has a different shape.

Making it uniform requires either indexing `IO` by an effect row, or giving `Base.IO.bind` a different semantics as a runtime primitive aware of the handler context. The latter must solve the problem that deferring `k` until the `IO` executes takes the residual effect outside the handler's dynamic context.

**Independent implicit handlers, and whether an order can be forced.** An implicit handler is inserted only where the plan is totally ordered by its dependencies (D29), so two capabilities lowering independently into one target — `Console` and `File` both into `LiftIO` — are an ambiguity, and such a site writes the composition itself ([Effect Handlers](../02-Surface-Language/02-Effect-Handlers.md)).

Two routes would lift it, and neither is available yet. One is a **proof that handlers meeting the conditions commute**, which needs an account of what a `fast` clause's performances do under a residual handler that resumes other than once (D28); the conditions as they stand do not supply one. The other is a **declared order**, which must come from the declarations rather than from the spelling of identifiers or the order of imports, or the meaning of a program would turn on either. Evidence about how often the case arises should come before the choice.

**How a helper could be written against a handler's cells.** A handler's cells are reached from its operation clauses, and a local function in a clause body reaches them where its type is inferred. A helper that must be written down does not: its row would have to mention `region r ι`, and no source syntax writes a `RegionKey` (D16, [Effect Handlers](../02-Surface-Language/02-Effect-Handlers.md)).

**What is missing is a spelling, not strength.** A written region element would discharge nothing on its own: `handle` reads an effect application out of the element it names, and a region carries none, so a `handle` naming a region is rejected whatever the surface admits ([Typing Rules](../03-Typed-Core/05-Typing-Rules.md)). Nor is rank-2 quantification called for. Such a helper is rank-1 — `forall (e : Row Effect). RegionKey ∉ e => forall (r : Type). Unit -{( region r ι | e )}-> τ` — and a clause calling it instantiates `r` from the ambient row, which is the row its own handler's region stands in. The `Lacks` is what `( region r ι | e )` needs to be sharp, and carrying it changes nothing about the rank. Rank-2 is what a `runST`-shaped function needs, one taking a region-polymorphic computation as its argument, and a helper of this kind is not one.

The question comes down to a surface spelling for the region element, which is the one thing D16 withholds. What a spelling would buy is factoring a clause body into named helpers, which is convenience rather than expressiveness, and evidence that clause bodies grow large enough to want it should come before the choice.

**Whether an implicit handler may take parameters.** The mechanism exists — a value parameter could be a synthesis goal, resolved by the hook type classes use — so this is a question of whether it is wanted rather than of whether it can be built, and it waits on Phase C in any case ([Effect Handlers](../02-Surface-Language/02-Effect-Handlers.md)). The argument against is that a parameter worth writing is one the caller means to choose.

**Masking and scoped labels for effect rows.** Effect rows are sharp (D4), so Koka's `mask<exn>` is not expressible. Named instances, below, cover many of the uses, but temporarily hiding one occurrence of an effect may still require something separate.

Forwarding belongs to the same gap, and what it cannot cross is a **key**, not an effect. A clause cannot pass its operation on to an outer handler of the same key, since `handle` removes that element from the row and the clause body is typed without it ([Effects](../03-Typed-Core/03-Effects.md)). Two instances of one effect are unaffected: a handler keyed `cache` may perform on `counter` freely, those being different keys. What is needed is a semantics that distinguishes the current handler for `k` from an outer handler of `k`, and a second occurrence of the key in the row is only one way to obtain it. Three candidates are available.

- **Masking, or scoped duplicates.** The distinction is carried by the row, as in Koka
- **An explicit `forward`.** The distinction is carried by a term that skips the current handler
- **A partial handler that keeps the element.** Its rule takes `( ent | ρ )` to `( ent | ρ )`, so the keyed element remains in the row and the operations the clauses do not name travel outwards. A single key suffices

**Multiple instances of one effect constructor — settled.** An effect element may carry a written `SymbolKey`, so `( cache : State Int, counter : State Int )` is well-kinded and two instances of one effect are distinguished by their keys (D16, [Effects](../03-Typed-Core/03-Effects.md)).

Making the key the whole element type would have removed the limitation too, and remains unavailable: whether `( State ?a, State Int )` has one element or two would depend on solving `?a`, so the point at which sharpness can be decided would depend on the progress of inference — the very property D4 exists to eliminate. A written key is rigid, and decides nothing later than it decides now.

What the surface writes for such an instance, and how ordinary code names one, is not settled ([Effects](../03-Typed-Core/03-Effects.md)).

## FFI and backends

**Writing the `Base` ABI specification.** The shape is settled: `Base.*` is the versioned runtime contract, its ABI entries are graded by profile while its protocols are not, and `Σ` records neither the grading nor what a backend implements ([Prim and Base](../06-Modules/02-Prim-and-Base.md)). What remains is the content.

- **Which entries each `Base` module holds**, and the observable meaning of each, stated in terms that name no backend
- **Which manifest intrinsic type constructors the ABI manifest supplies, portable and target alike.** `Base.Array.Array` and the uncurried families are intrinsic without being part of Core, so no declaration in any module can produce them. Each needs its opaque representation and its `foreign` operations fixed together
- **Which profiles exist beyond `core-runtime` and `standard`**, and what a backend states to claim one
- **Which entries may fault, and on which inputs.** A pure entry such as an unchecked array index can fail, and no Stella type describes it. A fault is not an effect and no handler intercepts it ([Semantics](../03-Typed-Core/06-Semantics.md)); Core records only that applying a `foreign` may produce one. Enumerating them and their preconditions belongs here.

  **Arithmetic is the case that shows this is not a matter of listing the obvious ones.** Whether `Base.Int.add` may fault is a question about the entry and not about a host: a backend on a host that traps on overflow can wrap instead, and one on a host that wraps can check instead, so either answer is implementable everywhere. What the ABI settles is which of them every backend owes — the same observable meaning on all of them, as with `String` (D27) — and until it does, a consumer treats every operation as one that may fault. Nothing in the compiler or in a lowering may decide it, and neither may a target's convenience
- How to restrict the types that may appear in a `foreign` declaration. `Int`, `String`, and opaque handles are safe, but passing a `Record r` or a user-defined ADT raw fixes its representation for every backend. Whether to introduce a mechanism restricting this to types with a declared ABI, or to leave it as convention
- How to associate a `foreign` declaration with its per-backend implementations. PureScript uses the implicit convention of a `.js` file beside the module, and alternative backends place parallel files. Adding a backend should not require editing modules

These lie outside Core, but the longer they are deferred the more the standard library settles into a shape that depends on FFI. The first version, `stella-base-0.1`, should be fixed while writing the Phase A JavaScript backend.

**A fast path for pure cases.** `mapArray` runs the Stella loop even when the effect row is empty, rather than falling through to `Array.prototype.map`. An elaboration macro that inspects the effect row can resolve this ([Modules](../06-Modules/01-Modules.md)); it needs only the Phase B foundation and need not wait for Phase E.

**Runtime representations shared between the JavaScript and Wasm backends.** How far these can coincide.

## Modules and surface syntax

**Anonymous `...` at `Row Type`.** The rule is that anonymous spreads in one signature denote one variable per kind ([Rows](../03-Typed-Core/02-Rows.md)). This is right for effect rows, but at `Row Type` the wish for two independent open rows arises more often.

Should that frequency prove high, the option is to **limit anonymous `...` at `Row Type` to one per signature**, making two or more an error that demands names. No incorrect program is admitted either way, since an over-strong signature fails at the call site, so the decision can wait for evidence about how much is written.

Neither rule is backward compatible with the other. Code that writes names works under both, so making multiple anonymous spreads a warning is a way to defer the decision.

**Brackets for variant rows.** Records use `{ … }` and effects use `{| … |}`, so variants need brackets of their own. A variant element is keyed by a `TagKey` written `#Ok`, or by a `SymbolKey` where a name is wanted, and the spread `...ρ` is shared; only the brackets remain to be chosen ([Rows](../03-Typed-Core/02-Rows.md)).

**Classical monads and `do` syntax.** D17 settles effect sequencing as direct style but leaves open whether monads as data structures, such as `Maybe` or a parser, should be writable with something like `<-`. **The direction is coexistence**; the syntax is not fixed.

The condition for coexistence is known: `bind` must be effect-polymorphic ([Effects](../03-Typed-Core/03-Effects.md)).

```text
bind : forall m. … => forall a b. forall (e : Row Effect).
       m a -> ( a -{e}-> m b ) -{e}-> m b
```

Core can express this and requires no additional constructor. Because the continuation carries the effect row, a monadic binding and an effectful call may be mixed in one block.

The reason for not deciding is that **`do` should be a library syntax macro**, following the same policy that keeps `class` and `instance` from being primitive keywords. The compiler need not know about `do`. Once the Phase B foundation exists, whether to provide it is a library's decision, and competing spellings may coexist.

There is a roadmap consequence: `do` with `bind` requires a `Monad` class and therefore **Phase C or later**, since desugaring produces a `{{ Monad m by Typeclass.resolve }}` synthesis goal. Direct style needs only Phase A and the effect part of Phase E, so it is available strictly earlier.

**Surface syntax for local open.** D22 separates declaring a dependency from introducing names into scope, but the spelling and details are open.

- Whether `lazy` is the right keyword. What is deferred is the point at which names enter scope, not the loading of a module
- Whether to provide both the expression form `M.( e )` and a block form `import M in e`
- Rules for nesting local opens and for shadowing outer bindings
- That the namespace token `A` is managed in a namespace separate from values and types
- **Whether a header may select or hide names**, as in `import Js.String (JSString)`. The three forms above bring in everything a module exports or nothing at all, and nothing between. A selective list leaves D22 intact, since the header still names the module and the dependency is on the module rather than on a name within it; what it changes is only which names enter scope unqualified

None of this reaches Core.

Should a design without the header entry be adopted later, it must be stated in the build system's specification that **dependencies are not determined by the header alone**; planning incremental builds and parallel compilation would then require scanning module bodies. That is where OCaml sits, and D22 avoids it.

**Strengthening the module system.** D22 forgoes functors and sealing by signature. Whether export lists alone suffice for abstraction in a large library needs validation in practice. Strengthening the system requires returning to the design of Core, so the decision has low reversibility and should be assessed once the shape of the standard library is visible, in Phase C or later.

## Implementation

**Compiling macro definitions during bootstrap.** How to build a processor that runs Core⁺ and `Elab`: whether to write it in the Phase A compiler as a language that does not yet have macros, or in a host language.

**Caching and loading compiled metaprograms.**

**Coherence and termination guarantees for the standard type class resolver.** These are library policy, and Core imposes nothing ([Elaboration](../02-Surface-Language/01-Elaboration.md)).

**A serialization format for Core**, corresponding to CoreFn's JSON. What a module's interface carries — types, attributes, effect declarations, constructor tags, bodies eligible for inlining — is directly tied to the unit of separate compilation.

D34 settles where the artefacts are and which of them others build on: the compiler writes a `.dmi` and a `.dmo` per module, and what a backend outside it reads is the lowered form rather than Typed Core ([Bytecode](../05-Backend/01-Bytecode.md)). Two things remain. The **content of a `.dmi`** is determined by what optimization across a module boundary requires, and is settled when the optimizer is written. Whether **Typed Core is serialized at all** is separate: nothing outside the compiler consumes it, and whether the compiler itself wants to cache it is a question about incremental builds rather than about what is published.

**Kind inference for mutually recursive data and effect declarations.** Core assumes every kind is explicit; the procedure by which elaboration supplies them must be settled.

## The runtime ABI

D25 places execution of `IO` outside Core, which leaves a specification to be written. Until it exists, no program can be run end to end, so it is required before the vertical slice can do more than type check and compute pure values.

It must define:

- execution of `Base.IO.pure` and `Base.IO.bind`
- execution of native leaf actions, the `IO` values that `foreign` declarations construct
- the world state or external events these act upon, and whether execution is deterministic with respect to them
- the invocation of `main : IO Unit`, and what a program's exit value is
- what happens when a native action raises, since D23 keeps such behaviour out of the type

Two properties should be stated there rather than in Core. That an `IO` value is inert until executed is what Core guarantees to the ABI, given a conforming `G` — D23 keeps effects out of the arrows of a `foreign` type, and condition (3) of `Σ ⊨ G` keeps them out of the implementation. That the ABI executes each action exactly once per execution of the value containing it is what the ABI guarantees in return.

Whether the ABI is shared between the JavaScript and Wasm backends, or specified per backend with a common core, is open. It interacts directly with the `Base` ABI specification above, since native leaf actions are exactly what the `core-runtime` profile obliges a backend to implement.
