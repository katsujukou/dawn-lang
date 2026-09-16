# Open Questions

Questions that v0.1 leaves open, with what is already known about each.

## Required for v1.0

**Close the soundness gap for multi-shot continuations.** The v0.1 JavaScript and Wasm backends do not satisfy the reference semantics; a second resumption raises a run-time error ([Semantics](08-Semantics.md)). This is a soundness gap that v0.1 accepts deliberately and that v1.0 must close.

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

**Label polymorphism and a `Symbol` kind.** D13 restricts labels to literals, so the kind grammar has nothing corresponding to `Symbol` and labels are not types.

**The principal use of `Symbol` is already served.** Reflecting type-level labels to run-time strings — PureScript's `IsSymbol` and `reflectSymbol` — is the work of a metaprogram using `normalizeRow` ([Elaboration](10-Elaboration.md)), so a JSON encoder derived from a closed record row is unaffected.

What remains missing is **label-polymorphic functions**: a library function that takes which field to operate on as an argument.

```purescript
over :: Proxy l -> (a -> b) -> { l :: a, ...r } -> { l :: b, ...r }   -- not expressible
```

Direct access is unaffected, since `rec.name` becomes `select name rec`, so only libraries are affected.

**The condition for introducing it.** Adding `Symbol` to the kinds entails re-validating row normalization: once labels are types, the `l` of `( l : τ | ρ )` may be a type variable, row keys cease to be rigid, and the decidability of `nf` collapses.

The condition is the one already imposed on effect row elements: **keep label variables out of Core's row-extension position, confining them to constraints and the elaboration layer.** This is how PureScript handles label variables through `Cons` and `RowToList` while keeping them out of `RCons`. So long as the condition holds, adding `Symbol` is compatible with D4 and D16.

**Type equality and GADTs.** D1 does not adopt FC coercions. This should be revisited when GADTs, type-level equality proofs, or something equivalent to `Coercible` for newtypes becomes necessary.

**Relaxing the value restriction.** If restricting the body of a `Λ` to a value form becomes a burden on elaboration, it may be relaxed to requiring only an empty effect row, in which case the erasability of `Λ` needs separate justification.

D17 has increased the weight of this item: under direct style the right-hand side of a surface `let` may perform effects, so the value restriction continuously underwrites the fact that let-generalization does not generalize a non-value right-hand side. Any relaxation should be evaluated against that frequency.

**The operational cost of D8.** Should explicit insertion of `openEff` make elaboration unduly complex, the fallback is a decidable effect subsumption judgement `ρ ≤ ρ'`, decidable by inclusion of normal forms, which would keep type equality syntactic. Note that retreating would lose the diagnostic precision D8 provides ([Effects](05-Effects.md)).

**Whether `split` is needed.** The inverse of `merge`, `Record (r ⊎ s) -> Tuple (Record r) (Record s)`, cannot be executed unless the labels of `r` are known. Whether it is needed should be validated in Phase D.

## Effects

**Declaring non-conformance, and per-clause multi-shot opt-in.** Under D18 the v0.1 JavaScript and Wasm backends remain non-conforming and provisionally tolerated.

One question is **how to declare and check the extent of non-conformance**. Detecting a second resumption at run time suffices for now, but a program able to state that a handler requires multi-shot could fail at build time on a backend that does not conform.

That requires a per-clause opt-in comparable to Koka's `ctl`, which adds a flag to each clause of Core's `handle`. There is no need to add it now, but it is where Core's syntax may change; the addition is backward compatible, since existing clauses read as unrestricted.

The other is **confirming the Wasm stack-switching proposal**. The tables in [Semantics](08-Semantics.md) assume that its continuations are one-shot and linear and that no cloning primitive is in the MVP. This is secondhand and should be verified against primary sources before Phase E.

**Effect-polymorphism of handlers that sequence native actions.** By D23 and the purity of `IO.bind`, a handler that sequences a native action **before the continuation** must take a closed row ([Effects](05-Effects.md)). This is not true of `IO`-returning handlers in general: one that merely resumes synchronously, or merely abandons the continuation, may remain effect-polymorphic.

In the standard library this constraint falls on terminal interpreters, producing a non-uniformity in which only the terminal stage has a different shape.

Making it uniform requires either indexing `IO` by an effect row, or giving `IO.bind` a different semantics as a runtime primitive aware of the handler context. The latter must solve the problem that deferring `k` until the `IO` executes takes the residual effect outside the handler's dynamic context.

**Masking and scoped labels for effect rows.** Effect rows are sharp (D4), so Koka's `mask<exn>` is not expressible. Named instances, below, would cover many of the uses, but temporarily hiding one occurrence of an effect may still require something separate.

**Multiple instances of one effect constructor.** By D16 an effect row's key is the constructor name, so `( Exn String, Exn Int )` and two independent `State`s are not expressible. The workaround is to declare separate effects.

Making the key the whole element type would remove the limitation but is not available: whether `( State ?a, State Int )` has one element or two would depend on solving `?a`, so the point at which sharpness can be decided would depend on the progress of inference — the very property D4 exists to eliminate.

The available extension is an **explicit instance name**, comparable to Koka's named handlers, allowing the key to be overridden as in `{| cache : State Int, counter : State Int |}`. Effect row elements would then have two forms, one with a derived key and one with an explicit key. Row theory is unchanged.

## FFI and backends

**Defining the primitive surface and its ABI.** Of D19, the Core type checker enforces only that every arrow of a `foreign` is pure (D23). The rest must be settled as conventions of the standard library and the build system.

- How to define the set of FFI a backend must implement, and how to version it, so that a new backend can state mechanically how much it must implement to work
- **Which primitives may fault, and on which inputs.** A pure primitive such as an unchecked array index can fail, and no Dawn type describes it. A fault is not an effect and no handler intercepts it ([Semantics](08-Semantics.md)); Core records only that applying a `foreign` may produce one. Enumerating the faulting primitives and their preconditions belongs here
- How to restrict the types that may appear in a `foreign` declaration. `Int`, `String`, and opaque handles are safe, but passing a `Record r` or a user-defined ADT raw fixes its representation for every backend. Whether to introduce a mechanism restricting this to types with a declared ABI, or to leave it as convention
- How to associate a `foreign` declaration with its per-backend implementations. PureScript uses the implicit convention of a `.js` file beside the module, and alternative backends place parallel files. Adding a backend should not require editing modules

These lie outside Core, but the longer they are deferred the more the standard library settles into a shape that depends on FFI. The minimum version should be fixed while writing the Phase A JavaScript backend.

**A fast path for pure cases.** `mapArray` runs the Dawn loop even when the effect row is empty, rather than falling through to `Array.prototype.map`. An elaboration macro that inspects the effect row can resolve this ([Modules](09-Modules.md)); it needs only the Phase B foundation and need not wait for Phase E.

**Runtime representations shared between the JavaScript and Wasm backends.** How far these can coincide.

## Modules and surface syntax

**Anonymous `...` at `Row Type`.** The rule is that anonymous spreads in one signature denote one variable per kind ([Rows](04-Rows.md)). This is right for effect rows, but at `Row Type` the wish for two independent open rows arises more often.

Should that frequency prove high, the option is to **limit anonymous `...` at `Row Type` to one per signature**, making two or more an error that demands names. No incorrect program is admitted either way, since an over-strong signature fails at the call site, so the decision can wait for evidence about how much is written.

Neither rule is backward compatible with the other. Code that writes names works under both, so making multiple anonymous spreads a warning is a way to defer the decision.

**Brackets for variant rows.** Records use `{ … }` and effects use `{| … |}`, so variants need brackets of their own. The element syntax `L :: τ` and the spread `...ρ` are shared; only the brackets remain to be chosen.

**Classical monads and `do` syntax.** D17 settles effect sequencing as direct style but leaves open whether monads as data structures, such as `Maybe` or a parser, should be writable with something like `<-`. **The direction is coexistence**; the syntax is not fixed.

The condition for coexistence is known: `bind` must be effect-polymorphic ([Effects](05-Effects.md)).

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

None of this reaches Core.

Should a design without the header entry be adopted later, it must be stated in the build system's specification that **dependencies are not determined by the header alone**; planning incremental builds and parallel compilation would then require scanning module bodies. That is where OCaml sits, and D22 avoids it.

**Strengthening the module system.** D22 forgoes functors and sealing by signature. Whether export lists alone suffice for abstraction in a large library needs validation in practice. Strengthening the system requires returning to the design of Core, so the decision has low reversibility and should be assessed once the shape of the standard library is visible, in Phase C or later.

## Implementation

**Compiling macro definitions during bootstrap.** How to build a processor that runs Core⁺ and `Elab`: whether to write it in the Phase A compiler as a language that does not yet have macros, or in a host language.

**Caching and loading compiled metaprograms.**

**Coherence and termination guarantees for the standard type class resolver.** These are library policy, and Core imposes nothing ([Elaboration](10-Elaboration.md)).

**A serialization format for Core**, corresponding to CoreFn's JSON. What a module's interface carries — types, attributes, effect declarations, constructor tags, bodies eligible for inlining — is directly tied to the unit of separate compilation.

**Kind inference for mutually recursive data and effect declarations.** Core assumes every kind is explicit; the procedure by which elaboration supplies them must be settled.

## The runtime ABI

D25 places execution of `IO` outside Core, which leaves a specification to be written. Until it exists, no program can be run end to end, so it is required before the vertical slice can do more than type check and compute pure values.

It must define:

- execution of `IO.pure` and `IO.bind`
- execution of native leaf actions, the `IO` values that `foreign` declarations construct
- the world state or external events these act upon, and whether execution is deterministic with respect to them
- the invocation of `main : IO Unit`, and what a program's exit value is
- what happens when a native action raises, since D23 keeps such behaviour out of the type

Two properties should be stated there rather than in Core. That an `IO` value is inert until executed is what Core guarantees to the ABI, given a conforming `G` — D23 keeps effects out of the arrows of a `foreign` type, and condition (3) of `Σ ⊨ G` keeps them out of the implementation. That the ABI executes each action exactly once per execution of the value containing it is what the ABI guarantees in return.

Whether the ABI is shared between the JavaScript and Wasm backends, or specified per backend with a common core, is open. It interacts directly with the definition of the primitive surface above, since native leaf actions are exactly the FFI a backend must implement.
