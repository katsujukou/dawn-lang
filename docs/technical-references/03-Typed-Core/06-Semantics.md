# Semantics

Evaluation is strict and call-by-value. Because effect rows expose the points at which effects occur, Core must fix the evaluation order.

## Evaluation order

| Construct | Order |
| --- | --- |
| `e1 e2` | `e1` → `e2` → apply |
| `extend k e1 e2` | `e1` → `e2` |
| `update k e1 e2` | `e1` → `e2` |
| `merge e1 e2` | `e1` → `e2` |
| `let x = e1 in e2` | `e1` → `e2` |
| `case (e1 … en) of dt` | `e1` → … → `en` → `dt` |
| `jump j (e1 … en)` | `e1` → … → `en` → transfer |
| `perform k.op [τ̄] e` | `e` → capture the continuation |
| `handle e with h` | install the handler → `e` |

`e1 e2` evaluates the function before the argument, matching JavaScript. The Wasm backend observes the same order.

### What "apply" resolves to

After `e1` and `e2` are evaluated to values, the value form of `e1` determines what happens.

| Value form of `e1` | Behaviour |
| --- | --- |
| `λ (x : τ) . e` | β-reduction: evaluate `e[x := v2]` |
| `M.Ctor [τ̄] v̄` with `\|v̄\| < arity` | append the argument, giving `M.Ctor [τ̄] (v̄, v2)`. **The result is again a value; no computation occurs** |
| an application of `foreign f` | call the implementation, a primitive step, which yields a value or a fault. That the call produces no external effect is a conformance obligation on the implementation, not a consequence of D23 alone; effects occur when the runtime executes the returned `IO` |

A saturated constructor application does not have a function type and so never appears in the position of `e1`.

**Consequence for backends.** A partially applied constructor may be passed around as a value, so a backend must be able to represent one. Whether it generates curried functions or a partial-application object carrying the arity and the collected arguments is the backend's choice; Mid IR retains constructor application in a form that lowers to either.

## Erasure: overview

A number of forms carry no run-time content and are removed before evaluation on a backend. The erasure function and its properties appear below, once every form it removes has been introduced.

## Recursive bindings

`letrec { x̄ = v̄ }` allocates an uninitialized location for each `x_i`, evaluates each `v_i`, and writes the result back. Guardedness (D14) makes each `v_i` a function value whose evaluation does not read any `x_j`, so an uninitialized reference cannot occur.

## Handlers and continuations

Handlers are deep. `perform k.op` captures the continuation up to the **innermost** handler whose key is `k`, and passes `(argument, continuation)` to that handler's `op` clause. Resuming the continuation reinstalls the same handler.

**Handlers of one key do nest at run time**, and the innermost wins. A function that handles `E` internally is pure to its caller, so calling it through `openEff [( E )]` from under an outer handler for `E` puts two on the stack at once. `Ev_k` is what picks between them: every `handle` on the path from the chosen one to the hole has some other key.

What sharpness gives is narrower and static: **no row holds one key twice**, so a `perform` names the element it means with a key alone, and needs nothing to say which occurrence. A design permitting duplicates within the row, as Koka's scoped labels do, must name an occurrence instead — which `E` of the several the row carries — and `mask` manipulates that offset. In Dawn the notion of an offset does not arise, and that is the by-product of D4.

### How many times a continuation may be resumed

**Core imposes no limit** (D18). A continuation `k_i` is an ordinary function value, and its type `τ_i' -{ρ}-> β` says nothing about how often it is used. The reference semantics is therefore multi-shot.

- calling it zero times abandons the computation, as an interpreter of `Partial` into `Maybe` does
- calling it once is ordinary resumption
- calling it more than once branches the computation: non-determinism, backtracking, probabilistic programming

Even a one-shot restriction would be **affine** — at most once — rather than linear, since abandonment is expressed by zero calls.

Restricting this in Core would require affine types for continuations. That would noticeably enlarge the trusted core in exchange for a static guarantee about one backend's convenience, so v0.1 does not include it.

### Implementation capability, and provisional non-conformance

The cost is backend-specific.

| Lowering | Arbitrary call depth | Multi-shot | Cost on JavaScript |
| --- | --- | --- | --- |
| exceptions with a locally reified continuation | no | yes | low |
| generators with `yield*` | yes | no | moderate |
| full CPS conversion | yes | yes | high |
| Wasm stack switching | yes | no | low (native) |

Achieving both arbitrary call depth and multi-shot on JavaScript requires full CPS conversion, which costs the native stack and stack traces. Generators handle arbitrary depth via `yield*`, and a driver loop gives deep handler semantics directly, but JavaScript offers no way to clone a generator, so generators are strictly one-shot.

Each backend therefore declares what it can implement. This is **not a capability difference permitted by the language semantics**; it is provisional tolerance of non-conformance.

- **JavaScript backend**: one-shot for now, using a generator-based lowering.
- **Wasm backend**: one-shot for now, following the stack-switching proposal.
- **Native backend**: nothing prevents multi-shot.
- **JavaScript backend beyond v0.1**: may extend to multi-shot by paying for CPS conversion.

### The known soundness gap in v0.1

Stated precisely:

> **The v0.1 JavaScript and Wasm backends do not satisfy type soundness.** Since the reference semantics is multi-shot, a program that resumes a continuation more than once is well typed. On these backends such a program raises a run-time error.

v0.1 **accepts this as a known gap**, under three conditions.

1. **Failure is loud and specific.** A second resumption raises a dedicated run-time error, comparable to OCaml 5's `Continuation_already_resumed`. It must not be undefined behaviour and must not silently produce a wrong result.
2. **A static best-effort check is performed.** Detecting multiple resumption is undecidable in general, since `k` can be stored and called in a loop, but the **syntactically evident** cases are detectable: a clause that mentions `k` more than once, or passes `k` to another function, warns at compile time. Most accidents are caught there, leaving the run-time check as a backstop.
3. **Closing the gap is a requirement for v1.0**, recorded in [Open Questions](../07-Open-Questions/01-Open-Questions.md).

The routes to closing it appear in the table above: full CPS conversion on JavaScript, or a cloning primitive entering the Wasm stack-switching proposal. Making the reference semantics target-parameterized is a third possibility, but it would mean the same Core has different meanings on different backends, which conflicts with the backend independence of Mid IR.

### Consequence for Mid IR

Mid IR is designed in Phase A; effect lowering belongs to Phase E. Because of that order, **the representation of continuations in Mid IR must not assume one-shot**. This is a constraint to observe already in Phase A, and it is why Mid IR is specified to carry handler and continuation operations.

## Reduction

The table above fixes the order in which subterms are evaluated. This section gives the reduction relation itself.

Two relations are distinguished.

| Relation | On | Preserves types |
| --- | --- | --- |
| `G ⊢ e → c` | Core terms, to a configuration | yes, whenever c is a term |
| `⌊e⌋ →ᵤ …` | erased terms | not applicable; types are gone |

A configuration is either a term or a fault.

```text
c ::= e  |  fault φ
```

Preservation constrains only the case in which `c` is a term; a fault has no type to preserve.

Keeping them apart matters because the coercion forms that erasure removes — `openEff`, `weaken`, `[[κ̄]]` — **change a term's type**. Removing them is not a step of typed reduction.

### The global environment

Reduction is parameterized by a global environment, obtained by linking a module with those it depends on.

The signature `Σ` is fixed throughout and left implicit, as it is in the typing rules: `cursorΣ` and the rules below consult it whenever a declared type is wanted. `G` is what linking produces, and availability is decided there.

```text
G ::= ·
    | G, M.x : σκ = v          a top-level value definition
    | G, M.f : σκ = δ_f        a foreign, with its implementation
    | G, M.Ctor                a data constructor
```

A global name reduces by looking itself up, which is also where a kind scheme is instantiated.

```text
  (M.x : forall k̄. σ = v) ∈ G
  ──────────────────────────────
  G ⊢ M.x [[κ̄]] → v[k̄ := κ̄]
```

This preserves the type: `M.x [[κ̄]] : σ[k̄ := κ̄]`, and `v` has type `σ` under `k̄`.

A constructor spine is already a value, saturated or not, so it needs no unfolding rule of its own; the spine formation rule below turns the atomic reference into one.

### Module initialization

`G` holds values, whereas a `nonrec` declaration admits any pure expression. The two are connected by **evaluating right-hand sides at link time**.

The order mirrors the three stages of declaration checking ([Modules](../06-Modules/01-Modules.md)). Type checking collects every constructor, operation, and `foreign` into `Σ_decl` before checking any value declaration, so a `nonrec` may legitimately refer to a `foreign` or a constructor that appears later in the text. Initialization must therefore populate those first, or such a module would stall.

```text
  G_Prim = the data constructors of Prim, which is Prim.Unit alone

  G_decl = G_Prim
         ∪ the definitions of the imported modules
         ∪ every constructor declared by M
         ∪ every foreign implementation δ_f declared by M

  then, folding only the value binding groups in declaration order:

    nonrec x : σκ = e     G_i ⊢ e →* c           (at ambient row ())
                          if c = v:        G_{i+1} = G_i, M.x : σκ = v
                          if c = fault φ:  initialization fails with φ

    rec { x̄ : σ̄ = v̄ }     G_{i+1} = G_i, M.x_1 : σκ_1 = v_1, …, M.x_n : σκ_n = v_n
```

`G_Prim` mirrors `Σ_Prim` on the value side ([Prim and Base](../06-Modules/02-Prim-and-Base.md)). `Prim` is not imported, so without it a `Prim.Unit` occurring in the module would have nothing to unfold to, and condition (1) of `Σ ⊨ G` would fail. The implementations the runtime ABI is obliged to supply arrive with the imports, since the module that declares them is imported like any other.

A `rec` group installs **every entry at once, with the right-hand sides themselves**. Guardedness makes each `v_i` a value already, so nothing is evaluated, and a recursive reference inside `v_i` is `M.x_j [[κ̄]]`, an ordinary global name resolved by the lookup rule. No local recursive closure is involved, and each `v_i` keeps the kind binder `k̄_i` under which it was checked.

The fold over value declarations is well defined because they are in dependency order and cycles are confined to `rec` groups.

Evaluating eagerly rather than on first reference is the choice consistent with strict evaluation, and it is observable: **a top-level declaration whose right-hand side diverges hangs initialization even if nothing refers to it.** Lazy global lookup would leave such a declaration harmless. Dawn takes the strict reading.

### Faults

A pure primitive may fail. Indexing an array out of bounds is the standard example, and no type in Dawn describes it.

A failure of this kind is **not an effect**. It is not intercepted by `handle`, it does not appear in an effect row, and it is not the `Partial` effect, which is an ordinary handleable effect for non-exhaustive matches (D10). It is a fault, in the same category as exhausting the stack.

Reduction therefore relates a term to a configuration, `G ⊢ e → c`, where `c` is a term or a fault. The rule propagating a fault out of an evaluation context appears with the contexts below.

**Which entries may fault, and on which inputs, belongs to the `Base` ABI specification** ([Open Questions](../07-Open-Questions/01-Open-Questions.md)) rather than to Core. Core only records that a fault is a possible outcome of applying a `foreign`.

### Conformance of the global environment

A `foreign` declaration's type is trusted ([Modules](../06-Modules/01-Modules.md)), and D23 constrains only the **arrows appearing in that type**. It says nothing about whether the implementation returns what it claims, performs effects behind Core's back, or terminates. Those are obligations on the implementation, and the properties below depend on them, so they are stated rather than assumed.

```text
Σ ⊨ G   holds when

  (1) G covers every global name mentioned by the module under evaluation,
      and by the definitions in G itself

  (2) for each (M.x : forall k̄. σ = v) ∈ G,  under Σ:
        ·, k̄ ; · ; · ⊢ v : σ ! ()
      that is, a global definition is a well-typed value with no effects

  (3) for each (M.f : σκ = δ_f) ∈ G, and for every spine ς that is saturated
      for M.f with cursorΣ(M.f, ς) = ⟨ σ ; θ ⟩  (see The spine cursor below),
      writing v̄ = values(ς):
        δ_f(v̄) is defined
        δ_f(v̄) is either a value of type θ(σ) or a fault
        δ_f(v̄) performs no effect observable to Core
        δ_f(v̄) terminates
```

Condition (2) applies to the entries a `rec` group installs as well. Each `v_i` is checked under its own `k̄_i` and refers to its neighbours through `Σ`, which the declaration rules populated before any value declaration was checked.

Condition (3) is stated through the cursor because the result type of a polymorphic foreign depends on the instantiation the spine carries. Applying `forall a. a -> a` at `[Int]` obliges `δ_f` to return an `Int`, and the raw declared type does not say so.

Condition (3) is what makes a `foreign` returning `IO` inert until the runtime executes it. **That property does not follow from D23.** D23 makes the declared type honest about where effects may appear; conformance of `δ_f` is what makes the implementation match the declaration. A backend is responsible for both.

Admitting a fault in (3) is what keeps the condition consistent with progress: a saturated `foreign` always either produces a value or produces a fault, and never leaves a term stuck.

### Values

```text
v ::= c
    | λ (x : τ) . e
    | Λ (a : κ) . v
    | Λ (_ : C) . v
    | M.Ctor ς                 a constructor spine
    | M.f ς                    a foreign spine that is not saturated
    | rec_i(x̄ : σ̄. v̄)         a component of a local recursive group
    | {} | extend k v1 v2
    | inject k v
    | weaken k [τ] v          a value of a wider variant
    | openEff [ρ] v           a function value at a wider effect row
    | opaque ω [τ]            a value of an intrinsic type, produced by a foreign

ς ::= ·  |  ς, [[κ̄]]  |  ς, [τ]  |  ς, [•]  |  ς, v      an argument spine
```

### Opaque values

A `foreign` returns a value of its instantiated result type, and what shape that value has follows from the type.

| Result type | The value `δ_f` returns |
| --- | --- |
| a data type | a constructor spine |
| an intrinsic type | the canonical form of `Σ(T)`'s class ([Prim and Base](../06-Modules/02-Prim-and-Base.md)) |

The second row covers more than one case. A `foreign` whose result is `Int` returns a literal, one whose result is a function type returns a function value — `foreign make : forall a. a` instantiated at `Int -> Int` does exactly that, below — and one whose result is a `Record` returns `{}` or an `extend`. Only the `intrinsic opaque` class is left without a form of its own.

`opaque ω [τ]` is what `δ_f` returns there. `ω` is the payload the backend holds — a JavaScript thunk, a Wasm reference, a native handle — and Core knows only that it is there.

```text
  τ = T τ̄     Σ(T) = intrinsic opaque     Γ ⊢ τ : Type
  ────────────────────────────────────────────────────
  Γ;Δ ⊢ opaque ω [τ] : τ ! ρ
```

The premise names the **canonical-value class** `Σ` records of `T` ([Prim and Base](../06-Modules/02-Prim-and-Base.md)), not merely that `T` is intrinsic. Admitting any intrinsic type here would admit `opaque ω [Boolean]`, and a `guard` would then meet a value that is neither `true` nor `false`; the same argument applies to `Record` against `select` and to `Function` against application. Progress holds class by class, and this is the premise that keeps it so.

**The payload is what distinguishes one opaque value from another.** Two `IO Unit` values obtained from different foreign applications are different values, and a form carrying only `τ` could not say so.

This is a run-time form: elaboration never produces one, and **no rule takes one apart or compares two**. Core carries an opaque value from the `foreign` that produced it to the `foreign` that consumes it, and observes nothing in between — which is what keeps `IO` representation-independent.

`IO` is the case that matters for D25. Reduction halts once it has constructed a value of type `IO`, and `opaque ω [IO Unit]` is what it halts on; executing that value is the runtime ABI's obligation, not a step of this relation.

Erasure keeps the payload, which carries the run-time content, and drops the type.

```text
⌊opaque ω [τ]⌋ = opaque ω
```

A global constructor or foreign accumulates its arguments on a **single ordered spine**. Each entry is a kind, type, or constraint instantiation, or a value, and the order is whatever the declared type calls for; nothing requires the erased entries to precede the values. `values(ς)` is the subsequence of value arguments, which is what erasure keeps and what `δ_f` receives.

Without a spine, a polymorphic `foreign` could not be used at all: `Base.IO.pure : forall a. a -> IO a` requires `Base.IO.pure [Int]`, and the rule for type application applies only to a `Λ`.

A **constructor spine is always a value**, saturated or not: a saturated one is a completed structure, an unsaturated one behaves as a function. A **foreign spine is a value only while it is unsaturated**; once saturated it is a redex that invokes `δ_f`.

`weaken` and `openEff` are **value forms, not redexes**. Reducing them away would change the type — `weaken k [τ] v : Variant ( k : τ | r )` while `v : Variant r` — and D8 provides no subtyping to identify the two. They are consumed by the constructs that examine them: pattern matching looks through `weaken`, and application looks through `openEff`.

### Run-time forms

Four forms arise during reduction and are never produced by elaboration.

```text
match θ dt            descending a decision tree
openEffC [ρ] e        a computation whose effects are bounded by a wider row
rec_i(x̄ : σ̄. v̄)       the i-th component of a local recursive binding group
opaque ω [τ]          a value an implementation returned, typed above
```

The last is the only one a `δ_f` produces, and the only one that is a value rather than a step in progress; its rule is given with the values.

```text
  Γ;Δ ⊢ e : τ ! r    Γ ⊨ r # ρ
  ────────────────────────────────
  Γ;Δ ⊢ openEffC [ρ] e : τ ! (r ⊎ ρ)

  Γ' = Γ, x̄ : σ̄     each i: v_i is a FunVal (D14) and Γ'; Δ ⊢ v_i : σ_i ! ()
  ──────────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ rec_i(x̄ : σ̄. v̄) : σ_i ! ρ
```

`openEffC [ρ] e` widens the **ambient row of a computation**, where `openEff` widens the **effect row inside a function's type**. Both are needed and neither subsumes the other: `openEff` is what allows a pure function to be passed where a wider arrow type is expected, and `openEffC` is what allows the result of applying such a function to sit in a context whose ambient row is the wider one.

`rec_i` carries the type annotations of the group it came from, which is what makes its typing rule derivable and hence what makes preservation hold for `letrec`. It is a **local** form only. A top-level `rec` group installs its right-hand sides into `G` directly, and its recursive references are global names.

### The spine cursor

Reduction carries no `Γ`, so saturation must be decidable from the declaration and the spine alone. `cursorΣ` is a partial function that walks the **declared** type, consuming one spine entry at a time. It performs no well-formedness checking.

```text
cursorΣ(M.g, ς)  =  ⟨ σ ; θ ⟩       σ is the unconsumed remainder of the declared type
                                     θ is the accumulated kind and type substitution
```

```text
cursorΣ(M.g, ·)            = ⟨ σκ ; id ⟩              where ( M.g : σκ ) ∈ Σ
cursorΣ(M.g, (ς, [[κ̄]]))   = ⟨ σ ; θ[k̄ := κ̄] ⟩        where cursorΣ(M.g, ς) = ⟨ forall k̄. σ ; θ ⟩
cursorΣ(M.g, (ς, [τ]))     = ⟨ σ ; θ[a := τ] ⟩        where cursorΣ(M.g, ς) = ⟨ forall (a : κ). σ ; θ ⟩
cursorΣ(M.g, (ς, [•]))     = ⟨ σ ; θ ⟩                where cursorΣ(M.g, ς) = ⟨ C => σ ; θ ⟩
cursorΣ(M.g, (ς, w))       = ⟨ τ2 ; θ ⟩               where cursorΣ(M.g, ς) = ⟨ τ1 -{()}-> τ2 ; θ ⟩
```

It is undefined in every other case. At most one clause applies at each step, since the shape of the unconsumed declared type distinguishes them.

Nothing constrains the order of entries: a declared type may interleave quantifiers, constraints, and arrows freely, and the cursor follows it. A type such as `Int -> forall a. a -> a` is therefore usable, with `[String]` supplied after the first value argument.

The arrow consumed by the last clause is pure. A constructor's arrows are pure by declaration, and a `foreign`'s are pure by D23.

A kind instantiation `[[κ̄]]` consumes the whole vector at once and can occur at most once, since kind schemes are prenex (D3).

#### Saturation is a position in the declared type

**A spine is saturated** when `cursorΣ(M.g, ς) = ⟨ σ ; θ ⟩` and the **unconsumed declared type `σ`** is not a `forall`, a constraint arrow, or a function type.

The test is on `σ`, not on `θ(σ)`. Substitution can introduce arrows that the declaration never called for, and treating those as argument positions would absorb arguments that do not belong to the foreign.

```text
foreign id : forall a. a -> a

M.id ·                       ⟨ forall a. a -> a ; id ⟩         expects a type
M.id ([Int -> Int])          ⟨ a -> a ; [a := Int -> Int] ⟩     expects one value
M.id ([Int -> Int], f)       ⟨ a ; [a := Int -> Int] ⟩          saturated
```

The last line is saturated because the declared remainder is the variable `a`, even though `θ(a) = Int -> Int` is a function type. So `δ_id(f)` runs and returns `f`, and the application `(M.id ([Int -> Int], f)) 0` proceeds as an ordinary application of the returned function. Testing `θ(σ)` instead would have absorbed `0` into the spine and called `δ_id(f, 0)`.

`foreign make : forall a. a` instantiated at a function type behaves the same way: `M.make ([Int -> Int])` is saturated at once, and whatever function `δ_make()` returns is applied normally.

**Arity is a static property of the declaration.** The number of value-argument positions is the number of arrows on the declared type's spine, which is what the cursor walks and what substitution never changes. Erasure therefore preserves it: after type arguments are gone, a backend still calls `δ_f` with exactly that many run-time arguments.

### Typing a spine

Typing a spine is the cursor together with the well-formedness of each entry.

```text
  cursorΣ(M.g, ς) = ⟨ σ ; θ ⟩       every entry of ς is well formed, as below
  ────────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ M.g ς : θ(σ) ! ρ
```

An entry is well formed when, writing `⟨ σ' ; θ' ⟩` for the cursor **before** it is consumed:

| Entry | Condition |
| --- | --- |
| `[[κ̄]]` | `Γ ⊢ κ̄ qkind` and `\|κ̄\| = \|k̄\|` |
| `[τ]` | `Γ ⊢ τ : θ'(κ)`, where `σ' = forall (a : κ). …` |
| `[•]` | `Γ ⊨ θ'(C)`, where `σ' = C => …` |
| `w` | `Γ;Δ ⊢ w : θ'(τ1) ! ρ`, where `σ' = τ1 -{()}-> τ2` |

Separating the two is what lets reduction proceed without a `Γ`. **Saturation and the reduction rules consult `cursorΣ` alone**; the conditions in the table are discharged once, when the term is type checked. In particular the entailment `Γ ⊨ θ'(C)` for a `[•]` entry is a type-checking obligation and is never re-examined at run time, consistently with constraints carrying no run-time content.

### Forming and reducing a spine

The atomic global reference forms the initial spine. A defined global unfolds to a value instead; a constructor and a foreign have nothing to unfold to.

```text
  ( M.Ctor ) ∈ G  with  ( M.Ctor : σκ ) ∈ Σ
  or  ( M.f : σκ = δ_f ) ∈ G
  ─────────────────────────────────────────────
  G ⊢ M.g [[κ̄]] → M.g ([[κ̄]])
```

Where the kind scheme is empty, `[[κ̄]]` is elided on both sides and the rule reads `M.g → M.g ·`.

An unsaturated spine absorbs the argument its cursor calls for; a saturated foreign invokes its implementation.

```text
α ::= [τ]  |  [•]  |  v            a spine argument after formation
```

```text
  (M.g ς) α                →  M.g (ς, α)           when ς is not saturated for M.g
                                                    and cursorΣ(M.g, (ς, α)) is defined

  M.f ς                    →  δ_f( values(ς) )     when ς is saturated for M.f
```

`[[κ̄]]` is absent from `α` because the whole kind vector is consumed at formation and a kind scheme is prenex, so no second kind instantiation can arise.

The two rules do not overlap. A saturated foreign spine reduces to `δ_f` **before** it can be applied to anything further, so a result that happens to be a function is applied by the ordinary rule for application rather than being absorbed.

The second rule is also what makes an arity-zero `foreign` work. A declaration such as `foreign clock : IO Time` forms a spine that is saturated immediately, so it steps to `δ_clock()` rather than sitting as a value that is neither reducible nor complete.

A saturated **constructor** spine is a value and does not reduce; a saturated **foreign** spine is a redex. The difference is that a constructor has an implementation nowhere but in its own structure. A constructor's declared result is `T ā`, never an arrow, so the question of absorbing further arguments does not arise for it.

Erasure discards the erased entries and keeps the values.

```text
⌊M.g ς⌋ = M.g ⌊values(ς)⌋
```

### Evaluation contexts

An evaluation context marks the single position at which reduction may occur. Its shape encodes the order tabulated above.

```text
Ev ::= []
     | Ev e  |  v Ev                        function before argument
     | Ev [τ]  |  Ev [•]
     | openEff [ρ] Ev  |  openEffC [ρ] Ev
     | extend k Ev e  |  extend k v Ev
     | update k Ev e  |  update k v Ev
     | merge Ev e  |  merge v Ev
     | select k Ev  |  restrict k Ev
     | inject k Ev  |  weaken k [τ] Ev  |  absurd [τ] Ev
     | let x : τ = Ev in e
     | case (v̄, Ev, ē) of dt
     | match θ (guard Ev dt1 dt2)
     | letjoin j (x̄ : τ̄) : τ = e1 in Ev
     | jump j (v̄, Ev, ē)
     | perform k.op [τ̄] Ev
     | handle Ev with h
```

```text
  G ⊢ e → e'                        G ⊢ e → fault φ     Ev ≠ []
  ──────────────────                ─────────────────────────────
  G ⊢ Ev[e] → Ev[e']                G ⊢ Ev[e] → fault φ
```

That `handle Ev with h` is a context expresses evaluation proceeding **under** an installed handler. That `letjoin … in Ev` is one lets the body of a join point binding be evaluated normally. A fault propagates out of every context, including `handle`, since no handler can intercept it.

Capturing a continuation requires a second notion: a context installing no handler for the key in question.

```text
Ev_k ::= an evaluation context in which every `handle _ with h'` on the path
         to the hole has a key other than k
```

A `jump` appears only in tail position, so the position it may occupy is narrower than a general context.

```text
Tl ::= []  |  letjoin j' (x̄ : τ̄) : τ = e' in Tl
```

### Ordinary reduction

```text
  (λ(x : τ). e) v                    →  e[x := v]
  (Λ(a : κ). v) [σ]                  →  v[a := σ]
  (Λ(_ : C). v) [•]                  →  v

  (openEff [ρ] v) w                  →  openEffC [ρ] (v w)
  openEffC [ρ] v                     →  v


  let x : τ = v in e                 →  e[x := v]

  select k (extend k v1 v2)          →  v1
  select k (extend k' v1 v2)         →  select k v2               when k ≠ k'
  restrict k (extend k v1 v2)        →  v2
  restrict k (extend k' v1 v2)       →  extend k' v1 (restrict k v2)   when k ≠ k'
  update k (extend k v1 v2) v3       →  extend k v3 v2
  update k (extend k' v1 v2) v3      →  extend k' v1 (update k v2 v3)  when k ≠ k'
  merge {} v                         →  v
  merge (extend k v1 v2) v3          →  extend k v1 (merge v2 v3)
```

`absurd [τ] v` has no rule: its argument has type `Variant ()`, which is uninhabited, so the redex does not arise.

**Application through `openEff`.** Discarding the coercion outright would not preserve typing. Consider a pure `f : Int -> Int` inside

```text
let x : Int = (openEff [( E )] f) 0 in perform E.op Prim.Unit
```

The whole term is typed at ambient row `( E )`, and the rule for `let` requires both its parts to share that row. Rewriting the bound expression to `f 0` would give it row `()`, which no longer matches the body, and no common ambient row exists. Widening the type of the function value is therefore replaced by widening the **ambient row of the resulting computation**, which `openEffC` records. Once that computation reaches a value, the coercion is discharged: a value is pure, so `openEffC [ρ] v → v` keeps both the type and the row.

**Foreign and constructor application** is given by the spine rules above. A foreign reduces once its spine is saturated, and `δ_f` yields a value or a fault.

**Recursive bindings** install recursive closures, and a closure unfolds only where it is eliminated.

```text
  letrec { x̄ : σ̄ = v̄ } in e          →  e[ x̄ := rec̄ ]    where rec_i = rec_i(x̄ : σ̄. v̄)

  rec_i(x̄ : σ̄. v̄) w                  →  (v_i[ x̄ := rec̄ ]) w
  rec_i(x̄ : σ̄. v̄) [σ]                →  (v_i[ x̄ := rec̄ ]) [σ]
  rec_i(x̄ : σ̄. v̄) [•]                →  (v_i[ x̄ := rec̄ ]) [•]
```

Unfolding is confined to elimination position, so the rules do not overlap and no term steps to itself. Guardedness (D14) makes each `v_i` a function value, which is what allows initialization to install `rec_i` without evaluating anything; it does **not** claim that a recursive computation terminates, and Core makes no such claim anywhere.

An implementation allocates locations and back-patches rather than duplicating the binding group. The two agree because no `v_i` reads an `x_j` while it is itself being installed.

### Pattern matching

Descending a decision tree takes reduction steps of its own, so that a `guard`'s condition can be evaluated in place and each of its steps remains observable from the surrounding handler.

`match θ dt` is a run-time form, not source syntax. `θ` maps occurrences to values.

```text
  case (v̄) of dt                     →  match {s_i ↦ v_i} dt

  match θ (leaf e)                   →  e
  match θ (bind x = o in dt)         →  match θ (dt[x := θ(o)])      substitute first
  match θ (guard true dt1 dt2)       →  match θ dt1
  match θ (guard false dt1 dt2)      →  match θ dt2

  match θ (switchCtor o { Ctor_i -> dt_i } [default -> dt_0])
     →  match θ dt_i        when θ(o) is an application of Ctor_i
     →  match θ dt_0        otherwise, if a default is present

  match θ (switchLit o { c_i -> dt_i } default -> dt_0)
     →  match θ dt_i        when θ(o) = c_i
     →  match θ dt_0        otherwise

  match θ (switchKey o { k_i -> dt_i } [default -> dt_0])
     →  match θ dt_i        when θ(o) injects k_i, looking through weaken
     →  match θ dt_0        otherwise, if a default is present
```

Substituting in `bind` **before** the recursive step is what allows a later `guard` to mention the bound variable; deferring the substitution would leave the condition with a free variable and no way to evaluate.

`θ(o)` follows the projection path of the occurrence, which involves no computation. `switchKey` looks through any `weaken` wrapping the value to find the key actually injected.

Local totality ([Terms and Matching](04-Terms-and-Matching.md)) guarantees that one case always applies, so `match` never gets stuck.

`guard` is the only sequential test; every `switch*` is a single dispatch, so the written order of its branches has no influence.

### Join points

```text
  letjoin j (x̄ : τ̄) : τ = e1 in Tl[jump j (v̄)]
      →  letjoin j (x̄ : τ̄) : τ = e1 in Tl[ e1[x̄ := v̄] ]

  letjoin j (x̄ : τ̄) : τ = e1 in v    →  v
```

`Tl` is a tail context, and a join point is out of scope under `λ`, `Λ`, and `handle`, so the position of the `jump` lies within the same function activation as the `letjoin`. That is what allows a backend to compile a jump as a transfer of control rather than as a continuation.

The second rule discards a binding whose join point is no longer reachable.

### Operations and handlers

```text
  handle v with h                             →  e_r[x := v]

  handle Ev_k[ perform k.op [σ̄] v ] with h    →  e_i[ b̄_i := σ̄,  x_i := v,
                                                     k_i := λ(y : τ_i'). handle Ev_k[y] with h ]
                                                 where h = { handles ent ; … }, key(ent) = k,
                                                   and its clause for op is
                                                   op [b̄_i] (x_i, k_i) -> e_i
```

Two things are visible in the second rule.

**The handler is reinstalled.** The continuation `k_i` rebuilds `handle Ev_k[y] with h`, so resuming returns under the same handler. This is what makes handlers deep (D15).

**Only the key of the handled element is consulted.** A handler writes the element whole, `handles ent`, because typing needs its payload; reduction reads `key(ent)` and nothing else, so an erased handler keeps the key alone.

**The innermost handler of the key is the target.** `Ev_k` lets no `handle` of key `k` stand between the chosen one and the hole, which is what makes it innermost; handlers of one key may nest, and this is how one is picked. No offset is needed to say which element of the row is meant, since sharpness leaves only one of that key. Two instances of one effect do not interfere either: a handler keyed `cache` is not a handler for `counter`, and a `perform counter.get` passes straight through it.

`k_i` is an ordinary function value. Nothing in the rule restricts how often it may be applied, which is the sense in which the reference semantics is multi-shot (D18).

`fail τ` reduces through this rule too, being derived notation for `perform Partial.abort [τ] Prim.Unit`.

## The runtime boundary

Core reduction halts once it has constructed a value of type `IO`. **This is by design, not an omission** (D25).

Executing an `IO` belongs to the runtime ABI, which is a separate normative specification. Core's semantics ends at the boundary, and the ABI is obliged to define:

- execution of `Base.IO.pure` and `Base.IO.bind`
- execution of native leaf actions, that is, the `IO` values that `foreign` declarations construct
- the world state or external events these act upon
- the invocation of `main : IO Unit`, the point at which a program begins

The two sides of the boundary carry different kinds of obligation, and conflating them overstates what the type system delivers.

| | Established by |
| --- | --- |
| A `foreign` type is honest about where effects may appear in its arrows | D23, checked syntactically ([Modules](../06-Modules/01-Modules.md)) |
| A `foreign` implementation constructs a value and performs nothing | `Σ ⊨ G` condition (3) above, a conformance obligation on the backend |
| An `IO` value is executed, and executed once per execution of the value containing it | the runtime ABI |

That `Js.Console.log s` defers its effect therefore rests on the second row, not the first. D23 makes the declaration incapable of *claiming* to be effect-free while sitting on an effectful arrow; it cannot make an implementation behave.

Placing execution outside Core keeps the trusted core free of world state and keeps the reduction relation a closed, deterministic system. The cost is that the ABI must be specified separately before a program can be run end to end ([Open Questions](../07-Open-Questions/01-Open-Questions.md)).

## Erasure

Erasure `⌊·⌋` removes the forms that carry no run-time content.

```text
⌊Λ (a : κ) . v⌋   = ⌊v⌋        ⌊e [τ]⌋           = ⌊e⌋
⌊Λ (_ : C) . v⌋   = ⌊v⌋        ⌊e [•]⌋           = ⌊e⌋
⌊T [[κ̄]]⌋         = ⌊T⌋        ⌊M.x [[κ̄]]⌋       = ⌊M.x⌋
⌊openEff [ρ] e⌋   = ⌊e⌋        ⌊openEffC [ρ] e⌋  = ⌊e⌋
⌊weaken k [τ] e⌋  = ⌊e⌋

⌊letjoin j (x̄ : τ̄) : τ = e1 in e2⌋  = letjoin j (x̄) = ⌊e1⌋ in ⌊e2⌋

⌊{ handles ent ; return (x : τ) -> e_r ; op_i [b̄_i] (x_i : σ_i, k_i : τ_i) -> e_i }⌋
    = { key key(ent) ; return x -> ⌊e_r⌋ ; op_i (x_i, k_i) -> ⌊e_i⌋ }

⌊handle e with h⌋ = handle ⌊e⌋ with ⌊h⌋
```

This is **not** a reduction relation. `openEff`, `openEffC`, `weaken`, and `[[κ̄]]` change a term's type or its ambient row, and `[[κ̄]]` additionally discards an instantiation that the typed rules require. A backend erases first and then evaluates; the typed relation above evaluates without erasing.

An erased handler carries the key alone: the payload of the element is what says which operations the clauses must exhaust, and that is settled before evaluation begins. The result type of a join point goes the same way, being written for the checker rather than for reduction.

A variant value loses its `weaken` wrappers, so an erased `switchKey` dispatches on the key the value carries directly. Recursive closures survive erasure, since `rec_i(x̄. v̄)` carries computational content.

## Properties

The following are stated as the properties the implementation is expected to have. They are not proved here. [Implementation Plan](../01-Introduction/04-Implementation-Plan.md) describes how each becomes a property test.

Every property assumes `Σ ⊨ G`. Without it the global environment may supply an ill-typed definition or a `δ_f` that returns the wrong thing, and no property of the reduction relation can hold.

**Preservation.** If `Σ ⊨ G` and `Γ; Δ ⊢ e : τ ! ρ` and `G ⊢ e → e2` for a **term** `e2`, then `Γ; Δ ⊢ e2 : τ ! ρ`.

A step to `fault φ` is outside the statement: a fault carries no type.

Both the type and the ambient row are preserved exactly. Widening is never discarded by a step: applying through an `openEff` moves it to `openEffC`, and `openEffC` is discharged only against a value, whose type does not mention the ambient row. Handling an operation likewise leaves the row unchanged, since the clause body is typed at the residual row that the `handle` already had.

**Progress.** If `Σ ⊨ G` and `·; · ⊢ e : τ ! ()`, then `e` is a value, or there exists `e2` with `G ⊢ e → e2`, or `G ⊢ e → fault φ` for some fault φ.

The third case is what admitting faults in condition (3) of `Σ ⊨ G` buys. A saturated `foreign` whose implementation fails would otherwise be neither a value nor a redex.

Condition (1) of `Σ ⊨ G` is what linking establishes. Without it a global name has nothing to unfold to, and the property fails for a reason unrelated to the type system.

**Effect safety.** If `Σ ⊨ G` and `·; · ⊢ e : τ ! ()`, then no reduction sequence from `e` reaches a term of the form `Ev_k[ perform k.op [σ̄] v ]` in which no handler of key `k` encloses the hole.

The claim is **not** that operations are never performed. A term may be well typed at ambient row `()` and still perform operations internally: `handle (perform E.op v) with h` is such a term, and its reduction does reach the clause for `op`. What the empty row guarantees is that no operation **escapes**: every `perform` that runs is enclosed by a handler for its key, so evaluation never gets stuck on an unhandled operation.

This is the property the whole design rests on, and it is the one that testing is least likely to reveal. A violation does not crash: it produces a program that silently performs effects it declared it would not. D7 places effect rows on arrows, D20 keeps `IO` out of the effect world, and D23 forbids effectful `foreign` arrows, all in service of this single statement. Note that D23 alone is not sufficient: a conforming `δ_f`, condition (3) of `Σ ⊨ G`, is equally required, since `handle` intercepts only `perform` while a `foreign` application calls its implementation directly.

**Erasure.** If `G ⊢ e → e2` then `⌊e⌋` reduces to `⌊e2⌋` in zero or one steps under the erased relation, the zero-step case being a step that only introduced or discharged a coercion. If `G ⊢ e → fault φ` then `⌊e⌋` reduces to the same fault `φ`; an erased evaluator and a typed one fail identically. The value restriction is what makes this hold: the body of a type or constraint abstraction is already a value, so erasing the abstraction cannot move evaluation to a different point.

**Non-conformance of the v0.1 backends.** The reduction rule for handlers places no bound on applications of `k_i`, so a term applying it twice is well typed and has a defined reduction sequence. The v0.1 JavaScript and Wasm backends do not reproduce that sequence; they raise a run-time error at the second application. This is the precise content of the soundness gap recorded above.
