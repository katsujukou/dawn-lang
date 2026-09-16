# Semantics

Evaluation is strict and call-by-value. Because effect rows expose the points at which effects occur, Core must fix the evaluation order.

## Evaluation order

| Construct | Order |
| --- | --- |
| `e1 e2` | `e1` → `e2` → apply |
| `extend l e1 e2` | `e1` → `e2` |
| `update l e1 e2` | `e1` → `e2` |
| `merge e1 e2` | `e1` → `e2` |
| `let x = e1 in e2` | `e1` → `e2` |
| `case (e1 … en) of dt` | `e1` → … → `en` → `dt` |
| `jump j (e1 … en)` | `e1` → … → `en` → transfer |
| `perform E.op [τ̄] e` | `e` → capture the continuation |
| `handle e with h` | install the handler → `e` |

`e1 e2` evaluates the function before the argument, matching JavaScript. The Wasm backend observes the same order.

### What "apply" resolves to

After `e1` and `e2` are evaluated to values, the value form of `e1` determines what happens.

| Value form of `e1` | Behaviour |
| --- | --- |
| `λ (x : τ) . e` | β-reduction: evaluate `e[x := v2]` |
| `M.Ctor [τ̄] v̄` with `\|v̄\| < arity` | append the argument, giving `M.Ctor [τ̄] (v̄, v2)`. **The result is again a value; no computation occurs** |
| an application of `foreign f` | call the implementation, a primitive step. Since every arrow of a `foreign` type is pure (D23), the call produces no external effect; effects occur when the runtime executes the returned `IO` |

A saturated constructor application does not have a function type and so never appears in the position of `e1`.

**Consequence for backends.** A partially applied constructor may be passed around as a value, so a backend must be able to represent one. Whether it generates curried functions or a partial-application object carrying the arity and the collected arguments is the backend's choice; Mid IR retains constructor application in a form that lowers to either.

## Erasure

The following disappear during lowering to Mid IR and have no run-time step.

- `Λ (a : κ) . v` and `e [τ]`
- `T [[κ̄]]` and `M.x [[κ̄]]`, the instantiation of kind schemes
- `Λ (_ : C) . v` and `e [•]`
- `openEff [ρ] e`
- type annotations

The value restriction ensures that erasing these does not change the evaluation order.

## Recursive bindings

`letrec { x̄ = v̄ }` allocates an uninitialized location for each `x_i`, evaluates each `v_i`, and writes the result back. Guardedness (D14) makes each `v_i` a function value whose evaluation does not read any `x_j`, so an uninitialized reference cannot occur.

## Handlers and continuations

Handlers are deep. `perform E.op` captures the continuation up to the **innermost** handler for key `E` and passes `(argument, continuation)` to that handler's `op` clause. Resuming the continuation reinstalls the same handler.

Because rows are sharp, the same key cannot nest, so **the target handler is determined by the key alone**.

A design permitting duplicates, as Koka's scoped labels do, can also resolve the target statically through evidence passing. What it needs, however, is not a key but an offset — which occurrence of that key — and `mask` manipulates that offset. In Dawn the notion of an offset does not arise. This is a by-product of D4.

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
3. **Closing the gap is a requirement for v1.0**, recorded in [Open Questions](14-Open-Questions.md).

The routes to closing it appear in the table above: full CPS conversion on JavaScript, or a cloning primitive entering the Wasm stack-switching proposal. Making the reference semantics target-parameterized is a third possibility, but it would mean the same Core has different meanings on different backends, which conflicts with the backend independence of Mid IR.

### Consequence for Mid IR

Mid IR is designed in Phase A; effect lowering belongs to Phase E. Because of that order, **the representation of continuations in Mid IR must not assume one-shot**. This is a constraint to observe already in Phase A, and it is why Mid IR is specified to carry handler and continuation operations.
