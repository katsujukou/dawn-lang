# The Core Type Checker

The Core type checker is independent of the surface language, macros, elaborators, and solvers. Its inputs are a Core module and the signatures of the modules it depends on.

## What it verifies

1. That no metavariable, goal, or hole is present ([Elaboration](10-Elaboration.md))
2. Kind well-formedness ([Kinds](03-Kinds-and-Types.md))
3. Kinding of types, including the side conditions `k ∉ ρ` for row extension and `ρ1 # ρ2` for row union
4. Re-derivation of `Γ ⊨ C` ([Rows](04-Rows.md)). No proof term is accepted; the checker derives it
5. Term typing ([Typing Rules](07-Typing-Rules.md))
6. Guardedness of `letrec` ([Terms](06-Terms-and-Matching.md))
7. That the body of a `Λ` is a value form, the value restriction
8. That `jump` occurs in tail position with matching arity and types, and that join points are out of scope under `λ`, `Λ`, and `handle`
9. That occurrences agree with their types
10. That each `switch*` is locally total. `switchCtor` dispatches on a data type rather than an intrinsic one ([Prim](16-Prim.md)) — no `switchCtor` on `Int`, `IO`, or an ABI intrinsic — its branches are distinct constructors of that type, and absent a default they exhaust them; `switchLit` has a mandatory default and distinct literals of one type; `switchKey`, absent a default, has an empty unknown tail and exhausts the known keys
11. That default branches are typed, and that in `switchKey`'s default the occurrence is refined to the residual variant type
12. That a `perform k.op` finds `k ↦ E τ̄` in the ambient row, and that its argument and result match the signature `Σ(E)` gives `op`. **The key selects the element and the payload selects the protocol**: `k` is never looked up in `Σ`. That a `handle` removes the one element its key names, and that its clauses exhaust `dom(Σ(E))` for the `E` of that element's payload, each operation once
13. Well-formedness of declarations and modules ([Modules](09-Modules.md)): that the module is not named `Prim`, which is reserved, and declares no name twice in one namespace; that value declarations are in dependency order with no backward reference from a `nonrec`; that exported names are present in the signature; that constructor types land in the right type; effect declarations; that every arrow of a `foreign` is pure (D23); that a `newtype` has one constructor with one field; and that top-level right-hand sides typecheck at ambient row `()`
14. That each `[[κ̄]]` matches the arity of the kind scheme and that every `κ` in it is a quantifiable kind
15. That every site introducing a type variable — `forall`, `Λ`, declaration type parameters, operation type parameters — uses a quantifiable kind, and that `Row` is applied only to a row element kind
16. Constraint well-formedness: that both sides share one row element kind and that the key is well formed for that kind

## What it does not verify

- **Coverage of source patterns.** A tree that does not cover the original program merely carries a `Partial` effect and is well typed
- **Termination.** A `letrec` may diverge
- **The meaning of attributes**
- **Hygiene**, which is complete by the time a term reaches Core
- **The implementation of a `foreign`**, whose declared type is trusted
- **The correctness of optimizations**, which belong to Mid IR and beyond

## The trusted computing base

Only the following are trusted.

```text
the Core AST definition
the kind checker
row normalization, nf
the entailment decision, Γ ⊨ C
the type equality decision, ≡
term type checking
well-formedness of declarations
```

So long as this set stays small, the justification for the correctness of accepted programs does not change however many syntax macros, type class resolvers, derive mechanisms, and row-directed metaprograms are added.

Two decisions exist to keep it small. Not adopting FC coercions (D1) keeps type equality free of a coercion language. Not admitting `Map` (D6) keeps computation of unsettled termination out of the trusted set. Making kind instantiation explicit (D3) removes bidirectional kind checking and first-order matching from it as well.
