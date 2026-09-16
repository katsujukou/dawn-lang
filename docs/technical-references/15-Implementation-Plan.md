# Implementation Plan

Once this specification is settled, the target of Phase A is determined.

1. **Define the Core AST** ([Kinds and Types](03-Kinds-and-Types.md), [Terms and Matching](06-Terms-and-Matching.md), [Modules](09-Modules.md))
2. **Row normalization `nf`, the entailment decision `Γ ⊨ C`, and row unification** ([Rows](04-Rows.md), [Elaboration](10-Elaboration.md)) — the first target for unit tests and property tests
3. **The Core type checker** ([Core Type Checker](11-Core-Type-Checker.md))
4. **Hand-write the Core module of the vertical slice** ([Examples](13-Examples.md)) and run it through step 3 — the type checker's first end-to-end test
5. **Lowering to Mid IR**: the erasures of [Semantics](08-Semantics.md), and the mapping of decision trees and join points
6. **The JavaScript backend**
7. **Parser, name resolution, type inference, and elaboration**, built on top of steps 1 through 4

Steps 2 and 4 precede step 7 because the type checker can run before the parser exists. Being able to write Core by hand is also what demonstrates in practice that Core type checking is self-contained.

## Notes on step 2

Row unification is where subtle errors concentrate, and two properties deserve explicit regression tests.

**Two-sided refinement.** A constraint such as `{ a : A | ?r } ≡ { b : B | ?s }` cannot be solved by substituting into one side; it requires a fresh variable substituted into both. A one-sided substitution either produces an incorrect solution or fails an occurs check and rejects a solvable constraint.

**The rigid/flexible distinction.** A rigid row variable is not assignable but can be absorbed by a flexible tail on the other side. Case analysis that only checks whether a tail is empty gets this wrong.

## Notes on step 5

Two constraints must be respected even though the constructs they concern belong to Phase E.

**Do not assume one-shot continuations** in Mid IR's representation ([Semantics](08-Semantics.md)). Mid IR is designed in Phase A while effect lowering belongs to Phase E, so the assumption would be baked in before the decision is made.

**Represent partially applied constructors** ([Semantics](08-Semantics.md)). A constructor application with fewer arguments than its arity is a value and may be passed around. Mid IR should retain constructor application in a form that lowers either to curried functions or to a partial-application object.

## Notes on step 6

The set of FFI the backend must implement is the first version of the primitive surface ([Open Questions](14-Open-Questions.md)). The longer it is deferred, the more the standard library settles into a shape that depends on FFI, so the minimum version should be fixed while writing this backend.
