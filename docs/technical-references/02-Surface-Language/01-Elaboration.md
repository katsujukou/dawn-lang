# Elaboration

## Core⁺

The representation elaborators work with is Core⁺: Core with unresolved holes added.

```text
κ⁺ ::= … | ?k                          kind metavariable
τ⁺ ::= … | ?α                          type metavariable
e⁺ ::= … | ?m                          term metavariable
         | ⟨ τ by f ⟩                  synthesis goal
         | hole τ                      typed hole, for diagnostics
```

**Invariant: a term handed to the Core type checker belongs to Core⁺ minus `{?k, ?α, ?m, ⟨…⟩, hole}`.** If any remain after zonking — after applying the accumulated substitution — the goal is unresolved and compilation fails.

```text
Ψ ::= ·
    | Ψ, ?α : κ [Γ]         unresolved; Γ is the local context the metavariable lives in
    | Ψ, ?α := τ            solved
    | Ψ, ?m : τ [Γ]
    | Ψ, ?m := e
```

Recording `[Γ]` allows the scope check that decides whether a solution mentioning local variables may be assigned to a metavariable.

## Constraints

```text
Constraint ::= κ1 ≡ κ2                 kind equality
             | τ1 ≡ τ2                 type equality
             | ρ1 ≡ ρ2                 row equality
             | k ∉ ρ                   Lacks, as in Core
             | ρ1 # ρ2                 Disjoint, as in Core
             | Synth ?m τ f            synthesis goal
```

A `HasField k τ r` predicate is not a separate constraint. It is the row equality

```text
r ≡ ( k : τ | ?r )
```

for a fresh `?r`. Likewise `t = Union r s` is `t ≡ r ⊎ s`. Keeping the number of constraint forms small is what keeps the solver small.

## Row unification

Solving `ρ1 ≡ ρ2` operates on the normal form. The procedure is **identical for record rows and effect rows**: effect row keys are rigid (D16), so `dom(F)` does not depend on how metavariables are solved and the case analysis does not depend on the order in which inference proceeds.

### Rigid and flexible

Row variables appearing in a normal form's tail are of two kinds, and the case analysis requires the distinction.

| | Origin | Assignable |
| --- | --- | --- |
| **rigid** `r` | a type variable of `Γ`, bound by `forall (r : Row ε)` | no |
| **flexible** `?r` | a metavariable of `Ψ` | yes |

A rigid row variable can equal only itself. It can, however, **be absorbed by a flexible tail on the other side**: `?s := ( a : A | r )` is correct.

### The procedure

```text
solve(ρ1 ≡ ρ2):
  ⟨F1;T1⟩ = nf(ρ1)
  ⟨F2;T2⟩ = nf(ρ2)

  1. match the payloads of shared keys
     L = dom(F1) ∩ dom(F2)
     emit F1(k) ≡ F2(k) for each k ∈ L
     D1 = F1 ∖ L,  D2 = F2 ∖ L        (thereafter dom(D1) ∩ dom(D2) = ∅)

  2. cancel shared tails
     T1' = T1 ∖ T2,  T2' = T2 ∖ T1     (thereafter T1' ∩ T2' = ∅)

  3. split into rigid and flexible
     T1' = R1 ⊎ M1,  T2' = R2 ⊎ M2

  4. case analysis on |M|, the number of flexible tails

     (a) |M1| = 0, |M2| = 0
           success if D1 = D2 = ∅ and R1 = R2 = ∅
           otherwise failure, with a row diagnostic

     (b) |M1| = 0, |M2| = 1  (M2 = {?s})
           the left side is determined, so the right side's remainder must be empty
           failure if D2 ≠ ∅ or R2 ≠ ∅
           otherwise  ?s := D1 ⊎ R1
           the case |M1| = 1, |M2| = 0 is symmetric

     (c) |M1| = 1, |M2| = 1  (M1 = {?r}, M2 = {?s}; step 2 gives ?r ≠ ?s)
           introduce a fresh ?t and **substitute on both sides**
             ?r := D2 ⊎ R2 ⊎ ?t
             ?s := D1 ⊎ R1 ⊎ ?t

     (d) |M1| ≥ 2 or |M2| ≥ 2
           Stuck: no unique solution, so wait until one of them is instantiated

  every substitution performs an occurs check and the Lacks propagation below
```

### Case (c) is the substance

`{ a : A | ?r } ≡ { b : B | ?s }` falls here.

```text
D1 = {a ↦ A},  D2 = {b ↦ B},  M1 = {?r},  M2 = {?s}

fresh ?t
?r := ( b : B | ?t )
?s := ( a : A | ?t )

check: left  = ( a : A | ?r ) = ( a : A, b : B | ?t )
       right = ( b : B | ?s ) = ( b : B, a : A | ?t )     equal under nf
```

**A substitution on one side alone cannot solve this.** Setting `?s := ( a : A | ?r )` makes the right side `( b : B, a : A | ?r )`, which does not match `( a : A | ?r )` on the left; substituting symmetrically into `?r` as well fails the occurs check and rejects a solvable constraint. Introducing a fresh `?t` and **refining both unknown tails at once** is the essence of row unification in this style.

### Failure and diagnostics

Failures in (a) and (b) are where a row problem is reported as a row problem: "`r` has no `name`", or "`r` is universally quantified and so cannot have `name`". It is not an instance resolution failure.

A leftover rigid tail fails the same way. `forall (r : Row Type). Record r ≡ Record ( name : String )` fails at "R1 ≠ ∅" in (b), because `r` is rigid.

Stuck in (d) is not failure; the scheduler resumes it.

### Preserving sharpness

Every substitution constructs a `⊎` and must satisfy its well-formedness conditions.

- For `?s := D1 ⊎ R1`, check that every `k ∉ ?s` assumed of `?s` holds of `D1` and `R1`.
- For the fresh `?t` of case (c), impose

```text
Lacks(?t) ⊇ dom(D1) ∪ dom(D2) ∪ Lacks(?r) ∪ Lacks(?s)
?t # R1,  ?t # R2
```

Neglecting this produces Core that is not well-kinded. The Core type checker re-validates the side conditions, so an omission is caught.

## Synthesis goals

```text
⟨ τ by f ⟩        f is an ordinary function of type Goal -> Elab Expr
```

The elaborator turns this into the constraint `Synth ?m τ f` and places `?m` in term position. Running `f` later assigns the result to `?m`.

**`f` is not a compiler builtin.** The type class resolver is an ordinary value in the standard library. The compiler carries only the goal's type and the synthesizer's name; it holds no algorithm specific to type classes.

## Scheduling synthesis

```text
data SynthesisResult
  = Solved   Expr
  | Stuck    (Set Meta)
  | Failed   Diagnostic
```

The scheduler is not specific to type classes. A `Stuck` goal is registered in a queue for each metavariable it awaits.

```text
blocked : Meta ⇀ Set Goal

assign(?α := τ):
  record the substitution in Ψ
  for g in blocked[?α]:
    remove g from blocked and re-run it
  re-solve the constraints that propagated
```

Termination:

- every goal is `Solved`: zonk and hand the term to the Core type checker
- no progress and `Stuck` goals remain: report insufficient information, naming the metavariables awaited
- any goal is `Failed`: report that diagnostic

Distinguishing "unsolvable" from "not enough information yet" is exactly this three-way split. `Show (Array ?a)` is `Stuck {?a}`, not `Failed`.

Case (d) of row unification joins the same queue. The row solver and the synthesis scheduler share one resumption mechanism.

## Operations available to metaprograms

`Elab` is a monad running under compile-time effects.

```text
-- observation
whnf            : Type -> Elab Type
normalizeRow    : Type -> Elab RowNormalForm
kindOf          : Type -> Elab Kind
typeOf          : Expr -> Elab Type
localContext    : Elab (Array (Ident, Type))
localConstraints: Elab (Array Constraint)
lookupGlobal    : QIdent -> Elab (Maybe Decl)
declsWithAttr   : AttrKey -> Elab (Array QIdent)

-- metavariables
freshMetaType   : Kind -> Elab Type
freshMetaTerm   : Type -> Elab Expr
isAssigned      : Meta -> Elab Boolean

-- constraints
unify           : Type -> Type -> Elab Unit
entails         : Constraint -> Elab Boolean
require         : Constraint -> Elab Unit

-- construction
quote           : Syntax                        -- quotation and antiquotation
check           : Syntax -> Type -> Elab Expr
infer           : Syntax -> Elab (Tuple Expr Type)
freshIdent      : Elab Ident

-- control
transact        : Elab a -> Elab (Either Diagnostic a)
postpone        : Set Meta -> Elab a
withFuel        : Int -> Elab a -> Elab a
throw           : Diagnostic -> Elab a
warn            : Diagnostic -> Elab Unit
```

`transact` supports trying candidates transactionally. A rollback restores `Ψ`, the constraint set, the queues, and any terms constructed.

`declsWithAttr` supports finding declarations that carry an attribute. It must work across modules, which is why attributes are persisted in a compiled interface ([Modules](../06-Modules/01-Modules.md)).

`localConstraints` exposes row constraints to elaborators, so that a derive mechanism working over rows can consult which Lacks constraints are already assumed.

Residual computation over an unknown tail takes this shape: `normalizeRow` extracts the known elements and the unknown tail, an encoder is assembled recursively over the known part, and where the tail `T` is non-empty the corresponding evidence is requested with `freshMetaTerm` and pushed out to the caller. **Closing the row is never required.**

## What an elaborator may and may not do

An elaborator may:

- construct any Core⁺ term, including ill-typed ones
- fail, diverge, or exhaust resources
- produce unhelpful diagnostics

An elaborator may not:

- bypass the Core type checker
- pass a term that has not been type checked to Mid IR
- fabricate a derivation of `Γ ⊨ C` — there is nothing to fabricate, since no proof term is carried
- change the behaviour of type checking through attributes
