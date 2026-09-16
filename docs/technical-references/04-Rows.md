# Rows

Rows are a first-class structure of the type system. Structural relationships between rows are discharged by a dedicated solver, not encoded as type class search.

## A row is a keyed set

Row theory concerns **keyed, unordered, duplicate-free collections**. How a key is written is not a concern of the theory.

| Kind | Element syntax | Key | Payload |
| --- | --- | --- | --- |
| `Row Type` | `l : τ` | `l`, the field name | `τ` |
| `Row Effect` | `E τ̄` | `E`, the effect constructor | `τ̄` |

For records and variants the key cannot be recovered from the element's type: `String` alone does not say whether the field is `name` or `title`, so the key is written.

For effects the key is the constructor at the head of the element. Writing `Console` gives the key `Console`; writing `State Int` gives the key `State`. **Nothing needs to be written.** An effect row element has no label component at all (D16).

Sharing one theory does not mean sharing one notation.

## Sharpness

A well-kinded row never contains the same key twice (D4).

PureScript, following Leijen's scoped labels, admits `( a :: Int, a :: String )`. That choice makes row unification unitary, which is a real benefit. Dawn nevertheless rejects it, because Dawn has `⊎`.

With duplicates permitted, `⊎` is not commutative, and worse, the **position of known fields relative to an unknown tail** becomes significant.

```text
  ( l : Int ) ⊎ r     versus     r ⊎ ( l : Int )
```

Under scoped labels these differ once `r` turns out to contain `l`. `⊎` then has no normal form, and deciding row equality must wait for `r` to be instantiated — which defeats the goal of normalizing open rows without closing them.

With sharp rows, `⊎` is a disjoint union: commutative, associative, with unit `()`. A normal form always exists and no row variable need be closed. The price is managing Lacks constraints.

For effect rows, sharpness means that no effect constructor occurs twice. `( Exn String, Exn String )` is not well-kinded, and neither is `( Exn String, Exn Int )`, since both have the key `Exn`. Distinguishing two uses of one effect requires declaring separate effects. Koka-style languages permit duplicates in effect rows and use them for masking (`mask<exn>`); Dawn does not, and has no masking in v0.1.

## Constraints

Core has exactly two constraints.

```text
C ::= l ∉ ρ        ρ does not contain the key l
    | ρ1 # ρ2      ρ1 and ρ2 share no key
```

`l ∉ ρ` is equivalent to `( ent | () ) # ρ` for any element `ent` whose key is `l` — `( l : τ | () ) # ρ` at `Row Type`, `( E τ̄ | () ) # ρ` at `Row Effect`. It is kept as a separate form because the kinding rule for row extension uses it constantly.

### Entailment

The rules are **kind-independent**: a row element is an `ent` with key `key(ent)`, and the shape is the same at `Row Type` and `Row Effect`.

```text
  (C) ∈ Γ                    ────────────      ──────────
  ─────────                  Γ ⊨ l ∉ ()        Γ ⊨ ρ # ()
  Γ ⊨ C

  l ≠ key(ent)    Γ ⊨ l ∉ ρ               Γ ⊨ ρ1 # ρ2
  ───────────────────────────             ───────────────
  Γ ⊨ l ∉ ( ent | ρ )                     Γ ⊨ ρ2 # ρ1

  Γ ⊨ l ∉ ρ1    Γ ⊨ l ∉ ρ2                Γ ⊨ ρ1 # ρ3    Γ ⊨ ρ2 # ρ3
  ────────────────────────                ────────────────────────────
  Γ ⊨ l ∉ ρ1 ⊎ ρ2                         Γ ⊨ (ρ1 ⊎ ρ2) # ρ3

  Γ ⊨ key(ent) ∉ ρ2    Γ ⊨ ρ1 # ρ2
  ──────────────────────────────────
  Γ ⊨ ( ent | ρ1 ) # ρ2
```

`Console ∉ e` at `Row Effect` and `name ∉ r` at `Row Type` are derived by the same rules.

**Constraints carry no run-time content.** Introduction and elimination appear in terms as `Λ(_ : C). e` and `e [•]`, and both are erased. This has nothing to do with dictionary passing: the row solver and the type class resolver are separate mechanisms (D5).

The Core type checker **re-derives** `Γ ⊨ C` for each `e [•]`. No proof term is carried. The derivation is comparison of normal forms plus a scan of the context, and involves no search.

## Normal form

Every well-kinded row has a normal form.

```text
RNF ::= ⟨ F ; T ⟩

F : Label ⇀ Payload       a finite map; sharpness makes keys unique
T : { RowVar }            a finite set of row variables
```

The payload is determined by the kind: a type `τ` at `Row Type`, an argument vector `τ̄` at `Row Effect`.

`⟨ F ; T ⟩` represents the union of the known elements `F` with the row variables of the unknown tail `T`.

```text
nf( () )              = ⟨ ∅ ; ∅ ⟩
nf( a )               = ⟨ ∅ ; {a} ⟩
nf( (ent | ρ) )       = ⟨ F ∪ {key(ent) ↦ payload(ent)} ; T ⟩   where ⟨F;T⟩ = nf(ρ)
nf( ρ1 ⊎ ρ2 )         = ⟨ F1 ∪ F2 ; T1 ∪ T2 ⟩                   where ⟨Fi;Ti⟩ = nf(ρi)
```

The kinding side conditions guarantee that both unions are disjoint, so `∪` is well defined, and that `T` is a set.

`nf` terminates and its result is unique, provided `key(ent)` cannot change during normalization. For record rows the key is the written label, which is a literal (D13). For effect rows it is the head constructor, which the element well-formedness rule requires to be rigid (D16). **Keys do not depend on metavariables**, and that is the substance of both decisions.

### Equality

```text
Γ ⊢ ρ1 ≡ ρ2   ⟺   nf(ρ1) = ⟨F1;T1⟩,  nf(ρ2) = ⟨F2;T2⟩,
                   dom(F1) = dom(F2),
                   ∀l ∈ dom(F1). Γ ⊢ F1(l) ≡ F2(l),
                   T1 = T2
```

Row equality is therefore decidable and **never requires closing a row variable**.

```text
nf( ( name : String | r ) ⊎ ( age : Int ) )
  = ⟨ {name ↦ String, age ↦ Int} ; {r} ⟩
  = nf( ( age : Int, name : String | r ) )

nf( ( Console | e ) ⊎ ( State Int ) )
  = ⟨ {Console ↦ [], State ↦ [Int]} ; {e} ⟩
  = nf( ( State Int, Console | e ) )
```

`T1 = T2` is literal set equality. Order is irrelevant, so `⟨∅;{r,s}⟩` and `⟨∅;{s,r}⟩` are equal. Distinct row variables, however, are **not** identified.

```text
( name : String | r )   and   ( name : String | s )     are different rows
```

`r` and `s` are different type variables standing for different unknowns. Identifying them would force the following type to preserve the remaining fields, which is a stronger claim than it makes.

```purescript
forall r s. Record { name :: String, ...r } -> Record { name :: String, ...s }
```

The symbol `≡` serves two roles that should not be conflated.

| | Where | Subject | Character |
| --- | --- | --- | --- |
| Equality | Core type checker | rigid row variables only, since Core has no metavariables | a decision procedure; it identifies nothing |
| Constraint | elaboration | may contain metavariables | [unification](10-Elaboration.md) constructs a substitution |

`( name : String | ?r ) ≡ ( name : String | ?s )` is a constraint, not a question of equality, and unification solves it with a fresh `?t`, setting `?r := ?t` and `?s := ?t`. Unification produces a substitution that makes the rows equal; equality itself identifies nothing.

## Deciding entailment

```text
Γ ⊨ l ∉ ρ        ⟺   nf(ρ) = ⟨F;T⟩,  l ∉ dom(F),
                       ∀t ∈ T. (l ∉ t) ∈ Γ*

Γ ⊨ ρ1 # ρ2      ⟺   nf(ρi) = ⟨Fi;Ti⟩,
                       dom(F1) ∩ dom(F2) = ∅,
                       ∀t ∈ T1. ∀l ∈ dom(F2). (l ∉ t) ∈ Γ*,
                       ∀t ∈ T2. ∀l ∈ dom(F1). (l ∉ t) ∈ Γ*,
                       ∀t1 ∈ T1. ∀t2 ∈ T2. t1 ≠ t2 ∧ (t1 # t2) ∈ Γ*
```

### `Γ*`: decomposing assumptions into atomic facts

The conditions above look for **atomic facts about row variables** — `l ∉ t` and `t1 # t2` — whereas assumptions in `Γ` concern composite rows. Each assumption is decomposed over the normal form.

```text
assumption (l ∉ ρ)      with nf(ρ) = ⟨F;T⟩
                          if l ∈ dom(F) the assumption is unsatisfiable
                          otherwise it yields  { l ∉ t | t ∈ T }

assumption (ρ1 # ρ2)    with nf(ρi) = ⟨Fi;Ti⟩
                          if dom(F1) ∩ dom(F2) ≠ ∅ the assumption is unsatisfiable
                          otherwise it yields
                            { l ∉ t | l ∈ dom(F1), t ∈ T2 }
                            { l ∉ t | l ∈ dom(F2), t ∈ T1 }
                            { t1 # t2 | t1 ∈ T1, t2 ∈ T2 }
```

The only closure added is symmetry of `#`. Since `Γ` is finite and each `nf` is finite, `Γ*` is finite and is constructed once.

There is no backtracking and no search order. This is the answer to the objection that instance chain search order becomes an accidental compile-time language.

## Diagnostics

A failed row constraint is reported by the row solver directly.

```text
  row constraint unsatisfied
    required : "name" ∉ r
    r is universally quantified at Example.dawn:12:8
    no assumption gives "name" ∉ r
```

It does not appear as an instance resolution error. A failure that is a row problem is reported as a row problem.

## Why `Difference` and `Map` are not in Core

**`Difference ρ L`.** For an open row, `ρ - {l}` has no determinate meaning unless membership of `l` is known. Where `l` is a known field, the term-level `restrict` already covers it, with type `Record (l : τ | ρ) -> Record ρ`. A type-level `Difference` would be needed only to name the remainder of `ρ` while assuming `l ∈ ρ`, and that is an **equality constraint**, `ρ ≡ (l : τ | ρ')`. A `HasField l τ r` predicate is therefore not a new constraint in Core but the equation `r ≡ ( l : τ | r' )` for a fresh `r'`. The solver solves an equation, not a predicate.

**`Map f ρ`.** This requires type-level functions, whose introduction and termination are unsettled. Admitting computation of unknown termination into the trusted core is not compatible with the checker's self-contained character. Uses such as `Record (Map Maybe r)` are expressed for now with term-level residual evidence ([Elaboration](10-Elaboration.md)).

Both can be added later as type-level functions over `Row ε`. Adding them now would make row equality undecidable.

## Surface syntax: spread notation

This section describes convention rather than Core. It belongs with row theory because it is **common to every row kind**: if rows are one theory, they should have one notation.

### The common shape

A row literal is written as a set of elements. Brackets differ by kind; the contents obey the same rules.

```text
RowLit ::= open ent1 "," … "," entn close       (n >= 0)

ent ::= element                 written per kind
      | "..." ρ                 spreading a row
      | "..."                   anonymous spread
```

| Kind | Brackets | Element | Example |
| --- | --- | --- | --- |
| `Row Type` (record) | `{` `}` | `l :: τ` | `{ name :: String, age :: Int }` |
| `Row Type` (variant) | undetermined | `L :: τ` | — |
| `Row Effect` | `{\|` `\|}` | `E τ̄` | `{\| Console, State Int \|}` |

Desugaring is `⊎` at every kind.

```text
{ name :: String, ...r }        ⟹  ( name : String ) ⊎ r
{ ...r, ...s }                  ⟹  r ⊎ s
{| Console, ...e |}             ⟹  ( Console ) ⊎ e
{| ...e, ...f |}                ⟹  e ⊎ f
{}  /  {||}                     ⟹  ()
```

`( name : String ) ⊎ r` and the row extension `( name : String | r )` share a normal form, so which one the desugaring chooses does not affect meaning; the Lacks constraint `name ∉ r` is the same either way.

`...` follows JavaScript's spread syntax. It does not make case distinguish roles, and it generalizes: **what is spread need not be a variable.**

```purescript
{ id :: Int, ...(Shape.fieldsOf t) }
{| Console, ...(Handler.effectsOf f) |}
```

`...τ` requires only that `τ` have the right kind. That generality belongs to `⊎` already; singling out variables would be arbitrary.

### Anonymous spread

The operand of `...` may be omitted, denoting an implicitly quantified row variable.

**Every anonymous `...` in one signature denotes the same variable, per kind.** Writing a name is what distinguishes separate variables.

This rule is what makes useful signatures expressible. Under a rule that generates a fresh variable per occurrence, none of the following can be written.

```purescript
-- record: "preserves the other fields" becomes inexpressible
setAge :: Int -> { age :: Int, ... } -> { age :: Int, ... }
-- forall r. age ∉ r => Int -> Record ( age : Int | r ) -> Record ( age : Int | r )

-- effect: a higher-order function's effect transparency becomes inexpressible
map :: (a -> b / {| ... |}) -> List a -> List b / {| ... |}
-- forall e. (a -{e}-> b) -> List a -{e}-> List b

-- handler: "remove this one, leave the rest" becomes inexpressible
runState :: (Unit -> a / {| State s, ... |}) -> s -> Tuple a s / {| ... |}
-- forall e. State ∉ e => (Unit -{ ( State s ) ⊎ e }-> a) -> s -{e}-> Tuple a s
```

The rule can instead be too strong, when two independent open rows are wanted.

```purescript
-- intended: two unrelated records
-- actual: forall r. a ∉ r, b ∉ r => Record ( a : Int | r ) -> Record ( b : Int | r ) -> Int
f :: { a :: Int, ... } -> { b :: Int, ... } -> Int
```

Names are written in that case (`...r` and `...s`). What matters is that the rule **never admits an incorrect program**: an over-strong signature fails at the call site rather than quietly meaning something else. A diagnostic should say that the anonymous spreads in a signature denote one row and that names separate them.

This limitation is met more often at `Row Type` than at `Row Effect`, because an effect row is a single ambient context for a computation whereas record arguments may be unrelated.

Implicit quantification is always **outermost**. A quantifier at a higher-rank position must be written explicitly.

### Openness is visible in the syntax

Without `...` a row is closed; with it, open.

```purescript
exactly :: { name :: String } -> String              -- a record with only `name`
atLeast :: { name :: String, ... } -> String         -- `name` and possibly more

handleAll  :: (Unit -> a / {| Console |}) -> a        -- Console alone
handleSome :: (Unit -> a / {| Console, ... |}) -> a   -- Console and possibly more
```

In PureScript, whether a row is open or closed varies with the surrounding inference context. `...` settles it in the text of the signature. This, rather than brevity, is the notation's principal value.

PureScript's `{ name :: String | r }` is not adopted because `|` privileges the tail position: it cannot be written among the elements, cannot appear more than once, cannot spread anything but a variable, and cannot be omitted. `...` does all four.

### Nothing reaches Core

`...`, anonymity, implicit quantification, and the filling in of Lacks constraints all disappear during elaboration. Core sees only `⊎`, `forall`, and `∉`.

**Implicit quantification of Lacks constraints.** `{ name :: String, ...r }` is `( name : String ) ⊎ r`, which the kinding rules require `name ∉ r` for. That constraint is supplied implicitly, exactly as `forall` is, whether the spread is named or anonymous.

```purescript
logAll :: List String -> Unit / {| Console, ...e |}

-- implicitly
-- forall (e : Row Effect). Console ∉ e
--   => List String -{ ( Console ) ⊎ e }-> Unit
```

The author never writes a Lacks constraint. The cost of sharpness is absorbed here.
