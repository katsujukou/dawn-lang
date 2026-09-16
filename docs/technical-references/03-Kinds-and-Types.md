# Kinds and Types

## Names and binding

By the time a term reaches Core, name resolution and hygiene are complete.

- A **qualified name** `M.x` refers to a top-level name of module `M`, where `M` is a fully qualified module name.
- A **local name** `x` is introduced by `λ`, `Λ`, `let`, `letrec`, or a decision tree's `bind`.
- Core terms are unique up to α-equivalence; every bound variable is renamed to be unique within its context.
- Names introduced by macro expansion are already made unique. **Core carries no hygiene information.** Scopes and expansion traces belong to the Surface AST and to diagnostics.

```text
ModuleName ::= Upper ("." Upper)*
Ident      ::= value-level identifier
TyIdent    ::= type-level identifier
Ctor       ::= data constructor name
Label      ::= a row key: a record field name, a variant tag, or an effect constructor name
EffName    ::= effect name
OpName     ::= effect operation name
JoinName   ::= join point name

QIdent ::= ModuleName "." Ident | Ident
```

A label is not a name; it is the separate syntactic class above. For records and variants it is the field or tag name that is written; for effects it is the effect constructor at the head of the element ([Rows](04-Rows.md)).

Every Core node carries a source span. Spans have no influence on type checking or semantics; they exist for diagnostics alone, and the grammars below omit them.

## Kinds

Kinds and types are separate syntactic classes (D2). Kinds are stratified into three layers (D24).

```text
ε ::= Type | Effect                  row element kinds

κ ::= k                              kind variables
    | Type                           the kind of value types
    | Effect                         the kind of effect constructors
    | Row ε                          rows of ε
    | κ1 -> κ2                       type constructors

q ::= k                              quantifiable kinds, a subset of κ
    | Type
    | Row Type
    | Row Effect
    | q1 -> q2
```

Kind equality is syntactic, up to α-equivalence. There is no computation at the kind level.

Representative kinds:

```text
Int        : Type
List       : Type -> Type
Record     : Row Type -> Type
Variant    : Row Type -> Type
Function   : Type -> Row Effect -> Type -> Type
State      : Type -> Effect
```

`Row Type` is the row kind of records and variants; `Row Effect` is that of effect rows. Both share the row theory of [Rows](04-Rows.md).

### Why the three layers

**`Row` takes only `ε`.** Row element well-formedness is defined for exactly two shapes: `l : τ` at `Row Type` and `E τ̄` at `Row Effect`. Permitting `Row κ` for arbitrary `κ` would admit degenerate row kinds such as `Row (Type -> Type)`, inhabited only by the empty row, row variables, and `⊎`, and having no elements at all.

**Quantification is restricted to `q`**, expressed by the judgement `Γ ⊢ κ qkind`.

```text
  Γ ⊢ κ qkind    Γ, a : κ ⊢ τ : Type
  ──────────────────────────────────
  Γ ⊢ forall (a : κ). τ : Type
```

The same condition applies at every site that introduces a type variable: `forall (a : κ). τ`, `Λ (a : κ). v`, the type parameters of data and effect declarations, the type parameters of operations, and the instantiation `[[κ̄]]`.

| | Admitted | Reason |
| --- | --- | --- |
| `forall (r : Row Effect). …` | yes | `Row Effect ∈ q` |
| `forall (f : Type -> Type). …` | yes | higher-kinded types are retained |
| `forall (e : Effect). …` | **no** | `Effect ∉ q`. Abstracting over a single effect is done with a `Row Effect` variable |
| `forall (f : Type -> Effect). …` | **no** | `Effect ∉ q` |
| `Proxy [[Effect]]` | **no** | instantiation also requires `qkind` |
| `State : Type -> Effect` | yes | the kind of a declared constructor is a `κ`, not a `q` |

`Effect` belongs to `κ` but not to `q`: it is required as the result kind of effect constructors, and it cannot be quantified.

One could instead permit quantification over `Effect`. That design is also coherent, but it then needs a separate rule forbidding a type variable at the head of a row element, since effect row keys must be rigid (D16). Dawn takes the stratification instead.

## Kind schemes

```text
σκ ::= forall k1 .. kn . κ       (n >= 0)
```

Kind schemes appear **only on declarations**. The global signature `Σ` carries one for each of three things.

| Entity | Form |
| --- | --- |
| Type constructor | `T : forall k̄. κ` |
| Data constructor | `Ctor : forall k̄. σ` |
| Top-level value or foreign | `M.x : forall k̄. σ` |

Neither the type grammar nor the term grammar has a kind **quantifier**: there is no `forall (k : Kind). τ` and no `Λ (k : Kind). e`. Quantification happens only in declarations. A kind variable enters the local context `Γ` only while checking a declaration whose scheme binds it.

### Instantiation is explicit

A kind scheme is instantiated **explicitly at the use site**, in both types and terms.

```text
τ ::= …  | T [[κ̄]]        instantiate a type constructor's kind scheme
e ::= …  | M.x [[κ̄]]      instantiate a global name's kind scheme
```

`[[…]]` is not an application to an arbitrary expression; it is an annotation on the occurrence of a global name. Since D3 provides no introduction form for kind abstraction, there can be no elimination form either, and the grammar forbids terms such as `(λ(x : τ). x) [[Type]]`.

When the scheme is empty, `[[]]` is omitted. Most declarations are in this case, so `[[…]]` appears only where a kind-polymorphic declaration is used.

```text
Proxy [[Type]] Int              -- in a type
Proxy [[Type]] [Int]            -- in a term
List Int                        -- empty kind scheme; nothing is written
```

Making instantiation explicit keeps the rules a matter of **substitution alone**. Implicit instantiation would require bidirectional kind checking and first-order matching in the type checker, together with a well-formedness condition guaranteeing that every bound kind variable is determined. Two grammar productions cost less than that machinery in the trusted core. This is also consistent with Core generally: implicit arguments become ordinary arguments (D11), type instantiation is `e [τ]`, constraints are `e [•]`, and effect widening is `openEff`.

Surface syntax never contains `[[κ]]`; the elaborator emits it.

## Types

```text
τ, σ, ρ ::= a                        type variable
          | T [[κ̄]]                  type constructor; `T` when κ̄ is empty
          | τ1 τ2                    type application
          | forall (a : κ) . τ       universal quantification
          | C => τ                   constraint abstraction, erased
          | ()                       the empty row
          | ( ent | ρ )              row extension
          | ρ1 ⊎ ρ2                  row union

ent ::= l : τ                        a `Row Type` element; the key `l` is written
      | E τ̄                          a `Row Effect` element; the key `E` is derived

C ::= l ∉ ρ                          Lacks
    | ρ1 # ρ2                        Disjoint
```

A function type is an application of the type constructor `Function`; Core has no arrow syntax.

```text
τ1 -{ρ}-> τ2   ≡   Function τ1 ρ τ2
τ1 -> τ2       ≡   Function τ1 () τ2        (a pure function)
```

**The arrow is notation used in these documents and in surface syntax, not a Core name.** Core names are fully qualified, so the constructor is `Prim.Function`. All infix operators are surface aliases resolved to qualified names during name resolution; Core has no counterpart to PureScript's `TypeOp`. These documents write `Int`, `List`, `Record`, and `Function` without the `Prim.` prefix for readability.

`Record ρ` and `Variant ρ` are likewise ordinary type constructor applications.

## Kinding

The judgement is `Γ ⊢ τ : κ`. Contexts are defined in [Typing Rules](07-Typing-Rules.md).

```text
  (a : κ) ∈ Γ                (T : forall k̄. κ) ∈ Σ   Γ ⊢ κ̄' qkind   |κ̄'| = |k̄|
  ───────────                ────────────────────────────────────────────────
  Γ ⊢ a : κ                  Γ ⊢ T [[κ̄']] : κ[k̄ := κ̄']

  Γ ⊢ τ1 : κ1 -> κ2    Γ ⊢ τ2 : κ1
  ────────────────────────────────
  Γ ⊢ τ1 τ2 : κ2

  Γ ⊢ κ qkind    Γ, a : κ ⊢ τ : Type     Γ ⊢ C ok    Γ ⊢ τ : Type
  ──────────────────────────────────     ───────────────────────────
  Γ ⊢ forall (a : κ). τ : Type           Γ ⊢ C => τ : Type

  ─────────────────
  Γ ⊢ () : Row ε

  Γ ⊢ ent : ε entry    Γ ⊢ ρ : Row ε    Γ ⊨ key(ent) ∉ ρ
  ──────────────────────────────────────────────────────  ← sharpness
  Γ ⊢ ( ent | ρ ) : Row ε

  Γ ⊢ ρ1 : Row ε    Γ ⊢ ρ2 : Row ε    Γ ⊨ ρ1 # ρ2
  ────────────────────────────────────────────────  ← disjointness
  Γ ⊢ ρ1 ⊎ ρ2 : Row ε
```

That row extension and row union require **entailment from the context** is the centre of the design. PureScript admits `RCons` unconditionally and performs no elimination of duplicate labels; in Dawn a well-kinded row is sharp by construction.

### Row elements

```text
  Γ ⊢ τ : Type                          ( E : forall k̄. κ̄ -> Effect ) ∈ Σ    Γ ⊢ τ̄ : κ̄
  ────────────────────────              ─────────────────────────────────────────────
  Γ ⊢ ( l : τ ) : Type entry            Γ ⊢ E τ̄ : Effect entry

  key( l : τ ) = l                      key( E τ̄ ) = E
```

An element of a `Row Effect` **must have a declared effect constructor at its head**; an element headed by a type variable is not admitted. Effect row keys are therefore always rigid, independent of how metavariables are solved, which is what makes row equality decidable ([Rows](04-Rows.md)). The `qkind` condition of D24 reinforces this: since `Effect` is not quantifiable, `forall (e : Effect). …` cannot be written, so a type variable can never reach the head of an element.

### Constraint well-formedness

```text
  Γ ⊢ ρ : Row ε    Γ ⊢ l key ε          Γ ⊢ ρ1 : Row ε    Γ ⊢ ρ2 : Row ε
  ─────────────────────────────         ───────────────────────────────
  Γ ⊢ l ∉ ρ ok                          Γ ⊢ ρ1 # ρ2 ok
```

Key well-formedness is determined by `ε`.

```text
  ────────────────────          ( E : forall k̄. κ̄ -> Effect ) ∈ Σ
  Γ ⊢ l key Type                ─────────────────────────────────
  (any label)                   Γ ⊢ E key Effect
```

A `Row Type` key is any label; a `Row Effect` key must be a **declared effect constructor name**. A Lacks constraint over field labels therefore cannot be imposed on a `Row Effect`.

```text
name ∉ ( Console )        -- not admitted: `name` is not an effect constructor
Console ∉ e               -- admitted when e : Row Effect
```

Both sides of `#` must share the same `ε`; a Disjoint constraint spanning `Row Type` and `Row Effect` is not expressible.

## Type equality

`Γ ⊢ τ1 ≡ τ2` holds when the types are α-equivalent, their rows agree by the normal form of [Rows](04-Rows.md), and they are otherwise structurally identical.

There is no β-reduction and no δ-reduction, because there are no type-level functions. Apart from row normalization, deciding equality is syntactic.

The type grammar has application `τ1 τ2` but **no abstraction**, and that is what gives this property. Type constructors can be abstracted over — `forall (f : Type -> Type). …` — but anonymous type constructors cannot be defined. Core therefore lies between System F and System Fω (D1). Introducing a type-level lambda would make it Fω and would bring β-reduction into type equality.
