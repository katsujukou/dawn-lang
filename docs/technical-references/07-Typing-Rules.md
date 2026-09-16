# Typing Rules

## Contexts

```text
Σ ::= global signature                         (kind schemes: 03-Kinds-and-Types)
        type constructors   T : forall k̄. κ
        data constructors   Ctor : forall k̄. σ   (with owning type, tag, arity, field types)
        effect declarations E forall k̄. (ā : κ̄) { op : σ }
        foreign             f : forall k̄. σ
        top-level values    M.x : forall k̄. σ

Γ ::= ·                 local context
    | Γ, k              kind variable; introduced only while checking a declaration
    | Γ, a : κ          type variable
    | Γ, x : τ          value variable
    | Γ, C              row constraint assumption

Δ ::= · | Δ, j : (τ̄) -> τ ! ρ              join point context
Ω ::= occurrence ⇀ τ                        occurrence context
```

There are four contexts because their **scoping rules differ in four ways**. Merging them would erase the differences.

| | Σ | Γ | Δ | Ω |
| --- | --- | --- | --- | --- |
| Contains | declarations | local bindings | join points | occurrence types |
| Populated by | a module's declarations and its imports | `λ`, `Λ`, `let`, `letrec`, `bind`; kind variables while checking a declaration | `letjoin` | `case` and `switch*` |
| Lifetime | fixed throughout checking of a module | grows at a binder, shrinks on leaving it | **discarded at a lambda** | within a decision tree only |
| Structure | an unordered table | ordered; later entries may refer to earlier ones | ordered | a map from occurrences |
| Names | fully qualified `M.x`, `T`, `M.Ctor` | local names `x`, `a` | join names `j` | not names but paths |
| Kind schemes | yes | no | no | no |
| On lookup | instantiates the kind scheme | taken as is | taken as is | taken as is |
| In judgements | implicit, omitted below | explicit | explicit | decision tree judgements only |

The distinction between `Σ` and `Γ` is the most basic.

`Σ` is a table of declarations, built from a module's top-level declarations and from the signatures of imported modules, and fixed throughout the checking of that module. The typing rules neither extend nor shrink it; they only look things up in it. That is why the judgements below omit it.

`Γ` is a sequence of local bindings. It grows on entering `λ`, `Λ`, or `let` and shrinks on leaving. It is ordered, and later entries may refer to earlier ones: `Γ, a : Type, x : a` is meaningful while the reverse order is not.

The distinction is also the unit of **separate compilation**. `Σ` is what a module's interface publishes for other modules; `Γ` never crosses a module boundary. That only `Σ` carries kind schemes follows from instantiation occurring only when a declaration is referenced.

`Ω` is separate because an occurrence is not a variable. It is a path from a scrutinee, derived structurally as the tree is descended rather than introduced by a binder. It becomes a variable only by passing through `bind x = o`, at which point it enters `Γ`.

## Judgement forms

```text
Γ ⊢ κ kind                  kind well-formedness
Γ ⊢ κ qkind                 κ is a quantifiable kind
Γ ⊢ l key ε                 key well-formedness
Γ ⊢ τ : κ                   kinding
Γ ⊢ C ok                    constraint well-formedness
Γ ⊨ C                       constraint entailment
Γ ⊢ τ1 ≡ τ2                 type equality
Γ; Δ ⊢ e : τ ! ρ            term typing; ρ is the ambient effect row
Γ; Δ; Ω ⊢ dt : τ ! ρ        decision tree typing
Ω ⊢ o : τ                   occurrence typing
```

`ρ` is the range of effects a term's evaluation may produce. Pure constructs are typeable under any `ρ`. Constructs that produce effects require agreement with `ρ`. Containment on an arrow's effect row is never inserted automatically (D8).

## Basic rules

```text
  (x : τ) ∈ Γ       (M.x : forall k̄. σ) ∈ Σ   Γ ⊢ κ̄' qkind   |κ̄'| = |k̄|
  ─────────────────  ─────────────────────────────────────────────────────
  Γ;Δ ⊢ x : τ ! ρ    Γ;Δ ⊢ M.x [[κ̄']] : σ[k̄ := κ̄'] ! ρ

  Γ, x : τ1; · ⊢ e : τ2 ! ρ'
  ────────────────────────────────────────────   ← the body's effects go on the arrow
  Γ;Δ ⊢ λ(x : τ1). e : τ1 -{ρ'}-> τ2 ! ρ         ← Δ is discarded

  Γ;Δ ⊢ e1 : τ1 -{ρ}-> τ2 ! ρ    Γ;Δ ⊢ e2 : τ1 ! ρ
  ────────────────────────────────────────────────   ← the arrow's row equals the ambient row
  Γ;Δ ⊢ e1 e2 : τ2 ! ρ

  Γ ⊢ κ qkind    Γ, a : κ; · ⊢ v : τ ! ()    v is a value form
  ────────────────────────────────────────────────────────────
  Γ;Δ ⊢ Λ(a : κ). v : forall (a : κ). τ ! ρ

  Γ;Δ ⊢ e : forall (a : κ). τ ! ρ    Γ ⊢ σ : κ
  ─────────────────────────────────────────────
  Γ;Δ ⊢ e [σ] : τ[a := σ] ! ρ

  Γ ⊢ C ok    Γ, C; · ⊢ v : τ ! ()    v is a value form
  ─────────────────────────────────────────────────────
  Γ;Δ ⊢ Λ(_ : C). v : C => τ ! ρ

  Γ;Δ ⊢ e : C => τ ! ρ    Γ ⊨ C
  ───────────────────────────────   ← no proof term; the checker re-derives
  Γ;Δ ⊢ e [•] : τ ! ρ

  Γ;Δ ⊢ e1 : τ1 ! ρ    Γ, x : τ1; Δ ⊢ e2 : τ2 ! ρ
  ───────────────────────────────────────────────
  Γ;Δ ⊢ let x : τ1 = e1 in e2 : τ2 ! ρ

  Γ' = Γ, x1 : σ1, …, xn : σn
  each i:  vi is a FunVal   and   Γ'; Δ ⊢ vi : σi ! ()
  Γ'; Δ ⊢ e : τ ! ρ
  ──────────────────────────────────────────────────
  Γ;Δ ⊢ letrec { xi : σi = vi } in e : τ ! ρ

  Γ;Δ ⊢ e : τ1 ! ρ    Γ ⊢ τ1 ≡ τ2
  ────────────────────────────────   ← conversion is by equality; there is no subtyping
  Γ;Δ ⊢ e : τ2 ! ρ
```

The rules for global names instantiate a kind scheme with `κ̄'`, which is **pure substitution**: `κ̄'` is written in the term, so the checker neither guesses nor searches for it. It verifies only that the arity matches and that each `κ'` is a quantifiable kind. Where a global name has an empty scheme, `[[]]` is omitted and the rule reads as `(M.x : σ) ∈ Σ`, which is the case for most of Core.

## Records and variants

```text
  ───────────────────────────
  Γ;Δ ⊢ {} : Record () ! ρ

  Γ;Δ ⊢ e1 : τ ! ρ    Γ;Δ ⊢ e2 : Record r ! ρ    Γ ⊨ l ∉ r
  ────────────────────────────────────────────────────────
  Γ;Δ ⊢ extend l e1 e2 : Record ( l : τ | r ) ! ρ

  Γ;Δ ⊢ e : Record ( l : τ | r ) ! ρ
  ──────────────────────────────────
  Γ;Δ ⊢ select l e : τ ! ρ

  Γ;Δ ⊢ e : Record ( l : τ | r ) ! ρ
  ─────────────────────────────────────
  Γ;Δ ⊢ restrict l e : Record r ! ρ

  Γ;Δ ⊢ e1 : Record ( l : τ | r ) ! ρ    Γ;Δ ⊢ e2 : τ' ! ρ
  ────────────────────────────────────────────────────────   ← the type may change
  Γ;Δ ⊢ update l e1 e2 : Record ( l : τ' | r ) ! ρ

  Γ;Δ ⊢ e1 : Record r1 ! ρ    Γ;Δ ⊢ e2 : Record r2 ! ρ    Γ ⊨ r1 # r2
  ───────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ merge e1 e2 : Record (r1 ⊎ r2) ! ρ

  Γ;Δ ⊢ e : τ ! ρ    Γ ⊨ l ∉ r    Γ ⊢ r : Row Type
  ────────────────────────────────────────────────
  Γ;Δ ⊢ inject l e : Variant ( l : τ | r ) ! ρ

  Γ;Δ ⊢ e : Variant r ! ρ    Γ ⊨ l ∉ r    Γ ⊢ τ : Type
  ────────────────────────────────────────────────────
  Γ;Δ ⊢ weaken l [τ] e : Variant ( l : τ | r ) ! ρ

  Γ;Δ ⊢ e : Variant () ! ρ    Γ ⊢ τ : Type
  ────────────────────────────────────────
  Γ;Δ ⊢ absurd [τ] e : τ ! ρ
```

The type of `merge` is the Core form of a row-polymorphic record merge.

```text
Prim.merge
  : forall (r : Row Type). forall (s : Row Type).
    r # s => Record r -> Record s -> Record ( r ⊎ s )
```

`r # s` is a `C => τ`, not a dictionary argument, and disappears at run time.

## Effects

```text
  ( E τ̄ ) ∈ nf(ρ)
  ( op : forall (b̄ : κ̄'). σ ->* τ ) ∈ Σ(E)      E's type parameters are ā
  Γ ⊢ σ̄ : κ̄'      Γ;Δ ⊢ e : σ[ā := τ̄][b̄ := σ̄] ! ρ
  ────────────────────────────────────────────────────
  Γ;Δ ⊢ perform E.op [σ̄] e : τ[ā := τ̄][b̄ := σ̄] ! ρ

  h = { return (x : α) -> e_r ; E.op_i [b̄_i] (x_i : σ_i', k_i : τ_i' -{ρ}-> β) -> e_i }
  Γ;· ⊢ e : α ! ( E τ̄ | ρ )                         ← inside handle the row grows
  Γ, x : α; · ⊢ e_r : β ! ρ
  each i:  Σ(E).op_i = forall (b̄_i : κ̄_i). σ_i ->* τ_i
           σ_i' = σ_i[ā := τ̄]    τ_i' = τ_i[ā := τ̄]
           Γ, b̄_i : κ̄_i, x_i : σ_i', k_i : τ_i' -{ρ}-> β; · ⊢ e_i : β ! ρ
           (b̄_i is bound by the clause; a handler must respect an operation's polymorphism)
  { op_i } = dom(Σ(E))                              ← the clauses exhaust E's operations
  ───────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ handle e with h : β ! ρ

  Γ;Δ ⊢ e : τ1 -{r1}-> τ2 ! ρ    Γ ⊨ r1 # r'    Γ ⊢ r' : Row Effect
  ─────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ openEff [r'] e : τ1 -{r1 ⊎ r'}-> τ2 ! ρ
```

That handlers are deep (D15) shows in the type of the continuation `k_i`, namely `τ_i -{ρ}-> β`: calling it returns under the same handler, so the result type is `β`, the result of the `handle`, and the ambient row is `ρ`, the row outside it. A shallow handler would give `τ_i -{( E τ̄ | ρ )}-> α`.

`openEff` is required where a pure function is used in an effectful context.

```text
-- f : Int -> Int                        (pure)
-- to call f where g : Int -{( Console )}-> Int
g = λ(n : Int). (openEff [( Console )] f) n
```

The explicitness is the price of D8. The elaborator inserts it, so an author does not see it.

## Join points and decision trees

```text
  Γ, x̄ : τ̄; Δ, j : (τ̄) -> τ ! ρ ⊢ e1 : τ ! ρ
  Γ;      Δ, j : (τ̄) -> τ ! ρ ⊢ e2 : τ ! ρ
  ───────────────────────────────────────────────
  Γ;Δ ⊢ letjoin j (x̄ : τ̄) = e1 in e2 : τ ! ρ

  ( j : (τ̄) -> τ ! ρ ) ∈ Δ    each i: Γ;Δ ⊢ e_i : τ_i ! ρ    jump is in tail position
  ──────────────────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ jump j (ē) : τ ! ρ

  each i: Γ;Δ ⊢ e_i : τ_i ! ρ        Γ;Δ; { s_i ↦ τ_i } ⊢ dt : τ ! ρ
  ────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ case (ē) of dt : τ ! ρ

  Γ;Δ ⊢ e : τ ! ρ                      Ω ⊢ o : τ_o    Γ, x : τ_o; Δ; Ω ⊢ dt : τ ! ρ
  ────────────────────────             ────────────────────────────────────────────
  Γ;Δ;Ω ⊢ leaf e : τ ! ρ               Γ;Δ;Ω ⊢ bind x = o in dt : τ ! ρ

  Ω ⊢ o : T σ̄       each Ctor_i is a constructor of T, Ctor_i : forall ā. τ̄_i -> T ā
  the Ctor_i are distinct
  each i: Γ;Δ; Ω ∪ { o ! Ctor_i . j ↦ τ_ij[ā := σ̄] } ⊢ dt_i : τ ! ρ
  with a default:     Γ;Δ;Ω ⊢ dt_0 : τ ! ρ
  without a default:  {Ctor_i} exhausts the constructors of T
  ─────────────────────────────────────────────────────────────
  Γ;Δ;Ω ⊢ switchCtor o { Ctor_i -> dt_i } [default -> dt_0] : τ ! ρ

  Ω ⊢ o : τ_o       τ_o is a primitive type with literals
  the c_i are literals of τ_o and are distinct
  each i: Γ;Δ;Ω ⊢ dt_i : τ ! ρ
  Γ;Δ;Ω ⊢ dt_0 : τ ! ρ                          ← a default is mandatory
  ─────────────────────────────────────────────────────────────
  Γ;Δ;Ω ⊢ switchLit o { c_i -> dt_i } default -> dt_0 : τ ! ρ

  Ω ⊢ o : Variant r        nf(r) = ⟨F ; T⟩
  each l_i ∈ dom(F) and the l_i are distinct
  each i: Γ;Δ; Ω ∪ { o ? l_i ↦ F(l_i) } ⊢ dt_i : τ ! ρ
  with a default:     Γ;Δ; Ω ∪ { o ↦ Variant r' } ⊢ dt_0 : τ ! ρ
                      where nf(r') = ⟨ F ∖ {l_1..l_n} ; T ⟩
  without a default:  T = ∅ and {l_i} = dom(F)
  ─────────────────────────────────────────────────────────────
  Γ;Δ;Ω ⊢ switchLabel o { l_i -> dt_i } [default -> dt_0] : τ ! ρ

  Γ;Δ ⊢ e : Boolean ! ρ    Γ;Δ;Ω ⊢ dt_1 : τ ! ρ    Γ;Δ;Ω ⊢ dt_2 : τ ! ρ
  ─────────────────────────────────────────────────────────────────────
  Γ;Δ;Ω ⊢ guard e dt_1 dt_2 : τ ! ρ

  Γ ⊢ ρ ≡ ( Partial | ρ' )    Γ ⊢ τ : Type
  ──────────────────────────────────────────────────  (derived; see 05-Effects)
  Γ;Δ;Ω ⊢ fail : τ ! ρ
```

In the default branch of `switchCtor` and `switchLit` the occurrence context `Ω` is unchanged, because Core does not track the refinement "not one of the enumerated cases". Refinement happens only in the default branch of `switchLabel`, where the occurrence takes the residual type `Variant r'`.

That branch is the term-level appearance of residual computation over an unknown tail: when `T ≠ ∅` the condition `{l_i} = dom(F)` cannot be met, so a default is required, and its type is the residual. An open variant cannot be enumerated by pretending it is closed.
