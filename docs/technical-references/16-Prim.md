# The Prim Module

## Two different axes

`Prim` and `intrinsic` are often conflated. They answer different questions.

| | Question | Answer |
| --- | --- | --- |
| `Prim` | where does a name live, and must it be imported | a reserved module, visible without being imported |
| `intrinsic` | is this type constructor a `data` declaration | a classification `Σ` records |

Neither implies the other.

| | `data` | `intrinsic` |
| --- | --- | --- |
| **in `Prim`** | `Prim.Unit` | `Prim.Int`, `Prim.Function`, `Prim.Variant`, `Prim.IO` |
| **outside `Prim`** | `Main.List`, `Maybe.Maybe` | `Array.Array`, `Function.Uncurried.Fn2` |

`Prim.Unit` is an ordinary data type that happens to be reserved; `Array.Array` is intrinsic and imported like anything else.

## What `Prim` holds

`Prim` holds the vocabulary the rules of [Typing Rules](07-Typing-Rules.md) and [Modules](09-Modules.md) name, and nothing else. Every kind scheme is empty, so no use site writes `[[κ̄]]`.

```text
Prim.Function : Type -> Row Effect -> Type -> Type
Prim.Record   : Row Type -> Type
Prim.Variant  : Row Type -> Type
Prim.Int      : Type
Prim.Number   : Type
Prim.String   : Type
Prim.Char     : Type
Prim.Boolean  : Type
Prim.Unit     : Type
Prim.IO       : Type -> Type
```

Each is here because at least one rule names it.

| Type constructor | Named by |
| --- | --- |
| `Function` | `λ` and application, and therefore every arrow these documents write as `τ1 -{ρ}-> τ2` |
| `Record` | `{}`, `extend`, `select`, `restrict`, `update`, `merge` |
| `Variant` | `inject`, `weaken`, `absurd`, and the residual type in a `switchLabel` default |
| `Int`, `Number`, `String`, `Char`, `Boolean` | `litType`, which gives a literal its type |
| `Boolean` | also the condition of a `guard` |
| `IO`, `Unit` | the entry point `main : IO Unit` |

`Prim` declares one data type.

```text
data Unit = Unit
  -- Prim.Unit : Unit        tag 0, arity 0
```

`Unit` is a data declaration rather than a literal, so a `switchCtor` exhausts it with one branch. As a literal it would fall under `switchLit`, where a default is mandatory because literals cannot be exhausted ([Typing Rules](07-Typing-Rules.md)).

**`Array` and the uncurried families are not here.** Core names neither, and neither needs to be reachable without an import; they are intrinsic all the same, and the section below places them.

## Intrinsic type constructors

An intrinsic type constructor has a kind in `Σ` and no data constructors whatever.

That is not the same as a data declaration with an empty list of constructors, and the difference is load-bearing. The rule for `switchCtor` permits a missing default when `{Ctor_i}` exhausts the constructors of `T`; a type with no constructors would exhaust vacuously, so a `switchCtor` on an `Int` with no branches and no default would pass. **A `switchCtor` whose occurrence has an intrinsic type is ill-formed**, and `switchLit` is what dispatches on those.

`Σ` therefore distinguishes them, and a type constructor entry is one or the other:

```text
T : forall k̄. κ   intrinsic C        where C is the canonical-value class below
T : forall k̄. κ   data { Ctor … }    the constructors the declaration gives it
```

**The class is part of the entry, not a comment on it.** Rules consult it: the typing of an opaque value requires `Σ(T) = intrinsic opaque` ([Semantics](08-Semantics.md)), and the canonical-forms lemma progress rests on is stated class by class.

### Where an intrinsic comes from

```text
intrinsic
├─ Core intrinsic   Function, Record, Variant, the literal types, IO
└─ ABI intrinsic    Array, the uncurried families, opaque handles
```

Both are beyond a user's reach. They differ in who settles them: a **Core intrinsic** is fixed by this specification, an **ABI intrinsic** by the versioned primitive surface that a compiler and its backends implement together ([Open Questions](14-Open-Questions.md)).

### The canonical-value class

Having no constructors, an intrinsic type gets its values another way. Which way is the entry's **canonical-value class**, and there are five.

| Class | Type constructors | Canonical form | What examines one |
| --- | --- | --- | --- |
| `intrinsic literal` | `Int`, `Number`, `String`, `Char`, `Boolean` | a literal | `switchLit`, `guard` |
| `intrinsic function` | `Function` | `λ`, an unsaturated spine, `openEff`, `rec_i` | application |
| `intrinsic record` | `Record` | `{}`, `extend` | `select`, `restrict`, `update`, `merge` |
| `intrinsic variant` | `Variant` | `inject`, `weaken` | `switchLabel`, `absurd` |
| `intrinsic opaque` | `IO`, and every ABI intrinsic | `opaque ω [τ]` | nothing |

`switchCtor` is absent from the last column throughout: it takes a **data** value apart, and no intrinsic has one.

The last row is the one that shapes the others. **Core has no rule that compares or decomposes an opaque value**; it carries one from the `foreign` that produced it to the `foreign` that consumes it. That is also why the class must be mechanically decidable — `opaque ω [Boolean]` must not typecheck, or a `guard` would meet a value that is not `true` and not `false`.

### No declaration creates one

A module declares `data`, `newtype`, and `foreign`. **None of them produces an intrinsic entry**, and there is no surface syntax that does.

The reason is that an intrinsic is not one thing but several, and a declaration would have to supply all of them: a canonical value form, typing rules, an erasure, a backend representation, a convention for crossing the `foreign` boundary, the canonical-forms lemma progress rests on, and whatever equality or observation it admits. Adding one is an extension of the language, Core, and the backend ABI together — not a library.

A compiler therefore builds its initial signature rather than reading it from source.

```text
Prim.Int      : Type                                    intrinsic literal
Prim.Boolean  : Type                                    intrinsic literal
Prim.Function : Type -> Row Effect -> Type -> Type      intrinsic function
Prim.Record   : Row Type -> Type                        intrinsic record
Prim.Variant  : Row Type -> Type                        intrinsic variant
Prim.IO       : Type -> Type                            intrinsic opaque
```

An ABI intrinsic reaches `Σ` the same way, through the manifest of the primitive surface, and is then imported by name like any other declaration.

## How `Σ` acquires these names

`Prim` is never imported, so the rules that build `Σ` must put it there before anything else.

```text
Σ_Prim = the intrinsic type constructors of Prim
       ∪ { Unit : Type  data { Prim.Unit } }  with Prim.Unit's tag, arity, and field types
```

[Modules](09-Modules.md) collects type-level declarations into `Σ_ty` before checking any interior. That collection starts from `Σ_Prim` rather than from the imports alone.

```text
Σ_ty = Σ_Prim ∪ Σ_ABI(M) ∪ Σ_imp ∪ { the module's own data and effect declarations }
```

`Σ_ABI(M)` is what the manifest supplies to `M` itself, and is empty for every module the manifest does not name; the section on ABI intrinsics below says what it holds and why it comes before the module's own declarations.

Three consequences are worth stating.

**`Prim` is a reserved module name.** Core names are fully qualified, so a module declaring `Int` contributes `Main.Int` and collides with nothing; what must be forbidden is a second module named `Prim` supplying a rival `Prim.Int`. Within a module, declaring one name twice in a namespace is ill-formed as it is anywhere.

**Header completeness is unaffected** (D22). A module's header determines its dependencies, and `Prim` is a dependency of every module without exception, so a build system needs no entry to discover it. Nothing has to be written because nothing varies. An ABI intrinsic is different: a module using `Array.Array` imports `Array`, and the header says so.

**Linking includes `Prim`.** The global environment `G` of [Semantics](08-Semantics.md) is built from `G_Prim`, which holds the data constructors of `Prim` — `Prim.Unit` alone — beside the definitions of the imported modules. `Prim` is not among those imports, so without `G_Prim` a `Prim.Unit` in the module would have nothing to unfold to and condition (1) of `Σ ⊨ G` would fail.

## The ABI minimum

```text
foreign IO.pure : forall a. a -> IO a
foreign IO.bind : forall a b. IO a -> (a -> IO b) -> IO b
```

These live in a module named `IO`, whose `pure` and `bind` are distinct from the `Prim.IO` type constructor they are typed with. **That module is imported like any other**, so a module using them names it in its header and header completeness is untouched (D22). What sets them apart from an ordinary `foreign` is the obligation on the other side: a backend that does not implement them is not ABI-conformant and cannot provide the standard runtime in full, whereas one that omits an arithmetic primitive merely fails to run the programs that use it.

The value a saturated `IO.pure` returns is opaque, `IO` having neither literals nor constructors to be built from ([Semantics](08-Semantics.md)).

**`IO.bind`'s continuation is a pure arrow.** Every arrow in a `foreign` type has an empty effect row (D23), so `( a -{f}-> IO b )` cannot be declared; and the semantics would not hold either, since deferring `k` until the `IO` is executed would run the residual effect `f` outside the dynamic context of the handler that installed it ([Effects](05-Effects.md)).

Executing these two is the runtime ABI's obligation (D25), which is why they are fixed here rather than left to the surface.

## Literal domains are not yet fixed

The types of literals are settled above; **the values they range over are not**.

What Core requires of them is narrow: `switchLit` demands that its literals be distinct, so literal identity must be decidable. What Core does not settle is the range of `Int`, the representation of `Number` and how NaN and signed zero behave under that identity, whether a `Char` is a Unicode scalar value or a code unit, and what a `String` is a sequence of.

The question is wider than the values themselves, since which surface token denotes which Core value belongs to it: `42`, `0x2a`, and `0b101010` are one literal, and `"\n"` and `"\u{A}"` are another. `switchLit` compares the value, never the spelling.

These are recorded as open ([Open Questions](14-Open-Questions.md)). Until they are settled, **the choices an implementation happens to make are not the specification** — that the first compiler is written in PureScript does not make Dawn's `Int` a 32-bit one.

## ABI intrinsics, which live outside `Prim`

**The manifest supplies type constructors and nothing else.** It is not source, and no module may write an intrinsic entry; this is how the primitive surface states what it supplies and to whom.

```text
-- primitive-surface manifest
module Array
  intrinsic opaque Array : Type -> Type

module Function.Uncurried
  intrinsic opaque Fn2 : Type -> Type -> Type -> Type
```

The operations are ordinary source, written in the module the manifest names.

```purescript
module Array (Array, length, unsafeIndex, fromList) where
  foreign length      :: forall a. Array a -> Int
  foreign unsafeIndex :: forall a. Array a -> Int -> a
  foreign fromList    :: forall a. List a -> Array a
```

Splitting it this way keeps the manifest to what only it can express. A `foreign` is checked wherever it is written — every arrow pure (D23), the type well-kinded — and a manifest entry would either duplicate that or become a trusted input for no reason. It also leaves the module free to hold Dawn code beside its primitives, which the standard library needs: `mapArray` is written in Dawn and uses `unsafeIndex` ([Modules](09-Modules.md)).

Checking such a module therefore needs its own entries in scope before its declarations are collected. Writing `Σ_ABI(M)` for what the manifest supplies to `M` — empty for every module the manifest does not name — the collection of [Modules](09-Modules.md) reads:

```text
Σ_ty = Σ_Prim ∪ Σ_ABI(M) ∪ Σ_imp ∪ { the module's own data and effect declarations }
```

An importer sees the entry through `Σ_imp`, by the ordinary route. **What it sees is not a data type**: the import path is the same, the entry is not. `Array.Array` keeps its `intrinsic opaque` class, so a `switchCtor` on it is as ill-formed in the importing module as anywhere else.

Core names neither `Array` nor `Fn2`, and the module a name lives in is a question of visibility rather than of status. Both are imported, and a header that omits them is incomplete.

That `Array` has first-class surface syntax is not a reason to move it. **The syntax, the type, and Core are three independent things**: a library syntax macro can expand `[ e1, e2 ]` into a call, leaving Core with an ordinary `foreign` application and an opaque value. Where a standard surface is wanted, it is the standard library that provides it.

Arithmetic is the same story without an intrinsic type of its own: `Int.add : Int -> Int -> Int` operates on a Core intrinsic but is an ordinary `foreign` of a standard library module, and a module using it imports that one.

**`Fn2` and its siblings take no effect row** (D19). Being uncurried and having effects are orthogonal, so `Fn2 a b (IO c)` covers what PureScript needs `EffectFn2` for.

**What may fault, and on which inputs, is unsettled.** An unchecked array index can fail, and no Dawn type describes it; a fault is not an effect and no handler intercepts it ([Semantics](08-Semantics.md)). Enumerating the faulting primitives belongs to the surface specification.

## Names that are not `Prim`

`List` is a standard library type, not a `Prim` one; the vertical slice of [Examples](13-Examples.md) declares its own `Main.List`.

`Partial` is not here either. It is an ordinary effect declaration of the standard library ([Effects](05-Effects.md)), and `fail` is derived notation for `perform Partial.abort [τ] Prim.Unit` that elaboration expands. The Core type checker never mentions either.

## What is not a name at all

**`merge` is a term constructor, not a value of `Prim`.** The type these documents give it,

```text
forall (r : Row Type). forall (s : Row Type). r # s => Record r -> Record s -> Record ( r ⊎ s )
```

describes the rule for `merge e1 e2`; it declares no global name. The same holds of `extend`, `select`, `restrict`, `update`, `inject`, `weaken`, and `absurd`. Writing them as values as well as constructors would be the duplication Core exists to avoid.
