# Prim and Base

Four layers stand between the trusted core and an application. Each is settled
by someone different, which is what keeps the boundaries between them worth
drawing.

| Layer | What it holds | Settled by |
| --- | --- | --- |
| `Prim` | the types and constructors the rules of Core name | the Core specification |
| `Base.*` | the versioned runtime ABI surface a backend implements | the ABI specification and backend conformance profiles |
| `Prelude` | the default portable environment: foundational types, classes, ordinary names, and syntax macros | the standard library specification |
| portable libraries — `Data.*`, `Effect.*`, and the rest | portable API written in Dawn over `Prelude` and, where necessary, `Base.*` | their library packages |

`Prim` is visible without being imported; every other layer is imported like
anything else. A module touching `Base.*` says so in its header (D22), so which
code depends on the ABI surface is readable from headers alone.

**A portable library is one to which neither Core nor the ABI gives any
privilege.** The classification is not about who publishes it: `Data.List` is
distributed with the compiler and is a portable library all the same, holding
no standing that a package written by anyone else lacks.

## The dependency direction is one-way

```text
Prim
  ↑
Base.*
  ↑
Prelude
  ↑
Data.* / Effect.* / user packages          Js.* / Wasm.*
  ↑                                              ↑
applications
```

A portable library may reach past `Prelude` to `Base.*` where it must —
`Data.Array` wraps `Base.Array`, while `Effect.State` needs nothing of the ABI
and is written in Dawn alone. What no layer does is reach upwards.

**A target namespace stands beside the portable libraries rather than within
them.** `Js.*` and `Wasm.*` sit at the same depth as `Data.*`, and may name what
`Prelude` owns as freely, so `Js.String.fromJSString` returning a `Maybe` is
well placed where the same signature in `Base.String` would not be. Two things
separate them from a portable library: the ABI manifest may supply a target
namespace with intrinsics, and a program importing one has thereby chosen its
target. `Prelude` depends on neither.

### Who owns a foundational identity

Keeping the direction one-way requires deciding where the **identity** of a
foundational type or effect is declared, separately from where its operations
are written. Otherwise `Prelude` and a library downstream of it each need the other.

| Identity | Owned by | Operations |
| --- | --- | --- |
| `List` | `Prelude` | `Data.List` |
| `Maybe` | `Prelude` | `Data.Maybe` |
| `Array` | `Base.Array`, being a manifest intrinsic | `Data.Array`, with literal syntax from `Prelude` |
| `Partial` | `Prelude` | handlers, wherever they are written |
| `State`, `Except` | the `Effect.*` library declaring each | the same library |

`Array` is the case where the split does visible work. The `[ … ]` macro belongs
to `Prelude`, and because the type is owned upstream, that macro expands to the
low-level construction entries of `Base.Array` rather than to anything in
`Data.Array`. `Data.Array` then adds a convenient API over the same
`Base.Array.Array`, and `Prelude` does not depend on it.

`Partial` is owned by `Prelude` for a different reason: elaboration emits
`perform Partial.abort` for a non-exhaustive match (D10), so the name has to be
resolvable wherever a program is elaborated. **That is a dependency of
elaboration, not of Core** — the Core type checker still never mentions
`Partial` or `fail`, and an effect declaration is what it finds in `Σ`.

What makes the name resolvable is a rule about the surface, not a privilege.

```text
`import Prelude` is written, as every dependency but `Prim` is.
Elaboration emits the fully qualified `Prelude.Partial` for a non-exhaustive match.
A module that does not import `Prelude` therefore cannot contain one.
```

The dependency is on the **module**, as every dependency is: a header names
`Prelude`, never a name within it. Nothing has to enter scope unqualified
either, since what elaboration emits is already fully qualified.

Writing the import is what keeps D22 intact, and it keeps `Prim` the one thing a
header omits. `Prelude` is an ordinary module in every other respect: the
surface header names it, and the Core header records it as it records any import
([Modules](09-Modules.md)). `Prelude.Partial` reaches `Σ` by the ordinary route rather than
being conjured by the elaborator; without the import an emitted `EffectKey`
would name an effect no `Σ` holds, and the `perform` would not typecheck. A
non-exhaustive match in a module that does not import `Prelude` is reported at
the match, and what it asks for is the import.

## What a backend owes the standard environment

Supporting `Prelude` is what lets a backend run ordinary Dawn, so the condition
for it is stated against `Prelude` rather than against `Base.*` as a whole.

```text
backend supports the Base ABI profile that Prelude requires
```

Which profile that is belongs to the version of `Prelude` in question, so a
backend states what it implements once and the condition is decided by
comparison. A backend meeting no more than `core-runtime` fails this condition
and is conformant all the same, at the profile it claims: belonging to `Base.*`
and being obligatory stay separate questions.

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
| **outside `Prim`** | `Main.List`, `Prelude.Maybe` | `Base.Array.Array`, `Base.Function.Uncurried.Fn2` |

`Prim.Unit` is an ordinary data type that happens to be reserved; `Base.Array.Array` is intrinsic and imported like anything else.

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
| `Variant` | `inject`, `weaken`, `absurd`, and the residual type in a `switchKey` default |
| `Int`, `Number`, `String`, `Char`, `Boolean` | `litType`, which gives a literal its type |
| `Boolean` | also the condition of a `guard` |
| `IO`, `Unit` | the entry point `main : IO Unit` |

`Prim` declares one data type.

```text
data Unit = Unit
  -- Prim.Unit : Unit        tag 0, arity 0
```

`Unit` is a data declaration rather than a literal, so a `switchCtor` exhausts it with one branch. As a literal it would fall under `switchLit`, where a default is mandatory because literals cannot be exhausted ([Typing Rules](07-Typing-Rules.md)).

**`Array` and the uncurried families are not here.** Core names neither, and neither needs to be reachable without an import; they are intrinsic all the same, and they belong to `Base.*`, which the section below places.

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
├─ Core intrinsic       Function, Record, Variant, the literal types, IO
└─ manifest intrinsic
   ├─ portable  Base.*        Base.Array.Array, the uncurried families
   └─ target    Js.*, Wasm.*  Js.String.JSString, opaque handles
```

Both are beyond a user's reach. They differ in who settles them: a **Core intrinsic** is fixed by this specification, a **manifest intrinsic** by the versioned ABI specification that a compiler and its backends implement together.

The second splits again by portability, and the split decides where an entry lives rather than how it behaves.

A **portable** manifest intrinsic is one whose observable meaning is the same on every backend, and it lives in `Base.*`. Portable is not the same as universally present: which backends owe it is what a profile says, so an entry of `Base.Array` is owed by every backend claiming a profile that contains it. A backend claiming `core-runtime` alone owes none of `Base.Array` and is conformant all the same, whether or not it happens to supply some.

A **target** manifest intrinsic is one only some targets have, and it lives under the namespace naming that target — `Js.*`, `Wasm.*` — so that a program naming one has thereby chosen its target.

Both reach `Σ` by the one route, `Σ_ABI(M)`, and the ABI manifest names modules of both kinds.

**A target namespace is a root segment, not a prefixed path.** `Js.String` rather than `Platform.JavaScript.String`: the target is what the first segment says, and reading `import Js.String` in a header is what tells a reader the module is not portable. Which roots exist is not open-ended — the ABI manifest names them, one per target it describes, and package resolution owns each as it owns `Base` (above), so no ordinary package may claim `Js` or `Wasm`.

**A build imports the root of the target it is building for, and no other.** The ABI manifest knows several roots and a build selects one target, so target validation rejects a module whose header names a different root. Importing `Js.String` and `Wasm.String` in one build is the same failure met twice over, and it is caught where the target is known rather than left to produce a program that cannot be lowered.

### The canonical-value class

Having no constructors, an intrinsic type gets its values another way. Which way is the entry's **canonical-value class**, and there are five.

| Class | Type constructors | Canonical form | What examines one |
| --- | --- | --- | --- |
| `intrinsic literal` | `Int`, `Number`, `String`, `Char`, `Boolean` | a literal | `switchLit`, `guard` |
| `intrinsic function` | `Function` | `λ`, an unsaturated spine, `openEff`, `rec_i` | application |
| `intrinsic record` | `Record` | `{}`, `extend` | `select`, `restrict`, `update`, `merge` |
| `intrinsic variant` | `Variant` | `inject`, `weaken` | `switchKey`, `absurd` |
| `intrinsic opaque` | `IO`, and every manifest intrinsic | `opaque ω [τ]` | nothing |

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

A manifest intrinsic reaches `Σ` the same way, through the ABI manifest, and is then imported by name like any other declaration.

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

`Σ_ABI(M)` is what the ABI manifest supplies to `M` itself, and is empty for every module it does not name; the ABI manifest names `Base.*` modules and the target namespaces it describes, and no others, and the section on manifest intrinsics below says what it holds and why it comes before the module's own declarations.

Three consequences are worth stating.

**`Prim` is reserved, and `Base` is owned.** Core names are fully qualified, so a module declaring `Int` contributes `Main.Int` and collides with nothing. What must be forbidden is a module supplying a rival `Prim.Int`, or a rival `Base.Int.add` beside the one a backend implements — but the two are forbidden by different parties, and conflating them puts a condition in the checker that the checker cannot decide.

`Prim` is a reserved module name, and **the Core type checker rejects a module named `Prim`**. It can: the compiler builds `Σ_Prim` itself, so a second `Prim` rivals something the checker holds.

`Base` is a reserved prefix, and **ownership of it is verified by package resolution, not by the Core type checker**. The modules of `Base.*` are ordinary source — `foreign` declarations with the manifest supplying what type constructors they need — so nothing in a Core module, or in the `Σ` it is checked against, tells the ABI implementation of `Base.Int` from a forgery of it. What decides is which package a module came from, and only the package implementing the ABI may claim a name under `Base`. A resolver enforces that against the ABI manifest before any module reaches the checker.

Handing the checker a provenance to trust would not improve on this. It would verify nothing, and a trusted unchecked input is what the `newtype` flag is deliberately not ([Modules](09-Modules.md)).

Within a module, declaring one name twice in a namespace is ill-formed as it is anywhere.

**Header completeness is unaffected** (D22). A module's header determines its dependencies, and `Prim` is a dependency of every module without exception, so a build system needs no entry to discover it. Nothing has to be written because nothing varies. `Base.*` is different: a module using `Base.Array.Array` imports `Base.Array`, and the header says so.

**Linking includes `Prim`.** The global environment `G` of [Semantics](08-Semantics.md) is built from `G_Prim`, which holds the data constructors of `Prim` — `Prim.Unit` alone — beside the definitions of the imported modules. `Prim` is not among those imports, so without `G_Prim` a `Prim.Unit` in the module would have nothing to unfold to and condition (1) of `Σ ⊨ G` would fail.

## The Base ABI surface

`Base.*` is the versioned runtime ABI surface. Its declarations are ordinary
`foreign` declarations, checked where they are written like any other (D23,
well-kindedness); what sets the layer apart is the obligation on the other
side, that a backend supply a conforming implementation for each.

```text
Base.Int.add                 : Int -> Int -> Int
Base.Int.sub                 : Int -> Int -> Int
Base.String.length           : String -> Int
Base.String.codePointAt      : Int -> String -> Char    -- faults out of range
Base.Array.Array             : Type -> Type            -- manifest intrinsic
Base.Array.unsafeIndex       : forall a. Array a -> Int -> a
Base.Function.Uncurried.Fn2  : Type -> Type -> Type -> Type   -- manifest intrinsic
Base.IO.pure                 : forall a. a -> IO a
Base.IO.bind                 : forall a b. IO a -> (a -> IO b) -> IO b
```

**A public `IO`, `Int`, or `Array` module is ordinary Dawn code over `Base.*`.**
Nothing obliges `Prelude` or a portable library to expose these names as they
stand; the layers above are where a portable API is shaped.

### Implementation is what varies, not meaning

A `Base` operation has one observable meaning, fixed by the ABI specification,
and backends differ only in how they implement it. A backend free to choose
what `Base.String.length` returns would give one Core term two meanings, which
is what the backend independence of Mid IR exists to prevent.

Representation is a separate matter and stays free. A JavaScript backend may
hold a `String` as a JavaScript string and a Wasm backend as UTF-8 bytes; what
neither may do is let that choice reach the result of a `Base` operation.

### Profiles

Obligation is graded, and a **profile** is a named set of `Base` entries a
backend undertakes to implement.

| Profile | Contents |
| --- | --- |
| `core-runtime` | `Base.IO.pure` and `Base.IO.bind`, together with the execution D25 places outside Core: native leaf actions, world state, and the invocation of `main` |
| `standard` | `core-runtime`, together with `Base.Int`, `Base.String`, `Base.Array`, the uncurried families, and whatever else the `Prelude` of a given version requires |

**A profile is a floor, not a ceiling.**

```text
A backend implements every entry of every profile it claims.
It may implement further entries, which its manifest records.
```

A small backend offering `core-runtime` and part of `Base.Int` is expressible as
it stands: it claims `core-runtime`, records the arithmetic entries it supplies,
and claims `standard` not at all. What decides whether a program builds is the
manifest; a profile is the shorthand a backend claims, not the limit of what it
may hold.

A backend claiming `core-runtime` alone can run a program that performs no
arithmetic; it is conformant at that profile and not at `standard`. Saying so is
more precise than saying that programs using arithmetic happen not to run.

`standard` is the profile the condition above names, so which entries it holds
moves with the version of `Prelude` rather than being fixed once. A portable
library reaching past `Prelude` to a `Base` entry the backend manifest records
nowhere — neither in a profile it claims nor among the entries it adds — is what
target validation rejects.

### Where obligation is recorded

**Not in `Σ`.** `Σ` answers a question about type checking, and for a `Base`
entry the answer is the same as for any other `foreign`.

```text
Base.Int.add : Int -> Int -> Int        declared type, trusted
                                        every arrow pure (D23)
```

Which backends implement it is a fact about targets and linking, and it belongs
to a manifest. Two are in play and they answer different questions: the
**ABI manifest** defines the surface and the profiles over it, once per version,
while a **backend manifest** states what one backend implements — the profiles
it claims, and any entries it adds beyond them.

```text
-- ABI manifest
ABI version: dawn-base-0.1

profiles:
  core-runtime:
    Base.IO.pure
    Base.IO.bind

  standard:
    includes core-runtime
    Base.Int.*
    Base.String.*
    Base.Array.*
    Base.Function.Uncurried.*
```

```text
-- backend manifest, for one small target
implements profile: core-runtime
implements also:    Base.Int.add, Base.Int.sub
```

Three stages then divide the work, and none of them duplicates another.

| Stage | What it establishes |
| --- | --- |
| type checking | the declared type is well-kinded and every arrow is pure (D23) |
| target validation | the backend manifest records every `Base` entry the program uses, through a profile it claims or beyond them, and every target root the program imports is the selected target's |
| linking | `Σ ⊨ G` condition (3): each `δ_f` returns what it claims, performs nothing observable to Core, and terminates ([Semantics](08-Semantics.md)) |

**An unsupported entry is rejected at target validation, not at run time.** A
program naming a `Base` entry the chosen backend does not implement fails to
build, rather than building and faulting where the call is reached.

### What the ABI specification must fix per entry

- **Observable meaning**, in terms that name no backend
- **Whether it may fault**, and on which inputs ([Semantics](08-Semantics.md))
- **Whether it returns `IO`.** An entry whose effect is observable from outside
  returns `IO`, mutable allocation included: a `Base.Array.unsafeNew` creating a
  mutable array returns one. An allocation whose mutation no one can observe may
  be pure

**A `Base` signature ranges over `Prim` types and portable manifest intrinsics.** A standard
library type such as `Maybe` standing in one would fix that type's
representation for every backend, and would make the ABI surface depend on the
layer built over it. A leaf that can fail therefore faults or returns a sentinel,
and a portable library is where a total wrapper is written. What mechanism, if
any, should enforce this is open ([Open Questions](14-Open-Questions.md)).

### `Base.IO.pure` and `Base.IO.bind`

```text
foreign Base.IO.pure : forall a. a -> IO a
foreign Base.IO.bind : forall a b. IO a -> (a -> IO b) -> IO b
```

Their `pure` and `bind` are distinct from the `Prim.IO` type constructor they
are typed with. **`Base.IO` is imported like any other module**, so a module
using them names it in its header and header completeness is untouched (D22).

The value a saturated `Base.IO.pure` returns is opaque, `IO` having neither
literals nor constructors to be built from ([Semantics](08-Semantics.md)).

**The continuation of `Base.IO.bind` is a pure arrow.** Every arrow in a
`foreign` type has an empty effect row (D23), so `( a -{f}-> IO b )` cannot be
declared; and the semantics would not hold either, since deferring `k` until the
`IO` is executed would run the residual effect `f` outside the dynamic context
of the handler that installed it ([Effects](05-Effects.md)).

Executing these two is the runtime ABI's obligation (D25), which is why they are
fixed here rather than left to the surface, and why they alone constitute the
`core-runtime` profile.

## Text: the meaning is portable, the representation is not

`String` is a sequence of **Unicode scalar values**, and `Char` is one. This is
the meaning every backend presents, whatever it holds in memory.

| | Representation | Free to choose |
| --- | --- | --- |
| JavaScript backend | a JavaScript string, UTF-16 code units | yes |
| Wasm and native backends | UTF-8 bytes | yes |
| what a `Base.String` operation returns | scalar values, counted and indexed as such | **no** |

Splitting the two is what keeps the same program computing the same thing
everywhere. Were `String` instead a sequence of whatever code unit the target
holds, `length "😀"` would be 2 on JavaScript, 4 on a UTF-8 backend counting
bytes, and 1 on one counting scalars — a difference in the meaning of a program
rather than in its representation, reaching `switchLit`, equality, and every
decomposition into `Char`.

The cost falls where representation and meaning diverge: a JavaScript backend
implements `Base.String.length` as a count of scalar values rather than as
`.length`, and a slice never divides a surrogate pair.

### Lone surrogates

A JavaScript string may hold an unpaired surrogate, which is not a scalar value.
**A Dawn `String` may not.** A literal is a sequence of scalar values, a `Char`
is a scalar value, and a string arriving through the FFI is validated.

Code that must carry a JavaScript string through unchanged uses an opaque type
of its own rather than `String`, and that type is a target manifest intrinsic of
the JavaScript namespace.

```text
-- ABI manifest
module Js.String
  intrinsic opaque JSString : Type
```

```purescript
module Js.String (JSString, fromJSString, fromJSStringLossy, toJSString) where
  import Prelude

  foreign fromJSString      :: JSString -> Maybe String
  foreign fromJSStringLossy :: JSString -> String
  foreign toJSString        :: String -> JSString
```

A `Maybe` may stand here where it may not in a `Base` signature: `Js.String` is
a target module rather than part of the portable ABI, so it sits downstream of
`Prelude` and may name what `Prelude` owns.

### Naming says which unit is meant

An operation names the unit it counts in, so that no reader has to infer it.

| Name | Unit | Where it lives |
| --- | --- | --- |
| `codePointAt` | Unicode scalar value | `Base.String`, being portable |
| `utf16CodeUnitAt` | UTF-16 code unit | `Js.String`, or an encoding library |
| `utf8ByteAt` | UTF-8 byte | the namespace of the target that has it, or an encoding library |

A name such as `codeAt` says none of the three and is not used.

**Target-specific operations live in the namespace of their own target, not in
`Base.*`.** Both are imported, so by D22 a module observing UTF-16 directly says
as much in its header — `import Js.String` names the target in its first
segment — and code that is portable is distinguishable from code that is not by
reading headers. Using UTF-16 inside a backend is unremarkable; making it
observable through the ordinary `String` is what would cost portability.

## Literal domains that remain open

The types of literals are settled above, and so is what `String` and `Char`
range over. **What `Int` and `Number` range over is not.**

What Core requires of them is narrow: `switchLit` demands that its literals be
distinct, so literal identity must be decidable. What Core does not settle is
the range of `Int`, nor the representation of `Number` together with how NaN and
signed zero behave under that identity.

The question is wider than the values themselves, since which surface token
denotes which Core value belongs to it: `42`, `0x2a`, and `0b101010` are one
literal, and `"\n"` and `"\u{A}"` are another. `switchLit` compares the value,
never the spelling.

These are recorded as open ([Open Questions](14-Open-Questions.md)). Until they
are settled, **the choices an implementation happens to make are not the
specification** — that the first compiler is written in PureScript does not make
Dawn's `Int` a 32-bit one.

## Manifest intrinsics, which live outside `Prim`

**The ABI manifest supplies type constructors and nothing else.** It is not source, and no module may write an intrinsic entry; this is how the ABI surface states what it supplies and to whom.

```text
-- ABI manifest
module Base.Array
  intrinsic opaque Array : Type -> Type

module Base.Function.Uncurried
  intrinsic opaque Fn2 : Type -> Type -> Type -> Type
```

The operations are ordinary source, written in the module the manifest names.

```purescript
module Base.Array (Array, length, unsafeIndex) where
  foreign length      :: forall a. Array a -> Int
  foreign unsafeIndex :: forall a. Array a -> Int -> a
```

**`fromList` is not among them.** `List` belongs to `Prelude`, and a `Base`
signature mentions only `Prim` types and portable manifest intrinsics, so a conversion between
the two is `Data.Array`. Which construction entries `Base.Array` does supply, and
whether each is pure or returns `IO`, is part of the ABI content that remains
open ([Open Questions](14-Open-Questions.md)).

Splitting it this way keeps the manifest to what only it can express. A `foreign` is checked wherever it is written — every arrow pure (D23), the type well-kinded — and a manifest entry would either duplicate that or become a trusted input for no reason. It also leaves the module free to hold Dawn code beside its primitives, which a portable library needs: `Data.Array.mapArray` is written in Dawn and uses `unsafeIndex` ([Modules](09-Modules.md)).

Checking such a module therefore needs its own entries in scope before its declarations are collected. Writing `Σ_ABI(M)` for what the manifest supplies to `M` — empty for every module the manifest does not name — the collection of [Modules](09-Modules.md) reads:

```text
Σ_ty = Σ_Prim ∪ Σ_ABI(M) ∪ Σ_imp ∪ { the module's own data and effect declarations }
```

An importer sees the entry through `Σ_imp`, by the ordinary route. **What it sees is not a data type**: the import path is the same, the entry is not. `Base.Array.Array` keeps its `intrinsic opaque` class, so a `switchCtor` on it is as ill-formed in the importing module as anywhere else.

Core names neither `Array` nor `Fn2`, and the module a name lives in is a question of visibility rather than of status. Both are imported, and a header that omits them is incomplete.

That `Array` has first-class surface syntax is not a reason to move it. **The syntax, the type, and Core are three independent things**: a library syntax macro can expand `[ e1, e2 ]` into a call, leaving Core with an ordinary `foreign` application and an opaque value. Where a standard surface is wanted, it is the standard library that provides it.

Arithmetic is the same story without an intrinsic type of its own: `Base.Int.add : Int -> Int -> Int` operates on a Core intrinsic, so it needs no manifest entry and is an ordinary `foreign` of `Base.Int`. A module using it imports that one.

**`Fn2` and its siblings take no effect row** (D19). Being uncurried and having effects are orthogonal, so `Fn2 a b (IO c)` covers what PureScript needs `EffectFn2` for.

**What may fault, and on which inputs, is unsettled.** An unchecked array index can fail, and no Dawn type describes it; a fault is not an effect and no handler intercepts it ([Semantics](08-Semantics.md)). Enumerating the faulting entries, and the preconditions of each, belongs to the ABI specification.

## Names that are not `Prim`

`List` belongs to `Prelude`, not to `Prim`; the vertical slice of [Examples](13-Examples.md) declares its own `Main.List` rather than reaching for either.

`Partial` is not here either. It is an ordinary effect declaration of `Prelude` ([Effects](05-Effects.md)), and `fail` is derived notation for `perform Partial.abort [τ] Prim.Unit` that elaboration expands. The Core type checker never mentions either.

## What is not a name at all

**`merge` is a term constructor, not a value of `Prim`.** The type these documents give it,

```text
forall (r : Row Type). forall (s : Row Type). r # s => Record r -> Record s -> Record ( r ⊎ s )
```

describes the rule for `merge e1 e2`; it declares no global name. The same holds of `extend`, `select`, `restrict`, `update`, `inject`, `weaken`, and `absurd`. Writing them as values as well as constructors would be the duplication Core exists to avoid.
