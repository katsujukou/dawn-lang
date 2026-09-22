# Mid IR

Mid IR is the backend-independent stage between Typed Core and a target. It is
an **A-normal form**: every intermediate result is named by a binding, every
argument is an atom, and every control construct stands in tail position.

Core defines what a program means. Mid IR fixes what a program *does*, in terms
every backend can carry out: allocating a closure, calling a known function,
building and taking apart a data value, jumping to a join point, installing a
handler, capturing a continuation. It commits to none of how a target
represents those things. JavaScript functions and objects, Wasm GC structs, and
layouts in linear memory belong past this stage and must not appear in it.

Three lowerings consume Mid IR: bytecode ([Bytecode](../05-Backend/01-Bytecode.md)),
JavaScript, and WebAssembly.

## What Mid IR settles, and what it leaves open

| Settled here | Left to a backend |
| --- | --- |
| Which functions exist, and what each captures | How a closure is laid out |
| Where a call is known and where it is not | The calling convention |
| Which values are data, records, variants, closures, or opaque | How each is represented |
| Where control transfers, and whether a transfer is a jump or a call | Which machine construct realizes it |
| Which handler clause binds a continuation | How a continuation is captured |
| The order in which effects occur | Nothing; the order is normative |

## Representation types

Every binding in Mid IR carries a **representation type**, written `Rep`. A
`Rep` says which class of value flows through a binding. It is not a type in the
sense of Core: it has no rows, no quantifiers, no constraints, and no effect
row.

```text
Rep ::= Int | Number | Char | String | Boolean     the literal classes
      | Clos                                        anything callable
      | Rec                                         a record
      | Variant                                     a variant
      | Data T                                      a value of the data type T
      | Opaque                                      a value only a foreign observes
      | Val                                         unknown
```

The classes correspond one for one to the canonical-value classes `Σ` records
of an intrinsic type constructor ([Prim and Base](../06-Modules/02-Prim-and-Base.md)),
with two additions: `Data T` for a declared data type, which has constructors
rather than a canonical class, and `Val` for a position whose Core type is a
variable and so says nothing.

`Clos` covers every callable value alike: a closure, a partially applied
constructor or foreign, and a continuation a handler clause received. What
unites them is that applying one is the only thing to do with it.

`Rep Int` names a class and not a width. What `Int` and `Number` range over is
unsettled ([Open Questions](../07-Open-Questions/01-Open-Questions.md)), and Mid IR
neither settles it nor depends on it.

### The map from a Core type

`rep` is total on well-kinded types of kind `Type`.

```text
rep( Prim.Int )                     = Int            and likewise for the other literal types
rep( Prim.Function τ ρ σ )          = Clos
rep( Prim.Record ρ )                = Rec
rep( Prim.Variant ρ )               = Variant
rep( T τ̄ )   where T is a data entry of Σ        = Data T
rep( T τ̄ )   where T is intrinsic opaque         = Opaque
rep( forall (a : κ). τ )            = rep( τ )
rep( C => τ )                       = rep( τ )
rep( a τ̄ )                          = Val
```

A `forall` and a constraint arrow contribute nothing, because the abstractions
they type are erased and a value of such a type is a value of its body. Applying
a type variable leaves the head unknown, which is `Val`.

### A representation type is descriptive

**A `Rep` records what the Core type already said; it obliges a backend to
nothing.** Mid IR has no coercion node, and no instruction converts between
representation types. A backend that keeps one uniform representation ignores
`Rep` entirely. A backend that wants an unboxed `Int` or a Wasm GC struct per
data type reads `Rep` to decide where it may, and inserts whatever conversions
its own choice requires.

Making `Rep` prescriptive instead would mean deciding boxing in Mid IR, which is
a representation decision and therefore the one thing this stage exists not to
make.

## Names

```text
Local     a binding within one function; unique within that function
JoinName  a join point; unique within the function that binds it
FuncId    an entry of the module's function table
GlobalRef a fully qualified top-level value or foreign, as Core names it
CtorRef   a fully qualified data constructor
```

Locals are unique within a function rather than globally, so a backend may map
them onto a flat frame without renaming. Core's names are already unique up to
α-equivalence ([Kinds and Types](../03-Typed-Core/01-Kinds-and-Types.md)), and
translation preserves that.

## Atoms

An atom denotes a value without computing, allocating, or performing anything.
Atoms are what every other form takes as an argument, and that is the whole of
A-normal form.

```text
atom ::= local x                   a binding in scope
       | lit c                     a literal
       | global M.x                a top-level value, by reference
       | const M.Ctor              a constructor of arity 0
```

`global M.x` reads a top-level value that module initialization has already
stored, which is a load and not a call. **A foreign is never an atom**: a
foreign whose declared arity is 0 saturates as soon as its spine is formed and
therefore calls its implementation ([Semantics](../03-Typed-Core/06-Semantics.md)),
and one of arity `n > 0` referenced bare is a partial application.

`const M.Ctor` is a saturated constructor of arity 0, which allocates nothing
new: `Prim.Unit`, `Prelude.Nothing`, a `Nil`. A backend builds one value per
constructor per module and shares it.

## Computations

A computation is bound by a `let` or stands in tail position. It is the only
place an effect, an allocation, or a call occurs.

```text
comp ::= pure atom                                 name a value

       -- calls
       | callk M.x [ā]                             |ā| equals M.x's arity
       | callu a [ā]                               the callee is not known statically
       | ffi   M.f [ā]                             a saturated foreign; may fault
       | ctor  M.Ctor [ā]                          |ā| equals the constructor's arity
       | pap   callee [ā]                          0 ≤ |ā| < callee's arity
       | closure f [ā]                             allocate a closure over function f

       -- data
       | field a M.Ctor j                          the j-th field of a constructor value
       | payload k a                               what a variant carries at key k

       -- records
       | recEmpty
       | recExtend k a1 a2   | recSelect k a
       | recRestrict k a     | recUpdate k a1 a2
       | recMerge a1 a2

       -- variants
       | inject k a          | absurd a

       -- effects
       | perform k.op a                            invoke an operation of the element keyed k
       | handle h f [ā]                            install h and call the body

callee ::= M.x | M.f | M.Ctor
```

**`handle` is a computation, and its body is a function of no parameters.** Its
value is what the handler's return clause produces, so binding it with a `let`
is all that is needed to use it, and no other form has to carry a destination
for it.

### Calls

**A call whose callee and arity are both known statically is a different
instruction from one that is not.** `callk` names a top-level value whose
definitional arity — the number of leading lambdas its erased right-hand side
has — equals the number of arguments supplied. `ffi` and `ctor` are the same
case for a foreign and a constructor, whose arities come from their declarations.

`callu` covers everything else: applying a local, applying a closure, applying a
continuation, and supplying more arguments than a callee takes. It is where
under- and over-application are resolved, and a backend implements it once.

**Folding a spine into one call is sound because an application evaluates its
argument before its function** (D35). Every argument of a spine reaches a value
before any application happens, so one multi-argument call performs exactly what
the nested applications performed, in the same order. Under the opposite order
the evaluation of `f x` would stand between the arguments of `f x y`, and
whatever it performed would move.

What the known/unknown split buys is that `callk` is a transfer to an entry
point whose arity is settled — no arity test, no under- or over-application to
resolve — where `callu` needs all three. `pap` has to exist either way, so the
split costs no machinery that avoiding it would save.

### Partial application

`pap` is a value. A constructor or a foreign applied to fewer arguments than its
arity, and a known global applied to fewer than its definitional arity, produce
one; applying it produces either another `pap` or, once saturated, the call.

Retaining this form is what keeps a partially applied constructor representable
([Implementation Plan](../01-Introduction/04-Implementation-Plan.md)). A backend
lowers a `pap` to a curried function or to an object carrying the callee, the
arity, and the arguments collected so far, as it prefers.

### Faults

`ffi` is the only computation that may produce a fault. A fault is not an effect:
no handler intercepts it, it appears in no row, and it is not the `Partial`
effect ([Semantics](../03-Typed-Core/06-Semantics.md)). It propagates out of every
construct including a handler, and a backend implements it as an abrupt
termination of the whole reduction.

## Expressions

An expression is the body of a function, of a join point, or of a branch.
Control constructs stand in tail position only; a `case` whose value is consumed
by a surrounding context is expressed by binding that context as a join point
and jumping to it. A `handle` needs none of that, being a computation.

```text
expr ::= ret a                                     the value of the enclosing function
       | let x : Rep = comp in expr
       | letrec { x_i : Rep = closure f_i [ā_i] } in expr
       | letjoin j (x̄ : Rep) = expr in expr
       | jump j [ā]
       | tail comp                                 a computation in tail position
       | switchCtor a { M.Ctor_i -> expr_i } [ default -> expr ]
       | switchLit  a { c_i -> expr_i }   default -> expr
       | switchKey  a { k_i -> expr_i }   [ default -> expr ]
       | if a then expr else expr
```

`tail comp` is what makes a tail call visible: a backend reads it as an
obligation to transfer control rather than to push a frame. Whether it can
honour that obligation for a given target is the backend's affair, but Mid IR
never hides which calls are in tail position.

`if` is `guard` with its condition already named. Core's `guard` is the one
sequential test in a decision tree; every `switch*` is a single dispatch whose
branches are mutually exclusive and whose written order carries no meaning
([Terms and Matching](../03-Typed-Core/04-Terms-and-Matching.md)).

`switchLit` has a mandatory default and `switchCtor` and `switchKey` have one
unless their branches exhaust, exactly as in Core. **Mid IR does not re-derive
local totality; it preserves it.** The Core type checker established it, and a
verifier over Mid IR checks the syntactic condition and nothing more.

### Occurrences are gone

Core dispatches on an **occurrence**, a path from a scrutinee such as
`s0 ! Main.Cons . 1`. Mid IR dispatches on an atom, and every step of such a
path is an explicit `field`, `payload`, or `recSelect` bound by a `let`.

Making projections explicit is what lets a backend see each one, and it costs
nothing: an occurrence is a projection, has no effect, and may be named once and
referenced any number of times.

### Join points

`letjoin` and `jump` carry over from Core unchanged but for the loss of types.
A join point is not a value, forms no closure, is jumped to only from tail
position, and **does not cross a function boundary**. Translation preserves
those properties rather than establishing them, Core having required them
already.

A join point lowers to a named block and a `jump` to a transfer naming it. That
correspondence is the reason Core carries join points at all
([Terms and Matching](../03-Typed-Core/04-Terms-and-Matching.md)).

## Functions and closures

**Mid IR has no nested function.** Every lambda of Core, the body of every
`handle`, every handler clause, and every return clause becomes an entry of the
module's function table, and the free variables it needed become an explicit
capture list.

```text
Function ::= { id       : FuncId
             , params   : [ (Local, Rep) ]
             , captures : [ (Local, Rep) ]
             , body     : expr
             }
```

`closure f [ā]` allocates a value of the function `f` over the atoms `ā`, which
fill its captures in order. Applying that value binds the parameters and makes
the captures available.

Closure conversion happens here rather than in a backend because a target may
have no nested function to fall back on: Wasm has none, and a Wasm GC backend
must be handed the capture list rather than have to compute it. A backend with
nested functions, such as JavaScript, may ignore the capture list and let its
host close over the variables; the list stays correct either way.

`letrec` binds a group of closures that may capture one another. A backend
allocates every closure of the group before filling any capture list, which is
what a mutually recursive group requires. Guardedness (D14) is what makes this
safe: each right-hand side is a function value, so no capture is read while the
group is still being built.

**A top-level recursive group captures nothing.** Its members refer to one
another by global name, so each is a closure over an empty capture list
([Semantics](../03-Typed-Core/06-Semantics.md)).

## Handlers and continuations

```text
handle h f [ā]

h ::= { key      : RowKey
      , return   : ClauseRef
      , clauses  : [ { op : OpName, form : full | fast, clause : ClauseRef } ]
      }

ClauseRef ::= { func : FuncId, captures : [atom] }
```

**The handler carries the key alone.** Core's handler writes the row element
whole because typing needs its payload to say which operations the clauses must
exhaust; reduction consults `key(ent)` and nothing else, so erasure keeps the
key ([Semantics](../03-Typed-Core/06-Semantics.md)).

### Everything a handler runs is a function

The body `f` is a function of no parameters, over the captures `[ā]`. So is each
clause, and so is the return clause: a clause is entered from a `perform` site
that lies at an arbitrary depth inside the body and in general in another
activation, and the return clause is entered when the body produces its value.
A `full` clause takes two parameters, the operation's argument and the
continuation; a `fast` clause and the return clause take one.

**The handler stands between the caller and the body, not inside either.**
Installing it and calling `f` is one step, and the value the whole `handle`
produces is what the return clause gives back. Three things follow, and each
would otherwise need a rule of its own.

**The result of a `handle` reaches its context by ordinary means.** It is the
value of a computation, so a `let` binds it. A body that instead ran in the
enclosing activation would have to say where the return clause's value goes,
and the return clause — being a function entered later — could not simply jump
to a join point of that activation to deliver it.

**Returning needs no special rule.** A function returns from its activation; the
handler is below the body's activation, so the body's return reaches it, runs
the return clause, and the return clause's own value goes on to whatever called
the `handle`. This is `handle v with h → e_r[x := v]` read as a machine step.

**A tail call inside the body keeps the handler.** It replaces the body's
activation, which the handler does not stand in, so the path from wherever
control ends up back to the marker and its return clause is unchanged. The same
holds of a tail call inside a clause.

Join points do not enter a `handle`. A function boundary already discards them,
so this is a consequence of the shape above rather than a restriction Mid IR
imposes; Core discards the join point context at a `handle` for the same reason.

### The two clause forms stay apart

`full` and `fast` are recorded on every clause, as Core records them (D28).
They carry no type information; what they say is which reduction applies, and a
backend lowers them differently.

| Form | What the backend does |
| --- | --- |
| `fast` | Call the clause with the operation's argument, the handler still installed. Control returns to the `perform` with the clause's value. **No continuation is constructed** |
| `full` | Capture the continuation up to and including this handler, call the clause with the argument and that continuation. The clause's value is the value of the `handle` |

**A `fast` clause is the reason the two are kept apart.** Implementing one asks
nothing of a backend beyond an ordinary call, so the cost of a continuation is
reserved for `full` alone.

### Continuations are not one-shot

**Nothing in Mid IR bounds how often a continuation may be applied.** A
continuation is a value of `Rep Clos`, applied by `callu` like any other, and no
form marks it or counts its uses.

This is a constraint on the representation and not merely an omission. Mid IR is
designed before effect lowering is written ([Implementation Plan](../01-Introduction/04-Implementation-Plan.md)),
so a representation admitting only one resumption would settle D18 by accident,
in a stage that has no standing to settle it. A backend whose continuations are
one-shot is non-conforming and says so; Mid IR records no such limitation on its
behalf.

## Modules

```text
MidModule ::= { name      : ModuleName
              , imports   : [ModuleName]
              , ctors     : [ { ref : CtorRef, owner : TyName, tag : Int, arity : Int
                             , isNewtype : Boolean } ]
              , effects   : [ { ref : QEffName, ops : [OpName] } ]
              , foreigns  : [ { ref : GlobalRef, arity : Int } ]
              , functions : [Function]
              , globals   : [ { ref : GlobalRef, init : GlobalInit } ]
              , exports   : [GlobalRef]
              }

GlobalInit ::= run  FuncId        evaluate a function of no parameters and store the result
             | func FuncId        store a closure over an empty capture list
```

The constructor table is what survives of the data declarations: a tag, an
arity, the type that owns them, and whether that type is a `newtype`. Field
types do not survive, `Rep` on each binding carrying what a backend needs of
them.

**`isNewtype` is carried because nothing else recovers it.** A `newtype` is one
constructor of one field, which an ordinary data declaration may also be, so a
backend that erases the representation cannot tell the two apart from the shape
of the table. Mid IR is all that `lower` receives, so the flag has to reach it
here or it reaches no backend at all. The Core type checker is what verified the
shape the flag claims ([Modules](../06-Modules/01-Modules.md)), so nothing
downstream re-checks it.

The effect table records which operations each effect declares. No signature
survives: an operation's argument and resume types were consumed by type
checking.

**A `perform` and a handler clause name an operation by its own name alone**,
and the effect it belongs to appears in neither. A `perform` finds its handler
by key, and a handler's clauses are the operations of exactly one effect, so the
name cannot be ambiguous where it is looked up. A row key is likewise compared
for equality and nothing else. Both are interned, so that a backend compares
integers rather than strings.

Identifying an operation this way is what keeps translation from needing the
ambient effect row: the row is erased, and the key at a `perform` site does not
by itself say which effect the element carries.

**`globals` is an ordered list, and the order is the dependency order Core
required.** A `run` entry is a `nonrec` declaration, whose right-hand side is
evaluated once when the module is initialized; a `func` entry is a member of a
top-level `rec` group, installed without evaluating anything. Evaluating eagerly
in declaration order is observable, a divergent right-hand side hanging
initialization whether or not anything refers to it, and Mid IR preserves that
rather than deferring to first reference ([Semantics](../03-Typed-Core/06-Semantics.md)).

## What Mid IR does not have

Each of the following is present in Core and absent here. The right-hand column
says what became of it.

| Absent | Where it went |
| --- | --- |
| Types, kinds, rows, constraints | `Rep` on each binding; everything else was consumed by type checking |
| `Λ`, `e [τ]`, `e [•]`, `T [[κ̄]]`, `M.x [[κ̄]]` | Erased |
| `openEff`, `openEffC` | Erased. Both are the identity at run time |
| `weaken` | Erased. A `switchKey` dispatches on the key a variant actually carries |
| Occurrences | Explicit `field`, `payload`, and `recSelect` bindings |
| Nested lambdas | The function table, with explicit captures |
| `fail` | It was never a node: Core writes `perform Partial.abort`, and translation carries that through |
| The payload of a handled row element | The handler's key |
| Curried application chains | `callk`, `callu`, `ffi`, `ctor`, and `pap` |

## Invariants

A verifier over Mid IR checks the following. None of it re-derives anything the
Core type checker established; each is a property translation is obliged to
produce and a later pass is obliged to preserve.

1. Every argument of every computation is an atom
2. Every `local` is bound by a parameter, a capture, a `let`, a `letrec`, or a join point parameter of an enclosing scope, and no local is bound twice in one function
3. Every `jump` names a join point of an enclosing scope in the same function, with matching arity, and stands in tail position
4. Every function a `handle` names — its body, its clauses, its return clause — is an entry of the function table, so no join point of the `handle`'s own scope reaches any of them
5. Every branch of every `switch*` and `if` ends in `ret`, `tail`, `jump`, or another control construct
6. `switchLit` has a default; `switchCtor` and `switchKey` have one or exhaust
7. `callk` supplies exactly the callee's arity, as do `ffi` and `ctor`; `pap` supplies fewer
8. Every `closure f [ā]` supplies exactly the captures of `f`
9. Every `FuncId`, `CtorRef`, `QEffName`, and operation index resolves in the module's tables
10. A handler names no operation twice, and each clause function has the arity its form requires: two parameters for a `full` clause, one for a `fast` clause and for the return clause

That a handler's clauses **exhaust** the operations of the effect its element
carried is not among them. The element's payload is what said which operations
those are, and it was erased; the Core type checker established exhaustiveness
while the payload was still there ([Typing Rules](../03-Typed-Core/05-Typing-Rules.md)).
