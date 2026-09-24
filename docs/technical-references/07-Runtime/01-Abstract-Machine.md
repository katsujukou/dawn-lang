# Abstract Machine

*Steam* is the **bytecode interpreter** that executes a `.dmo`. The instruction
set, the continuation, the container, and the obligations all three impose are
[Bytecode](../05-Backend/01-Bytecode.md). **This document fixes the interpreter**:
what it is for, what a value is while it runs, how its stack is shaped, how a
module enters its registry, where a foreign implementation comes from, and how a
run ends.

It is not a virtual machine of the kind the JVM and BEAM are, and nothing here is
a step towards one. What it is instead is small enough to read and useful as it
stands, and it is what the REPL runs on.

## What Steam is for

**The REPL is Steam, and that is a delivered use.** Stella's read-eval-print loop
is a loop over this interpreter: an entered expression is compiled to a module of its
own and loaded against the modules already present, which is what keeps the container
free of whole-program indices ([Bytecode](../05-Backend/01-Bytecode.md)). The
interpreter therefore reaches users, and the module lifecycle below is written for
that use rather than for a batch compiler's — the session mode below is what the
shell talks to.

**The compiler is a user too.** Elaboration is split into policy, which is guest
Stella, and mechanism, which is the compiler's (D39): a synthesizer named by a
`⟨ τ by f ⟩` is an ordinary Stella function, and the compiler runs it on this
interpreter, reaching it by the resolved qualified name the constraint carries
([Elaborator API](../02-Surface-Language/03-Elaborator-API.md)).

**What that use shares is the machine, and not a protocol.** The registry, loading a
module at a time, resolving a name, and the interpreter running the code are the same
for it as for anything else. What it asks for beyond them is its own: a synthesizer is
a function, so it is **applied** to a goal the host holds; an `Elab` operation it
performs is answered by the host and **the same attempt continues** from that answer;
and an attempt the host abandons **discards what the run had reached**. Whether that
becomes a mode of its own or a capability the session mode gains is not settled
([Open Questions](../99-Open-Questions/01-Open-Questions.md)).

Two uses stand beside those, and neither reaches a user.

- **A second evaluator to compare the Core evaluator against.** One program run
  both ways gives the same value and the same sequence of observable effects, which
  exercises the whole of translation and lowering at once
  ([Implementation Plan](../01-Introduction/04-Implementation-Plan.md))
- **A way to run what the web backends cannot.** A continuation applied more than
  once is what D33 undertakes and what D18 records the v0.1 JavaScript and Wasm
  backends as lacking

## Two modes

Steam runs in one of two modes, and **the front end is what a user runs**: the
Stella CLI compiles, decides what Steam is given, and prints what comes back.

| | **Session** | **Run** |
| --- | --- | --- |
| lives | across many inputs | for one program |
| is given | one module, then a request naming what to report | every module of the program in dependency order, and the entry point by name |
| answers | the value that module's declaration holds | the `IO` of the entry point, executed |
| ends | when the front end closes it | when that `IO` has been executed, or at the first failure |

**What this mode fixes is the loading half**, which the compiler's use shares: a
module at a time, and a request naming what to report. Running a synthesizer asks for
more than that, and how it asks is open (above).

**Session is what the REPL is built on.** The shell belongs to the Stella CLI: it
parses, elaborates, type checks, and compiles an entry to a module of its own, hands
that module to a Steam running beside it, and prints the value Steam answers with
beside the type it checked. Steam holds the modules that accumulate and nothing of
the source.

**Run is one program, once.** The CLI builds the project to `.dmo` files, orders the
modules by their dependencies, hands Steam the list and the entry point, and Steam
loads them in the order it was given before executing that entry point.

**The entry point is named, not found.** Several modules may declare a `main`, a
`.dmo` carries no types and marks no entry point, and a list in dependency order says
nothing about which of them was meant — so the name comes with the list, as a
qualified name or as the module whose own `main` is meant. It is read from the
declaring module's globals and **not** through its exports: an entry point need not
be exported. What a process makes of the run afterwards — an exit status, and what it
is for a fault — belongs to the runtime ABI and is not settled
([Open Questions](../99-Open-Questions/01-Open-Questions.md)); what the mode fixes is
that the `IO` that global holds is executed to completion, or that a fault ends the
run.

**Steam resolves no module.** It neither reads an import graph to decide an order
nor looks for a file: what it is given is what it loads, and in the order it is
given. A module's `imports` is read as a **condition** — every one of them is
already in the registry, or the load fails — and never as a way to find anything.
Ordering is the front end's, which is where the source, the search paths, and the
build plan are.

## Scope

- **A reference interpreter running on Node**, written as a JavaScript application
- **Its input is a decoded and validated `.dmo`.** The bytes are the reader's
  concern ([Encoding](../05-Backend/02-Encoding.md)), and a module reaches the
  interpreter as tables it can index. Nothing here parses a byte
- **The host's values and the host's collector.** An `Int` is a JavaScript number,
  a `String` a JavaScript string, and what reclaims a value is the host
- **`Rep` is ignored.** Every value is held one way; `Rep` exists for a backend
  choosing a representation per class, and this one chooses none (D31)
- **No just-in-time compilation, no collector of its own, no register allocation,
  no native code generation, and no optimization of the code it runs**

**The interpreter is a JavaScript application rather than a Wasm one** (D38). It
runs where Node runs, a foreign written in JavaScript is callable directly, and one
written in Wasm is reached through a JavaScript adapter. An interpreter compiled to
Wasm would need bridges for strings, closures, continuations, and the JavaScript
FFI before it could run anything, and the REPL gains nothing from them.

## The core and the host

A **host** is what the interpreter runs on and reaches the outside world through.
The **core** is everything an instruction means, and it is written once so that a
second host changes no rule.

**A host is not always a command line.** For a session the compiler opens, the
compiler is the host: an `Elab` operation — unify these two, make a metavariable,
abandon the attempt — is a capability it supplies where another host supplies a
native action ([Elaborator API](../02-Surface-Language/03-Elaborator-API.md)).

| The core holds | The host supplies |
| --- | --- |
| the value representation, the stack, and dispatch | — |
| finding a marker, splitting a segment, applying one again | — |
| the operations of `PRIMS`, whose meaning the ABI fixes | — |
| the `Base` ABI entries it claims, `Base.IO.pure` and `Base.IO.bind` among them | — |
| a registry of names waiting to be filled | the adapter behind each of those |
| the shape of an `IO` value, and the loop that executes one | the actions an `IO` is built from |
| what a fault is, and that it discards the stack | where a report goes |

**The core names nothing of the host** — no dynamic import, no file system, no
path, no console, no clock — because what a program computes is Core's and the
ABI's. An interpreter whose host could decide any of it would give one `.dmo` two
meanings.

## What a value is

This is the interpreter's internal representation and **not a published ABI**: no
`.dmo` depends on it, and a foreign reaches it only through the boundary below.

| | The interpreter holds |
| --- | --- |
| `Int` | a JavaScript number, always an int32 (D37) |
| `Number` | a JavaScript number (D37) |
| `Char` | the integer of a Unicode scalar value (D27) |
| `String` | a JavaScript string, whose meaning is a sequence of scalar values |
| `Boolean` | a JavaScript boolean |
| data | `{ ctor, fields }`, `ctor` being a resolved constructor identity |
| record | a map from a `RuntimeKeyId` to a value |
| variant | `{ key, payload }`, `key` being a `RuntimeKeyId` |
| closure | `{ function, captures }` |
| partial application | `{ callee, args }` |
| continuation | a captured stack segment |
| `IO` | an opaque action |

**Everything but a closure's capture vector and a region cell is immutable**, which
is what lets the host's collector be the whole of memory management.

**Literal identity is equality of the value, with a `Number`'s bit pattern deciding
and all NaNs taken as one** (D37). `BRL` implements that rather than the host's
`==`, which identifies the two zeros and separates a NaN from itself.

## Keys, operations, and constructors are interned at load

**An index into a module's table is that file's own.** Two modules may hold the key
`SymbolKey "n"` at different `KEYS` indices, and a record one of them built is
selected from by the other; comparing the two indices compares nothing. The same
holds of `OPS`, since the `perform` and the handler that answers it need not be in
one module.

**At load every `KEYS` entry is interned into a table shared by every loaded
module, giving a `RuntimeKeyId`**, and every `OPS` entry likewise. Equal keys get
one id whichever module wrote them, the mapping from a module's own indices is
built once where that module is loaded, and nothing compares an index afterwards.

What holds an id rather than an index:

| | |
| --- | --- |
| a record's fields, and a variant's key | `RSEL`, `RRES`, `RUPD`, `BRK` compare ids |
| a handler marker's key, and the clauses under it | `PERF` finds a marker by id and a clause by an operation's id |
| a region frame's cell keys | `CGET` and `CSET` find the innermost frame declaring an id |

**A constructor resolves the same way.** A data value holds the identity a loader
resolved — the declaring module's name with the constructor's own — and not an index
into the tables of whoever built it. `BRC` in one module dispatches on values
another module constructed, so both must compare one thing.

## The execution loop

The interpreter holds five things.

```text
current activation
stack
module registry
global slots
the intern tables for keys and operations
```

An **activation** holds what one call is running.

```text
function          the function table entry it is inside
registers         one slot per local, the parameters first
closure           the captures CAPT reads
node, position    where it stands in that function's tree of Nodes
```

A **branch is not a call.** `BRIF`, `BRC`, `BRL`, and `BRK` select a `Node` of the
current activation and continue there, and a `JMP` writes its arguments into a join
point's slots as a parallel move and does the same. Nothing is pushed for either.

The control instructions are these. Every other instruction reads and writes
registers of the current activation, and what each one means is where the
instruction set is ([Bytecode](../05-Backend/01-Bytecode.md)).

```text
CALLK d, f, r…   push Resume { current activation, d }, then enter f with the
                 arguments in fresh registers

CALLU d, s, r…   by what s holds and how many arguments it takes
                   exactly       push Resume { …, d } and enter
                   too few       write a partial application into d
                   too many      push Resume { …, d }, then
                                 ApplyRemaining { the arguments past the arity },
                                 then enter with the arity's worth
                   continuation  push Resume { …, d }, then
                                 ApplyRemaining { the arguments past the first }
                                 where there are any, then copy the captured
                                 segment, push it, and resume at its top

TAILK f, r…      enter f, replacing the current activation and pushing no Resume
TAILU s, r…      as CALLU without the Resume: an argument past the callee's
                 arity, or past a continuation's one, pushes ApplyRemaining
                 alone, and the value reaches what is below

RET s            hand s to the top of the stack, by the table below

HNDL d, …        push Resume { current activation, d }, then a region frame where
                 the handler declares cells, then an owner marker, then enter the
                 body's closure
TAILHNDL …       the same without the Resume

PERF d, key, op, s
                 the innermost marker whose key is key
                   fast clause   push Resume { …, d } and call the clause with the
                                 argument; the stack otherwise stands
                   full clause   push Resume { current activation, resuming after
                                 this PERF, d }, then split at the marker
                                 inclusive — that entry among the removed — and
                                 call the clause with the argument and the segment;
                                 what the clause returns reaches what is below the
                                 marker
```

## The stack

**The host's call stack cannot carry this.** `PERF` searches the stack and splits
it, and a continuation is applied more than once; neither is a nesting of host
calls. So the stack is a structure of the interpreter's own, and **every entry says
what it does with a value that reaches it**.

```text
StackEntry
  = Resume          { activation, dest }
  | ApplyRemaining  { args }
  | HandlerMarker   { key, clauses, return clause, owner }
  | RegionFrame     { cells }
```

`Resume` is the only entry that carries a destination register. A tail call pushes
none, which is the whole of what makes it a tail call, and `TAILHNDL` differs from
`HNDL` in exactly that.

| A value reaching | What happens to it |
| --- | --- |
| `Resume { activation, dest }` | it is written into `dest` and that activation continues |
| `ApplyRemaining { args }` | it is applied to `args`, and what that produces reaches the entry below |
| an **owner** marker | the region frame below the marker closes first, then the return clause runs with the value, and what the clause produces reaches the entry below |
| a **reinstatement** marker | the marker pops alone and its return clause runs with the value; the frame it stood in is untouched, and what the clause produces reaches the entry below |
| a `RegionFrame` whose owner is gone | it pops with no return clause, and the value reaches the entry below |

The last three are the three completion paths, and a marker's `owner` flag is what
distinguishes them ([Bytecode](../05-Backend/01-Bytecode.md)). Nothing in a `.dmo`
carries that flag: an owner marker is one `HNDL` pushed, and a reinstatement is one
that arrived at the bottom of a re-pushed segment.

**Applying a continuation copies the segment.** What is copied is the register array
of each activation in it, the markers, and the region frames it contains — not the
values those hold, which are immutable and shared. This is the one thing a light
interpreter cannot leave out: re-pushing the captured entries instead would let one
application write over the state the next one needs.

**A continuation takes one argument, and may be applied to more.** A `handle`'s
answer type is a type like any other and may be a function type, so `k x y` is well
typed and folds to one `CALLU k [x, y]` (D30). The continuation's run-time arity is
one: the first argument is what the resumption resumes with, and the rest is pending
work, which is why its `ApplyRemaining` stands between the caller's `Resume` and the
segment. What the segment returns is then applied to the arguments that were left.

**The activation that performed the operation is inside the segment.** A `full`
clause's continuation begins at the `perform` and not after it, so the `PERF`
pushes that activation before splitting: the `Resume` it pushes carries the register
file, the point after the `PERF`, and the register the operation's value is written
into. Applying the continuation writes the value there and continues from that
point, which is what makes a resumption resume ([Bytecode](../05-Backend/01-Bytecode.md)).

**An over-application's pending work is on this stack too.** An `ApplyRemaining`
stands between the call that produced it and the value it waits for, so a `full`
clause capturing that stretch captures it — which is precisely what leaving it in
the host's call stack would lose.

## Loading, and the REPL's module lifecycle

There is no linker. There is a **persistent registry** of loaded modules, and
loading one is a short procedure against it.

```text
loadModule(dmo):
  every import is already in the registry, and every condition below holds
  intern the keys, the operations, and the constructors it declares
  open a slot for each global it declares, holding nothing
  build the tables of what it declares, under the names it declares them at
  resolve every reference against those tables and the registry
  initialize the globals in declaration order, against the working registry
  commit the module to the registry
```

**The slots come before the references because a resolved reference is a slot.** A
`GLOBALREFS` entry of this module's own name resolves to the slot this load has just
opened, and so does a `CALLEES` entry over one; resolving either against a registry
that does not hold the module yet is what the order above avoids.

**Initialization runs against a working registry**, which is the persistent one with
the candidate module beside it. It has to: a `run` global's own code reads that
module's constants, calls the closures its earlier `func` globals installed, and
names its own globals through `GLOBALREFS`, all of which need the candidate's tables
and slots to be reachable while nothing of it is yet loaded. The working registry is
private to the load.

**A module is committed only once it has initialized.** One whose initialization
faults leaves the persistent registry as it was, and the working registry is
discarded with it — which is what keeps a failed entry from being visible to the next
one.

**An interned identity is not taken back.** An identity belongs to a name rather than
to a module: two modules writing one key get one `KeyId`, and a failed load leaves at
most an identity nothing refers to. A later module declaring the same name is given
the same identity, which is the rule the tables exist for, so undoing an interning
would buy nothing and would need the machine to count what refers to one.

What loading refuses:

| | |
| --- | --- |
| A module whose name is already in the registry | one name is one module |
| A declaration whose qualified name belongs to another module | `CTORS`, `EFFECTS`, `FOREIGNS`, and `GLOBALS` are what **this** module declares ([Bytecode](../05-Backend/01-Bytecode.md)) |
| A constructor whose owner type belongs to another module | a `CTORS` entry comes from a `data` declaration of this module, so the constructor's name and the type it belongs to are both of it |
| Two declarations of one name in one namespace: two constructors, two effects, or two values — a global and a foreign among them | the tables are arrays and a name table is what loading makes of them, so which of two a name meant would otherwise depend on the order they were written in |
| An exported name that is not a value this module declares | `EXPORTS` names its own globals and foreigns, and nothing else |
| Two join points of one function under one name | a transfer names one of them ([Bytecode](../05-Backend/01-Bytecode.md)) |
| An import that is not loaded | nothing is resolved against a module that is not there |
| A reference to a module this one does not import | **a header says which modules a term may name**, and the order modules happen to be loaded in adds nothing to it. This is not the row above: the module may be loaded and still be one this one never imported |
| A global or foreign an imported module does not export | `EXPORTS` holds the value names a module publishes, its initialized globals and its foreign declarations alike |
| A reference that reaches the wrong kind of declaration | a `CTORREFS` entry must reach a constructor, a `FOREIGNREFS` entry a foreign, a `GLOBALREFS` entry a top-level value ([Bytecode](../05-Backend/01-Bytecode.md)) |
| A foreign with no implementation | resolution happens at load, so a program whose foreigns are incomplete does not start |
| An operation code the interpreter does not implement | at the profile it claims ([Prim and Base](../06-Modules/02-Prim-and-Base.md)) |

**What a count must be is the declaring module's to say, and this is where the
modules are together.** Every call in the code is read against the declaration it
reaches, so **a call a wrong arity produced is caught here** rather than where it
would run.

**What is checked are the calls and not the interface.** A `.dmi` is not read at
load, and nothing establishes that one was right: an entry no call used is caught by
nothing, and a `PAP` a wrong arity produced passes wherever it is still below the
true one — which is a partial application meaning exactly what it means
([Interface](../05-Backend/03-Interface.md)).

| The code holds | Why |
| --- | --- |
| A `CALLK` or `TAILK` supplying other than the definitional arity the declaring module states, or reaching a global that states none | a known call is a transfer to an entry whose arity is settled (D30) |
| A `PAP` supplying the callee's arity or more, **whatever kind of callee it stands over** — a global, a constructor, a foreign, or an operation | a partial application is what is applied below an arity; at or above one it is a call |
| A `CTOR` supplying other than the constructor's arity, or a `LOADC` naming a constructor that takes fields | a saturated constructor application is what either is |
| An `FFI` or `TAILFFI` supplying other than the arity the foreign declares | a foreign takes all of its arguments at once (D23) |
| A `PRIM` supplying other than the operation's arity | an operation's arity is the ABI's ([Prim and Base](../06-Modules/02-Prim-and-Base.md)) |

**How a global is installed is read against the function it names.**

| The module holds | Why |
| --- | --- |
| A `func` global whose function takes no parameters | a definitional arity counts leading lambdas and is at least one, so a value with none is a `run` global instead |
| A `run` global whose function takes parameters | it is entered with no arguments |
| Either, where the function expects captures | a global installs a closure over an empty capture list: at the top level every free name is a global, so there is nothing to capture |

**A constructor's export is not in the file.** `EXPORTS` holds value names — a
global's and a foreign's — so what a loader establishes about a constructor
reference is that it reaches a constructor some loaded module declares, not that the
declaring module published it. Data abstraction is settled where types are (D22): a compiler resolved
the name against `Σ`, and a `.dmo` is downstream of that. Enforcing it at load would
mean `EXPORTS` carrying constructors, which it does not.

**Each REPL entry is a module of its own**, and the modules accumulate.

```text
Repl.1
Repl.2   imports Repl.1
Repl.3   imports Repl.1, Repl.2
```

**A redefinition replaces nothing.** It is a new module, and it is the front end's
name resolution that sends later entries to the new definition. A closure built
before it keeps calling what it was built against, so a redefinition cannot break a
value the user is still holding.

**A `.dmi` is not read at run time.** It is what a compiler reads in order to emit
a `CALLK`; what the interpreter checks that call against is the declaring module's
own `.dmo`.

### What each mode asks of loading

**Initialization is the evaluation.** A `run` global is evaluated once as its module
is loaded, so a module that has loaded has already computed what its declarations
hold ([Bytecode](../05-Backend/01-Bytecode.md)). A session's request therefore names
a global and reads its slot; there is no second step in which a declaration is run.

| | Session | Run |
| --- | --- | --- |
| one module arrives | loaded against the registry as it stands | the same, for each of the list in turn |
| a load fails | the registry is as it was, and the next input is answered | the run ends, and the entry point is not executed |
| a fault while initializing | the same: the module is not committed | the same, and the run ends |
| what is reported | the value a named global holds | the named entry point's `IO`, executed |

**A session outlives its failures.** That is the whole of why a module is committed
only once it has initialized: an entry that faulted must leave nothing behind for the
next entry to trip over.

### Rendering a value

A session answers with a value, and what it can say about one is **structural**: a
scalar as itself, a constructor by the name its declaration carries with its fields
beside it, a record by its keys, and a closure, a continuation, or an `IO` as what it
is and nothing more.

**So interning keeps both directions.** A value carries an identity and an identity
is compared, not read, so rendering one needs the way back: a `CtorId` to the
qualified constructor name it was assigned for, a `KeyId` to the key, and an `OpId`
to the operation's name where a report names one. Loading is where those are kept,
which is what stops a session's answer from depending on the `DEBUG` section — a
section a file need not carry ([Bytecode](../05-Backend/01-Bytecode.md)).

**Type-directed printing is the front end's.** Steam holds no types (D34), so
rendering by a `Show` instance is the CLI's to do beside the type it checked.

## Foreign implementations

A foreign comes from one of two places. **The interpreter itself implements the
`Base` ABI entries it claims** — their meaning is one for every backend and what
they compute over is the interpreter's own representation — and **everything else
comes from the host**: a target entry constructing a native action, and a program's
own foreigns.

The host side is one map, and what it holds is an **adapter**: a host function of
the interpreter's values.

```text
ForeignRegistry : QualifiedName -> Adapter
Adapter         : Value… -> Value                -- synchronous; may fault
```

**An adapter is uncurried.** A saturated call hands it every argument at once, which
is what the `FFI` instruction does and what a `foreign`'s implementation is written
as; currying belongs to the declared type, and a partial application is the
interpreter's to hold ([Modules](../06-Modules/01-Modules.md)).

**Where the interpreter's value is the host's own, an adapter is the
implementation.** `Int`, `Number`, `Char`, `String`, and `Boolean` are held as host
values, so an ES module export written against those types is installed as it
stands — which is what the host does on Node, resolving a module name to a module
specifier and an unqualified name to an export of it, so `Js.Console.log` is the
export `log` of whatever `Js.Console` resolves to. The mapping is the host's and the
core never sees it.

**Anything else needs an adapter written for it.** A data value, a record, a
closure, or a continuation is held in a shape that is the interpreter's own and is
not a published ABI, so an implementation taking or returning one is reached through
an adapter, which is versioned with the interpreter rather than with the `.dmo`. A
Wasm implementation is one such case: the adapter is JavaScript, the interpreter
sees the same callable, and how a string or a data value is laid out in Wasm memory
is that adapter's concern and later the Wasm backend's.

**A `.dmo` says nothing about a foreign's type.** `FOREIGNS` holds a name and an
arity ([Encoding](../05-Backend/02-Encoding.md)), so no check at load can establish
that an implementation and a declaration agree about what crosses between them.
Which types a `foreign` declaration may carry is therefore the front end's to
restrict, where types still exist
([Open Questions](../99-Open-Questions/01-Open-Questions.md)); what a loader
establishes is that every name has an adapter and that the adapter is callable.

**An adapter applies no Stella closure.** It may receive one and carry it into what
it returns — `Base.IO.bind` takes `a -> IO b` and stores it in the `IO` value it
builds — but applying one is what `Σ ⊨ G` condition (3) forbids, the reduction rule
for a saturated `foreign` being one atomic step
([Semantics](../03-Typed-Core/06-Semantics.md)). So an adapter needs nothing of the
interpreter but its values, and the interpreter is never re-entered from inside one.

What an adapter owes is that condition: it takes all of its arguments at once,
returns a value of the instantiated result type or faults, performs nothing
observable to Core, applies no Stella function value, and terminates.

**The one place a closure is applied from the host side is the drive loop**, which
executes an `IO` value and is outside the reduction relation (D25) — below.

**Two layers, and they stay apart.**

| | |
| --- | --- |
| a foreign invocation | synchronous, and returns a value or faults |
| executing an `IO` action | may use a promise |

The registry is **internal** until the JavaScript backend's own FFI convention is
settled, at which point the two share one.

## The operations

`PRIMS` names operations, and executing a `PRIM` is carrying out the `Base` entry
its code stands for. **What each one means, and which of them fault, is the ABI's
and is one meaning for every backend** — the five the format carries are fixed in
[Prim and Base](../06-Modules/02-Prim-and-Base.md) — so the interpreter implements
what is written there and decides nothing of its own. A code it does not implement
is a load error rather than something discovered when a `PRIM` runs.

## Executing an `IO`

**Reduction halts once it has constructed a value of type `IO`** (D25). To the
instruction set such a value is opaque; to the interpreter it is one of three
things, which are what the runtime ABI builds.

```text
IOValue
  = Pure Value
  | Bind IOValue Closure
  | Native host action
```

The **drive loop** executes one: `Pure v` yields `v`; a native action is performed
and yields what it gives; `Bind io k` executes `io`, **applies the Stella closure
`k`** to the value that comes out — re-entering the interpreter — and executes the
`IO` that returns. Each such application is a run of its own, and it is the only
way the host side enters the interpreter: `k` is a pure arrow (D23), so it performs
no effect of its own and reaches no marker outside that run.

**A native action may be asynchronous.** The loop awaits it before applying the
continuation, and nothing of Core observes the wait: executing an `IO` is outside
the reduction, and the reduction is not re-entered while the loop is waiting.

**A session does not execute an `IO` of its own accord.** Recognizing one is not the
difficulty — an `IO` value is one of the three forms above, and the interpreter can
see which. What it cannot know is whether the value was meant to be run: a `.dmo`
carries no types, and a session keeps evaluating an entry and executing an action
apart on purpose. So an entry whose value is an `IO` is answered as one, and
executing it is asked for: by a request of its own in a session, which is what a
`:run` becomes, and by the invocation of `main` in the run mode.

## Failures

Three kinds, reported differently because they mean different things.

| | What it is | What it means |
| --- | --- | --- |
| **Load error** | an unresolved reference, an arity that does not agree, a missing foreign | the module is not loaded, and nothing of it ran |
| **Fault** | an operation or a foreign failing as the ABI says it may | the stack is discarded and the run ends; nothing catches one ([Bytecode](../05-Backend/01-Bytecode.md)) |
| **Interpreter bug** | reaching `VABS`, applying what is not callable, reading a register that holds nothing | a state no `.dmo` admits. Reaching one is a defect in the interpreter, in lowering, or in a check a loader owes |

The `DEBUG` section is where a report finds a function's name in a file that carries
one ([Bytecode](../05-Backend/01-Bytecode.md)). How much more a report holds — a
stack trace, a source span — is the REPL's to decide and is not fixed here.

## What Steam owes

The ten obligations of a consumer of a `.dmo` are Bytecode's, and Steam meets
(3) — a continuation applicable any number of times — where the v0.1 JavaScript and
Wasm backends do not.

Two of them are the ABI's and are worth stating as this interpreter's:

- **The `Base` profile it claims**, recorded in its backend manifest. Executing
  anything at all requires `core-runtime`, which is `Base.IO.pure` and
  `Base.IO.bind` ([Prim and Base](../06-Modules/02-Prim-and-Base.md))
- **The entries of a target root, where its host can supply them.** A target entry
  is what constructs a native action, and on Node it is an ES module export like any
  other host foreign
