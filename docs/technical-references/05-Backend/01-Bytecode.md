# Bytecode and the `.dmo` module object

Bytecode is one lowering of Mid IR, beside JavaScript and WebAssembly. Its
target is a machine Dawn owns, which is what lets a program be executed before
either of the other two backends exists.

`lower` takes a Mid IR module and produces a **`.dmo` file**, a module object
holding the module's tables and the code of its functions.

The virtual machine that executes a `.dmo` is specified separately. This
document fixes the instruction set and the container, and states what a consumer
owes them.

## A `.dmo` is the artefact others build on

Mid IR is an in-memory representation, and a compiler that goes on to generate
JavaScript or Wasm need not write anything to disk between the two. **A `.dmo`
is what a consumer outside this compiler reads**, and the format is fixed here
for that reason rather than for the machine's convenience.

PureScript publishes `corefn.json`, and several backends outside its compiler
consume it. Dawn publishes the lowered form instead, and what that buys a
consumer is the work already done: erasure, A-normal form, spine folding,
explicit closures with their capture lists, and decision trees whose branches no
longer overlap. A consumer of Typed Core would have to perform every one of
those before generating code, and each is a place to differ from the reference
compiler.

| Consumer | Reads |
| --- | --- |
| The virtual machine | A `.dmo` |
| The JavaScript and Wasm backends | Mid IR, or a `.dmo`; both are available and neither is fixed here |
| A backend outside this compiler | A `.dmo` |

The two routes for the first-class backends are a question of what a build is
convenient to organize — a single command generating JavaScript without an
intermediate file is the likely shape — and not one the format answers. What the
format does settle is that a `.dmo` is enough on its own.

### The interface file

A `.dmo` is one of a pair. Beside it stands a **`.dmi` file**, the interface of
the same module, and the two together are what the compiler writes.

| File | Holds |
| --- | --- |
| `.dmi` | A module's exported types, and what a module downstream of it needs in order to optimize across the boundary — the bodies of functions eligible for inlining among them |
| `.dmo` | The module's tables and the code of its functions |

**What a `.dmi` carries is settled when the optimizer is written**, its content
being determined by what optimization across a module boundary turns out to
require. What is fixed already is the split: compiling a module reads the `.dmi`
of each module it imports, and reads a `.dmo` only to link or to execute.

One thing in this document depends on that file already. `callk` names a
top-level value together with its **definitional arity**, which is the number of
leading lambdas its right-hand side has and not something its type says
([Translation](../04-MiddleEnd/02-Translation.md)); for an imported value the
`.dmi` is where it comes from. Where it is absent the call is a `callu`, which is
correct for every callee, so a `.dmi` that does not yet publish arity costs
sharpness and nothing else.

### What it therefore carries

**The meaning of every instruction is fixed by this document**, in terms of
[Semantics](../03-Typed-Core/06-Semantics.md), and not by what the machine
happens to do. A consumer that is not the machine reads the same specification.

**Representation types reach the file.** A backend choosing a Wasm GC struct per
data type, or an unboxed integer, needs to know which class of value a register
holds, and `Rep` is what says so ([Mid IR](../04-MiddleEnd/01-Mid-IR.md)).
Dropping it would leave a consumer with a uniform representation and no way to
improve on it.

**Debug information is worth writing even though it may be stripped.** Source
spans are what a consumer emits a source map from, and no other section carries
them.

### What it does not carry

Core's types, rows, effect rows, and constraints are gone, and `Rep` is what
survives of them. A consumer wanting to optimize on the strength of a row — a
record whose fields are all known, an effect row that turns out empty — has to
read Typed Core instead.

That is the trade the format makes: **lowered and ready to generate code from,
rather than typed and general.** Type-directed work belongs before this stage,
where the types still exist.

## Semi-linearized form

Code is linear within a straight run of instructions and **structured above
it**. A function is not one instruction array. It is a tree of instruction
sequences, whose edges name their destinations.

```text
Function ::= { nparams   : Int
             , regs      : [Rep]     one per register; the first nparams are the parameters
             , captures  : [Rep]     one per capture slot
             , joins     : [Join]
             , body      : Node
             }

Join     ::= { name : JoinName, params : [Reg], body : Node }

Node     ::= { code : [Instr], tail : Tail }
```

A `Node` is a straight run of instructions ending in exactly one `Tail`. A
`Tail` either leaves the function, jumps to a join point, or **dispatches into
further `Node`s held inline**.

Two things are therefore not flattened, and both are deliberate.

**A transfer to a join point names its destination; it is never an offset.** A
jump carries the name, which the machine resolves when it loads the module.

**A decision tree stays a decision tree.** The dispatches of a Core `case` nest
here as they nest in Core, each branch holding its own instruction sequence
rather than standing as an edge to a block somewhere else in the function.

### Why the structure survives

What a consumer must do afterwards is the reason. Offsets into a flat array
discard the loop and branch structure that a language with `if`, `switch`, and
nested blocks needs, and recovering it means running a **relooper** — an
algorithm that reconstructs structured control flow from an arbitrary control
flow graph. It is substantial to write, and what it recovers is worse than what
was thrown away.

A backend handed this form walks it instead. A nested dispatch becomes a nested
`switch`, a join point becomes a label or a local function, and nothing has to
be reconstructed because nothing was lost. **That holds whether such a backend
reads Mid IR or reads a `.dmo`**, and keeping it true of the `.dmo` is what
leaves the second route open.

The cost falls on the machine, which resolves names and walks a tree rather than
incrementing a program counter. For a first evaluator that is the right side to
pay on, and it is the only side that a relooper could not be written for.

### Join points

**A join point names the registers its parameters occupy, and a jump supplies
them.** A Mid IR `letjoin` becomes a `Join` and a `jump` becomes a `JMP`
carrying arguments. Nothing else is needed to express what a join point is, and
the machine reconstructs no data flow across a transfer.

The registers are part of the file. Lowering assigns them, and a `JMP` writes
its arguments into them, so a consumer that did not know which they were could
not perform the transfer at all — the `Join` carries `params` for that reason
rather than a count.

The join table is flat. Join names are unique within a function, and Mid IR has
already established that every `jump` names one in scope and stands in tail
position, so nesting the table would re-state a property that holds already.

## Registers

A function has a flat register file, indexed from 0. Parameters occupy the first
`nparams`, and a join point's parameters occupy slots the lowering assigns.
Every other Mid IR local takes a slot of its own.

Mid IR names each local once, so the naive assignment of one slot per local is
already correct and lowering performs no register allocation. Reusing slots is a
later concern and changes nothing above this line.

**Each slot carries the `Rep` of what it holds**, which is the `Rep` Mid IR
wrote on the binding ([Mid IR](../04-MiddleEnd/01-Mid-IR.md)). A consumer
choosing a representation reads it there; one keeping a uniform representation
ignores it. `Rep Data T` names a type constructor, whose constructors are found
in the `CTORS` table of whichever module declares it — this one, or one it
imports.

Reusing a slot later would mean a slot holding two classes of value over its
lifetime, so whatever does it records a `Rep` per definition rather than per
slot. Nothing in this document does.

A `JMP` writes its arguments into the join point's parameter slots. Where an
argument register is itself a parameter slot of that join point, the writes are
performed as a parallel move rather than in sequence.

Captures are not registers. `CAPT` reads one from the closure of the current
activation.

## Instructions

Operands are written `d` for a destination register, `s` for a source register,
and `r…` for a vector of source registers. An index into a module table is
written by the name of the table.

### Loading

| Instruction | Effect |
| --- | --- |
| `LOADK d, const` | The literal at `const` in the constant pool |
| `LOADG d, global` | The value stored in a global slot |
| `LOADC d, ctor` | The constructor `ctor`, whose arity is 0 |
| `MOVE d, s` | |
| `CAPT d, i` | Capture `i` of the current activation's closure |

### Allocation and calls

| Instruction | Effect |
| --- | --- |
| `CLOS d, func, n, r…` | A closure over `func` with `n` captures |
| `CLOSN d, func, n` | A closure over `func` with `n` capture slots, unfilled |
| `SETCAP d, i, s` | Fill capture slot `i` of the closure in `d` |
| `PAP d, callee, n, r…` | A partial application; `n` is below the callee's arity |
| `CTOR d, ctor, n, r…` | A saturated constructor; `n` is its arity |
| `CALLK d, global, n, r…` | Call the closure in a global slot; `n` is its arity |
| `CALLU d, s, n, r…` | Call the value in `s` with `n` arguments |
| `FFI d, foreign, n, r…` | Call a foreign implementation; `n` is its arity. **May fault** |

`CLOSN` and `SETCAP` exist for a recursive group, whose members capture one
another: every closure of the group is allocated before any capture list is
filled. `CLOS` is the whole of the non-recursive case.

`CALLU` is where under- and over-application are resolved. Applying a `PAP`
below its arity yields another `PAP`; applying one that saturates it performs
the call; supplying more arguments than a callee takes calls it and applies the
rest to the result — left to right, the arguments being values already.
**Applying a continuation is an ordinary `CALLU`**, a continuation being an
ordinary function value ([Semantics](../03-Typed-Core/06-Semantics.md)).

**An argument vector is in source order, and every register in it already holds
a value.** Dawn evaluates an application's argument before its function, so a
spine is evaluated right to left (D35) — but that happened in Mid IR, where each
argument became a binding of its own in that order. By the time a call
instruction runs there is nothing left to evaluate and nothing to reorder, so
`r…` reads as the call reads.

### Data, records, and variants

| Instruction | Effect |
| --- | --- |
| `FIELD d, s, ctor, j` | The `j`-th field of the constructor value in `s` |
| `RNEW d` | The empty record |
| `REXT d, key, s_v, s_r` | Extend the record in `s_r` at `key` with the value in `s_v` |
| `RSEL d, key, s` | |
| `RRES d, key, s` | Restrict |
| `RUPD d, key, s_r, s_v` | Update |
| `RMRG d, s1, s2` | Merge two records |
| `VINJ d, key, s` | Inject into a variant at `key` |
| `VPAY d, key, s` | The payload the variant in `s` carries at `key` |
| `VABS d, s` | Unreachable; the operand's type is uninhabited |

`VABS` has no defined result. Core's `absurd` has no reduction rule because its
argument has type `Variant ()`, so the instruction is never reached; the machine
treats reaching it as an internal error rather than as a fault.

### Effects

| Instruction | Effect |
| --- | --- |
| `PERF d, key, op, s` | Perform `op` on the element keyed `key` with the argument in `s` |
| `HNDL d, handler, r_body, r_ret, n, r…` | Install the handler and call the body; `d` receives what the return clause gives |

`PERF` is not a `Tail`. Where the clause found is `fast`, control returns to
the instruction after it with the clause's value in `d`; where it is `full`,
control does not return to it at all unless the clause resumes the continuation,
and the resumed value arrives in `d`.

**`HNDL` is an ordinary instruction and not a `Tail`**, because the value of a
`handle` is the value of a computation. It supplies its functions in registers:
`r_body` holds the body, `r_ret` the return clause, and `r…` the operation
clauses in the order the handler table lists them. Each is built by an ordinary
`CLOS`, so nothing here carries a capture list of its own.

Installing the marker and calling the body is one step. **The marker stands
between the calling activation and the body's**, which is what lets the return
clause's value arrive in `d` by the ordinary route a call's value arrives by.

### Tails

A `Tail` ends a `Node`. `node` below stands for a `Node` held **inline**, which
is what keeps a decision tree a tree; `join` stands for a join point's name.

| Tail | Effect |
| --- | --- |
| `RET s` | Return the value in `s` |
| `TAILK global, n, r…` | A tail call to a global |
| `TAILU s, n, r…` | A tail call to a value |
| `TAILFFI foreign, n, r…` | A tail call to a foreign. **May fault** |
| `JMP join, n, r…` | Enter a join point with arguments |
| `BRIF s, node, node` | Branch on a boolean |
| `BRC s, [(ctor, node)…], node?` | Dispatch on a constructor tag |
| `BRL s, [(const, node)…], node` | Dispatch on a literal |
| `BRK s, [(key, node)…], node?` | Dispatch on the key a variant carries |
| `TAILHNDL handler, r_body, r_ret, n, r…` | The same as `HNDL`, in tail position |

**A branch is a `Node` and not a name**, so the instructions a branch needs
before its own dispatch stand inside it. This is where the projections of a
decision tree land: the `FIELD` reading a constructor's field sits in the branch
that selected that constructor, which is the only place the field exists
([Translation](../04-MiddleEnd/02-Translation.md)).

Sharing a branch between several leaves is what a join point is for: such a
branch is a `Join`, and the leaves that share it end in `JMP`. Lowering
introduces none of its own, Mid IR's join points being exactly the ones Core
wrote.

`BRL` always carries a default and the other two carry one unless their cases
exhaust, which Mid IR already guarantees. **The machine performs no totality
check**: the Core type checker established local totality and Mid IR preserved
it.

A Mid IR `tail` of a computation that is not a call — a `ctor`, a `closure`, a
record operation — lowers to that instruction followed by `RET`. Only a call has
a `Tail` of its own, because only a call is a transfer of control that a
backend must be told not to push a frame for.

### `RET` and an installed handler

**`RET` returns from the current activation, and that is the whole of the rule.**
It has no case for a handler.

What makes a handler work is where its marker stands. `HNDL` pushes the marker
and then calls the body, so the marker is **below** the body's activation.
Returning from the body therefore reaches the marker, which pops, calls the
return clause with the value, and delivers that clause's own result to the
`HNDL` that installed it. This is `handle v with h → e_r[x := v]`, and it needs
no rule beyond returning from an activation.

It is also why `HNDL` needs no matching instruction to close the region: a
handler's extent is the part of the continuation above its marker, and whatever
leaves that part removes it.

**A tail call inside the body does not disturb any of this.** `TAILK` and its
kin replace the body's activation, and the marker is not in that activation, so
the path from wherever control ends up back to the marker and its return clause
is the same one. The same holds of a tail call inside a clause.

## A worked function

The `sum` of [Translation](../04-MiddleEnd/02-Translation.md), lowered:

```text
function Main.sum   nparams 1   captures []   joins []
  regs  [ Data Main.List, Int, Int, Data Main.List, Int ]

  body
    tail  BRC r0, [ Main.Nil -> A, Main.Cons -> B ]      no default; the two exhaust

      A   code  LOADK r1, #0
          tail  RET r1

      B   code  FIELD r2, r0, Main.Cons, 0
                FIELD r3, r0, Main.Cons, 1
                CALLK r4, Main.sum, 1, [r3]
          tail  TAILFFI Base.Int.add, 2, [r2, r4]
```

`r0` is the parameter, `r2` to `r4` are the three Mid IR locals of the `Cons`
branch, and `r1` is a slot lowering introduced for itself: an atom that is a
literal has to reach a register before an instruction can take it, and `LOADK`
is what puts it there. Slots are never shared, not even between branches that
cannot both run, there being no register allocation here.

`A` and `B` are not blocks the function holds and jumps to. They are the two
branches of the `BRC`, written out here because a nested `Node` does not fit on
one line, and a JavaScript backend emits them as the two arms of a `switch`.

The rest of the function follows from that shape. The `FIELD`s stand inside `B`
and nowhere else, that being the only branch in which the fields exist. The
recursive `CALLK` is an ordinary call because its value is an argument, and the
addition is a `TAILFFI` because it stands where the function returns. Nothing is
shared between the branches, so the function has no join points at all.

A shared branch is what produces one. Where a decision tree reaches one body from
two leaves, Core lifts that body into a `letjoin`, and the two leaves become
`JMP`s naming it.

```text
function …   joins [ alt0 params [r3] ]

  body
    tail  BRC r0, [ Main.Nil  -> A, Main.Cons -> B ]

      A   code  LOADK r1, #0
          tail  JMP alt0, 1, [r1]

      B   code  FIELD r2, r0, Main.Cons, 0
          tail  JMP alt0, 1, [r2]

  join alt0 params [r3]
    …
```

The body is held once, and the name is what both leaves carry. `r3` is where a
`JMP` writes its argument, and the `Join` names it so that a consumer can
perform the transfer at all.

## Handlers, `perform`, and continuations

The machine holds a **continuation**: a stack whose entries are activations and
handler markers. `HNDL` pushes a marker carrying the handler's key, the forms
and closures of its clauses, and the return clause.

`PERF key, op` walks the continuation from the top for the first marker whose
key is `key`. The innermost wins, which is what makes handlers deep, and
handlers of one key may nest — a function that handles an effect internally is
pure to its caller, so calling it under an outer handler of the same effect puts
two markers on the stack at once ([Semantics](../03-Typed-Core/06-Semantics.md)).

| The clause found | What the machine does |
| --- | --- |
| `fast` | Call the clause closure with the argument, leaving the continuation as it is. The clause returns to the `PERF` site with its value |
| `full` | Split the continuation at that marker, inclusive. Make the removed segment a continuation value. Call the clause closure with the argument and that value, its result returning to what remains below the marker |

Nothing here consults an effect row, a type, or an operation's signature. A key
is compared for equality and an operation is found by name among the clauses of
the one handler the key selected.

### Resuming more than once

**A continuation may be applied any number of times, and each application
proceeds from the state that was captured** (D33). Two applications of one
continuation share no register file and no handler marker, and the second begins
from the captured state exactly as the first did.

**Each application returns to whoever applied it.** The captured segment ends at
the marker, and the value the return clause produces there goes to the
`CALLU` that applied the continuation — not to the `HNDL` that first installed
the handler. A continuation is a function value, and this is what being one
means.

What is captured is a run of **whole activations**, from the one performing the
operation up to and including the marker, each with its registers and the point
it resumes at. None of them is a fragment: the body of a `handle` is an
activation of its own, so no activation straddles the marker.

Copying the segment at each application is the straightforward way to provide
this, and it is what a register machine with mutable frames must do — re-pushing
the frames it captured would have the first application write over the state the
second needs. **The requirement is the behaviour, not the mechanism**: immutable
frames shared between applications satisfy it equally, and D33 fixes only that
the machine provides it.

The cost falls on `full` clauses alone. A `fast` clause captures nothing (D28),
so the common case of translating one operation into another pays none of it.

**This makes the virtual machine conforming with respect to D18**, where the
v0.1 JavaScript and Wasm backends are not: the reference semantics is multi-shot
and no backend that raises an error on a second resumption reproduces it
([Semantics](../03-Typed-Core/06-Semantics.md)).

What that buys the test suite is narrower than being the evaluator the
properties are stated over. The machine is **a second evaluator to compare the
Core evaluator against** — one program run both ways, giving the same value and
the same sequence of observable effects — and it is what **exercises a program
that resumes a continuation more than once**, which the web backends cannot run
at all. Preservation and erasure are stated over Typed Core and its erasure, and
a machine state carries no types, so those two stay with the Core evaluator
([Implementation Plan](../01-Introduction/04-Implementation-Plan.md)).

## Faults

A foreign implementation may fail, and the failure is a **fault**: not an
effect, intercepted by no handler, absent from every row, and distinct from the
`Partial` effect ([Semantics](../03-Typed-Core/06-Semantics.md)).

A fault discards the whole continuation, handler markers included, and ends
execution. The machine reports it; nothing in the bytecode catches it, and no
instruction produces one but `FFI` and `TAILFFI`.

## Executing an `IO` is outside the machine's reduction

Reduction halts once it has constructed a value of type `IO` (D25), and
executing one belongs to the runtime ABI. To the bytecode an `IO` value is an
opaque value like any other: it is produced by an `FFI`, carried by whatever
carries it, and consumed by another `FFI`. No instruction examines one.

Running a program end to end therefore requires the machine to implement the
runtime ABI beside the instruction set: `Base.IO.pure`, `Base.IO.bind`, the
native leaf actions, and the invocation of `main`
([Prim and Base](../06-Modules/02-Prim-and-Base.md)). That is an obligation on
the machine as a backend, graded by the profile it claims, and not part of this
instruction set.

## The `.dmo` container

```text
header   magic "DMO\0"  |  format version  |  flags  |  ABI version

section  id | length | payload           repeated to the end of the file
```

| Section | Holds |
| --- | --- |
| `STRINGS` | Every string the other sections refer to, UTF-8 |
| `CONSTANTS` | The literal pool: tagged `Int`, `Number`, `String`, `Char`, and `Boolean` values |
| `KEYS` | Row keys: a tag and, for three of the four, a string or an integer |
| `OPS` | Operation names |
| `IMPORTS` | The modules this one depends on |
| `CTORS` | Per constructor: name, owning type, tag, arity, and whether its type is a `newtype` |
| `EFFECTS` | Per effect: name and the operations it declares |
| `FOREIGNS` | Per foreign: qualified name and arity |
| `CALLEES` | Per partial-application target: what kind it is, which entry, and its arity |
| `HANDLERS` | Per handler: its key, and per clause the operation and its form |
| `FUNCTIONS` | Per function: `nparams`, the `Rep` of each register and of each capture slot, its join points with the registers each takes its arguments in, and its body |
| `GLOBALS` | Per top-level value: its name, whether it is run or installed, and which function |
| `EXPORTS` | The globals this module exports |
| `DEBUG` | Source spans, function names, and local names |

`DEBUG` is the one section a reader may skip. Everything else is required, and a
machine rejects a file missing any of it rather than guessing.

**Keys and operation names are interned on load.** They are compared for
equality and for nothing else, so the machine replaces each with an integer
identifying it across every module it has loaded.

**A join point's name is resolved on load too**, to whatever the machine reaches
a `Join` by. A name is what the file holds so that the structure survives the
format; nothing looks a name up while the function is running, and a name is
never compared at run time.

### Initialization

`GLOBALS` is ordered, and initialization runs it in order: a `run` entry
evaluates its function once and stores the result, and a `func` entry installs a
closure over an empty capture list without evaluating anything. A module's
imports are initialized before it is.

A right-hand side that diverges hangs initialization whether or not anything
refers to it, and one that faults ends it. Both follow from evaluating eagerly
in declaration order, which Core fixes and this format preserves
([Semantics](../03-Typed-Core/06-Semantics.md)).

### The format admits modules that arrive one at a time

A `.dmo` names what it imports and refers to another module's globals by
qualified name. Nothing in it is resolved against a closed set of modules, and
no section indexes anything outside the file.

This is what a read-eval-print loop needs: an entered expression becomes a
module of its own, compiled and loaded against the modules already present,
without relinking them. Keeping the format free of whole-program indices costs
nothing now and is expensive to retrofit.

## What lowering does not do

- **No optimization.** No inlining, no constant folding, no dead code elimination, no common subexpression elimination. Mid IR is where those would belong, and none of them is in scope
- **No register allocation.** One slot per Mid IR local, and one more wherever an atom has to reach a register before an instruction can take it
- **No totality or arity checking.** The Core type checker established the first and Mid IR's invariants the second
- **No typing.** `Rep` is carried through to the file, and nothing re-derives or checks it. Core's types, rows, and effect rows are gone by the time Mid IR exists

## What a consumer owes

These hold of anything that executes a `.dmo` or generates code from one, the
virtual machine included. They are obligations of the format rather than of any
one implementation.

1. The evaluation order of [Semantics](../03-Typed-Core/06-Semantics.md), which is observable because any subterm may perform an effect
2. `PERF` finding the innermost marker of its key
3. A continuation applicable any number of times, each application proceeding from the captured state and returning to whoever applied it
4. A handler marker standing below the body's activation, so that returning from the body runs the return clause and a tail call inside the body leaves the path to it intact
5. A fault discarding the continuation entirely, handler markers included
6. Conformance of every foreign implementation it supplies: condition (3) of `Σ ⊨ G` — each returns a value of the instantiated result type or a fault, performs nothing observable to Core, and terminates
7. The runtime ABI at the profile it claims, including the execution of `main`

A consumer unable to meet (3) is non-conforming in the way D18 records, and says
so rather than failing quietly: the v0.1 JavaScript and Wasm backends are in
exactly that position, and the virtual machine is not.
