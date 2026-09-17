# Overview

Dawn is a pure functional language influenced by PureScript. It is not a PureScript dialect: source compatibility, package compatibility, and semantic compatibility are not goals. Where a more coherent design is available, Dawn takes it.

The initial compilation targets are the web — JavaScript and WebAssembly — but the compiler keeps a backend-independent intermediate representation so that native backends remain possible.

## Two central positions

Two choices distinguish Dawn from PureScript. Both follow from a single observation: PureScript loads too much work onto type class resolution.

**Rows are a first-class structure in the type system, not something manipulated through type classes.** A dedicated row solver normalizes open rows without closing them. Structural relationships between rows are constraints the solver discharges, not instances a search procedure finds.

**Type classes are a library, not a compiler builtin.** The compiler provides one general synthesis hook. The standard library implements class declarations as syntax macros and dictionary synthesis as an ordinary elaborator.

## What Dawn inherits from PureScript

- Pure functional programming by default
- Strict evaluation
- A surface syntax close to PureScript's
- Local type inference in the Hindley–Milner tradition
- Explicit type annotations at library boundaries
- Algebraic data types and pattern matching
- Higher-kinded types
- Row-polymorphic records and variants
- A clear separation between safe code and the unsafe FFI boundary

These are influences, not compatibility requirements.

## A small trusted core

Surface language features elaborate into a small typed Core.

Syntax macros and elaborators can fail, diverge, or produce malformed syntax. They must never cause the compiler to accept an ill-typed Core term. An independent Core type checker validates every Core term that elaboration produces.

This separation is what allows type classes, derive mechanisms, and row-directed metaprograms to grow without enlarging the set of programs whose correctness the compiler vouches for. See [Core Type Checker](11-Core-Type-Checker.md).

## Compile-time computation is separated by concern

PureScript's type class resolution serves several purposes at once. Dawn gives each its own mechanism.

| Mechanism | Responsibility |
| --- | --- |
| Unification and type inference | Infer unknown types and solve type equations |
| Row solver | Normalize rows and discharge structural constraints |
| Type-level evaluation | Evaluate explicit type functions |
| Syntax macros | Transform syntax into syntax, hygienically |
| Elaborator | Build typed Core terms from expected types and the environment |
| Type class resolver | A library elaborator that synthesizes dictionary terms |

In particular, type class resolution is not a substitute for row computation or for general compile-time computation.

## Compiler pipeline

```text
Source
  │ parsing and syntax macro expansion
  ▼
Surface AST
  │ name resolution, type inference, elaboration
  ▼
Typed Core
  │ lowering of language semantics
  ▼
backend-independent Mid IR
  ├── JavaScript IR ──► ES modules
  ├── Wasm IR ────────► WebAssembly modules
  └── future IRs ─────► native and others
```

**Surface AST** carries source-oriented information: sugar, implicit arguments, holes, macro invocations, source locations, expansion provenance, and hygiene scopes. It is not a stable optimization interface.

**Typed Core** defines the semantics of the language. It makes explicit: type abstraction and application, evidence and dictionary arguments, record and variant operations, the decision structure of pattern matching, effect operations and handlers, and evaluation order wherever it is observable. The rest of these documents specify it.

**Mid IR** retains useful type information and invariants while depending on no particular backend. It expresses closure construction and application, algebraic data construction and destruction, join points and tail calls, primitive operations, explicit control flow, handler and continuation operations, and abstracted allocation. JavaScript functions and objects, Wasm GC structs, and linear-memory layouts must not leak into this stage.

## Backend strategy

The JavaScript backend is the reference backend. Delegating garbage collection, closures, and module mechanics to the host allows the parser, type system, elaboration, and language semantics to be validated first.

The Wasm backend prioritizes Wasm GC. A backend using linear memory and a custom collector can be added later as a separate lowering.

Effect handlers are the one place where backends differ in what they can implement. See [Semantics](08-Semantics.md).

## Roadmap

| Phase | Content |
| --- | --- |
| A | Lexer, parser, source spans and diagnostics, name resolution, kind checking, type inference, Typed Core, Mid IR, JavaScript backend |
| B | Hygienic syntax objects, quotation and antiquotation, declaration attributes, typed reflection, metavariable and goal APIs, transactional elaboration, synthesis scheduling |
| C | Library-defined type classes: dictionary record macros, instance declaration macros, the standard resolver, recursive instance search, coherence and ambiguity rules, search trace diagnostics |
| D | Native row programming: canonical open-row representation, row unification and normalization, structural constraints, reflection over known row fragments, residual computation over unknown tails |
| E | Effects and WebAssembly: effect rows in Core, first-order operations and handlers, higher-order and scoped effects, JavaScript runtime strategy, Wasm GC backend, browser interoperability |

Phases A through D require no effect handlers. The Typed Core specified in these documents includes effect rows and handlers from the start so that function types, the FFI boundary, exceptions, and asynchrony do not have to be redesigned when Phase E arrives.

## Examples that validate the design

1. A class-free functional program compiled through every IR to JavaScript
2. `Eq` or `Show` implemented using only the standard metaprogramming library
3. An alternative resolver demonstrating that resolution policy is replaceable
4. A JSON encoder derived from a closed record row
5. Open-row encoder composition that leaves the unknown tail's encoder explicit
6. Lowering of the same Typed Core to both JavaScript and Wasm

These serve as architecture tests as well as demonstrations.

## Document map

| Document | Content |
| --- | --- |
| [00-Notation](00-Notation.md) | Metavariables, sequences, symbols |
| [02-Design-Decisions](02-Design-Decisions.md) | The numbered decisions D1–D25 |
| [03-Kinds-and-Types](03-Kinds-and-Types.md) | Names, kinds, types, kinding rules |
| [04-Rows](04-Rows.md) | Row theory, normal form, entailment, surface syntax |
| [05-Effects](05-Effects.md) | Effect rows, operations, handlers, `IO` |
| [06-Terms-and-Matching](06-Terms-and-Matching.md) | Core terms, value forms, join points, decision trees |
| [07-Typing-Rules](07-Typing-Rules.md) | Contexts and the typing rules |
| [08-Semantics](08-Semantics.md) | Evaluation order, erasure, handlers and continuations |
| [09-Modules](09-Modules.md) | Modules, declarations, FFI, entry point |
| [10-Elaboration](10-Elaboration.md) | Core⁺, metavariables, unification, synthesis |
| [11-Core-Type-Checker](11-Core-Type-Checker.md) | What the checker verifies, and what it does not |
| [12-PureScript-CoreFn](12-PureScript-CoreFn.md) | Correspondence with PureScript's CoreFn |
| [13-Examples](13-Examples.md) | Worked examples in Core |
| [14-Open-Questions](14-Open-Questions.md) | Questions deferred beyond v0.1 |
| [15-Implementation-Plan](15-Implementation-Plan.md) | Order of implementation work |
| [16-Prim](16-Prim.md) | What `Prim` holds, and which part of it Core names |

The numbers record the order the documents were written in rather than the order to read them in. [16-Prim](16-Prim.md) belongs beside [Modules](09-Modules.md).
