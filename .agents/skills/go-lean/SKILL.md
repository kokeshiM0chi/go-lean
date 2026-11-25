---
name: go-lean
description: Write and verify strict Go models with go-lean, use curated Lean-like values, and prove package laws over generated Lean definitions.
---

# Verify a Go package

Use Go 1.26 or later and install Elan. Run commands from the Go module root. In a consuming module, install the tool and initialize its workspace:

```sh
go get -tool github.com/frederik-jatzkowski/go-lean/cmd/go-lean@latest
go tool go-lean setup
go tool go-lean doctor
go tool go-lean transpile ./pkg
go tool go-lean verify ./pkg
```

In the go-lean repository, use `go run ./cmd/go-lean` in place of `go tool go-lean`. The pinned toolchain is Lean 4.36.0. Use `.`, `./pkg`, `./pkg/...`, or `./...` for package selection. A selected package outside the managed Lake source directories needs a `lean_lib` with a local `srcDir` and a managed roots block. Keep manually maintained roots outside the block.

# Write the modeled Go

Separate pure decision logic from I/O and other runtime behavior. Every modeled Go function has unnamed results and a statically resolved call graph or explicit dependency contracts. Multiple results become right-associated products; return forwarding, immutable destructuring, blanks, and if initializers are supported. Callees are evaluated once even when results are discarded. Named results and direct spreading of a multi-result expression into another call remain unsupported. Use named value structs with fully keyed literals, explicit immutable local initializers, `if`, early returns, scalar comparisons, Boolean operators, and integer addition or subtraction. Use integer constants or typed parameters for inputs. Fixed-width Go arithmetic wraps in Lean, and `int` and `uint` follow the Go target architecture. Strings model raw bytes in lexicographic order.

The modeled graph supports boolean, integer, and string scalars, value structs, curated types, read-only pointers, and opaque passing of package-level named interfaces, including external modules and builtin error. Interface fields do not require modeling unused method signatures or implementations. Preserve values of the same named interface type (including aliases), or use explicit nil initializers, arguments, fields, and returns. Lean represents these values as `Option` of an opaque carrier and supports comparisons to nil. External carriers use a fixed generated golean_types.lean module in the consuming module; no dependency caches are edited. Boxing, conversions between distinct interfaces, equality between interface values, assertions, and anonymous interfaces remain unsupported. Raw slices and maps, function values, reassignment, raw Go loops, unannotated or mutual recursion, switches, and user-defined generics are outside the subset. Ordinary Go can use these features outside the modeled graph. Use a curated fold when the complete bounded traversal belongs in the model.

Direct calls to user-defined methods on supported concrete value or pointer receivers are modeled as functions with the receiver first. This includes `value.Method(args)` and `Type.Method(value, args)`, plus read-only implicit address-taking and dereferencing. Refer to the generated method as `«Type$Method»` in Lean laws. Promoted methods and stored method values remain unsupported. Pointer payloads use immutable snapshots when their types are supported and acyclic; other pointers stay opaque and may only be passed unchanged or checked for nil. Pointer writes and identity comparisons are rejected. Dereferencing a supported pointer adds an outer Option failure result, propagated to concrete callers; nil pointer receivers are still allowed when the method never dereferences them. Pointer representations are stable across focused regeneration. Measured recursion and fold steps cannot contain partial pointer reads. Methods follow the same directive and unnamed-result rules as functions. Name ordinary functions or interface methods in dependency contracts.

Interface method calls require explicit contracts: put `//golean:assume` laws on the interface method and `//golean:abstract Interface.Method` (or `alias.Interface.Method`) on a verified root. Both `value.Method(args)` and `Interface.Method(value, args)` work. A method contract's operation takes the receiver first, followed by modeled arguments, and has modeled results (products for multiple results). In assumptions, refer to it by the method name. Such roots return `Option Result`: `some value` is normal completion and `none` is a nil interface call, propagated with Go's branching and Boolean short-circuiting. A Go nil result is `some none`. Runtime methods must satisfy the explicit pure, total contract on nonnil receivers; implementations, mutable I/O, and additional panics are not verified. Contracts remain local to the root, cannot combine with measured recursion, and do not propagate to concrete callers. Calls through promoted embedded interface methods remain unsupported.

Use the Go package `github.com/frederik-jatzkowski/go-lean/pkg/lean` for values with Lean counterparts:

| Go | Lean |
| --- | --- |
| `Array[T]`, `ByteArray` | `Array`, `ByteArray` |
| `OrderedMap[K,V]`, `OrderedSet[K]` | `Std.TreeMap`, `Std.TreeSet` |
| `Option[T]`, `List[T]` | `Option`, `List` |
| `Box[T]` | `Option`, with the modeled Go zero value as the fallback for `Get()` |
| `BitVec` | A width at most 64 paired with a `BitVec` of that width |

Empty curated Go literals have empty Lean models. Updates preserve prior versions. Access outside the bounds yields `None`, and out-of-bounds writes preserve the input. Byte extraction uses clamped half-open bounds. `ByteArrayFromBytes` copies a raw Go slice at the boundary. Pass its result into a modeled function. When transferring a Lean statement about arbitrary collection sizes to Go, restrict inputs and intermediates to lengths representable by a Go `int`. Bit indexes count from the least significant bit, and a width above 64 yields `None`.

## Model iteration with folds

| Go helper | Named step signature |
| --- | --- |
| `lean.FoldN(n, initial, step)` | `func(uint, S) S` |
| `lean.FoldNUntil(n, initial, step)` | `func(uint, S) lean.FoldControl[S]` |
| `lean.FoldList(items, initial, step)` | `func(T, S) S` |
| `lean.FoldListUntil(items, initial, step)` | `func(T, S) lean.FoldControl[S]` |

A counted fold visits indices in `[0,n)` in order with a `uint` index. A list fold visits the head first and runs in linear time. An early-stop step returns `lean.FoldControl[S]{State: next, Stop: stop}`. The helper returns the stopping step's state and flag, including when it stops on the last visit. Exhaustion returns the final state with a false flag. Empty inputs return the initial state with no step calls.

Pass a directly named, non-generic function. Put extra inputs in an immutable state record. Closures, method values, and stored callbacks are unsupported. The step participates in the same export, contract, and recursion checks as direct calls. A modeled function can call several folds, and a named step can call another fold through an acyclic helper.

For arrays and byte arrays, fold over `Size()` and read with `Get(index)`. For a bounded state machine, use `FoldNUntil` with explicit fuel. Extract a pure step from an ordinary Go driver, move reassigned locals into its result state, and call the modeled fold driver from the runtime entry point. Keep I/O and raw representation conversions at the boundary.

Lean unfolds `«fold».count` and `«fold».countUntil` by recursion on a natural count. With zero fuel they return the seed, and a successor first applies the step then recurs with the next index unless the step stopped. `«fold».list` is a left fold with the step arguments flipped. `«fold».listUntil` has empty and cons equations with the same stop rule. `FoldControl[S]` is modeled as `S × Bool`, with `State` and `Stop` as the two projections. Use these equations to induct on the remaining count or list.

## Traverse recursive records

Use direct `lean.Box[Record]` fields to define a self-recursive record. Construct a populated box with `lean.NewBox(value)` and an empty box with `lean.Box[Record]{}`. Guard child reads with `IsSome()` before recursing on `Get()`. An empty box returns the Go zero value from `Get()`.

Add `//golean:termination:by sizeOf node` to a directly recursive function with a boxed record parameter named `node`. The measure is a Lean `Nat` expression scoped to the Go entry parameters. For example, use `n.toNat` for an unsigned countdown guarded against underflow. Verification checks that each recursive call decreases the measure. The generated function retains its ordinary modeled result type and exposes its `.eq_def` unfolding equation. Select the function with an export or verification directive, or call it from another modeled function.

# Select functions and state laws

Use directives in function or package doc comments with the exact `//golean:` prefix.

| Directive | Purpose |
| --- | --- |
| `//golean:export` | Model a function and permit concrete calls from other packages. Unmarked local helpers are modeled when reached. |
| `//golean:verify name : proposition` | Declare a Lean proposition with a name unique within the package. On a function or method, also select that operation for modeling. Continue it on consecutive `//golean:verify+` lines. |
| `//golean:verify:import Lean.Module` | In a package doc comment, import a Lean module into the generated model and law file. Use one dot-separated module name per directive. |
| `//golean:assume name : proposition` | Declare an explicit law about a scalar function or interface method. Refer to the operation by its unqualified Go name. Continue it with `//golean:assume+`. |
| `//golean:abstract alias.Function` | In a verified root, replace a named function or interface method call with a contract parameter. Use `Function`, `alias.Function`, `Interface.Method`, or `alias.Interface.Method`. |

An abstract root takes the generated contracts before its ordinary arguments. In its laws, use `dependency0`, `dependency1`, and so on in directive order. Its checked claims are conditional on the runtime callees satisfying those laws. Keep the assumption narrow and state independently what runtime behavior warrants it. See [assumed_worker](../../../examples/proven/assumed_worker/assumed_worker.go).

Concrete cross-package calls use the dependency's generated model. Export each called function and import the dependency's verification module from a handwritten proof to reuse its `Checked` theorems. See [clamp_import](../../../examples/proven/clamp_import/clamp_import_proofs.lean).

A package law can use operations selected by function directives or reached through modeled calls. Imported specifications must load independently of the model that uses them and its proof and verification modules. Put handwritten specification roots outside the managed Lake block.

# Discharge proof obligations

Generation puts the model and formal laws in `<package>.lean`, with a review copy of the laws at the top. Packages with laws also get separate proof and verification modules. If migrating from a workspace with a separate laws module, update the handwritten companion to import `<package>.lean` before removing the old generated model and laws files. Edit only the handwritten `<package>_proofs.lean` companion. Generation creates it on the first run and preserves it thereafter. Use the namespace `GoLean.«full/go/import/path».Proofs` and one theorem `theorem lawName : Laws.lawName` per obligation. State laws independently of the implementation wherever possible. Verification checks theorem types and axiom dependencies. Replace every scaffold `sorry` with a proof.

For a state machine, prove that the generated step preserves an invariant, then induct on histories from the initial state. Put observations such as accepting a move or reaching a goal in the law. The [grid game proof](../../../examples/proven/grid_game/grid_game_proofs.lean) covers all finite move histories in bounded and wrapping modes. Run verification again after changing a Go implementation or a proof.

# Best Practices

State the feature's requirements directly in `//golean:verify` directives by default. Use clear propositions about which inputs are valid, which outcomes are required, and what must be rejected. Include observable details such as diagnostic precedence when the requirements call for them.

Use an independent Lean specification module when the set of propositions is too broad to read comfortably in Go comments, for example when several laws share a grammar, an execution relation, or a substantial set of domain rules. Define that vocabulary and those rules in Lean, and use them in the Go-declared laws that connect the generated model to the requirements.

Avoid writing a reference implementation as the specification, especially a Lean copy of the Go control flow, intermediate data structures, or pass layout. Agreement with a second implementation is insufficient unless you also prove that it satisfies the rules. An executable definition belongs in the specification when its equations directly express the requirements, such as evaluating an expression by its syntax or scoring a strike by the next two deliveries.

Keep implementation-shaped invariants and representations in the proof companion or in a separate refinement module. Use an intermediate model only when it simplifies a specific proof, and prove the connection from that model to the domain rules. If a helper replays generated behavior, pass the generated step as an argument so the specification can load independently.

In [bowling](../../../examples/proven/bowling/README.md), the scoring rules express strike and spare bonuses in terms of later deliveries. The package law checks acceptance decisions and final scores over every finite history from the initial state.
