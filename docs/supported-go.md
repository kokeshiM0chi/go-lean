# Supported Go

go-lean checks the call graph reached from exported and verified operations. Ordinary Go at the boundary can use the full language. Within the modeled graph, use immutable local initializers, fully keyed value literals, conditionals, early returns, and unnamed results.

## Types and operations

| Go | Lean and behavior |
| --- | --- |
| Booleans and comparisons | Lean Boolean values. Laws can state propositions about their results. |
| Fixed-width integers | Signed or unsigned Lean machine integers. Addition and subtraction wrap at the modeled width. |
| `int`, `uint` | Machine integers at the Go target's width. |
| Strings | Byte sequences with lexicographic comparison. |
| Named value structs | Lean records with fields such as `value.«field:Name»`. |
| Package-level named interfaces, including external modules and builtin `error` | Opaque carriers, wrapped in `Option` to distinguish nil. Values can be stored and passed through unchanged. |
| Raw pointers | `Option` of an immutable payload for supported acyclic types, or of an opaque carrier for runtime-only types. Nil checks and unchanged passing work in both cases. |
| Multiple unnamed results | Right-associated Lean products. Destructuring evaluates the callee once; blank components do not suppress evaluation. |
| `lean.Array[T]`, `lean.ByteArray` | `Array` and `ByteArray`. Out-of-bounds reads return `None`, and out-of-bounds updates preserve the input. |
| `lean.List[T]`, `lean.Option[T]` | `List` and `Option`. |
| `lean.OrderedMap[K,V]`, `lean.OrderedSet[K]` | `Std.TreeMap` and `Std.TreeSet`. |
| `lean.Box[T]` | `Option`. Reading an empty box with `Get()` returns the modeled Go zero value. |
| `lean.BitVec` | A width paired with a bit vector of that width. Widths above 64 yield `None`. Index zero is the least significant bit. |

Empty curated collection literals model empty collections. Updates preserve earlier values. Byte extraction clamps half-open bounds. Use `lean.ByteArrayFromBytes` to copy a Go slice at the boundary. When applying a Lean statement over arbitrary collection sizes to Go, account for the lengths representable by Go's `int`.

## Calls and traversal

Direct calls resolve statically. Concrete value- and pointer-receiver calls and method expressions translate with the receiver first. Read-only implicit address-taking and dereferencing are supported. A modeled invocation of `board.stoneAt(point)` calls `«Board$stoneAt»` in Lean. For concrete calls across packages, mark the callee with `//golean:export`. See [runtime boundary types](runtime-boundary-types.md) for pointer failure and multiple-result examples.

| Helper | Step signature | Visits |
| --- | --- | --- |
| `lean.FoldN(n, seed, step)` | `func(uint, S) S` | Indices from zero through `n-1` |
| `lean.FoldNUntil(n, seed, step)` | `func(uint, S) lean.FoldControl[S]` | The same indices until the step stops |
| `lean.FoldList(items, seed, step)` | `func(T, S) S` | List items from the head |
| `lean.FoldListUntil(items, seed, step)` | `func(T, S) lean.FoldControl[S]` | List items from the head until the step stops |

Pass a directly named non-generic function. Empty traversals make no step calls. The early-stop result carries the stopping step's state and flag, including a stop on the last visit. Exhaustion returns the final state with a false flag. Lean models the state and flag as `S × Bool`. The generated count equations recurse on the remaining count, and the list equations unfold on empty and cons cases.

For direct recursion, supply a Lean `Nat` measure in scope of the entry parameters. Use a guarded unsigned countdown or a boxed self-recursive record with a decreasing size measure. See [writing modeled Go](writing-go.md).

## Interface fields at the model boundary

A value receiver can contain named interface fields even when the interface's
methods have signatures outside the modeled subset. For example, a
`FormRepository` containing a `Store` interface can expose a modeled method that
only reads a Boolean configuration field. The converter retains the store as an
opaque value and translates the method body without inspecting the store's
implementations or calling its methods.

Interface parameters, results, fields, and immutable locals may preserve a value
of the same named interface type, including aliases. An explicit `nil` initializer,
argument, field, or return value becomes `Option.none`. Reading an empty
`lean.Box[Record]` also gives nil to that record's interface fields.

The generated interface declaration is an opaque Lean type; a Go interface value
has Lean type `Option` of that carrier. The carrier's hidden definition supplies
no knowledge about implementations or their behavior. Laws using the generated
types must respect this abstraction: the model does not specify dynamic types,
method behavior, or runtime interface equality. Comparisons to nil are modeled
with `Option.isSome`; equality between two interface values remains unsupported.

### Interface method contracts

Interface calls can use explicit dependency contracts. Put `//golean:assume`
laws on the interface method, then select it with
`//golean:abstract Interface.Method` on a verified root. Imported interfaces use
`alias.Interface.Method`; interface aliases also work. Both `store.Read(n)` and
`Store.Read(store, n)` are supported, including calls through a struct field.

```go
type Store interface {
    //golean:assume increment : ∀ s n, Read s n = n + 1
    Read(n int64) int64
}

type FormRepository struct { Store Store }

//golean:abstract Store.Read
//golean:verify read : ∀ s n, «FormRepository$Read» dependency0 ⟨s⟩ n = s.map (fun _ => n + 1)
func (r FormRepository) Read(n int64) int64 {
    return r.Store.Read(n)
}
```

The contract's `operation` takes the interface receiver first, followed by the
method arguments. In assumptions, refer to it by the method name (`Read` above).
Each called interface method needs its own explicit contract. Unused methods do
not require supported signatures. Called methods must be non-variadic, have at
least one unnamed result, and use modeled parameter and result types. Multiple
method results become products, including `(value, error)` results.

A root with interface contracts returns **`Option Result`** in Lean:
`some value` denotes a normal return and `none` denotes an attempted nil
interface call. A returned Go nil interface is a normal return of an inner
`none`, so it becomes `some none`. Failure propagates through locals, arguments,
conditions, and return expressions. Boolean short-circuiting and skipped
branches preserve Go's behavior. Roots without interface contracts keep their
existing result types unless pointer dereferences or partial callees require the
same failure wrapper.

These proofs are conditional on nonnil runtime methods behaving as pure, total
functions and satisfying the declared assumptions. The converter does not
verify concrete implementations, database effects, mutable state, or additional
panics inside those implementations. The operation's value at a nil receiver is
unused. Use this model for pure interfaces or a separately justified pure
abstraction of a dependency; stateful I/O needs an explicit state model. As with
ordinary dependency contracts, contracts are local to a verified root: callers
cannot invoke that root as a concrete modeled dependency, and measured recursion
cannot be combined with its contracts.

Concrete-to-interface boxing, conversions between distinct interfaces, equality
between interface values, assertions, and type switches remain unsupported.
Anonymous interfaces and calls through an embedded
interface's promoted method also remain outside this support.

External interfaces such as `redis.Cmdable`, `context.Context`, and builtin
`error` use a fixed `golean_types.lean` support module in the consuming module.
No output is written to dependency checkouts or module caches. Retaining a
Redis interface does not model Redis operations or remove the requirement for
explicit, justified contracts on calls.

## Patterns outside the subset

Raw slices and maps, pointer mutation and identity comparisons, dereferencing opaque runtime payloads, interface calls without explicit contracts, function values, reassignments, raw Go loops, switches, user-defined generics, and unannotated or mutual recursion are outside the modeled subset. Promoted methods and stored method values remain unsupported. Nil-failing pointer reads cannot be used as fold steps or in measured recursive models.

When translation reports a Go location, trace the call from the marked operation and decide which values should cross the model boundary. The [grid game](../examples/proven/grid_game/README.md) shows a runtime driver calling a modeled step, and the [compiler](../examples/proven/stack_machine_compiler/README.md) shows raw bytes converted at the boundary.
