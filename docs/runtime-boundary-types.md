# Runtime boundary types

The converter supports read-only pointers, multiple results, and named
interfaces from external modules. This removes type-level blockers without
omitting executable statements or treating unknown I/O as verified behavior.

## Read-only pointers

Pointers to supported acyclic payloads use `Option Payload`. Both explicit `*p`
and implicit field or method dereferences preserve nil failure. A function that
can dereference a pointer returns `Option Result`; `none` means a nil access and
`some result` means normal completion. This wrapper propagates to its concrete
modeled callers. A pointer receiver that does not dereference its receiver can
still run with a nil receiver, as Go permits.

```go
type Value struct { N int64 }

func (v *Value) Read() int64 { return v.N }

//golean:verify nilRead : Read none = none
//golean:verify valueRead : ∀ n, Read (some ⟨n⟩) = some n
func Read(v *Value) int64 { return v.Read() }
```

Address-taking of immutable locals and direct fields is supported. Pointer
identity comparisons, writes through aliases, and updates to fields remain
unsupported. Snapshot eligibility depends on the type, not the selected roots,
so regenerating a dependency alone preserves its calling convention.

Pointers to runtime-only, external concrete, or recursive payloads can be held
and passed unchanged as opaque references. Nil checks still work, but attempting
to inspect those payloads fails with a source-located error. This is useful for
receivers holding clients or helpers that a selected method never reads.
Measured recursion and fold steps with nil-failing pointer reads are rejected;
they need an explicit failure state. The existing curated `lean.Box` semantics
are unchanged.

## Multiple results

Two or more unnamed results become right-associated products, such as
`Int64 × Bool` or `Int64 × Bool × List UInt8`. Direct return forwarding,
immutable destructuring, blanks, and `if` initializers work:

```go
func pair(n int64) (int64, bool) { return n + 1, n > 0 }

//golean:verify positive : Example 2 = 3
func Example(n int64) int64 {
    if value, ok := pair(n); ok { return value }
    return 0
}
```

The callee is evaluated once, including when all returned components are
discarded. Nil failures still propagate. Named results, bare returns, mixed
reassignment, and spreading a multi-result expression directly into another
call are unsupported; use explicit immutable locals for the latter.

An interface contract may return `(value, error)`. Builtin `error` is opaque and
supports nil checks. A method's normal `(value, nil)` result is `some (value,
none)` in a partial root, while a nil interface receiver gives outer `none`.

## External interfaces

External named interfaces such as `redis.Cmdable` and `context.Context` are
retained without translating their implementations or unused signatures.
Their carriers live in a generated `golean_types.lean` file in the consuming
module. That support file is independent of the selected types, so focused
generation cannot remove a carrier used by another generated package.

Concrete external records, arbitrary interface calls, and stateful Redis
effects are not inferred from these opaque types. Interface calls still need
explicit dependency assumptions. No dependency source is edited and no files
are generated in module caches.

## Probe original functions

Run the helper with the Go version required by the target module. It selects
functions in memory and preserves their original bodies, types, and imports.
The output directory must not already exist.

```sh
go run scripts/probe_package.go \
  -source /path/to/application \
  -package ./internal/service/... \
  -functions 'workspaceCommon.GetWorkspaceIDFromRole,consentCache.Check' \
  -output /tmp/new-go-lean-probe
```

For CGo projects, supply their normal `CGO_CFLAGS` and `CGO_LDFLAGS`. Use
`GOFLAGS=-mod=readonly` to prevent module metadata updates, and optionally
`GOPROXY=off GOSUMDB=off` when dependencies are already cached. The helper writes
complete models only after the entire selected graph lowers successfully.
For successful attempts it also writes a standalone Lake workspace for building
the models. It does not run proofs: `proof_verified` stays false, and any proof
companions are scaffolds. Incomplete generation returns a nonzero status after
saving `report.json`; per-function status is authoritative.

Model generation and proof verification are separate outcomes. If a probe
passes type lowering and then encounters an unsupported statement or an
uncontracted dependency, the complete graph remains unsupported. Retain its
failure report and source hashes; do not substitute a simplified body or count
a partial graph as a generated or verified application model.
