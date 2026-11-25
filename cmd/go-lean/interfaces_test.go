package main

import (
	"os/exec"
	"strings"
	"testing"
)

func TestOpaqueInterfaceValues(t *testing.T) {
	workspace(t, true)
	put(t, "ports/ports.go", `package ports
// The opaque carrier must not require modeling I/O signatures.
type Store interface { Save([]byte) (bool, error) }
`)
	put(t, "example.go", `package example
import (
  "example.test/model/ports"
  "github.com/frederik-jatzkowski/go-lean/pkg/lean"
)
type Store = ports.Store
type FormRepository struct { Store Store; Enabled bool }

//golean:verify ready : ∀ r, «FormRepository$Ready» r = r.«field:Enabled»
func (r FormRepository) Ready() bool { return r.Enabled }

func identity(s Store) Store { return s }

//golean:export
func (r FormRepository) With(s Store) FormRepository {
  var saved Store = identity(s)
  return FormRepository{Store: saved, Enabled: r.Enabled}
}

//golean:export
func Keep(r FormRepository) FormRepository { return r.With(r.Store) }

//golean:export
func Empty() Store { return (nil) }

//golean:export
func NilArgument(r FormRepository) FormRepository { return FormRepository.With(r, nil) }

//golean:export
func NilField() FormRepository { return FormRepository{Store: nil, Enabled: false} }

//golean:export
func NilLocal() Store { var s Store = nil; return s }

//golean:export
func Zero(box lean.Box[FormRepository]) FormRepository { return box.Get() }

//golean:export
func Some(s Store) lean.Option[Store] { return lean.Some[Store](s) }
`)
	if err := command("transpile", "."); err != nil {
		t.Fatal(err)
	}
	port := get(t, "ports/ports.lean")
	if strings.Count(port, "opaque «Store» : Type := _root_.Nat") != 1 || strings.Contains(port, "Save") {
		t.Fatalf("expected one opaque carrier without method implementations:\n%s", port)
	}
	model := get(t, "example.lean")
	for _, want := range []string{
		"import «ports».«ports»",
		"«field:Store» : (_root_.Option _root_.GoLean.«example.test/model/ports».«Store»)",
		"def «FormRepository$Ready»",
		"def «Keep»",
		"_root_.Option.none",
		"_root_.Option.getD",
	} {
		if !strings.Contains(model, want) {
			t.Errorf("expected %q in generated model:\n%s", want, model)
		}
	}
	if err := command("transpile", "."); err != nil {
		t.Fatal(err)
	}
	if get(t, "example.lean") != model || get(t, "ports/ports.lean") != port {
		t.Fatal("opaque interface generation is not deterministic")
	}
	t.Run("Lean", func(t *testing.T) {
		if _, err := exec.LookPath("lake"); err != nil {
			t.Skip("lake is unavailable")
		}
		proof := get(t, "example_proofs.lean")
		put(t, "example_proofs.lean", strings.Replace(proof, "  sorry", "  intro r; rfl", 1))
		if err := command("verify", "."); err != nil {
			t.Fatal(err)
		}
	})
}

func TestOpaqueInterfaceDiagnostics(t *testing.T) {
	workspace(t, true)
	const prefix = `package example
import "github.com/frederik-jatzkowski/go-lean/pkg/lean"
type Store interface { Check() bool }
type Other interface { Check() bool }
type Value bool
func (Value) Check() bool { return true }
type Holder struct { Store Store }
func consume(s Store) bool { return true }
func step(i uint, s Store) Store { return s }
var _ lean.Option[Store]
//golean:export
`
	for _, tc := range []struct{ name, source, diagnostic string }{
		{"dispatch", "func F(s Store) bool { return s.Check() }", "interface method calls require an explicit"},
		{"method_expression", "func F(s Store) bool { return Store.Check(s) }", "interface method calls require an explicit"},
		{"return_boxing", "func F() Store { return Value(false) }", "interface conversion"},
		{"local_boxing", "func F() Store { var s Store = Value(false); return s }", "interface conversion"},
		{"argument_boxing", "func F() bool { return consume(Value(false)) }", "interface conversion"},
		{"field_boxing", "func F() Holder { return Holder{Store: Value(false)} }", "interface conversion"},
		{"curated_boxing", "func F() lean.Option[Store] { return lean.Some[Store](Value(false)) }", "interface conversion"},
		{"fold_boxing", "func F() Store { return lean.FoldN[Store](0, Value(false), step) }", "interface conversion"},
		{"interface_conversion", "func F(s Store) Other { return s }", "interface conversion"},
		{"equality", "func F(s Store) bool { return s == s }", "unsupported operands"},
		{"assertion", "func F(s Store) Value { return s.(Value) }", "unsupported expression"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			put(t, "example.go", prefix+tc.source+"\n")
			err := command("transpile", ".")
			if err == nil || !strings.Contains(err.Error(), tc.diagnostic) || !strings.Contains(err.Error(), "example.go:") {
				t.Fatalf("expected source-located %q, got %v", tc.diagnostic, err)
			}
			missing(t, "example.lean")
		})
	}
}

func TestInterfaceMethodContracts(t *testing.T) {
	workspace(t, true)
	put(t, "ports/ports.go", `package ports
type Store interface {
  //golean:assume increment : ∀ s n, Read s n = n + 1
  Read(n int64) int64
  // An unused unsupported method must not prevent generation.
  Save([]byte) (bool, error)
}
`)
	put(t, "example.go", interfaceContractGo)
	if err := command("transpile", "."); err != nil {
		t.Fatal(err)
	}
	model := get(t, "example.lean")
	for _, want := range []string{
		"structure «contract:FormRepository$Read:example.test/model/ports.Store$Read»",
		"(let «Read» := operation;",
		" : (_root_.Option _root_.Int64) :=",
		"_root_.Option.bind",
		".isSome then (_root_.Option.some",
		"«dependency:example.test/model/ports.Store$Read».operation",
	} {
		if !strings.Contains(model, want) {
			t.Errorf("expected %q in the generated model:\n%s", want, model)
		}
	}
	if err := command("transpile", "."); err != nil {
		t.Fatal(err)
	}
	if get(t, "example.lean") != model {
		t.Fatal("interface contract generation is not deterministic")
	}
	t.Run("Lean", func(t *testing.T) {
		if _, err := exec.LookPath("lake"); err != nil {
			t.Skip("lake is unavailable")
		}
		put(t, "example_proofs.lean", interfaceContractProofs)
		if err := command("verify", "."); err != nil {
			t.Fatal(err)
		}
	})
}

const interfaceContractGo = `package example
import (
  p "example.test/model/ports"
  "github.com/frederik-jatzkowski/go-lean/pkg/lean"
)
type Store = p.Store
type FormRepository struct { Store Store }
type Result struct { Value int64 }
type Source interface {
  //golean:assume snapshot : ∀ s, (Snapshot s).«field:Value» = 3
  Snapshot() Result
}
type Chain interface {
  //golean:assume empty : ∀ s, Next s = none
  Next() Chain
}

//golean:abstract p.Store.Read
//golean:verify read : ∀ s n, «FormRepository$Read» dependency0 ⟨s⟩ n = s.map (fun _ => n + 1)
func (r FormRepository) Read(n int64) int64 { return r.Store.Read(n) }

//golean:abstract Store.Read
//golean:verify expression : ∀ s n, Expression dependency0 s n = s.map (fun _ => n + 1)
func Expression(s Store, n int64) int64 { return Store.Read(s, n) }

//golean:abstract p.Store.Read
//golean:verify nilCall : NilCall dependency0 0 = none
func NilCall(n int64) int64 { var s Store = nil; return s.Read(n) }

//golean:abstract Store.Read
//golean:verify guarded : Guarded dependency0 none 0 = some 7
func Guarded(s Store, n int64) int64 {
  if nil == s { return 7 }
  return s.Read(n)
}

//golean:abstract Store.Read
//golean:verify shortCircuit : ShortCircuit dependency0 none = some false
func ShortCircuit(s Store) bool { return s != nil && s.Read(0) > 0 }

//golean:abstract Store.Read
//golean:verify shortOr : ShortOr dependency0 none = some true
func ShortOr(s Store) bool { return s == nil || s.Read(0) > 0 }

//golean:abstract Store.Read
//golean:verify nested : ∀ s n, Nested dependency0 s n = s.map (fun _ => n + 2)
func Nested(s Store, n int64) int64 { return s.Read(s.Read(n)) }

//golean:abstract Store.Read
//golean:verify propagation : Propagation dependency0 none 0 = none
func Propagation(s Store, n int64) int64 {
  v := s.Read(n)
  return Result{Value: v + 1}.Value
}

//golean:abstract Store.Read
//golean:verify branch : Branch dependency0 none 0 = some 7
func Branch(s Store, n int64) int64 {
  if s != nil { v := s.Read(n); if v > 0 { return v } }
  return 7
}

//golean:abstract Store.Read
//golean:verify curated : Curated dependency0 none 0 = none
func Curated(s Store, n int64) lean.Option[int64] { return lean.Some(s.Read(n)) }

//golean:export
func IsNil(s Store) bool { return s == nil }

//golean:abstract Source.Snapshot
//golean:verify snapshotField : ∀ s, SnapshotField dependency0 s = s.map (fun _ => 3)
func SnapshotField(s Source) int64 { return s.Snapshot().Value }

//golean:abstract Chain.Next
//golean:verify nilResult : ∀ s, NilResult dependency0 s = s.map (fun _ => none)
func NilResult(s Chain) Chain { return s.Next() }

//golean:abstract Chain.Next
//golean:verify chain : ∀ s, Follow dependency0 s = none
func Follow(s Chain) Chain { return s.Next().Next() }
`

const interfaceContractProofs = `import «example»
namespace GoLean.«example.test/model».Proofs
theorem read : Laws.read := by
  intro d s n
  cases s <;> simp [«FormRepository$Read», d.increment]
theorem expression : Laws.expression := by
  intro d s n
  cases s <;> simp [Expression, d.increment]
theorem nilCall : Laws.nilCall := by intro d; rfl
theorem guarded : Laws.guarded := by intro d; rfl
theorem shortCircuit : Laws.shortCircuit := by intro d; rfl
theorem shortOr : Laws.shortOr := by intro d; rfl
theorem nested : Laws.nested := by
  intro d s n
  cases s <;> simp [Nested, d.increment, Int64.add_assoc]
theorem propagation : Laws.propagation := by intro d; rfl
theorem branch : Laws.branch := by intro d; rfl
theorem curated : Laws.curated := by intro d; rfl
theorem snapshotField : Laws.snapshotField := by
  intro d s
  cases s <;> simp [SnapshotField, d.snapshot]
theorem nilResult : Laws.nilResult := by
  intro d s
  cases s <;> simp [NilResult, d.empty]
theorem chain : Laws.chain := by
  intro d s
  cases s <;> simp [Follow, d.empty]
end GoLean.«example.test/model».Proofs
`

func TestInterfaceContractDiagnostics(t *testing.T) {
	workspace(t, false)
	for _, tc := range []struct{ name, declaration, directives, body, diagnostic string }{
		{"missing_assumptions", "Read(int64) int64", "//golean:abstract Store.Read\n", "return s.Read(0)", "golean:assume laws"},
		{"variadic", "//golean:assume law : True\nRead(...int64) int64", "//golean:abstract Store.Read\n", "return s.Read(0)", "function signature"},
		{"method_directive", "//golean:verify law : True\n//golean:assume ok : True\nRead(int64) int64", "//golean:abstract Store.Read\n", "return s.Read(0)", "interface methods only support"},
		{"duplicate", "//golean:assume law : True\nRead(int64) int64", "//golean:abstract Store.Read\n//golean:abstract Alias.Read\n", "return s.Read(0)", "duplicate abstract callee"},
		{"unused", "//golean:assume law : True\nRead(int64) int64", "//golean:abstract Store.Read\n", "return 0", "unused abstract callee"},
		{"stored_method", "//golean:assume law : True\nRead(int64) int64", "//golean:abstract Store.Read\n", "saved := s.Read; return saved(0)", "unsupported type func"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			put(t, "example.go", "package example\ntype Store interface {\n"+tc.declaration+"\n}\ntype Alias = Store\n"+tc.directives+
				"//golean:verify root : True\nfunc F(s Store) int64 { "+tc.body+" }\n")
			err := command("transpile", ".")
			if err == nil || !strings.Contains(err.Error(), tc.diagnostic) || !strings.Contains(err.Error(), "example.go:") {
				t.Fatalf("expected source-located %q, got %v", tc.diagnostic, err)
			}
			missing(t, "example.lean")
		})
	}
}
