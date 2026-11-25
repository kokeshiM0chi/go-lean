package main

import (
	"os/exec"
	"strings"
	"testing"
)

func TestRuntimeBoundaryTypes(t *testing.T) {
	workspace(t, true)
	put(t, "external/go.mod", "module example.test/redis\n\ngo 1.26.0\n")
	put(t, "external/redis.go", `package redis
import "context"
type Cmdable interface { Get(context.Context, string) *StringCmd }
type StringCmd struct { Data []byte; State map[string]string }
`)
	put(t, "go.mod", get(t, "go.mod")+"\nrequire example.test/redis v0.0.0\nreplace example.test/redis => ./external\n")
	put(t, "bridge/bridge.go", `package bridge
import redis "example.test/redis"
type Counter struct { N int64 }
//golean:export
func Echo(r redis.Cmdable) redis.Cmdable { return r }
//golean:export
func Forward(p *Counter) *Counter { return p }
`)
	put(t, "model.go", runtimeBoundaryGo)
	if err := command("transpile", "."); err != nil {
		t.Fatal(err)
	}
	model, carriers := get(t, "model.lean"), get(t, "golean_types.lean")
	for _, want := range []string{"def «Pair»", "def «Value$Read»", "(_root_.Option _root_.Int64)", "example.test/redis.Cmdable", "*example.test/redis.StringCmd"} {
		if !strings.Contains(model, want) {
			t.Errorf("missing %q in model:\n%s", want, model)
		}
	}
	if strings.Contains(carriers, "StringCmd") || !strings.Contains(carriers, "opaque «carrier»") {
		t.Fatal("support module must be independent of selected types")
	}
	if err := command("transpile", "./bridge"); err != nil {
		t.Fatal(err)
	}
	if get(t, "golean_types.lean") != carriers || get(t, "model.lean") != model {
		t.Fatal("focused generation invalidated existing models")
	}
	if !strings.Contains(get(t, "lakefile.toml"), "'model'") {
		t.Fatal("focused generation removed an unrelated root from Lake")
	}
	t.Run("Lean", func(t *testing.T) {
		if _, err := exec.LookPath("lake"); err != nil {
			t.Skip("lake is unavailable")
		}
		proof := get(t, "model_proofs.lean")
		for _, line := range strings.Split(proof, "\n") {
			if _, tail, ok := strings.Cut(line, ": Laws."); ok {
				law, _, _ := strings.Cut(tail, " := by")
				proof = strings.Replace(proof, ": Laws."+law+" := by\n  sorry", ": Laws."+law+" := by\n  unfold Laws."+law+"\n  intros\n  rfl", 1)
			}
		}
		put(t, "model_proofs.lean", proof)
		if err := command("verify", "."); err != nil {
			t.Fatal(err)
		}
	})
}

const runtimeBoundaryGo = `package model
import (
  "context"
  redis "example.test/redis"
  "example.test/model/bridge"
  "github.com/frederik-jatzkowski/go-lean/pkg/lean"
)
type SecureAccessChecker struct{}
type Service struct { Checker *SecureAccessChecker; Redis redis.Cmdable; Handle *redis.StringCmd }
type Alias = redis.StringCmd
type Value struct { N int64 }
func (v *Value) Read() int64 { return v.N }
func (v Value) Copy() int64 { return v.N }
func (v *SecureAccessChecker) Allow() bool { return true }

//golean:verify boundary : ∀ s, Keep s = s
func Keep(s Service) Service { return Service{Checker:s.Checker, Redis:bridge.Echo(s.Redis), Handle:s.Handle} }
//golean:verify opaqueAlias : ∀ p, AliasPointer p = p
func AliasPointer(p *Alias) *redis.StringCmd { return p }
//golean:verify context : ∀ ctx, KeepContext ctx = ctx
func KeepContext(ctx context.Context) context.Context { return ctx }
//golean:verify bridgeNil : ReadBridge none = none
func ReadBridge(p *bridge.Counter) int64 { q := bridge.Forward(p); return q.N }
//golean:verify nilReceiver : NilReceiver = true
func NilReceiver() bool { var c *SecureAccessChecker = nil; return c.Allow() }
//golean:verify readNil : Read none = none
func Read(p *Value) int64 { return p.Read() }
//golean:verify readSome : ∀ n, Read (some ⟨n⟩) = some n
func ReadSome(p *Value) int64 { return p.Read() }
//golean:verify implicitDeref : CopyRead none = none
func CopyRead(p *Value) int64 { return p.Copy() }
//golean:verify implicitAddress : ∀ n, AddressRead n = some n
func AddressRead(n int64) int64 { v := Value{N:n}; return v.Read() }
//golean:verify pointerExpression : PointerExpression none = none
func PointerExpression(p *Value) int64 { return (*Value).Read(p) }
//golean:verify valueExpression : ValueExpression none = none
func ValueExpression(p *Value) int64 { return (*Value).Copy(p) }
//golean:verify guarded : Guarded none = some 0
func Guarded(p *int64) int64 { if p == nil { return 0 }; return *p }
//golean:verify address : ∀ n, Address n = some n
func Address(n int64) *int64 { return &n }
//golean:verify zeroPointer : ZeroPointer none = none
func ZeroPointer(p lean.Box[*int64]) *int64 { return p.Get() }

//golean:export
func Pair(n int64) (int64, bool) { return n + 1, n > 0 }
//golean:verify forward : Forward 2 = (3, true)
func Forward(n int64) (int64, bool) { return Pair(n) }
//golean:verify destructure : Destructure 2 = 3
func Destructure(n int64) int64 { v, ok := Pair(n); if ok { return v }; return 0 }
func Triple() (bool, int64, string) { return true, 9, "ok" }
//golean:verify third : Third = ([111,107] : List UInt8)
func Third() string { _, _, s := Triple(); return s }
//golean:verify firstTwo : FirstTwo = (true, 9)
func FirstTwo() (bool, int64) { a, b, _ := Triple(); return a, b }
//golean:verify discard : Discard = true
func Discard() bool { var _, _ = Pair(0); return true }
func ReadPair(p *int64) (int64, bool) { return *p, true }
//golean:verify droppedFailure : DropPair none = none
func DropPair(p *int64) bool { var _, _ = ReadPair(p); return true }
//golean:export
func Maybe(p *int32) (*int32, error) { return p, nil }
//golean:verify errorTuple : ∀ p, MaybeLaw p = (p, none)
func MaybeLaw(p *int32) (*int32, error) { return Maybe(p) }
//golean:verify initializer : ∀ p, Initializer p = true
func Initializer(p *int32) bool { if _, err := Maybe(p); err != nil { return false }; return true }
`

func TestMultipleResultInterfaceContract(t *testing.T) {
	workspace(t, false)
	put(t, "model.go", `package model
type Reader interface {
  //golean:assume result : ∀ s n, Read s n = (n, none)
  Read(int64) (int64, error)
}
//golean:abstract Reader.Read
//golean:verify query : ∀ s n, Query dependency0 s n = s.map (fun _ => (n, none))
func Query(s Reader, n int64) (int64, error) {
  v, err := s.Read(n)
  if err != nil { return 0, err }
  return v, nil
}
`)
	if err := command("transpile", "."); err != nil {
		t.Fatal(err)
	}
	if _, err := exec.LookPath("lake"); err != nil {
		t.Skip("lake is unavailable")
	}
	put(t, "model_proofs.lean", `import «model»
namespace GoLean.«example.test/model».Proofs
theorem query : Laws.query := by
  intro d s n
  cases s <;> simp [Query, d.result]
end GoLean.«example.test/model».Proofs
`)
	if err := command("verify", "."); err != nil {
		t.Fatal(err)
	}
}

func TestReadOnlyPointerDiagnostics(t *testing.T) {
	workspace(t, false)
	for _, tc := range []struct{ name, source, diagnostic string }{
		{"write", "func F(p *int64) int64 { *p = 1; return *p }", "only immutable"},
		{"identity", "func F(a, b *int64) bool { return a == b }", "unsupported operands"},
		{"recursive_payload", "func F(n *Node) bool { return n.Next == nil }; type Node struct { Next *Node }", "pointer dereference requires"},
		{"named_result", "func F(n int64) (x int64, ok bool) { return n, true }", "named results"},
		{"void", "func F() {}", "at least one result"},
		{"tuple_arguments", "func F() int64 { return Add(Pair()) }; func Add(a, b int64) int64 { return a+b }; func Pair() (int64,int64) { return 1,2 }", "destructure multiple results"},
		{"opaque_address", "func F() *Node { return &Node{Next:nil} }; type Node struct { Next *Node }", "address-taking requires"},
		{"opaque_implicit_address", "func F(n Node) bool { return n.Valid() }; type Node struct { Next *Node }; func (*Node) Valid() bool { return true }", "implicit address-taking requires"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			put(t, "model.go", "package model\n//golean:export\n"+tc.source+"\n")
			err := command("transpile", ".")
			if err == nil || !strings.Contains(err.Error(), tc.diagnostic) {
				t.Fatalf("expected %q, got %v", tc.diagnostic, err)
			}
			missing(t, "model.lean")
		})
	}
}

func TestPartialPointerFoldDiagnostic(t *testing.T) {
	workspace(t, true)
	put(t, "model.go", `package model
import "github.com/frederik-jatzkowski/go-lean/pkg/lean"
func step(i uint, p *int64) *int64 { if *p == 0 { return nil }; return p }
//golean:export
func F(p *int64) *int64 { return lean.FoldN(1, p, step) }
`)
	err := command("transpile", ".")
	if err == nil || !strings.Contains(err.Error(), "fold steps with partial pointer reads") {
		t.Fatalf("expected partial step rejection, got %v", err)
	}
	missing(t, "model.lean")
}
