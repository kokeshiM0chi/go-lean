package main

import (
	"errors"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func command(args ...string) error {
	cmd := newCommand()
	cmd.SetArgs(args)
	return cmd.Execute()
}

func put(t *testing.T, name, contents string) {
	t.Helper()
	if err := os.MkdirAll(filepath.Dir(name), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(name, []byte(contents), 0o644); err != nil {
		t.Fatal(err)
	}
}

func get(t *testing.T, name string) string {
	t.Helper()
	data, err := os.ReadFile(name)
	if err != nil {
		t.Fatal(err)
	}
	return string(data)
}

func missing(t *testing.T, name string) {
	t.Helper()
	if _, err := os.Stat(name); !os.IsNotExist(err) {
		t.Fatalf("%s: expected missing, got %v", name, err)
	}
}

func workspace(t *testing.T, leanPackage bool) {
	t.Helper()
	repo, err := filepath.Abs("../..")
	if err != nil {
		t.Fatal(err)
	}
	repo = filepath.ToSlash(repo)
	t.Chdir(t.TempDir())
	t.Setenv("GOWORK", "off")
	mod := "module example.test/model\n\ngo 1.26.0\n"
	if leanPackage {
		mod += "\nrequire github.com/frederik-jatzkowski/go-lean v0.0.0\n" +
			"replace github.com/frederik-jatzkowski/go-lean => \"" + repo + "\"\n"
	}
	put(t, "go.mod", mod)
	if err := command("setup"); err != nil {
		t.Fatal(err)
	}
}

func TestPackageSelection(t *testing.T) {
	workspace(t, false)
	const source = `package client
import numbers "example.test/model/math"
//golean:verify law : Client 0 = 1
func Client(x int64) int64 { return numbers.Increment(x) }
func Ignored() { go func(){}() }
`
	put(t, "client/client.go", source)
	put(t, "math/math.go", `package math
//golean:export
func Increment(x int64) int64 { return helper(x) }
func helper(x int64) int64 { return x + 1 }
`)
	put(t, "client/nested/nested.go", "package nested\n//golean:export\nfunc Export() bool { return true }\n")
	put(t, "legacy/go.mod", "module example.test/legacy\n")
	put(t, "legacy/broken.go", "package this won't parse\n")
	// A manual root should survive both focused and workspace generation.
	put(t, "lakefile.toml", strings.Replace(get(t, "lakefile.toml"), "roots = [", "roots = [\n  'Manual',", 1))
	if err := command("transpile", "./client"); err != nil {
		t.Fatal(err)
	}
	missing(t, "client/nested/nested.lean")
	client := get(t, "client/client.lean")
	missing(t, "client/client_laws.lean")
	if !strings.Contains(client, "-- law :\n--   Client 0 = 1") ||
		strings.Index(client, "-- law :") > strings.Index(client, "import Std") ||
		!strings.Contains(client, "def «law» : Prop :=") {
		t.Fatal("model is missing the law review header or formal definition")
	}
	numbers := get(t, "math/math.lean")
	if !strings.Contains(client, "import «math».«math»") ||
		strings.Index(numbers, "def «helper»") > strings.Index(numbers, "def «Increment»") {
		t.Fatal("dependency was not generated and ordered")
	}
	proofFile := "client/client_proofs.lean"
	if !strings.HasPrefix(get(t, proofFile), "import «client».«client»\n") {
		t.Fatal("proof companion does not import the merged model")
	}
	if !strings.Contains(get(t, proofFile), "theorem «law» : Laws.«law»") {
		t.Fatal("missing scaffold")
	}
	const handwritten = "-- Handwritten proof companion.\r\n"
	put(t, proofFile, handwritten)
	if err := command("transpile", "./client/..."); err != nil {
		t.Fatal(err)
	}
	get(t, "client/nested/nested.lean")
	if err := command("transpile", "./..."); err != nil {
		t.Fatal(err)
	}
	lake := get(t, "lakefile.toml")
	if !strings.Contains(lake, "'Manual'") || strings.Contains(lake, "legacy") || get(t, proofFile) != handwritten {
		t.Fatal("generation changed a manual entry or proof, or selected an archived package")
	}
	if err := command("transpile", "./..."); err != nil {
		t.Fatal(err)
	}
	if get(t, "lakefile.toml") != lake || get(t, "client/client.lean") != client {
		t.Fatal("generation is not deterministic")
	}

	put(t, "client/client.go", strings.Replace(source, "return numbers.Increment(x)",
		"for x > 0 { x-- }; return numbers.Increment(x)", 1))
	err := command("transpile", "./...")
	if err == nil || !strings.Contains(err.Error(), "client.go:4:") || !strings.Contains(err.Error(), "raw loops are unsupported") {
		t.Fatalf("expected source-located loop rejection, got %v", err)
	}
	if get(t, "client/client.lean") != client || get(t, "math/math.lean") != numbers || get(t, "lakefile.toml") != lake {
		t.Fatal("a subset error changed generated output")
	}
}

func TestPackageLaws(t *testing.T) {
	workspace(t, false)
	put(t, "spec/Spec.lean", "def expected : Int64 := 1\n")
	put(t, "model/a.go", `//golean:verify:import spec.Spec
//golean:verify fromBoth : Step 0 = expected ∧
//golean:verify+ Initial = 0
package model

//golean:export
func Step(n int64) int64 { return n + 1 }

//golean:export
func Initial() int64 { return 0 }
`)
	put(t, "model/b.go", `//golean:verify:import spec.Spec
//golean:verify afterFirst : Initial = 0
package model
`)
	put(t, "model/excluded.go", "//go:build ignore\n\n//golean:verify+ This is ignored.\npackage model\n")
	put(t, "client/client.go", `package client
import "example.test/model/model"
//golean:export
func Call(n int64) int64 { return model.Step(n) }
`)
	put(t, "standalone/doc.go", "//golean:verify onlyLaw : True\npackage standalone\n")
	if err := command("transpile", "./client"); err != nil {
		t.Fatal(err)
	}
	modelFile := "model/model.lean"
	model := get(t, modelFile)
	if strings.Count(model, "import «spec».«Spec»") != 1 ||
		!strings.Contains(model, "-- fromBoth :\n--   Step 0 = expected ∧\n--   Initial = 0") ||
		!strings.Contains(model, "def «Initial»") ||
		!strings.Contains(model, "def «fromBoth» : Prop :=\n  Step 0 = expected ∧\n  Initial = 0") ||
		strings.Index(model, "-- afterFirst :") <= strings.Index(model, "-- fromBoth :") {
		t.Fatalf("unexpected model:\n%s", model)
	}
	missing(t, "model/model_laws.lean")
	missing(t, "standalone/standalone.lean")
	proofFile := "model/model_proofs.lean"
	if !strings.Contains(get(t, proofFile), "theorem «fromBoth» : Laws.«fromBoth»") ||
		!strings.Contains(get(t, "model/model_verify.lean"), "Checked.«fromBoth»") {
		t.Fatal("missing proof scaffold or checked theorem")
	}
	const handwritten = "import model.model\n-- A handwritten companion.\n"
	put(t, proofFile, handwritten)
	if err := command("transpile", "./client"); err != nil {
		t.Fatal(err)
	}
	if get(t, modelFile) != model || get(t, proofFile) != handwritten {
		t.Fatal("focused regeneration changed the dependency model or its handwritten proof")
	}
	if err := command("transpile", "./standalone"); err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(get(t, "standalone/standalone.lean"), "def «onlyLaw» : Prop") {
		t.Fatal("a package law must select a package with no modeled functions")
	}
}

func TestPackageDirectiveDiagnostics(t *testing.T) {
	workspace(t, false)
	for _, tc := range []struct{ source, diagnostic, position string }{
		{"//golean:verify:import spec..Bad\npackage example\n", "expected golean:verify:import Lean.Module", "f.go:1:"},
		{"//golean:verify:import Good Other\npackage example\n", "expected golean:verify:import Lean.Module", "f.go:1:"},
		{"//golean:verify+ True\npackage example\n", "unexpected golean:verify+ continuation", "f.go:1:"},
		{"//golean:verify law :\npackage example\n", "expected golean:verify name : proposition", "f.go:1:"},
		{"//golean:verify law : True\n//golean:verify law : True\npackage example\n", "duplicate package law law", "f.go:2:"},
		{"//golean:verify law : True\npackage example\n//golean:verify law : F = true\nfunc F() bool { return true }\n", "duplicate package law law", "f.go:3:"},
	} {
		put(t, "f.go", tc.source)
		err := command("transpile", ".")
		if err == nil || !strings.Contains(err.Error(), tc.diagnostic) || !strings.Contains(err.Error(), tc.position) {
			t.Errorf("got %v, expected %q at %s", err, tc.diagnostic, tc.position)
		}
	}
	missing(t, "example.lean")
}

func TestSubsetDiagnostics(t *testing.T) {
	workspace(t, false)
	for _, tc := range []struct{ body, diagnostic string }{
		{"func F() bool { for { return true } }", "raw loops are unsupported"},
		{"func F() bool { return helper() }; func helper() bool { for range 1 { return true }; return false }", "raw loops are unsupported"},
		{"func F(x int64) int64 { return F(x) }", "recursive call"},
		{"func F(x int64) int64 { y := x; y = 1; return y }", "only immutable"},
		{"func F(x []int64) int64 { return 0 }", "unsupported type"},
		{"func F(x int64) int64 { return x * 2 }", "unsupported binary operator"},
		{"func F() bool { return len([1]int{}) == 1 }", "unsupported constant builtin call"},
		{"func F(v Value) bool { return v.Check() }; type Value struct{ X bool }; func (v *Value) Check() bool { v.X = true; return v.X }", "only immutable"},
		{"func F() bool { return Outer{}.Check() }; type Outer struct{ Value }; type Value bool; func (v Value) Check() bool { return v == true }", "concrete value receiver"},
		{"func F(v interface{ Check() bool }) bool { return v.Check() }", "unsupported type"},
	} {
		put(t, "f.go", "package example\n//golean:export\n"+tc.body+"\n")
		err := command("transpile", ".")
		if err == nil || !strings.Contains(err.Error(), tc.diagnostic) || !strings.Contains(err.Error(), "f.go:3:") {
			t.Errorf("%s: got %v, expected %q at a source position", tc.body, err, tc.diagnostic)
		}
	}
	missing(t, "example.lean")

	put(t, "f.go", "package example\n//golean:export\nfunc F() bool { return true }\n")
	const handwritten = "-- handwritten model at the new output path\n"
	put(t, "example.lean", handwritten)
	err := command("transpile", ".")
	if err == nil || !strings.Contains(err.Error(), "would overwrite a handwritten file") || get(t, "example.lean") != handwritten {
		t.Fatalf("expected the handwritten file to be preserved, got %v", err)
	}
}

func TestFoldCallbackDiagnostics(t *testing.T) {
	workspace(t, true)
	for _, tc := range []struct{ body, diagnostic string }{
		{"return lean.FoldN(1, n, func(i, state uint) uint { return i + state })", "directly named"},
		{"return lean.FoldN(1, n, saved)", "directly named"},
		{"return lean.FoldN(1, n, generic[uint])", "non-generic"},
		{"return lean.FoldN(1, n, receiver{}.step)", "directly named"},
		{"return lean.FoldN(1, n, recursive)", "recursive call"},
	} {
		put(t, "f.go", `package example
import "github.com/frederik-jatzkowski/go-lean/pkg/lean"
func add(i, state uint) uint { return i + state }
var saved = add
func generic[T ~uint](i uint, state T) T { return state }
func recursive(i, state uint) uint { return F(i + state) }
type receiver struct{}
func (receiver) step(i, state uint) uint { return i + state }
//golean:export
func F(n uint) uint { `+tc.body+" }\n")
		err := command("transpile", ".")
		if err == nil || !strings.Contains(err.Error(), tc.diagnostic) {
			t.Errorf("%s: got %v, expected %q", tc.body, err, tc.diagnostic)
		}
	}
}

func TestDirectValueMethods(t *testing.T) {
	workspace(t, false)
	put(t, "example.go", `package example
type First struct { Value int64 }
type Second int64

//golean:export
func (v First) Add(n int64) int64 { return v.Value + n }
func (v Second) Add(n int64) int64 {
	if v == 0 { return n }
	return n - 1
}

//golean:export
func Run(first First, second Second, n int64) int64 {
	return first.Add(Second.Add(second, n))
}
`)
	if err := command("transpile", "."); err != nil {
		t.Fatal(err)
	}
	model := get(t, "example.lean")
	for _, want := range []string{
		"def «First$Add» («local:0» : ",
		".«First$Add» «local:0» (",
		"def «Second$Add» («local:0» : _root_.Int64)",
		".«Second$Add» «local:1» «local:2»",
	} {
		if !strings.Contains(model, want) {
			t.Errorf("expected %q in the generated model:\n%s", want, model)
		}
	}
}

func TestTargetWordSize(t *testing.T) {
	workspace(t, true)
	t.Setenv("GOOS", "linux")
	t.Setenv("GOARCH", "386")
	put(t, "word.go", `package word
import "github.com/frederik-jatzkowski/go-lean/pkg/lean"
func next(index, x uint) uint { return x + index }
//golean:export
func Sum(n uint) uint { return lean.FoldN(n, uint(0), next) }
`)
	if err := command("transpile", "."); err != nil {
		t.Fatal(err)
	}
	model := get(t, "word.lean")
	if !strings.Contains(model, "step : _root_.UInt32") || strings.Contains(model, "_root_.UInt64") {
		t.Fatalf("Go 386 word size did not reach the model:\n%s", model)
	}
}

func TestCuratedLeanSemantics(t *testing.T) {
	if _, err := exec.LookPath("lake"); err != nil {
		t.Skip("lake is unavailable")
	}
	workspace(t, true)
	put(t, "model.go", curatedGo)
	if err := command("transpile", "."); err != nil {
		t.Fatal(err)
	}
	file := "model_proofs.lean"
	scaffold := get(t, file)
	// Exercise the axiom audit even with warning-as-error disabled.
	put(t, "lakefile.toml", strings.Replace(get(t, "lakefile.toml"), "-DwarningAsError=true", "-DwarningAsError=false", 1))
	cmd := exec.Command("lake", "build", "+model_verify")
	output, err := cmd.CombinedOutput()
	var failure *exec.ExitError
	if !errors.As(err, &failure) || !strings.Contains(string(output), "unapproved axiom sorryAx") {
		t.Fatalf("expected scaffold to fail axiom audit, got %v\n%s", err, output)
	}
	for _, law := range []string{"arrays", "bits", "bytes", "branches", "folds", "lists", "options", "ordered", "overflow", "signedMinimum"} {
		proof := "theorem «" + law + "» : Laws.«" + law + "» := by\n"
		scaffold = strings.Replace(scaffold, proof+"  sorry", proof+"  unfold Laws.«"+law+"»\n  decide", 1)
	}
	put(t, file, scaffold)
	output, err = exec.Command("lake", "build", "+model_verify").CombinedOutput()
	if err != nil {
		t.Fatalf("proof verification failed: %v\n%s", err, output)
	}
}

const curatedGo = `package model

import curated "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type key int16

//golean:export
func Bool() bool { return true }

//golean:verify branches : Branches true = 7 ∧ Branches false = 7
func Branches(choose bool) int8 {
	x := int8(7)
	if choose {
		var x = x - 1
		if x == 0 { return x }
	} else {
		var x = x + 1
		if x == 0 { return x }
	}
	return x
}

//golean:verify arrays : Arrays = true
func Arrays() bool {
	empty := curated.Array[int8]{}
	a := empty.Push(5).Push(7)
	b := a.Set(0, 9).Set(8, 11).Pop()
	return empty.Pop().Size() == 0 && b.Size() == 1 &&
		b.Get(0).UnwrapOr(0) == 9 && !b.Get(1).IsSome() && a.Get(0).UnwrapOr(0) == 5
}

//golean:verify bytes : Bytes = true
func Bytes() bool {
	a := curated.ByteArray{}.Push(5).Push(7).Push(9)
	b := a.Set(1, 8).Set(9, 12).Extract(1, 10)
	return b.Size() == 2 && b.Get(0).UnwrapOr(0) == 8 && b.Get(1).UnwrapOr(0) == 9 &&
		!b.Get(2).IsSome() && b.Extract(1, 0).Size() == 0 && b.Extract(5, 9).Size() == 0
}

//golean:verify ordered : Ordered = true
func Ordered() bool {
	m := curated.OrderedMap[string, int8]{}.Insert("\xff", 7).Insert("\x00", 1)
	r := m.Insert("\xff", 8).Erase("\x00")
	s := curated.OrderedSet[key]{}.Insert(-2).Insert(1).Insert(-2).Erase(1)
	return before("\x00", "\xff") && !before("\xff", "\x00") && m.Find("\xff").UnwrapOr(0) == 7 &&
		r.Find("\xff").UnwrapOr(0) == 8 && !r.Contains("\x00") &&
		s.Contains(-2) && !s.Contains(1)
}

func before(a, b string) bool { return a < b }

//golean:verify options : Options = true
func Options() bool {
	a := curated.None[int8]()
	b := curated.Option[int8]{}
	c := curated.Some(int8(0))
	return !a.IsSome() && !b.IsSome() && c.IsSome() &&
		a.UnwrapOr(9) == 9 && c.UnwrapOr(9) == 0
}

//golean:verify lists : Lists = true
func Lists() bool {
	a := curated.Nil[int8]()
	b := curated.List[int8]{}
	return a.IsEmpty() && b.IsEmpty() && !curated.Cons(int8(0), a).IsEmpty()
}

//golean:verify bits : Bits = true
func Bits() bool {
	empty := curated.BitVec{}
	zero := curated.NewBitVec(0, 7).UnwrapOr(empty)
	a := curated.NewBitVec(64, 1).UnwrapOr(empty)
	b := a.Set(63, true).Set(0, false).Set(64, true)
	return zero.Width() == 0 && zero.ToUint64() == 0 && !zero.Get(0).IsSome() &&
		a.Width() == 64 && a.Get(0).UnwrapOr(false) && b.Get(63).UnwrapOr(false) &&
		!b.Get(0).UnwrapOr(true) && !b.Get(64).IsSome() &&
		b.ToUint64() == 9223372036854775808 && !curated.NewBitVec(65, 0).IsSome()
}

//golean:verify overflow : Overflow 127 = -128
func Overflow(x int8) int8 { return x + 1 }

//golean:verify signedMinimum : SignedMinimum = true
func SignedMinimum() bool { return Overflow(127) == -128 }

func grow(index uint, state uint) uint { return state + state + index }
func nested(index uint, state uint) uint { return curated.FoldN(index, state, grow) }
func stopAtOne(index uint, state uint) curated.FoldControl[uint] {
	return curated.FoldControl[uint]{Stop: index == 1, State: grow(index, state)}
}
func record(value int8, state int8) int8 { return state + state + value }
func stopAtTwo(value int8, state int8) curated.FoldControl[int8] {
	return curated.FoldControl[int8]{State: record(value, state), Stop: value == 2}
}

//golean:verify folds : Folds = true
func Folds() bool {
	one := curated.FoldN(1, uint(2), grow)
	count := curated.FoldN(3, one, nested)
	empty := curated.FoldNUntil(0, uint(1), stopAtOne)
	done := curated.FoldNUntil(8, uint(1), stopAtOne)
	last := curated.FoldNUntil(2, uint(1), stopAtOne)
	exhausted := curated.FoldNUntil(1, uint(1), stopAtOne)
	items := curated.Cons(int8(2), curated.Cons(int8(3), curated.Nil[int8]()))
	first := curated.FoldListUntil(items, int8(1), stopAtTwo)
	return count == 33 && empty.State == 1 && !empty.Stop &&
		done.Stop && done.State == 5 && last.Stop && last.State == 5 &&
		!exhausted.Stop && exhausted.State == 2 &&
		first.Stop && first.State == 4 && curated.FoldList(items, int8(1), record) == 11
}
`

func TestBoxedRecursion(t *testing.T) {
	if _, err := exec.LookPath("lake"); err != nil {
		t.Skip("lake is unavailable")
	}
	workspace(t, true)
	put(t, "model.go", `package model
import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type Tree struct {
	Value byte
	Left, Right lean.Box[Tree]
}

//golean:termination:by sizeOf tree
func Sum(tree Tree) byte {
	if tree.Left.IsSome() {
		left := Sum(tree.Left.Get())
		if tree.Right.IsSome() {
			return tree.Value + left + Sum(tree.Right.Get())
		}
		return tree.Value + left
	}
	return tree.Value
}

//golean:termination:by n.toNat
func Countdown(n byte) byte {
	if n > 0 {
		return Countdown(n - 1) + 1
	}
	return 0
}

//golean:verify result : Demo = 10
func Demo() byte {
	empty := lean.Box[Tree]{}
	zero := empty.Get()
	boxedZero := lean.NewBox(zero)
	leaf := Tree{Value: 2, Left: empty, Right: empty}
	tree := Tree{Value: 3, Left: lean.NewBox(leaf), Right: lean.NewBox(leaf)}
	if !empty.IsSome() && boxedZero.IsSome() && !zero.Left.IsSome() && !zero.Right.IsSome() {
		return Sum(tree) + Countdown(3)
	}
	return 0
}
`)
	if err := command("transpile", "."); err != nil {
		t.Fatal(err)
	}
	proofs := "model_proofs.lean"
	put(t, proofs, strings.Replace(get(t, proofs), "  sorry", "  simp [Laws.«result», Demo, Sum.eq_def, Countdown.eq_def, Tree.«field:Left», Tree.«field:Right», Tree.«field:Value»]", 1))
	if err := command("verify", "."); err != nil {
		t.Fatal(err)
	}
}

func TestRejectInvalidBoxedRecursion(t *testing.T) {
	for _, tc := range []struct {
		name, declaration, want string
	}{
		{"slice", "func F(x lean.Box[[]byte]) byte { return 0 }", "unsupported type []byte"},
		{"map", "func F(x lean.Box[map[byte]byte]) byte { return 0 }", "unsupported type map"},
		{"unannotated", "func F(x lean.Box[byte]) byte { return F(x) }", "recursive call"},
		{"mutual", "//golean:termination:by x.toNat\nfunc F(x byte) byte { return other(x) }\nfunc other(x byte) byte { return F(x) }", "recursive call"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			workspace(t, true)
			imports := ""
			if strings.Contains(tc.declaration, "lean.Box") {
				imports = "import \"github.com/frederik-jatzkowski/go-lean/pkg/lean\"\n"
			}
			put(t, "model.go", "package model\n"+imports+"//golean:export\n"+tc.declaration+"\n")
			if err := command("transpile", "."); err == nil || !strings.Contains(err.Error(), tc.want) {
				t.Fatalf("expected %q, got %v", tc.want, err)
			}
		})
	}
}

func TestRejectNondecreasingCall(t *testing.T) {
	if _, err := exec.LookPath("lake"); err != nil {
		t.Skip("lake is unavailable")
	}
	workspace(t, false)
	put(t, "model.go", `package model

//golean:export
//golean:termination:by n.toNat
func Bad(n byte) byte { return Bad(n + 1) }
`)
	if err := command("transpile", "."); err != nil {
		t.Fatal(err)
	}
	out, err := exec.Command("lake", "build", "+model").CombinedOutput()
	if err == nil || !strings.Contains(string(out), "could not prove that the recursive call decreases") {
		t.Fatalf("expected Lean to reject the decrease, got %v\n%s", err, out)
	}
}
