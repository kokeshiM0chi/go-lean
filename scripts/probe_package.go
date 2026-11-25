//go:build ignore

// Probe original functions without editing or copying application source.
// Run with the Go toolchain required by the source module, from go-lean's root.
package main

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"go/types"
	"os"
	"path/filepath"
	"runtime"
	"sort"
	"strings"

	golean "github.com/frederik-jatzkowski/go-lean"
	"github.com/frederik-jatzkowski/go-lean/internal/emit"
	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/load"
	"github.com/frederik-jatzkowski/go-lean/internal/lower"
)

type attempt struct {
	Function       string `json:"function"`
	Source         string `json:"source,omitempty"`
	SHA256         string `json:"source_sha256,omitempty"`
	Error          string `json:"error,omitempty"`
	ModelGenerated bool   `json:"model_generated"`
	ProofVerified  bool   `json:"proof_verified"`
}

func main() {
	if err := run(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

func run() error {
	source := flag.String("source", "", "original Go module directory (read only)")
	pattern := flag.String("package", "./...", "Go package selection")
	names := flag.String("functions", "", "comma-separated Function or Type.Method names")
	out := flag.String("output", "", "new directory for reports and complete models")
	flag.Parse()
	if *source == "" || *names == "" || *out == "" {
		return fmt.Errorf("-source, -functions, and -output are required")
	}
	root, err := filepath.Abs(*source)
	if err != nil {
		return err
	}
	if err := os.Mkdir(*out, 0o755); err != nil {
		return err
	}
	program, err := load.Read(context.Background(), root, *pattern)
	if err != nil {
		return fmt.Errorf("load: %w", err)
	}
	var results []attempt
	for index, requested := range strings.Split(*names, ",") {
		requested = strings.TrimSpace(requested)
		result := attempt{Function: requested}
		var matches []*types.Func
		for fn := range program.Functions {
			name := fn.Name()
			if recv := fn.Signature().Recv(); recv != nil {
				t := types.Unalias(recv.Type())
				if ptr, ok := t.(*types.Pointer); ok {
					t = types.Unalias(ptr.Elem())
				}
				if named, ok := t.(*types.Named); ok {
					name = named.Obj().Name() + "." + name
				} else {
					continue
				}
			}
			if name == requested {
				matches = append(matches, fn)
			}
		}
		if len(matches) != 1 {
			result.Error = fmt.Sprintf("expected one matching function; found %d", len(matches))
			results = append(results, result)
			continue
		}
		fn := matches[0]
		entry := program.Functions[fn]
		file := entry.Package.Fset.Position(entry.Decl.Pos()).Filename
		data, err := os.ReadFile(file)
		if err != nil {
			return err
		}
		hash := sha256.Sum256(data)
		result.SHA256 = hex.EncodeToString(hash[:])
		result.Source, _ = filepath.Rel(root, file)
		program.Roots = []*types.Func{fn}
		models, err := lower.Program(program)
		if err != nil {
			result.Error = strings.ReplaceAll(err.Error(), root+string(filepath.Separator), "<SOURCE>/")
		} else {
			dir := filepath.Join(*out, fmt.Sprintf("model_%02d", index))
			if err := writeModels(dir, models); err != nil {
				return err
			}
			result.ModelGenerated = true
		}
		results = append(results, result)
		fmt.Printf("%s: generated=%t %s\n", result.Function, result.ModelGenerated, result.Error)
	}
	report := struct {
		GoVersion     string    `json:"go_version"`
		Package       string    `json:"package"`
		SelectionOnly bool      `json:"selection_only"`
		Functions     []attempt `json:"functions"`
	}{runtime.Version(), *pattern, true, results}
	data, err := json.MarshalIndent(report, "", "  ")
	if err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(*out, "report.json"), append(data, '\n'), 0o644); err != nil {
		return err
	}
	for _, result := range results {
		if !result.ModelGenerated {
			return fmt.Errorf("incomplete model generation; see %s", filepath.Join(*out, "report.json"))
		}
	}
	return nil
}

func writeModels(dir string, packages []*ir.Package) error {
	modules, dirs := make(map[string]string), make(map[string]string)
	for _, p := range packages {
		hash := sha256.Sum256([]byte(p.Path))
		rel := "p_" + hex.EncodeToString(hash[:6])
		dirs[p.Path], modules[p.Path] = rel, emit.Module(rel, p.Name)
	}
	var roots []string
	for _, p := range packages {
		dest := filepath.Join(dir, dirs[p.Path])
		if err := os.MkdirAll(dest, 0o755); err != nil {
			return err
		}
		for _, artifact := range emit.Render(p, modules) {
			if err := os.WriteFile(filepath.Join(dest, artifact.Stem+".lean"), []byte(artifact.Content), 0o644); err != nil {
				return err
			}
		}
		roots = append(roots, dirs[p.Path]+"."+p.Name)
	}
	sort.Strings(roots)
	var lake strings.Builder
	lake.WriteString("name = \"goLeanProbe\"\ndefaultTargets = [\"ProbeModels\"]\nmoreLeanArgs = [\"-DwarningAsError=true\"]\n[[lean_lib]]\nname = \"ProbeModels\"\nsrcDir = \".\"\nroots = [\n")
	for _, root := range roots {
		fmt.Fprintf(&lake, "  %q,\n", root)
	}
	lake.WriteString("]\n")
	if err := os.WriteFile(filepath.Join(dir, "lakefile.toml"), []byte(lake.String()), 0o644); err != nil {
		return err
	}
	return os.WriteFile(filepath.Join(dir, "lean-toolchain"), []byte(golean.LeanToolchain), 0o644)
}
