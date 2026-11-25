package main

import (
	"bytes"
	"context"
	"fmt"
	"os"
	"path/filepath"

	"github.com/frederik-jatzkowski/go-lean/internal/emit"
	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/load"
	"github.com/frederik-jatzkowski/go-lean/internal/lower"
)

func generate(ctx context.Context, pattern string) ([]string, error) {
	workspace, err := readLake()
	if err != nil {
		return nil, err
	}
	source, err := load.Read(ctx, ".", pattern)
	if err != nil {
		return nil, err
	}
	packages, err := lower.Program(source)
	if err != nil {
		return nil, err
	}

	modules := make(map[string]string)
	locations := make(map[string]location)
	owners := make(map[string]string)
	for _, p := range packages {
		loc, err := workspace.locate(p.Dir)
		if err != nil {
			return nil, err
		}
		locations[p.Path] = loc
		modules[p.Path] = emit.Module(loc.rel, p.Name)
		if owner, found := owners[modules[p.Path]]; found {
			return nil, fmt.Errorf("Go packages %s and %s map to the same Lean module", owner, p.Path)
		}
		owners[modules[p.Path]] = p.Path
	}
	type output struct {
		path     string
		artifact emit.Artifact
	}
	var outputs []output
	var targets []string
	selectedLocations := make(map[string]location)
	for path, loc := range locations {
		if path != ir.ExternalTypesPackage {
			selectedLocations[path] = loc
		}
	}
	workspace.clearSelection(pattern, selectedLocations)
	for _, p := range packages {
		loc := locations[p.Path]
		checkStem := p.Name
		if len(p.Laws) != 0 {
			checkStem += "_verify"
		}
		for _, artifact := range emit.Render(p, modules) {
			outputs = append(outputs, output{path: filepath.Join(p.Dir, artifact.Stem+".lean"), artifact: artifact})
			name := loc.module(artifact.Stem)
			workspace.blocks[loc.block].roots[name] = true
			if artifact.Stem == checkStem {
				targets = append(targets, "+"+name)
			}
		}
	}
	for _, out := range outputs {
		if out.artifact.Preserve {
			continue
		}
		data, err := os.ReadFile(out.path)
		if err != nil && !os.IsNotExist(err) {
			return nil, err
		}
		if err == nil && !bytes.HasPrefix(data, []byte(emit.GeneratedHeader)) {
			return nil, fmt.Errorf("%s: generated output would overwrite a handwritten file", out.path)
		}
	}
	for _, out := range outputs {
		if out.artifact.Preserve {
			if err := createProof(out.path, out.artifact.Content); err != nil {
				return nil, err
			}
		} else if err := writeChanged(out.path, out.artifact.Content); err != nil {
			return nil, err
		}
	}
	if err := writeChanged("lakefile.toml", workspace.render()); err != nil {
		return nil, err
	}
	return targets, nil
}

func createProof(path, content string) error {
	f, err := os.OpenFile(path, os.O_CREATE|os.O_EXCL|os.O_WRONLY, 0o644)
	if os.IsExist(err) {
		info, statErr := os.Stat(path)
		if statErr != nil {
			return statErr
		}
		if info.Mode().IsRegular() {
			return nil
		}
		return fmt.Errorf("%s: expected a regular proof file", path)
	}
	if err != nil {
		return err
	}
	_, err = f.WriteString(content)
	closeErr := f.Close()
	if err != nil || closeErr != nil {
		_ = os.Remove(path)
		if err != nil {
			return err
		}
		return closeErr
	}
	return nil
}

func writeChanged(path, content string) error {
	old, err := os.ReadFile(path)
	if err == nil && string(old) == content {
		return nil
	}
	if err != nil && !os.IsNotExist(err) {
		return err
	}
	f, err := os.CreateTemp(filepath.Dir(path), ".golean-*")
	if err != nil {
		return err
	}
	defer os.Remove(f.Name())
	_, err = f.WriteString(content)
	closeErr := f.Close()
	if err != nil {
		return err
	}
	if closeErr != nil {
		return closeErr
	}
	return os.Rename(f.Name(), path)
}
