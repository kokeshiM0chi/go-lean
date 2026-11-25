// Package load indexes build-selected Go declarations and go-lean directives.
package load

import (
	"context"
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"path/filepath"
	"slices"
	"strings"
	"unicode"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"golang.org/x/tools/go/packages"
)

const Curated = "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type Function struct {
	Package           *packages.Package
	File              *ast.File
	Decl              *ast.FuncDecl
	Export            bool
	Termination       string
	Laws, Assumptions []ir.Proposition
	LawPositions      []token.Pos
	Abstract          []string
	Err               error
	Selected          bool
}

type Program struct {
	Roots         []*types.Func
	PackageRoots  map[string][]*types.Func
	LawPackages   []string
	PackageLaws   map[string][]ir.Proposition
	LeanImports   map[string][]string
	Functions     map[*types.Func]Function
	Packages      map[string]*packages.Package
	PackageIssues map[string]error
	TypeIssues    map[*types.TypeName]error
}

func Read(ctx context.Context, dir, pattern string) (*Program, error) {
	cfg := &packages.Config{Context: ctx, Dir: dir, Mode: packages.LoadAllSyntax | packages.NeedModule}
	roots, err := packages.Load(cfg, pattern)
	if err != nil {
		return nil, err
	}
	var diagnostics []string
	packages.Visit(roots, nil, func(p *packages.Package) {
		for _, issue := range p.Errors {
			diagnostics = append(diagnostics, issue.Error())
		}
	})
	if len(diagnostics) != 0 {
		slices.Sort(diagnostics)
		return nil, fmt.Errorf("%s", strings.Join(slices.Compact(diagnostics), "\n"))
	}
	program := &Program{
		PackageRoots:  make(map[string][]*types.Func),
		PackageLaws:   make(map[string][]ir.Proposition),
		LeanImports:   make(map[string][]string),
		Functions:     make(map[*types.Func]Function),
		Packages:      make(map[string]*packages.Package),
		PackageIssues: make(map[string]error),
		TypeIssues:    make(map[*types.TypeName]error),
	}
	requested := make(map[string]bool)
	for _, p := range roots {
		requested[p.ID] = true
	}
	packages.Visit(roots, nil, func(p *packages.Package) {
		program.Packages[p.PkgPath] = p
		files := slices.Clone(p.Syntax)
		slices.SortFunc(files, func(a, b *ast.File) int {
			return strings.Compare(p.Fset.PositionFor(a.Pos(), false).Filename, p.Fset.PositionFor(b.Pos(), false).Filename)
		})
		for _, file := range files {
			program.readPackageDirectives(p, file.Doc)
			for _, decl := range file.Decls {
				if d, ok := decl.(*ast.GenDecl); ok && d.Tok == token.TYPE {
					for _, raw := range d.Specs {
						spec := raw.(*ast.TypeSpec)
						program.readInterfaceMethods(p, file, spec)
						if pos := firstDirective(d.Doc, spec.Doc); pos.IsValid() {
							if obj, ok := p.TypesInfo.Defs[spec.Name].(*types.TypeName); ok {
								program.TypeIssues[obj] = Error(p, pos, "type directives are unsupported; attach laws to functions")
							}
						}
					}
				}
				f, ok := decl.(*ast.FuncDecl)
				if !ok {
					continue
				}
				obj, ok := p.TypesInfo.Defs[f.Name].(*types.Func)
				if !ok {
					continue
				}
				entry := Function{Package: p, File: file, Decl: f}
				entry.readDirectives()
				program.Functions[obj] = entry
				if p.PkgPath != Curated && entry.Selected {
					program.PackageRoots[p.PkgPath] = append(program.PackageRoots[p.PkgPath], obj)
				}
			}
		}
		marked := program.PackageRoots[p.PkgPath]
		slices.SortFunc(marked, func(a, b *types.Func) int {
			return strings.Compare(a.FullName(), b.FullName())
		})
		if p.PkgPath != Curated && requested[p.ID] {
			if len(program.PackageLaws[p.PkgPath]) != 0 {
				program.LawPackages = append(program.LawPackages, p.PkgPath)
			} else {
				program.Roots = append(program.Roots, marked...)
			}
		}
	})
	slices.Sort(program.LawPackages)
	slices.SortFunc(program.Roots, func(a, b *types.Func) int {
		return strings.Compare(a.FullName(), b.FullName())
	})
	for _, p := range roots {
		if issue := program.PackageIssues[p.PkgPath]; issue != nil {
			diagnostics = append(diagnostics, issue.Error())
		}
	}
	if len(diagnostics) != 0 {
		slices.Sort(diagnostics)
		return nil, fmt.Errorf("%s", diagnostics[0])
	}
	return program, nil
}

// Interface methods have no FuncDecl, but their doc comments can supply the
// same explicit assumptions as ordinary abstract dependencies.
func (program *Program) readInterfaceMethods(p *packages.Package, file *ast.File, spec *ast.TypeSpec) {
	iface, ok := spec.Type.(*ast.InterfaceType)
	if !ok {
		return
	}
	for _, method := range iface.Methods.List {
		if len(method.Names) != 1 {
			continue // Embedded interfaces own their method declarations.
		}
		name := method.Names[0]
		fn, ok := p.TypesInfo.Defs[name].(*types.Func)
		if !ok {
			continue
		}
		decl := &ast.FuncDecl{Doc: method.Doc, Name: name, Type: method.Type.(*ast.FuncType)}
		entry := Function{Package: p, File: file, Decl: decl}
		entry.readDirectives()
		if entry.Err == nil && (entry.Selected || entry.Termination != "") {
			entry.Err = Error(p, name.Pos(), "interface methods only support golean:assume laws")
		}
		program.Functions[fn] = entry
	}
}

func directive(text string) (kind, value string, ok bool) {
	text, ok = strings.CutPrefix(text, "//golean:")
	kind = strings.TrimSpace(text)
	if i := strings.IndexFunc(kind, unicode.IsSpace); i >= 0 {
		kind, value = kind[:i], strings.TrimSpace(kind[i:])
	}
	return kind, value, ok
}

func proposition(value string) (ir.Proposition, bool) {
	name, lean, ok := strings.Cut(value, ":")
	name, lean = strings.TrimSpace(name), strings.TrimSpace(lean)
	return ir.Proposition{Name: name, Lean: lean}, ok && token.IsIdentifier(name) && name != "_" && lean != ""
}

func validModule(value string) bool {
	for part := range strings.SplitSeq(value, ".") {
		if !token.IsIdentifier(part) || part == "_" {
			return false
		}
	}
	return true
}

func (program *Program) readPackageDirectives(p *packages.Package, doc *ast.CommentGroup) {
	path := p.PkgPath
	if doc == nil || program.PackageIssues[path] != nil {
		return
	}
	laws := program.PackageLaws[path]
	var previous *ir.Proposition
	for _, comment := range doc.List {
		kind, value, ok := directive(comment.Text)
		if !ok {
			previous = nil
			continue
		}
		fail := func(message string, args ...any) {
			program.PackageIssues[path] = Error(p, comment.Pos(), message, args...)
		}
		switch kind {
		case "verify":
			law, valid := proposition(value)
			if !valid {
				fail("expected golean:verify name : proposition")
				return
			}
			for _, existing := range laws {
				if existing.Name == law.Name {
					fail("duplicate package law %s", law.Name)
					return
				}
			}
			laws = append(laws, law)
			previous = &laws[len(laws)-1]
		case "verify+":
			if previous == nil || value == "" {
				fail("unexpected golean:verify+ continuation")
				return
			}
			previous.Lean += "\n" + value
		case "verify:import":
			previous = nil
			if !validModule(value) {
				fail("expected golean:verify:import Lean.Module")
				return
			}
			program.LeanImports[path] = append(program.LeanImports[path], value)
		default:
			fail("unsupported package golean:%s directive", kind)
			return
		}
	}
	program.PackageLaws[path] = laws
}

func firstDirective(groups ...*ast.CommentGroup) token.Pos {
	for _, group := range groups {
		if group == nil {
			continue
		}
		for _, comment := range group.List {
			if strings.HasPrefix(comment.Text, "//golean:") {
				return comment.Pos()
			}
		}
	}
	return token.NoPos
}

func Dir(p *packages.Package) string {
	if len(p.GoFiles) != 0 {
		return filepath.Dir(p.GoFiles[0])
	}
	return p.Dir
}

func Error(p *packages.Package, pos token.Pos, message string, args ...any) error {
	return fmt.Errorf("%s: %s", p.Fset.Position(pos), fmt.Sprintf(message, args...))
}

func (f *Function) readDirectives() {
	if f.Decl.Doc == nil {
		return
	}
	var previous *ir.Proposition
	var continuation string
	for _, comment := range f.Decl.Doc.List {
		kind, value, ok := directive(comment.Text)
		if !ok {
			previous = nil
			continue
		}
		if kind == "verify" || kind == "export" || strings.HasPrefix(kind, "verify") || kind == "abstract" {
			f.Selected = true
		}
		fail := func(format string, args ...any) {
			if f.Err == nil {
				f.Err = Error(f.Package, comment.Pos(), format, args...)
			}
		}
		if kind == "verify+" || kind == "assume+" {
			if previous == nil || continuation != kind || value == "" {
				fail("unexpected golean:%s continuation", kind)
			} else {
				previous.Lean += "\n" + value
			}
			continue
		}
		previous = nil
		switch kind {
		case "export":
			if f.Export || value != "" {
				fail("expected one bare golean:export")
			}
			f.Export = true
		case "termination:by":
			if value == "" || f.Termination != "" {
				fail("expected one nonempty golean:termination:by measure")
			}
			f.Termination = value
		case "abstract":
			if value == "" || slices.Contains(f.Abstract, value) {
				fail("expected a unique golean:abstract callee")
			}
			f.Abstract = append(f.Abstract, value)
		case "assume", "verify":
			law, ok := proposition(value)
			if !ok {
				fail("expected golean:%s name : proposition", kind)
				continue
			}
			list := &f.Laws
			if kind == "assume" {
				list = &f.Assumptions
			} else {
				f.LawPositions = append(f.LawPositions, comment.Pos())
			}
			for _, existing := range *list {
				if existing.Name == law.Name {
					fail("duplicate golean:%s law %s", kind, law.Name)
				}
			}
			*list = append(*list, law)
			previous, continuation = &(*list)[len(*list)-1], kind+"+"
		default:
			fail("unsupported golean:%s directive", kind)
		}
	}
}

// ResolveCallee resolves Function, alias.Function, Interface.Method, or
// alias.Interface.Method. Interface aliases resolve to the original method.
func (f Function) ResolveCallee(name string) *types.Func {
	parts := strings.Split(name, ".")
	scope := f.Package.Types.Scope()
	if len(parts) > 1 {
		for _, spec := range f.File.Imports {
			var imported *types.PkgName
			if spec.Name == nil {
				imported, _ = f.Package.TypesInfo.Implicits[spec].(*types.PkgName)
			} else {
				imported, _ = f.Package.TypesInfo.Defs[spec.Name].(*types.PkgName)
			}
			if imported != nil && imported.Name() == parts[0] {
				scope = imported.Imported().Scope()
				parts = parts[1:]
				break
			}
		}
	}
	if len(parts) == 1 {
		fn, _ := scope.Lookup(parts[0]).(*types.Func)
		return fn
	}
	if len(parts) == 2 {
		if typ, ok := scope.Lookup(parts[0]).(*types.TypeName); ok && types.IsInterface(typ.Type()) {
			obj, _, _ := types.LookupFieldOrMethod(typ.Type(), false, f.Package.Types, parts[1])
			fn, _ := obj.(*types.Func)
			return fn
		}
	}
	return nil
}
