// Package lower validates the supported Go subset and builds typed IR.
package lower

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"slices"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/load"
	"golang.org/x/tools/go/packages"
)

type compiler struct {
	source   *load.Program
	packages map[string]*ir.Package
	state    map[types.Object]uint8
	abstract map[*types.Func]bool
	roots    []*types.Func
	partial  map[*types.Func]bool
}

func Program(source *load.Program) ([]*ir.Package, error) {
	c := compiler{
		source:   source,
		packages: make(map[string]*ir.Package),
		state:    make(map[types.Object]uint8),
		abstract: make(map[*types.Func]bool),
		roots:    slices.Clone(source.Roots),
		partial:  make(map[*types.Func]bool),
	}
	for _, path := range source.LawPackages {
		c.output(path)
	}
	for i := 0; i < len(c.roots); i++ {
		if err := c.function(c.roots[i]); err != nil {
			return nil, err
		}
	}
	result := make([]*ir.Package, 0, len(c.packages))
	for _, p := range c.packages {
		slices.Sort(p.Imports)
		result = append(result, p)
	}
	slices.SortFunc(result, func(a, b *ir.Package) int { return strings.Compare(a.Path, b.Path) })
	for _, p := range result {
		if issue := source.PackageIssues[p.Path]; issue != nil {
			return nil, issue
		}
	}
	return result, nil
}

func symbol(obj types.Object) ir.Symbol {
	name := obj.Name()
	if fn, ok := obj.(*types.Func); ok && fn.Signature().Recv() != nil {
		recv := types.Unalias(fn.Signature().Recv().Type())
		if ptr, ok := recv.(*types.Pointer); ok {
			recv = types.Unalias(ptr.Elem())
		}
		receiver := recv.(*types.Named)
		name = receiver.Obj().Name() + "$" + name
	}
	return ir.Symbol{Package: obj.Pkg().Path(), Name: name}
}

func valueReceiver(fn *types.Func) bool {
	receiver := fn.Signature().Recv()
	if receiver == nil {
		return false
	}
	t := types.Unalias(receiver.Type())
	if ptr, ok := t.(*types.Pointer); ok {
		t = types.Unalias(ptr.Elem())
	}
	named, ok := t.(*types.Named)
	return ok && !types.IsInterface(named)
}

func interfaceMethod(fn *types.Func) bool {
	recv := fn.Signature().Recv()
	return recv != nil && types.IsInterface(recv.Type())
}

func (c *compiler) output(path string) *ir.Package {
	if p := c.packages[path]; p != nil {
		return p
	}
	source := c.source.Packages[path]
	p := &ir.Package{Path: path, Name: source.Name, Dir: load.Dir(source)}
	p.LeanImports = slices.Clone(c.source.LeanImports[path])
	slices.Sort(p.LeanImports)
	p.LeanImports = slices.Compact(p.LeanImports)
	if laws := c.source.PackageLaws[path]; len(laws) != 0 {
		for _, law := range laws {
			p.Laws = append(p.Laws, ir.Law{Proposition: law})
		}
		// Focused generation must retain the marked functions that a package law can reference.
		c.roots = append(c.roots, c.source.PackageRoots[path]...)
	}
	p.Word = ir.UInt64
	if source.TypesSizes.Sizeof(types.Typ[types.Uint]) == 4 {
		p.Word = ir.UInt32
	}
	c.packages[path] = p
	return p
}

func (c *compiler) depend(p *packages.Package, path string, pos token.Pos) error {
	if p.PkgPath == path {
		return nil
	}
	if issue := c.source.PackageIssues[path]; issue != nil {
		return issue
	}
	target := c.source.Packages[path]
	if p.Module == nil || target == nil || target.Module == nil || target.Module.Path != p.Module.Path {
		return load.Error(p, pos, "concrete dependency %s must be in the same Go module", path)
	}
	out := c.output(p.PkgPath)
	if !slices.Contains(out.Imports, path) {
		out.Imports = append(out.Imports, path)
	}
	return nil
}

func (c *compiler) function(fn *types.Func) error {
	src, ok := c.source.Functions[fn]
	if !ok {
		return fmt.Errorf("no Go source for %s", fn.FullName())
	}
	p, pos := src.Package, src.Decl.Pos()
	switch c.state[fn] {
	case 1:
		return load.Error(p, pos, "recursive call graph through %s", fn.Name())
	case 2:
		return nil
	}
	if src.Err != nil {
		return src.Err
	}
	c.state[fn] = 1
	sig := fn.Signature()
	if sig.Variadic() || sig.TypeParams().Len() != 0 || sig.Results().Len() == 0 || src.Decl.Body == nil {
		return load.Error(p, pos, "expected a concrete, non-variadic function with at least one result")
	}
	if sig.Recv() != nil && !valueReceiver(fn) {
		return load.Error(p, pos, "expected a concrete value receiver")
	}
	for i := 0; i < sig.Results().Len(); i++ {
		if sig.Results().At(i).Name() != "" {
			return load.Error(p, pos, "named results are unsupported")
		}
	}
	out := c.output(p.PkgPath)
	f := function{
		compiler: c, source: src, fn: fn, locals: make(map[*types.Var]int), used: make(map[int]bool),
		contracts: make(map[*types.Func]bool),
	}
	model := ir.Function{Symbol: symbol(fn), Termination: src.Termination}
	params := make([]*types.Var, 0, sig.Params().Len()+1)
	if sig.Recv() != nil {
		params = append(params, sig.Recv())
	}
	for i := 0; i < sig.Params().Len(); i++ {
		params = append(params, sig.Params().At(i))
	}
	for _, param := range params {
		t, err := c.goType(p, pos, param.Type())
		if err != nil {
			return err
		}
		model.Params = append(model.Params, ir.Binding{ID: f.bind(param), Name: param.Name(), Type: t, Unused: param.Name() == "_" || param.Name() == ""})
	}
	var err error
	model.Result, err = c.resultType(p, pos, sig.Results())
	if err != nil {
		return err
	}
	if src.Termination != "" && len(src.Abstract) != 0 {
		return load.Error(p, pos, "measured recursion does not support caller-local contracts")
	}
	if len(src.Abstract) != 0 && len(src.Laws) == 0 {
		return load.Error(p, pos, "go-lean abstraction requires a verified root")
	}
	c.abstract[fn] = len(src.Abstract) != 0
	var calleeNames []string
	for _, target := range src.Abstract {
		callee := src.ResolveCallee(target)
		decl, found := c.source.Functions[callee]
		if !found || callee == fn || len(decl.Assumptions) == 0 {
			return load.Error(p, pos, "abstract callee %q must name another function or interface method with golean:assume laws", target)
		}
		if decl.Err != nil {
			return decl.Err
		}
		if _, exists := f.contracts[callee]; exists {
			return load.Error(p, pos, "duplicate abstract callee %q", target)
		}
		contract, err := f.contract(fn, callee, decl.Assumptions)
		if err != nil {
			return err
		}
		f.contracts[callee] = false
		model.Contracts = append(model.Contracts, symbol(callee))
		calleeNames = append(calleeNames, target)
		out.Decls = append(out.Decls, contract)
		model.Partial = model.Partial || interfaceMethod(callee)
	}
	model.Body, err = f.block(src.Decl.Body.List, func() (ir.Expr, error) {
		return nil, load.Error(p, pos, "supported function paths must return a value")
	})
	if err != nil {
		return err
	}
	model.Partial = model.Partial || f.hasPartial
	if src.Termination == "" {
		for i := range model.Params {
			model.Params[i].Unused = model.Params[i].Unused || !f.used[model.Params[i].ID]
		}
	}
	if model.Partial && src.Termination != "" {
		return load.Error(p, pos, "measured recursion does not support partial pointer or interface models")
	}
	if src.Termination != "" && !f.recursive {
		return load.Error(p, pos, "termination measure requires a direct recursive call")
	}
	for _, name := range calleeNames {
		if !f.contracts[src.ResolveCallee(name)] {
			return load.Error(p, pos, "unused abstract callee %q", name)
		}
	}
	for i, law := range src.Laws {
		for _, existing := range out.Laws {
			if existing.Name == law.Name {
				return load.Error(p, src.LawPositions[i], "duplicate package law %s", law.Name)
			}
		}
		out.Laws = append(out.Laws, ir.Law{Proposition: law, Caller: model.Symbol, Contracts: model.Contracts})
	}
	out.Decls = append(out.Decls, model)
	c.partial[fn] = model.Partial
	c.state[fn] = 2
	return nil
}

type function struct {
	*compiler
	source     load.Function
	fn         *types.Func
	recursive  bool
	locals     map[*types.Var]int
	used       map[int]bool
	next       int
	contracts  map[*types.Func]bool
	hasPartial bool
}

func (f *function) bind(v *types.Var) int {
	id := f.next
	f.next++
	if v.Name() != "_" {
		f.locals[v] = id
	}
	return id
}

func (f *function) contract(caller, callee *types.Func, laws []ir.Proposition) (ir.Contract, error) {
	p, pos := f.source.Package, f.source.Decl.Pos()
	contract := ir.Contract{Caller: symbol(caller), Name: callee.Name(), Assumptions: laws}
	signature := callee.Signature()
	method := interfaceMethod(callee)
	if (signature.Recv() != nil && !method) || signature.Variadic() || signature.TypeParams().Len() != 0 || signature.Results().Len() == 0 {
		return contract, load.Error(p, pos, "abstract callee %s must have a scalar function signature", callee.Name())
	}
	if method {
		recv, err := f.goType(p, pos, signature.Recv().Type())
		if err != nil {
			return contract, err
		}
		contract.Params = append(contract.Params, recv)
	}
	contract.Callee = symbol(callee)
	scalar := func(typ types.Type) (ir.Type, error) {
		if method {
			return f.goType(p, pos, typ)
		}
		b, ok := typ.Underlying().(*types.Basic)
		if !ok {
			return ir.Type{}, load.Error(p, pos, "abstract callee %s requires scalar types", callee.Name())
		}
		return basic(p, pos, b)
	}
	for i := 0; i < signature.Params().Len(); i++ {
		t, err := scalar(signature.Params().At(i).Type())
		if err != nil {
			return contract, err
		}
		contract.Params = append(contract.Params, t)
	}
	var err error
	if method {
		contract.Result, err = f.resultType(p, pos, signature.Results())
	} else {
		if signature.Results().Len() == 1 {
			contract.Result, err = scalar(signature.Results().At(0).Type())
		} else {
			contract.Result.Kind = ir.Tuple
			for i := 0; i < signature.Results().Len(); i++ {
				t, e := scalar(signature.Results().At(i).Type())
				if e != nil {
					return contract, e
				}
				contract.Result.Elements = append(contract.Result.Elements, t)
			}
		}
	}
	return contract, err
}

type continuation func() (ir.Expr, error)

func endsWithReturn(stmts []ast.Stmt) bool {
	if len(stmts) == 0 {
		return false
	}
	switch last := stmts[len(stmts)-1].(type) {
	case *ast.ReturnStmt:
		return true
	case *ast.IfStmt:
		return endsWithReturn(last.Body.List) && elseReturns(last.Else)
	default:
		return false
	}
}

func elseReturns(branch ast.Stmt) bool {
	switch s := branch.(type) {
	case *ast.IfStmt:
		return endsWithReturn(s.Body.List) && elseReturns(s.Else)
	case *ast.BlockStmt:
		return endsWithReturn(s.List)
	default:
		return false
	}
}

func (f *function) block(stmts []ast.Stmt, tail continuation) (ir.Expr, error) {
	if len(stmts) == 0 {
		return tail()
	}
	p := f.source.Package
	statement := stmts[0]
	rest := func() (ir.Expr, error) { return f.block(stmts[1:], tail) }
	switch s := statement.(type) {
	case *ast.ReturnStmt:
		if len(stmts) != 1 {
			return nil, load.Error(p, s.Pos(), "expected a return at the end of a block")
		}
		results := f.fn.Signature().Results()
		if len(s.Results) == 1 && results.Len() > 1 {
			if !types.Identical(p.TypesInfo.TypeOf(s.Results[0]), results) {
				return nil, load.Error(p, s.Pos(), "implicit conversions in multiple return forwarding are unsupported")
			}
			return f.expr(s.Results[0])
		}
		if len(s.Results) != results.Len() {
			return nil, load.Error(p, s.Pos(), "return arity does not match function results")
		}
		values := make([]ir.Expr, len(s.Results))
		for i, node := range s.Results {
			v, err := f.value(node, results.At(i).Type())
			if err != nil {
				return nil, err
			}
			values[i] = v
		}
		if len(values) == 1 {
			return values[0], nil
		}
		return ir.TupleLiteral{Values: values}, nil
	case *ast.IfStmt:
		if s.Init != nil {
			branch := *s
			branch.Init = nil
			return f.block([]ast.Stmt{s.Init, &branch}, rest)
		}
		cond, err := f.expr(s.Cond)
		if err != nil {
			return nil, err
		}
		var after ir.Expr
		var afterErr error
		join := !endsWithReturn(s.Body.List) && !elseReturns(s.Else)
		joinID := f.next
		if join {
			f.next++
		}
		shared := func() (ir.Expr, error) {
			if join {
				return ir.Jump{ID: joinID}, nil
			}
			if after == nil && afterErr == nil {
				after, afterErr = rest()
			}
			return after, afterErr
		}
		yes, err := f.block(s.Body.List, shared)
		if err != nil {
			return nil, err
		}
		var no ir.Expr
		switch e := s.Else.(type) {
		case nil:
			no, err = shared()
		case *ast.BlockStmt:
			no, err = f.block(e.List, shared)
		case *ast.IfStmt:
			no, err = f.block([]ast.Stmt{e}, shared)
		}
		if err != nil {
			return nil, err
		}
		branch := ir.If{Cond: cond, Then: yes, Else: no}
		if join {
			next, err := rest()
			if err != nil {
				return nil, err
			}
			return ir.Join{ID: joinID, Next: next, Body: branch}, nil
		}
		if after == nil && len(stmts) > 1 {
			return nil, load.Error(p, stmts[1].Pos(), "unreachable statements after unconditional return")
		}
		return branch, nil
	case *ast.ForStmt, *ast.RangeStmt:
		return nil, load.Error(p, statement.Pos(), "raw loops are unsupported in modeled Go; use lean.FoldN, lean.FoldNUntil, lean.FoldList, or lean.FoldListUntil")
	case *ast.AssignStmt:
		if s.Tok != token.DEFINE {
			return nil, load.Error(p, s.Pos(), "only immutable short declarations with explicit values are supported")
		}
		var names []*ast.Ident
		for _, lhs := range s.Lhs {
			name, ok := lhs.(*ast.Ident)
			if !ok {
				return nil, load.Error(p, lhs.Pos(), "expected a local name")
			}
			names = append(names, name)
		}
		return f.bindings(names, s.Rhs, rest)
	case *ast.DeclStmt:
		d, ok := s.Decl.(*ast.GenDecl)
		if !ok || d.Tok != token.VAR || len(d.Specs) != 1 {
			return nil, load.Error(p, s.Pos(), "expected a single initialized local var declaration")
		}
		v := d.Specs[0].(*ast.ValueSpec)
		return f.bindings(v.Names, v.Values, rest)
	default:
		return nil, load.Error(p, s.Pos(), "unsupported statement %T", s)
	}
}

func (f *function) bindings(names []*ast.Ident, values []ast.Expr, tail continuation) (ir.Expr, error) {
	p := f.source.Package
	if len(values) == 1 && len(names) > 1 {
		tuple, ok := p.TypesInfo.TypeOf(values[0]).(*types.Tuple)
		if !ok || tuple.Len() != len(names) {
			return nil, load.Error(p, names[0].Pos(), "expected a matching multiple-result initializer")
		}
		value, err := f.expr(values[0])
		if err != nil {
			return nil, err
		}
		temp := f.next
		f.next++
		var bindings []ir.Let
		for i, name := range names {
			v, ok := p.TypesInfo.Defs[name].(*types.Var)
			if !ok {
				return nil, load.Error(p, name.Pos(), "reassignment is unsupported")
			}
			if _, err := f.goType(p, name.Pos(), v.Type()); err != nil {
				return nil, err
			}
			if !types.Identical(v.Type(), tuple.At(i).Type()) {
				return nil, load.Error(p, name.Pos(), "implicit conversions in multiple-result bindings are unsupported")
			}
			if name.Name != "_" {
				bindings = append(bindings, ir.Let{ID: f.bind(v), Value: ir.TupleRead{Value: ir.Local{ID: temp}, Index: i, Count: len(names)}})
			}
		}
		body, err := tail()
		if err != nil {
			return nil, err
		}
		for i := len(bindings) - 1; i >= 0; i-- {
			bindings[i].Body = body
			body = bindings[i]
		}
		return ir.Let{ID: temp, Value: value, Body: body, Unused: len(bindings) == 0}, nil
	}
	if len(names) != len(values) {
		return nil, load.Error(p, names[0].Pos(), "local bindings require individual initializers")
	}
	bindings := make([]ir.Let, len(names))
	for i, name := range names {
		v, ok := p.TypesInfo.Defs[name].(*types.Var)
		if !ok {
			return nil, load.Error(p, name.Pos(), "reassignment is unsupported")
		}
		if _, err := f.goType(p, name.Pos(), v.Type()); err != nil {
			return nil, err
		}
		value, err := f.value(values[i], v.Type())
		if err != nil {
			return nil, err
		}
		bindings[i] = ir.Let{ID: f.bind(v), Value: value, Unused: name.Name == "_"}
	}
	body, err := tail()
	if err != nil {
		return nil, err
	}
	for i := len(bindings) - 1; i >= 0; i-- {
		bindings[i].Body = body
		body = bindings[i]
	}
	return body, nil
}
