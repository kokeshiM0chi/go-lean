package lower

import (
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/load"
)

var binaryOps = map[token.Token]ir.BinaryOp{
	token.ADD: ir.Add, token.SUB: ir.Sub, token.EQL: ir.Eq, token.NEQ: ir.Ne,
	token.LSS: ir.Lt, token.LEQ: ir.Le, token.GTR: ir.Gt, token.GEQ: ir.Ge,
	token.LAND: ir.And, token.LOR: ir.Or,
}

// value checks contextual interface assignments before expression lowering.
// Go permits implicit boxing and conversions between distinct interfaces; the
// opaque model only preserves values of the very same named interface type.
func (f *function) value(node ast.Expr, want types.Type) (ir.Expr, error) {
	p := f.source.Package
	_, pointer := types.Unalias(want).(*types.Pointer)
	if types.IsInterface(want) || pointer {
		actual := p.TypesInfo.TypeOf(node)
		if actual == types.Typ[types.UntypedNil] {
			t, err := f.goType(p, node.Pos(), want)
			return ir.Primitive{Op: ir.None, Type: t}, err
		}
		if types.IsInterface(want) && !types.Identical(actual, want) {
			return nil, load.Error(p, node.Pos(), "interface conversion from %s to %s is unsupported; opaque interfaces can only be passed through unchanged", actual, want)
		}
	}
	return f.expr(node)
}

func (f *function) expr(node ast.Expr) (ir.Expr, error) {
	p := f.source.Package
	info := p.TypesInfo
	if paren, ok := node.(*ast.ParenExpr); ok {
		return f.expr(paren.X)
	}
	if binary, ok := node.(*ast.BinaryExpr); ok && binaryOps[binary.Op] == 0 {
		return nil, load.Error(p, node.Pos(), "unsupported binary operator %s", binary.Op)
	}
	tv := info.Types[node]
	if tv.Value != nil {
		if err := f.constantOperands(node); err != nil {
			return nil, err
		}
		t, err := f.goType(p, node.Pos(), tv.Type)
		if err != nil {
			return nil, err
		}
		value := tv.Value.ExactString()
		if t.Kind == ir.String {
			value = constant.StringVal(tv.Value)
		}
		return ir.Constant{Type: t, Value: value}, nil
	}
	switch e := node.(type) {
	case *ast.Ident:
		v, ok := info.Uses[e].(*types.Var)
		id, found := f.locals[v]
		if !ok || !found {
			return nil, load.Error(p, e.Pos(), "expected an immutable local or constant, got %s", e.Name)
		}
		f.used[id] = true
		return ir.Local{ID: id}, nil
	case *ast.UnaryExpr:
		if e.Op == token.AND {
			if _, ok := ast.Unparen(e.X).(*ast.StarExpr); ok {
				return nil, load.Error(p, e.Pos(), "address-of-indirection expressions are unsupported")
			}
			t, err := f.goType(p, e.Pos(), info.TypeOf(e))
			if err != nil {
				return nil, err
			}
			if t.Element == nil {
				return nil, load.Error(p, e.Pos(), "address-taking requires a modeled immutable payload")
			}
			value, err := f.expr(e.X)
			return ir.Primitive{Op: ir.Some, Type: t, Args: []ir.Expr{value}}, err
		}
		if e.Op == token.NOT {
			value, err := f.expr(e.X)
			return ir.Unary{Op: ir.Not, Value: value}, err
		}
	case *ast.StarExpr:
		value, err := f.expr(e.X)
		if err != nil {
			return nil, err
		}
		return f.deref(e.Pos(), info.TypeOf(e.X), value)
	case *ast.BinaryExpr:
		leftType, rightType := info.TypeOf(e.X), info.TypeOf(e.Y)
		if e.Op == token.EQL || e.Op == token.NEQ {
			value, typ := e.X, leftType
			if leftType == types.Typ[types.UntypedNil] {
				value, typ = e.Y, rightType
			}
			_, pointer := types.Unalias(typ).(*types.Pointer)
			if (types.IsInterface(typ) || pointer) && (leftType == types.Typ[types.UntypedNil] || rightType == types.Typ[types.UntypedNil]) {
				t, err := f.goType(p, value.Pos(), typ)
				if err != nil {
					return nil, err
				}
				operand, err := f.expr(value)
				var result ir.Expr = ir.Primitive{Op: ir.IsSome, Type: t, Args: []ir.Expr{operand}}
				if e.Op == token.EQL {
					result = ir.Unary{Op: ir.Not, Value: result}
				}
				return result, err
			}
		}
		t, err := f.goType(p, e.X.Pos(), info.TypeOf(e.X))
		if err != nil {
			return nil, err
		}
		op := binaryOps[e.Op]
		if t.Kind >= ir.Record || ((op == ir.Add || op == ir.Sub) && t.Kind < ir.Int8) {
			return nil, load.Error(p, e.Pos(), "unsupported operands for %s", e.Op)
		}
		left, err := f.expr(e.X)
		if err != nil {
			return nil, err
		}
		right, err := f.expr(e.Y)
		return ir.Binary{Op: op, Kind: t.Kind, Left: left, Right: right}, err
	case *ast.SelectorExpr:
		sel := info.Selections[e]
		if sel != nil && sel.Kind() == types.FieldVal && len(sel.Index()) == 1 {
			t, err := f.goType(p, e.X.Pos(), sel.Recv())
			if err != nil {
				return nil, err
			}
			receiver, err := f.expr(e.X)
			if err != nil {
				return nil, err
			}
			if t.Kind == ir.Pointer {
				receiver, err = f.deref(e.Pos(), sel.Recv(), receiver)
				if err != nil {
					return nil, err
				}
				t = *t.Element
			}
			return ir.FieldRead{Record: receiver, Name: sel.Obj().Name(), Control: t.Kind == ir.FoldControl}, err
		}
	case *ast.CompositeLit:
		return f.literal(e)
	case *ast.CallExpr:
		return f.call(e)
	}
	return nil, load.Error(p, node.Pos(), "unsupported expression %T", node)
}

// Go's type checker evaluates constants. Validate inline operands as well so
// constant folding cannot hide Go syntax outside the supported subset.
func (f *function) constantOperands(node ast.Expr) error {
	p := f.source.Package
	var operands []ast.Expr
	switch e := node.(type) {
	case *ast.BinaryExpr:
		operands = []ast.Expr{e.X, e.Y}
	case *ast.UnaryExpr:
		if e.Op != token.SUB && e.Op != token.ADD && e.Op != token.NOT {
			return load.Error(p, e.Pos(), "unsupported unary operator %s", e.Op)
		}
		operands = []ast.Expr{e.X}
	case *ast.CallExpr:
		if !p.TypesInfo.Types[e.Fun].IsType() {
			return load.Error(p, e.Pos(), "unsupported constant builtin call")
		}
		operands = e.Args
	}
	for _, operand := range operands {
		if _, err := f.expr(operand); err != nil {
			return err
		}
	}
	return nil
}

func (f *function) literal(e *ast.CompositeLit) (ir.Expr, error) {
	p := f.source.Package
	typ := p.TypesInfo.TypeOf(e)
	t, err := f.goType(p, e.Pos(), typ)
	if err != nil {
		return nil, err
	}
	if t.Kind > ir.Record && t.Kind != ir.FoldControl && len(e.Elts) == 0 {
		return ir.Primitive{Op: ir.Empty, Type: t}, nil
	}
	if t.Kind != ir.Record && t.Kind != ir.FoldControl {
		return nil, load.Error(p, e.Pos(), "expected a record literal or an empty curated value")
	}
	record := typ.Underlying().(*types.Struct)
	if len(e.Elts) != record.NumFields() {
		return nil, load.Error(p, e.Pos(), "record literals must initialize every field")
	}
	fields := make([]ir.Expr, record.NumFields())
	for _, el := range e.Elts {
		kv, ok := el.(*ast.KeyValueExpr)
		if !ok {
			return nil, load.Error(p, el.Pos(), "record literals require keyed fields")
		}
		name := kv.Key.(*ast.Ident).Name
		for i := 0; i < record.NumFields(); i++ {
			if record.Field(i).Name() != name {
				continue
			}
			fields[i], err = f.value(kv.Value, record.Field(i).Type())
			if err != nil {
				return nil, err
			}
			break
		}
	}
	if t.Kind == ir.FoldControl {
		return ir.FoldControlLiteral{State: fields[0], Stop: fields[1]}, nil
	}
	return ir.StructLiteral{Type: t.Record, Fields: fields}, nil
}

var constructors = map[string]ir.PrimitiveOp{
	"NewBox": ir.Some, "Some": ir.Some, "None": ir.None, "Nil": ir.Nil, "Cons": ir.Cons, "NewBitVec": ir.NewBitVec,
}

var methods = map[ir.Kind]map[string]ir.PrimitiveOp{
	ir.Array:      {"Push": ir.Push, "Pop": ir.Pop, "Get": ir.Get, "Set": ir.Set, "Size": ir.Size},
	ir.ByteArray:  {"Push": ir.Push, "Get": ir.Get, "Set": ir.Set, "Size": ir.Size, "Extract": ir.Extract},
	ir.OrderedMap: {"Find": ir.Find, "Contains": ir.Contains, "Insert": ir.Insert, "Erase": ir.Erase},
	ir.OrderedSet: {"Contains": ir.Contains, "Insert": ir.Insert, "Erase": ir.Erase},
	ir.Box:        {"IsSome": ir.IsSome, "Get": ir.BoxGet},
	ir.Option:     {"IsSome": ir.IsSome, "UnwrapOr": ir.UnwrapOr},
	ir.List:       {"IsEmpty": ir.IsEmpty},
	ir.BitVec:     {"Get": ir.Get, "Set": ir.Set, "Width": ir.Width, "ToUint64": ir.ToUint64},
}

func callBase(e ast.Expr) ast.Expr {
	for {
		switch node := e.(type) {
		case *ast.ParenExpr:
			e = node.X
		case *ast.IndexExpr:
			e = node.X
		case *ast.IndexListExpr:
			e = node.X
		default:
			return e
		}
	}
}

func (f *function) call(e *ast.CallExpr) (ir.Expr, error) {
	p := f.source.Package
	info := p.TypesInfo
	var fn *types.Func
	var receiver ast.Expr
	var selection *types.Selection
	switch target := callBase(e.Fun).(type) {
	case *ast.Ident:
		fn, _ = info.Uses[target].(*types.Func)
	case *ast.SelectorExpr:
		fn, _ = info.Uses[target.Sel].(*types.Func)
		selection = info.Selections[target]
		if selection != nil && selection.Kind() == types.MethodVal {
			receiver = target.X
		}
	}
	if fn == nil || fn.Pkg() == nil || e.Ellipsis.IsValid() {
		return nil, load.Error(p, e.Pos(), "expected a direct call to a supported function")
	}
	if fn.Pkg().Path() == load.Curated {
		if kind := folds[fn.Name()]; selection == nil && kind != 0 {
			return f.fold(e, kind)
		}
		var t ir.Type
		var op ir.PrimitiveOp
		var err error
		if selection == nil {
			op = constructors[fn.Name()]
			if op != 0 {
				t, err = f.goType(p, e.Pos(), info.TypeOf(e))
			}
		} else if receiver != nil && !selection.Indirect() && len(selection.Index()) == 1 {
			t, err = f.goType(p, receiver.Pos(), selection.Recv())
			op = methods[t.Kind][fn.Name()]
		}
		if err != nil {
			return nil, err
		}
		if op == 0 {
			return nil, load.Error(p, e.Pos(), "unsupported curated operation %s", fn.Name())
		}
		args, err := f.callArguments(e, receiver)
		if err == nil && op == ir.BoxGet {
			args = append(args, f.zero(*t.Element))
		}
		return ir.Primitive{Op: op, Type: t, Args: args}, err
	}
	if selection != nil {
		if types.IsInterface(selection.Recv()) {
			if !types.Identical(selection.Recv(), fn.Signature().Recv().Type()) {
				return nil, load.Error(p, e.Pos(), "interface method receiver conversions are unsupported; call through the declaring interface type")
			}
			if _, ok := f.contracts[fn]; !ok {
				return nil, load.Error(p, e.Pos(), "interface method calls require an explicit golean:abstract contract with golean:assume laws")
			}
			args, err := f.callArguments(e, receiver)
			if err != nil {
				return nil, err
			}
			f.contracts[fn] = true
			return ir.InterfaceCall{Target: symbol(fn), Args: args}, nil
		}
		if !valueReceiver(fn) || len(selection.Index()) != 1 {
			return nil, load.Error(p, e.Pos(), "expected a direct call on a concrete value receiver")
		}
	}
	args, err := f.callArguments(e, receiver)
	if err != nil {
		return nil, err
	}
	if selection != nil {
		want := fn.Signature().Recv().Type()
		_, pointerMethod := types.Unalias(want).(*types.Pointer)
		_, pointerValue := types.Unalias(selection.Recv()).(*types.Pointer)
		if pointerMethod && !pointerValue {
			t, err := f.goType(p, e.Pos(), want)
			if err != nil {
				return nil, err
			}
			if t.Element == nil {
				return nil, load.Error(p, e.Pos(), "implicit address-taking requires a modeled immutable payload")
			}
			args[0] = ir.Primitive{Op: ir.Some, Type: t, Args: []ir.Expr{args[0]}}
		} else if !pointerMethod && pointerValue {
			args[0], err = f.deref(e.Pos(), selection.Recv(), args[0])
			if err != nil {
				return nil, err
			}
		}
	}
	if fn == f.fn && f.source.Termination != "" {
		f.recursive = true
		return ir.Call{Target: symbol(fn), Args: args}, nil
	}
	abstract, err := f.callTarget(fn, e.Pos())
	if err != nil {
		return nil, err
	}
	if abstract {
		return ir.AbstractCall{Target: symbol(fn), Args: args}, nil
	}
	partial := f.compiler.partial[fn]
	f.hasPartial = f.hasPartial || partial
	return ir.Call{Target: symbol(fn), Args: args, Partial: partial}, nil
}

func (f *function) callTarget(fn *types.Func, pos token.Pos) (bool, error) {
	p := f.source.Package
	if _, ok := f.contracts[fn]; ok {
		f.contracts[fn] = true
		return true, nil
	}
	if fn.Pkg().Path() != p.PkgPath {
		if !f.compiler.source.Functions[fn].Export {
			return false, load.Error(p, pos, "cross-package call to %s requires golean:export or a contract", fn.FullName())
		}
		if err := f.depend(p, fn.Pkg().Path(), pos); err != nil {
			return false, err
		}
	}
	if f.state[fn] == 1 {
		return false, load.Error(p, pos, "recursive call to %s", fn.FullName())
	}
	if err := f.function(fn); err != nil {
		return false, err
	}
	if f.abstract[fn] {
		return false, load.Error(p, pos, "cannot call a function with caller-local contracts")
	}
	return false, nil
}

func (f *function) arguments(nodes []ast.Expr, sig *types.Signature) ([]ir.Expr, error) {
	args := make([]ir.Expr, len(nodes))
	for i, node := range nodes {
		if _, tuple := f.source.Package.TypesInfo.TypeOf(node).(*types.Tuple); tuple {
			return nil, load.Error(f.source.Package, node.Pos(), "destructure multiple results into locals before passing them as arguments")
		}
		value, err := f.value(node, sig.Params().At(i).Type())
		if err != nil {
			return nil, err
		}
		args[i] = value
	}
	return args, nil
}

func (f *function) deref(pos token.Pos, typ types.Type, value ir.Expr) (ir.Expr, error) {
	t, err := f.goType(f.source.Package, pos, typ)
	if err != nil {
		return nil, err
	}
	if t.Kind != ir.Pointer || t.Element == nil {
		return nil, load.Error(f.source.Package, pos, "pointer dereference requires a modeled immutable payload")
	}
	f.hasPartial = true
	return ir.Deref{Value: value}, nil
}

func (f *function) callArguments(e *ast.CallExpr, receiver ast.Expr) ([]ir.Expr, error) {
	sig := f.source.Package.TypesInfo.TypeOf(e.Fun).(*types.Signature)
	if sig.Variadic() {
		return nil, load.Error(f.source.Package, e.Pos(), "expected a non-variadic function call")
	}
	args, err := f.arguments(e.Args, sig)
	if err != nil {
		return nil, err
	}
	if receiver != nil {
		value, err := f.expr(receiver)
		if err != nil {
			return nil, err
		}
		args = append([]ir.Expr{value}, args...)
	}
	return args, nil
}
