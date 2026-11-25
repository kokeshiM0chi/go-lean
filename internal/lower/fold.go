package lower

import (
	"go/ast"
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/load"
)

var folds = map[string]ir.FoldKind{
	"FoldN": ir.FoldN, "FoldNUntil": ir.FoldNUntil,
	"FoldList": ir.FoldList, "FoldListUntil": ir.FoldListUntil,
}

func (f *function) fold(e *ast.CallExpr, kind ir.FoldKind) (ir.Expr, error) {
	p := f.source.Package
	step := ast.Unparen(e.Args[2])
	var fn *types.Func
	switch target := step.(type) {
	case *ast.Ident:
		fn, _ = p.TypesInfo.Uses[target].(*types.Func)
	case *ast.SelectorExpr:
		if p.TypesInfo.Selections[target] == nil {
			fn, _ = p.TypesInfo.Uses[target.Sel].(*types.Func)
		}
	}
	if fn == nil || fn.Pkg() == nil || fn.Pkg().Path() == load.Curated ||
		fn.Type().(*types.Signature).TypeParams().Len() != 0 {
		return nil, load.Error(p, step.Pos(), "fold step must be a directly named, non-generic function")
	}
	if _, err := f.goType(p, e.Pos(), p.TypesInfo.TypeOf(e)); err != nil {
		return nil, err
	}
	args, err := f.arguments(e.Args[:2], p.TypesInfo.TypeOf(e.Fun).(*types.Signature))
	if err != nil {
		return nil, err
	}
	abstract, err := f.callTarget(fn, step.Pos())
	if err != nil {
		return nil, err
	}
	if f.compiler.partial[fn] {
		return nil, load.Error(p, step.Pos(), "fold steps with partial pointer reads are unsupported; model failure explicitly in the fold state")
	}
	f.output(p.PkgPath).Folds |= kind
	return ir.Fold{Kind: kind, Input: args[0], Initial: args[1], Step: symbol(fn), Abstract: abstract}, nil
}
