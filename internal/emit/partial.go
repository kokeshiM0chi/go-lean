package emit

import "github.com/frederik-jatzkowski/go-lean/internal/ir"

// partialRenderer sequences expressions in Option. Only interface dispatch can
// fail; pure calls retain their existing model and are lifted with some.
// Negative local IDs keep generated temporaries separate from Go bindings.
type partialRenderer struct {
	renderer
	next int
}

func successful(value string) string { return "(_root_.Option.some " + value + ")" }

func (r *partialRenderer) bind(value ir.Expr, next func(ir.Expr) string) string {
	r.next--
	id := r.next
	expression := r.expr(value)
	return "(_root_.Option.bind " + expression + " (fun " + local(id) + " => " + next(ir.Local{ID: id}) + "))"
}

func (r *partialRenderer) values(values []ir.Expr, next func([]ir.Expr) string) string {
	if len(values) == 0 {
		return next(nil)
	}
	return r.bind(values[0], func(first ir.Expr) string {
		return r.values(values[1:], func(rest []ir.Expr) string {
			return next(append([]ir.Expr{first}, rest...))
		})
	})
}

func (r *partialRenderer) expr(e ir.Expr) string {
	lift := func(e ir.Expr) string { return successful(r.renderer.expr(e)) }
	switch v := e.(type) {
	case ir.Let:
		name := local(v.ID)
		if v.Unused {
			name = "_"
		}
		return "(_root_.Option.bind " + r.expr(v.Value) + " (fun " + name + " => " + r.expr(v.Body) + "))"
	case ir.Deref:
		return r.bind(v.Value, func(value ir.Expr) string { return r.renderer.expr(value) })
	case ir.TupleLiteral:
		return r.values(v.Values, func(values []ir.Expr) string { v.Values = values; return lift(v) })
	case ir.TupleRead:
		return r.bind(v.Value, func(value ir.Expr) string { v.Value = value; return lift(v) })
	case ir.If:
		return r.bind(v.Cond, func(cond ir.Expr) string {
			return "(if " + r.renderer.expr(cond) + " then " + r.expr(v.Then) + " else " + r.expr(v.Else) + ")"
		})
	case ir.Join:
		return "(let " + local(v.ID) + " := fun (_ : _root_.Unit) => " + r.expr(v.Next) + "; " + r.expr(v.Body) + ")"
	case ir.Jump:
		return r.renderer.expr(v)
	case ir.InterfaceCall:
		return r.values(v.Args, func(args []ir.Expr) string {
			operation := r.renderer.expr(ir.AbstractCall{Target: v.Target, Args: args})
			return "(if (" + r.renderer.expr(args[0]) + ").isSome then " + successful(operation) + " else _root_.Option.none)"
		})
	case ir.Unary:
		return r.bind(v.Value, func(value ir.Expr) string { v.Value = value; return lift(v) })
	case ir.Binary:
		return r.bind(v.Left, func(left ir.Expr) string {
			// Go's Boolean operators must not evaluate a skipped nil call.
			if v.Op == ir.And {
				return "(if " + r.renderer.expr(left) + " then " + r.expr(v.Right) + " else " + successful("_root_.Bool.false") + ")"
			}
			if v.Op == ir.Or {
				return "(if " + r.renderer.expr(left) + " then " + successful("_root_.Bool.true") + " else " + r.expr(v.Right) + ")"
			}
			return r.bind(v.Right, func(right ir.Expr) string { v.Left, v.Right = left, right; return lift(v) })
		})
	case ir.FieldRead:
		return r.bind(v.Record, func(value ir.Expr) string { v.Record = value; return lift(v) })
	case ir.StructLiteral:
		return r.values(v.Fields, func(fields []ir.Expr) string { v.Fields = fields; return lift(v) })
	case ir.Call:
		return r.values(v.Args, func(args []ir.Expr) string {
			v.Args = args
			if v.Partial {
				return r.renderer.expr(v)
			}
			return lift(v)
		})
	case ir.AbstractCall:
		return r.values(v.Args, func(args []ir.Expr) string { v.Args = args; return lift(v) })
	case ir.Primitive:
		return r.values(v.Args, func(args []ir.Expr) string { v.Args = args; return lift(v) })
	case ir.Fold:
		return r.values([]ir.Expr{v.Input, v.Initial}, func(args []ir.Expr) string { v.Input, v.Initial = args[0], args[1]; return lift(v) })
	case ir.FoldControlLiteral:
		return r.values([]ir.Expr{v.State, v.Stop}, func(args []ir.Expr) string { v.State, v.Stop = args[0], args[1]; return lift(v) })
	default:
		return lift(e)
	}
}
