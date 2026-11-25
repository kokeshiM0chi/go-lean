package lower

import (
	"go/token"
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/load"
	"golang.org/x/tools/go/packages"
)

func basic(p *packages.Package, pos token.Pos, b *types.Basic) (ir.Type, error) {
	var kind ir.Kind
	switch b.Kind() {
	case types.Bool, types.UntypedBool:
		kind = ir.Bool
	case types.String, types.UntypedString:
		kind = ir.String
	case types.Int8:
		kind = ir.Int8
	case types.Int16:
		kind = ir.Int16
	case types.Int32, types.UntypedRune:
		kind = ir.Int32
	case types.Int64:
		kind = ir.Int64
	case types.Uint8:
		kind = ir.UInt8
	case types.Uint16:
		kind = ir.UInt16
	case types.Uint32:
		kind = ir.UInt32
	case types.Uint64:
		kind = ir.UInt64
	case types.Int, types.UntypedInt:
		kind = ir.Int64
		if p.TypesSizes.Sizeof(types.Typ[types.Int]) == 4 {
			kind = ir.Int32
		}
	case types.Uint:
		kind = ir.UInt64
		if p.TypesSizes.Sizeof(b) == 4 {
			kind = ir.UInt32
		}
	default:
		return ir.Type{}, load.Error(p, pos, "unsupported scalar type %s", b)
	}
	return ir.Type{Kind: kind}, nil
}

var curatedTypes = map[string]ir.Kind{
	"Array": ir.Array, "ByteArray": ir.ByteArray, "OrderedMap": ir.OrderedMap, "OrderedSet": ir.OrderedSet,
	"Box": ir.Box, "Option": ir.Option, "BitVec": ir.BitVec, "List": ir.List, "FoldControl": ir.FoldControl,
}

func (c *compiler) goType(p *packages.Package, pos token.Pos, typ types.Type) (ir.Type, error) {
	if named, ok := typ.(interface{ Obj() *types.TypeName }); ok {
		if issue := c.source.TypeIssues[named.Obj()]; issue != nil {
			return ir.Type{}, issue
		}
	}
	switch t := types.Unalias(typ).(type) {
	case *types.Pointer:
		if c.snapshotPointer(p, t) {
			elem, err := c.goType(p, pos, t.Elem())
			return ir.Type{Kind: ir.Pointer, Element: &elem}, err
		}
		return ir.Type{Kind: ir.Pointer, Record: c.opaqueType(p, t)}, nil
	case *types.Basic:
		return basic(p, pos, t)
	case *types.Named:
		obj := t.Obj()
		if issue := c.source.TypeIssues[obj]; issue != nil {
			return ir.Type{}, issue
		}
		if obj.Pkg() != nil && obj.Pkg().Path() == load.Curated {
			kind, ok := curatedTypes[obj.Name()]
			if !ok {
				break
			}
			result := ir.Type{Kind: kind}
			for i := 0; i < t.TypeArgs().Len(); i++ {
				arg, err := c.goType(p, pos, t.TypeArgs().At(i))
				if err != nil {
					return ir.Type{}, err
				}
				if i == 0 && (kind == ir.OrderedMap || kind == ir.OrderedSet) {
					result.Key = &arg
				} else {
					result.Element = &arg
				}
			}
			return result, nil
		}
		if t.TypeParams().Len() != 0 {
			break
		}
		switch u := t.Underlying().(type) {
		case *types.Basic:
			return basic(p, pos, u)
		case *types.Interface:
			if obj.Pkg() == nil || c.source.Packages[obj.Pkg().Path()] == nil || c.source.Packages[obj.Pkg().Path()].Module == nil || p.Module == nil || c.source.Packages[obj.Pkg().Path()].Module.Path != p.Module.Path {
				return ir.Type{Kind: ir.Interface, Record: c.opaqueType(p, t)}, nil
			}
			if obj.Parent() != obj.Pkg().Scope() {
				break
			}
			id := symbol(obj)
			if err := c.depend(p, id.Package, pos); err != nil {
				return ir.Type{}, err
			}
			if c.state[obj] == 0 {
				out := c.output(id.Package)
				out.Decls = append(out.Decls, ir.OpaqueInterface{Symbol: id})
				c.state[obj] = 2
			}
			return ir.Type{Kind: ir.Interface, Record: id}, nil
		case *types.Struct:
			if obj.Parent() != obj.Pkg().Scope() {
				break
			}
			id := symbol(obj)
			if err := c.depend(p, id.Package, pos); err != nil {
				return ir.Type{}, err
			}
			if c.state[obj] == 1 {
				return ir.Type{}, load.Error(p, pos, "recursive record %s", obj.Name())
			}
			if c.state[obj] == 0 {
				c.state[obj] = 1
				owner := c.source.Packages[id.Package]
				record := ir.Struct{Symbol: id}
				for i := 0; i < u.NumFields(); i++ {
					field := u.Field(i)
					if field.Embedded() || field.Name() == "_" {
						return ir.Type{}, load.Error(owner, field.Pos(), "embedded and blank fields are unsupported")
					}
					if isSelfBox(field.Type(), obj) {
						elem := ir.Type{Kind: ir.Record, Record: id}
						record.Fields = append(record.Fields, ir.Field{Name: field.Name(), Type: ir.Type{Kind: ir.Box, Element: &elem}})
						record.Recursive = true
						continue
					}
					ft, err := c.goType(owner, field.Pos(), field.Type())
					if err != nil {
						return ir.Type{}, err
					}
					record.Fields = append(record.Fields, ir.Field{Name: field.Name(), Type: ft})
				}
				out := c.output(id.Package)
				out.Decls = append(out.Decls, record)
				c.state[obj] = 2
			}
			return ir.Type{Kind: ir.Record, Record: id}, nil
		}
	}
	return ir.Type{}, load.Error(p, pos, "unsupported type %s", typ)
}

func isSelfBox(typ types.Type, owner *types.TypeName) bool {
	box, ok := types.Unalias(typ).(*types.Named)
	if !ok || box.Obj().Pkg() == nil || box.Obj().Pkg().Path() != load.Curated || box.Obj().Name() != "Box" {
		return false
	}
	payload, ok := types.Unalias(box.TypeArgs().At(0)).(*types.Named)
	return ok && payload.Obj() == owner
}

func (c *compiler) zero(t ir.Type) ir.Expr {
	switch t.Kind {
	case ir.Record:
		for _, decl := range c.output(t.Record.Package).Decls {
			if record, ok := decl.(ir.Struct); ok && record.Symbol == t.Record {
				fields := make([]ir.Expr, len(record.Fields))
				for i, field := range record.Fields {
					fields[i] = c.zero(field.Type)
				}
				return ir.StructLiteral{Type: t.Record, Fields: fields}
			}
		}
		panic("missing record for Go zero value")
	case ir.Bool:
		return ir.Constant{Type: t, Value: "false"}
	case ir.String:
		return ir.Constant{Type: t}
	case ir.FoldControl:
		return ir.FoldControlLiteral{State: c.zero(*t.Element), Stop: c.zero(ir.Type{Kind: ir.Bool})}
	case ir.Interface, ir.Pointer:
		return ir.Primitive{Op: ir.None, Type: t}
	case ir.Tuple:
		values := make([]ir.Expr, len(t.Elements))
		for i, elem := range t.Elements {
			values[i] = c.zero(elem)
		}
		return ir.TupleLiteral{Values: values}
	default:
		if t.Kind < ir.Record {
			return ir.Constant{Type: t, Value: "0"}
		}
		return ir.Primitive{Op: ir.Empty, Type: t}
	}
}

// All external carriers share a fixed support module. Its contents do not vary
// with package selection, so focused generation cannot invalidate other models.
func (c *compiler) opaqueType(p *packages.Package, typ types.Type) ir.Symbol {
	if c.packages[ir.ExternalTypesPackage] == nil {
		c.packages[ir.ExternalTypesPackage] = &ir.Package{
			Path: ir.ExternalTypesPackage, Name: "golean_types", Dir: p.Module.Dir,
			Word: c.output(p.PkgPath).Word, Decls: []ir.Declaration{ir.OpaqueTypes{}},
		}
	}
	out := c.output(p.PkgPath)
	found := false
	for _, path := range out.Imports {
		found = found || path == ir.ExternalTypesPackage
	}
	if !found {
		out.Imports = append(out.Imports, ir.ExternalTypesPackage)
	}
	return ir.Symbol{Package: ir.ExternalTypesPackage, Name: types.TypeString(canonicalType(typ), nil)}
}

func canonicalType(t types.Type) types.Type {
	switch t := types.Unalias(t).(type) {
	case *types.Pointer:
		return types.NewPointer(canonicalType(t.Elem()))
	case *types.Slice:
		return types.NewSlice(canonicalType(t.Elem()))
	case *types.Array:
		return types.NewArray(canonicalType(t.Elem()), t.Len())
	case *types.Map:
		return types.NewMap(canonicalType(t.Key()), canonicalType(t.Elem()))
	case *types.Chan:
		return types.NewChan(t.Dir(), canonicalType(t.Elem()))
	case *types.Struct:
		fields, tags := make([]*types.Var, t.NumFields()), make([]string, t.NumFields())
		for i := range fields {
			f := t.Field(i)
			fields[i] = types.NewField(f.Pos(), f.Pkg(), f.Name(), canonicalType(f.Type()), f.Embedded())
			tags[i] = t.Tag(i)
		}
		return types.NewStruct(fields, tags)
	default:
		return t
	}
}

func (c *compiler) resultType(p *packages.Package, pos token.Pos, results *types.Tuple) (ir.Type, error) {
	if results.Len() == 1 {
		return c.goType(p, pos, results.At(0).Type())
	}
	result := ir.Type{Kind: ir.Tuple}
	for i := 0; i < results.Len(); i++ {
		t, err := c.goType(p, pos, results.At(i).Type())
		if err != nil {
			return ir.Type{}, err
		}
		result.Elements = append(result.Elements, t)
	}
	return result, nil
}
