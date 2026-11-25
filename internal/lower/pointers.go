package lower

import (
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/load"
	"golang.org/x/tools/go/packages"
)

// Pointer representations depend only on their Go type, never on the selected
// roots. Regenerating a dependency alone therefore preserves calling conventions.
// Payloads outside the immutable subset stay opaque and cannot be dereferenced.
func (c *compiler) snapshotPointer(p *packages.Package, typ types.Type) bool {
	return c.snapshotType(p, typ, make(map[types.Type]bool))
}

func (c *compiler) snapshotType(p *packages.Package, typ types.Type, visiting map[types.Type]bool) bool {
	typ = types.Unalias(typ)
	if visiting[typ] {
		return false
	}
	visiting[typ] = true
	defer delete(visiting, typ)
	switch t := typ.(type) {
	case *types.Basic:
		_, err := basic(p, 0, t)
		return err == nil
	case *types.Pointer:
		return c.snapshotType(p, t.Elem(), visiting)
	case *types.Named:
		if t.Obj().Pkg() != nil && t.Obj().Pkg().Path() == load.Curated {
			if curatedTypes[t.Obj().Name()] == ir.Kind(0) {
				return false
			}
			for i := 0; i < t.TypeArgs().Len(); i++ {
				if !c.snapshotType(p, t.TypeArgs().At(i), visiting) {
					return false
				}
			}
			return true
		}
		switch u := t.Underlying().(type) {
		case *types.Basic:
			_, err := basic(p, 0, u)
			return err == nil
		case *types.Interface:
			return true
		case *types.Struct:
			owner := t.Obj().Pkg()
			if owner == nil || t.Obj().Parent() != owner.Scope() || p.Module == nil {
				return false
			}
			decl := c.source.Packages[owner.Path()]
			if decl == nil || decl.Module == nil || decl.Module.Path != p.Module.Path || t.TypeParams().Len() != 0 {
				return false
			}
			for i := 0; i < u.NumFields(); i++ {
				f := u.Field(i)
				if f.Embedded() || f.Name() == "_" || !c.snapshotType(p, f.Type(), visiting) {
					return false
				}
			}
			return true
		}
	}
	return false
}
