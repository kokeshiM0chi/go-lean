// Package ir defines the closed, typed representation consumed by Lean emission.
package ir

type Symbol struct {
	Package string
	Name    string
}

type Kind uint8

const (
	Bool Kind = iota + 1
	String
	Int8
	Int16
	Int32
	Int64
	UInt8
	UInt16
	UInt32
	UInt64
	Record
	Array
	ByteArray
	OrderedMap
	OrderedSet
	Option
	BitVec
	List
	FoldControl
	Box
	Interface
	Pointer
	Tuple
)

const ExternalTypesPackage = "go-lean:types"

type Type struct {
	Kind   Kind
	Record Symbol
	// Element is the element or map value type. Key is the ordered key type.
	Element, Key *Type
	Elements     []Type
}

type Field struct {
	Name string
	Type Type
}

type Declaration interface{ declaration() }

type Struct struct {
	Symbol    Symbol
	Fields    []Field
	Recursive bool
}

func (Struct) declaration() {}

// OpaqueInterface preserves an interface value without modeling its methods or
// dynamic type. Its Lean carrier is opaque; nil is represented separately.
type OpaqueInterface struct{ Symbol Symbol }

func (OpaqueInterface) declaration() {}

type OpaqueTypes struct{}

func (OpaqueTypes) declaration() {}

type Binding struct {
	Unused bool
	Name   string
	ID     int
	Type   Type
}

type Function struct {
	Symbol      Symbol
	Params      []Binding
	Result      Type
	Body        Expr
	Contracts   []Symbol
	Termination string
	// Partial wraps the result in Option: none denotes a nil interface call.
	Partial bool
}

func (Function) declaration() {}

type Proposition struct {
	Name string
	Lean string
}

type Contract struct {
	Caller, Callee Symbol
	Params         []Type
	Result         Type
	Assumptions    []Proposition
	// Name is the Go name exposed to assumption propositions.
	Name string
}

func (Contract) declaration() {}

type Law struct {
	Proposition
	Caller    Symbol
	Contracts []Symbol
}

type Package struct {
	Path, Name, Dir string
	Word            Kind
	Imports         []string
	LeanImports     []string
	Decls           []Declaration
	Laws            []Law
	Folds           FoldKind
}

type Expr interface{ expression() }

type Constant struct {
	Type Type
	// Value is decimal for integers, true/false for booleans, and raw bytes for strings.
	Value string
}

type Local struct{ ID int }
type Let struct {
	ID          int
	Value, Body Expr
	Unused      bool
}
type If struct{ Cond, Then, Else Expr }

// Join binds the continuation of an if whose branches can both fall through.
type Join struct {
	ID         int
	Next, Body Expr
}

type Jump struct{ ID int }

type UnaryOp uint8

const Not UnaryOp = iota + 1

type Unary struct {
	Op    UnaryOp
	Value Expr
}

type BinaryOp uint8

const (
	Add BinaryOp = iota + 1
	Sub
	Eq
	Ne
	Lt
	Le
	Gt
	Ge
	And
	Or
)

type Binary struct {
	Op          BinaryOp
	Kind        Kind
	Left, Right Expr
}
type FieldRead struct {
	Record  Expr
	Name    string
	Control bool
}
type StructLiteral struct {
	Type   Symbol
	Fields []Expr
}
type Call struct {
	Target  Symbol
	Args    []Expr
	Partial bool
}

type TupleLiteral struct{ Values []Expr }
type TupleRead struct {
	Value        Expr
	Index, Count int
}
type Deref struct{ Value Expr }
type AbstractCall struct {
	Target Symbol
	Args   []Expr
}

// InterfaceCall dispatches through an explicit contract. Args includes the
// interface receiver first; a nil receiver aborts the enclosing partial model.
type InterfaceCall struct {
	Target Symbol
	Args   []Expr
}

type FoldKind uint8

const (
	FoldN FoldKind = 1 << iota
	FoldNUntil
	FoldList
	FoldListUntil
)

type Fold struct {
	Kind           FoldKind
	Input, Initial Expr
	Step           Symbol
	Abstract       bool
}

type FoldControlLiteral struct {
	State, Stop Expr
}

type PrimitiveOp uint8

const (
	Empty PrimitiveOp = iota + 1
	Some
	None
	IsSome
	UnwrapOr
	Nil
	Cons
	IsEmpty
	Push
	Pop
	Get
	Set
	Size
	Extract
	Find
	Contains
	Insert
	Erase
	NewBitVec
	Width
	ToUint64
	BoxGet
)

type Primitive struct {
	Op   PrimitiveOp
	Type Type
	Args []Expr
}

func (Constant) expression()           {}
func (Local) expression()              {}
func (Let) expression()                {}
func (If) expression()                 {}
func (Join) expression()               {}
func (Jump) expression()               {}
func (Unary) expression()              {}
func (Binary) expression()             {}
func (FieldRead) expression()          {}
func (StructLiteral) expression()      {}
func (Call) expression()               {}
func (AbstractCall) expression()       {}
func (InterfaceCall) expression()      {}
func (TupleLiteral) expression()       {}
func (TupleRead) expression()          {}
func (Deref) expression()              {}
func (Primitive) expression()          {}
func (Fold) expression()               {}
func (FoldControlLiteral) expression() {}
