package interp

import (
	"fmt"
	"go/constant"
	"reflect"
)

func typecheck(n *node) error {
	switch n.action {
	// Arithmetic checks.
	case aAndAssign, aAndNotAssign, aXorAssign, aOrAssign,
		aShlAssign, aShrAssign,
		aAddAssign, aRemAssign, aMulAssign, aSubAssign, aQuoAssign,
		aLand, aLor,
		aAnd, aAndNot, aXor, aOr,
		aEqual, aNotEqual,
		aGreaterEqual, aGreater, aLowerEqual, aLower,
		aShl, aShr,
		aAdd, aRem, aMul, aSub, aQuo:
		if err := typecheck(n.child[0]); err != nil {
			return err
		}
		if err := typecheck(n.child[1]); err != nil {
			return err
		}

		c0, c1 := n.child[0], n.child[1]
		if c0.typ == nil || c1.typ == nil {
			return nil
		}

		act := n.action
		switch n.action {
		case aAndAssign, aAndNotAssign, aXorAssign, aOrAssign,
			aShlAssign, aShrAssign,
			aAddAssign, aRemAssign, aMulAssign, aSubAssign, aQuoAssign:
			if !okForArith[c0.typ.cat] && !c0.typ.isString() {
				return n.cfgErrorf("invalid operation: non-numeric type %s", c0.typ.id())
			}
			// Move the action to the non-assign version
			act = n.action-1
		}

		if act == aShl || act == aShr {
			convertLiteral(c1, &itype{cat: uintT})
			if !c1.typ.isInt() {
				return n.cfgErrorf("invalid operation: shift count type %v, must be integer", c1.typ.id())
			}
			if c0.typ.cat != idealT && !c0.typ.isInt() {
				return n.cfgErrorf("invalid operation: shift of type %v", c0.typ.id())
			}
			break
		}

		defaultLiteral2(c0, c1)

		t := c0.typ
		if t.cat == idealT {
			t = c1.typ
		}

		canAssign := false
		if isComparisonNode(n) && t.cat != idealT && !c0.typ.equals(c1.typ) {
			if isInterface(c1.typ) && !isInterface(c0.typ) && !c0.typ.comparable() {
				return n.cfgErrorf("invalid operation: operator %v not defined on %s", n.action, c0.typ.id())
			}

			canAssign = c0.typ.assignableTo(c1.typ)
			if isInterface(c0.typ) && !isInterface(c1.typ) && !c1.typ.comparable() {
				return n.cfgErrorf("invalid operation: operator %v not defined on %s", n.action, c1.typ.id())
			}
		}

		if t.cat != idealT && !c0.typ.equals(c1.typ) {
			if isInterface(c0.typ) == isInterface(c1.typ) || !canAssign {
				return n.cfgErrorf("invalid operation: mismatched types %s and %s", c0.typ.id(), c1.typ.id())
			}
		}

		if !okFor[act][actualCat(t)] {
			return n.cfgErrorf("invalid operation: operator %v not defined on %s", n.action, c0.typ.id())
		}
		if c0.typ.cat == idealT && c1.typ.cat == idealT {
			// If both are constants, check the left type as well.
			if !okFor[act][actualCat(c0.typ)] {
				return n.cfgErrorf("invalid operation: operator %v not defined on %s", n.action, c0.typ.id())
			}
		}

	// if l.Type.IsArray() && !IsComparable(l.Type) {
	// 	yyerror("invalid operation: %v (%v cannot be compared)", n, l.Type)
	// 	n.Type = nil
	// 	return n
	// }
	//
	// if l.Type.IsSlice() && !l.isNil() && !r.isNil() {
	// 	yyerror("invalid operation: %v (slice can only be compared to nil)", n)
	// 	n.Type = nil
	// 	return n
	// }
	//
	// if l.Type.IsMap() && !l.isNil() && !r.isNil() {
	// 	yyerror("invalid operation: %v (map can only be compared to nil)", n)
	// 	n.Type = nil
	// 	return n
	// }
	//
	// if l.Type.Etype == TFUNC && !l.isNil() && !r.isNil() {
	// 	yyerror("invalid operation: %v (func can only be compared to nil)", n)
	// 	n.Type = nil
	// 	return n
	// }
	//
	// if l.Type.IsStruct() {
	// 	if f := IncomparableField(l.Type); f != nil {
	// 		yyerror("invalid operation: %v (struct containing %v cannot be compared)", n, f.Type)
	// 		n.Type = nil
	// 		return n
	// 	}
	// }
	//
	// t = l.Type
	// if iscmp[n.Op] {
	// 	// TIDEAL includes complex constant, but only OEQ and ONE are defined for complex,
	// 	// so check that the n.op is available for complex  here before doing evconst.
	// 	if !okfor[n.Op][TCOMPLEX128] && (Isconst(l, CTCPLX) || Isconst(r, CTCPLX)) {
	// 		yyerror("invalid operation: %v (operator %v not defined on untyped complex)", n, n.Op)
	// 		n.Type = nil
	// 		return n
	// 	}
	// 	evconst(n)
	// 	t = types.Idealbool
	// 	if n.Op != OLITERAL {
	// 		l, r = defaultlit2(l, r, true)
	// 		n.Left = l
	// 		n.Right = r
	// 	}
	// }
	//
	// if (op == ODIV || op == OMOD) && Isconst(r, CTINT) {
	// 	if r.Val().U.(*Mpint).CmpInt64(0) == 0 {
	// 		yyerror("division by zero")
	// 		n.Type = nil
	// 		return n
	// 	}
	// }

	case aBitNot, aNeg, aNot, aPos:
		if err := typecheck(n.child[0]); err != nil {
			return err
		}
		c0 := n.child[0]
		t := c0.typ
		if t == nil {
			return nil
		}
		if !okFor[n.action][actualCat(t)] {
			return n.cfgErrorf("invalid operation: %v %s", n.action, c0.typ.id())
		}
	}
	return nil
}

var bitlen = [...]int{
	intT:     64,
	int8T:    8,
	int16T:   16,
	int32T:   32,
	int64T:   64,
	uintT:    64,
	uint8T:   8,
	uint16T:  16,
	uint32T:  32,
	uint64T:  64,
	uintptrT: 64,
}

func defaultLiteral2(n0, n1 *node) {
	if n0.typ.isUntyped() && !n1.typ.isUntyped() {
		convertLiteral(n0, n1.typ)
	}

	if n1.typ.isUntyped() && !n0.typ.isUntyped() {
		convertLiteral(n1, n0.typ)
	}
}

func convertLiteral(n *node, t *itype) {
	if t != nil && t.isUntyped() {
		panic(fmt.Sprintf("bad conversion to untyped: %v", t))
	}
	if !n.typ.isUntyped() {
		return
	}

	v := convertVal(n, t)
	if !v.IsValid() {
		return
	}
	n.rval = v
	n.typ = t
}

func convertVal(n *node, t *itype) reflect.Value {
	if !n.typ.isUntyped() || !n.rval.IsValid() {
		return n.rval
	}

	c, _ := n.rval.Interface().(constant.Value)

	switch n.typ {
	case idealBool:
		if t.isBool() {
			return n.rval
		}
	case idealString:
		if t.isString() {
			return n.rval
		}
	case idealInt, idealRune, idealFloat, idealComplex:
		switch {
		case t.isInt() && t.isSigned():
			c = constant.ToInt(c)
			i, ok := constant.Int64Val(c)
			if !ok {
				return reflect.Value{}
			}
			l := constant.BitLen(c)
			if l > bitlen[t.cat] {
				panic(fmt.Sprintf("constant %s overflows %s", c.ExactString(), t.name))
			}
			return reflect.ValueOf(i).Convert(t.TypeOf())
		case t.isInt():
			c = constant.ToInt(c)
			i, ok := constant.Uint64Val(c)
			if !ok {
				return reflect.Value{}
			}
			l := constant.BitLen(c)
			if l > bitlen[t.cat] {
				panic(fmt.Sprintf("constant %s overflows %s", c.ExactString(), t.name))
			}
			return reflect.ValueOf(i).Convert(t.TypeOf())
		case t.isFloat():
			f, ok := constant.Float64Val(constant.ToFloat(c))
			if !ok {
				return reflect.Value{}
			}
			return reflect.ValueOf(f).Convert(t.TypeOf())
		case t.isComplex():
			r, _ := constant.Float64Val(constant.Real(c))
			i, _ := constant.Float64Val(constant.Imag(c))
			return reflect.ValueOf(complex(r, i)).Convert(t.TypeOf())
		}
	}

	return reflect.Value{}
}

func actualCat(t *itype) tcat {
	switch t.cat {
	case idealT:
		switch t {
		case idealInt:
			return intT
		case idealRune:
			return int32T
		case idealFloat:
			return float64T
		case idealComplex:
			return complex128T
		default:
			return nilT
		}
	case valueT:
		return catOf(t.rtype)
	case aliasT:
		return t.val.cat
	default:
		return t.cat
	}
}

var errType = reflect.TypeOf((*error)(nil)).Elem()

func catOf(t reflect.Type) tcat {
	if t == nil {
		return nilT
	}
	if t == errType {
		return errorT
	}
	switch t.Kind() {
	case reflect.Bool:
		return boolT
	case reflect.Int:
		return intT
	case reflect.Int8:
		return int8T
	case reflect.Int16:
		return int16T
	case reflect.Int32:
		return int32T
	case reflect.Int64:
		return int64T
	case reflect.Uint:
		return uintT
	case reflect.Uint8:
		return uint8T
	case reflect.Uint16:
		return uint16T
	case reflect.Uint32:
		return uint32T
	case reflect.Uint64:
		return uint64T
	case reflect.Uintptr:
		return uintptrT
	case reflect.Float32:
		return float32T
	case reflect.Float64:
		return float64T
	case reflect.Complex64:
		return complex64T
	case reflect.Complex128:
		return complex128T
	case reflect.Array, reflect.Slice:
		return arrayT
	case reflect.Chan:
		return chanT
	case reflect.Func:
		return funcT
	case reflect.Interface:
		return interfaceT
	case reflect.Map:
		return mapT
	case reflect.Ptr:
		return ptrT
	case reflect.String:
		return stringT
	case reflect.Struct:
		return structT
	case reflect.UnsafePointer:
		return uintptrT
	}
	return nilT
}
