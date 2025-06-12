import cpp
import z3.Z3

predicate supportedPrimitiveType(Type t, Z3::Sort s) {
  t instanceof BoolType and s instanceof Z3::BoolSort
  or
  t instanceof IntType and s instanceof Z3::IntSort
}

Z3::Sort z3SortForQlType(Type t, VariableAccess va) {
  va.getTarget().getType() = t and
  (
    t instanceof PointerType and dereferenced(va) and supportedPrimitiveType(t.stripType(), result)
    or
    (t instanceof PointerType and not dereferenced(va)) and
    result instanceof Z3::OptionNullSort
    or
    supportedPrimitiveType(t, result)
  )
}

Z3::Sort z3SortForQlType(VariableAccess va) {
  result = z3SortForQlType(va.getTarget().getType(), va)
}

string z3TypeForQlType(Type t, VariableAccess va) { z3SortForQlType(t, va).toString() = result }

string z3TypeForQlRawType(Type t) { z3SortForQlRawType(t).toString() = result }

Z3::Sort z3SortForQlRawType(Type t) {
  t instanceof PointerType and result instanceof Z3::OptionNullSort
  or
  supportedPrimitiveType(t, result)
}
