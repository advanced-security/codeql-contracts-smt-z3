import cpp
import semmle.code.cpp.rangeanalysis.SimpleRangeAnalysis
import semmle.code.cpp.controlflow.Nullness
import semmle.code.cpp.controlflow.Guards

string describe(VariableAccess va) {
  // Note: fields are not analyzed, as nullness checks don't work well on them.
  lowerBound(va) > 0 and result = "range analysis non-null"
  or
  upperBound(va) <= 0 and result = "range analysis null"
  or
  exists(GuardCondition guard, Expr left, Expr right, int k, BasicBlock block |
    guard.ensuresEq(left, right, k, block, true) and
    va.getEnclosingBlock() = block and
    left.(VariableAccess).getTarget() = va.getTarget() and
    right.getValue() = "0" and
    result = "guards == " + k.toString()
    or
    guard.ensuresEq(left, right, k, block, false) and
    va.getEnclosingBlock() = block and
    left.(VariableAccess).getTarget() = va.getTarget() and
    right.getValue() = "0" and
    result = "guards != " + k.toString()
  )
}

predicate possiblyNonNull(VariableAccess va) {
  lowerBound(va) > 0
  or
  exists(GuardCondition guard, Expr left, Expr right, int k, BasicBlock block |
    guard.ensuresEq(left, right, k, block, false) and
    va.getEnclosingBlock() = block and
    left.(VariableAccess).getTarget() = va.getTarget() and
    right.getValue() = "0"
  )
}

predicate possiblyNull(VariableAccess va) { not possiblyNonNull(va) }
