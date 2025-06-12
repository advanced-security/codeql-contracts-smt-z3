/**
 * @id cpp/test/SMT/Identifiers
 * @name Identifiers
 * @description Checks how identifiers are encoded in SMT.
 */

import cpp
import z3.cpp.contracts.SpecificationCase
import z3.cpp.contracts.SMT
import z3.cpp.contracts.style.AnnotatedCAssertStyleSpecifiedElement
import z3.Z3

string getBounds2(CodeQLSpecificationCase specCase, FunctionCall fc, Z3::Sort z3Sort) {
  // link these together
  fc.getTarget() = specCase.getFunction() and
  // analyze each argument
  exists(
    BoundaryAnalyzedFunctionCall bfc, ContractParameter p, Expr valueExpr, Expr anchorExpr,
    string id
  |
    fc = bfc and
    valueExpr = bfc.getAValueExpression(anchorExpr, p) and
    // pull the type from the parameter if it's the value
    // being passed to the function
    (
      if valueExpr = anchorExpr
      then (
        z3Sort = z3SortForQlRawType(p.getType()) and id = p.toId()
      ) else (
        z3Sort = z3SortForQlType(valueExpr) and
        id = valueExpr.(TerminalVariableAccess).toId(anchorExpr, p)
      )
    ) and
    //result = id
    // it isn't necessary to break up these cases --
    // we could just take a disjunction but this is presented
    // this way for clarity that we are taking different approaches
    // to value analysis.
    if z3Sort = Z3::TOptionNullSort()
    then
      exists(string categoricalValue |
        bfc.getACategoricalValue(valueExpr, anchorExpr, p) = categoricalValue and
        //and result = categoricalValueToAssert(id, categoricalValue)
        result = id + "CATEGORY INFER"
      )
    else
      exists(float lb, float ub |
        bfc.getALowerBound(valueExpr.getParent*(), anchorExpr, p) = lb and
        ub = bfc.getAUpperBound(valueExpr.getParent*(), anchorExpr, p) and
        //result = boundsToAssert(id, lb, ub)
        // lb = 0 and //ub = 0 and
        // ub = upperBound(valueExpr.getParent*().(Expr).getFullyConverted()) and
        result = id + "= NUMERIC INFER"
      )
  )
}

string testSubstituteRoot(
  CodeQLSpecificationCase specCase, FunctionCall fc, string orig, string anchorId
) {
  // link these together
  fc.getTarget() = specCase.getFunction() and
  // analyze each argument
  exists(
    BoundaryAnalyzedFunctionCall bfc, ContractParameter p, Z3::Sort z3Sort, Expr valueExpr,
    Expr anchorExpr, string id
  |
    fc = bfc and
    valueExpr = bfc.getAValueExpression(anchorExpr, p) and
    // pull the type from the parameter if it's the value
    // being passed to the function
    (
      if valueExpr = anchorExpr
      then (
        z3Sort = z3SortForQlRawType(p.getType()) and id = p.toId()
      ) else (
        z3Sort = z3SortForQlType(valueExpr) and
        id = valueExpr.(TerminalVariableAccess).toId(anchorExpr, p)
      )
    ) and
    id = result and
    orig = valueExpr.(TerminalVariableAccess).toId() and
    anchorId = anchorExpr.(TerminalVariableAccess).toId()
  )
}

predicate testValueExpressions(
  FunctionCall fc, CodeQLSingleSpecificationCase specCase, Expr anchorExpr, Expr expr
) {
  fc.getTarget() = specCase.getFunction() and
  exists(BoundaryAnalyzedFunctionCall bfc, ContractParameter p |
    fc = bfc and
    expr = bfc.getAValueExpression(anchorExpr, p)
  )
}

TerminalVariableAccess testGetAValueExpression(
  BoundaryAnalyzedFunctionCall bfc, Expr fcExpr, ContractParameter cp
) {
  bfc.getAnActualFormalParameterPair(fcExpr, cp) and
  (
    // an implicit reference that is the most recent one
    result = getAPrefixedVariableReferenceForExpr2(fcExpr) and
    isLastVariableReferenceInContext(result)
    or
    // an explicit one
    result = fcExpr
  )
}

TerminalVariableAccess getAPrefixedVariableReferenceForExpr2(Expr exp) {
  // first, convert the target into the normalized form. We
  // do this but if no conversion exists (because there isn't one
  // for example, in the case of an arithmetic expression) then the
  // `variableAccessesForExpression` predicate is empty.
  exists(TerminalVariableAccess parentVa |
    parentVa.forExpr() = exp and
    exists(TerminalVariableAccess childVa |
      // see if the parent is a prefix of the child.
      parentVa.refersTo(childVa) and
      // but not identical
      not childVa.toId() = parentVa.toId() and
      result = childVa
    )
  )
}

predicate testRefersTo(
  TerminalVariableAccess va1, TerminalVariableAccess va2, string id1, string id2
) {
  id1 = va1.toId() and
  id2 = va2.toId() and
  va1.refersTo(va2)
}

predicate testNotRefersTo(
  TerminalVariableAccess va1, TerminalVariableAccess va2, string id1, string id2
) {
  id1 = va1.toId() and
  id2 = va2.toId() and
  not va1.refersTo(va2)
}

predicate testStripPrefix(TerminalVariableAccess va1, string prefix, string stripped, string id) {
  va1.stripPrefix(prefix) = stripped and id = va1.toId()
}

predicate testStripPrefix2(
  TerminalVariableAccess va1, TerminalVariableAccess va2, string id1, string id2, string stripped1,
  string stripped2
) {
  va1.stripPrefix(_) = stripped1 and
  id1 = va1.toId() and
  va2.stripPrefix(_) = stripped2 and
  id2 = va2.toId()
}

predicate testTerminalVariableAccessId(TerminalVariableAccess va, string id) { id = va.toId() }

predicate testTerminalVariableAccessIdExpr(TerminalVariableAccess va, Expr exp, string id) {
  va.forExpr() = exp and id = va.toId()
}

Z3::Sort testTerminalVariableAccessTypes(TerminalVariableAccess va) {
  z3SortForQlRawType(va.getTarget().getType()) = result
}

Type testTerminalVariableAccessType(TerminalVariableAccess va, string clazz) {
  result = va.getTarget().getType() and
  result.getAQlClass() = clazz
}

predicate testBoundaryAnalyzedFunctionCall(BoundaryAnalyzedFunctionCall bfc) { any() }

predicate testContractParameter(ContractParameter cp) { any() }

predicate testContractPairs(BoundaryAnalyzedFunctionCall bfc, Expr expr, ContractParameter p) {
  bfc.getAnActualFormalParameterPair(expr, p)
}

Z3::Sort z3SortForQlType2(Type t, VariableAccess va) {
  (
    t instanceof PointerType and dereferenced(va) and supportedPrimitiveType(t.stripType(), result)
    or
    (t instanceof PointerType and not dereferenced(va)) and
    result instanceof Z3::OptionNullSort
    or
    supportedPrimitiveType(t, result)
  )
}

Z3::Sort z3SortForQlType3(Type t, TerminalVariableAccess va) {
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

/// note: predicates above are for debugging
from FunctionCall fc, CodeQLSpecificationCase specCase, string bounds
where
  fc.getTarget() = specCase.getFunction() and
  Contracts::getBounds(specCase, fc) = bounds
// getBounds2(specCase, fc) = bounds
select fc, specCase, bounds

// check that the preconditions are getting generated
query string checkPreconditions(CodeQLSpecificationCase specCase) {
  Contracts::concatPreconditions(specCase) = result
}

// check that the declarations are getting generated
query string checkDeclarations(FunctionCall fc, CodeQLSpecificationCase specCase) {
  fc.getTarget() = specCase.getFunction() and
  Contracts::extractDeclarations(specCase, fc) = result
}
