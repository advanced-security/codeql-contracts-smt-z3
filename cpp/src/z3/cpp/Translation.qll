/**
 * A Specification consists of specification cases which in turn consist of
 * specification clauses.
 */

import cpp
import semmle.code.cpp.rangeanalysis.SimpleRangeAnalysis
import z3.cpp.Util
import z3.cpp.contracts.Nullity
import z3.cpp.contracts.SpecificationCase

/**
 * The `isSupported` predicate for mainline versions.
 */
predicate isSupported(Expr exp) {
  // exp = requires.getClauseExpr() and
  not exp.getAChild*() instanceof FunctionCall and
  forex(VariableAccess va, Type t |
    va.getParent*() = exp and
    t = va.getTarget().getType() and
    not va.getTarget().getName() = "__PRETTY_FUNCTION__"
  |
    not va instanceof Qualifier
    implies
    (
      // it's a dereferenced pointer to a known type
      t instanceof PointerType and dereferenced(va) and supportedPrimitiveType(t.stripType(), _)
      or
      // it's a pointer type we leave opaque
      t instanceof PointerType and not dereferenced(va)
      or
      supportedPrimitiveType(t, _)
    )
  )
}

module Historical {
  predicate isSupportedPOC(Expr exp) {
    forall(VariableAccess va |
      va.getParent*() = exp and not va.getTarget().getName() = "__PRETTY_FUNCTION__"
    |
      va.getTarget().getType() instanceof IntType or
      va.getTarget().getType() instanceof BoolType
    )
  }

  predicate isSupportedEvaluation1(Expr exp) {
    // exp = requires.getClauseExpr() and
    not exp.getAChild*() instanceof FunctionCall and
    forex(VariableAccess va, Type t |
      va.getParent*() = exp and
      t = va.getTarget().getType() and
      not va.getTarget().getName() = "__PRETTY_FUNCTION__"
    |
      not va instanceof Qualifier
      implies
      (
        // it's a dereferenced pointer to a known type
        t instanceof PointerType and
        dereferenced(va) and
        supportedPrimitiveTypeEvaluation1(t.stripType(), _)
        or
        // it's a pointer type we leave opaque
        t instanceof PointerType and not dereferenced(va)
        or
        supportedPrimitiveTypeEvaluation1(t, _)
      )
    )
  }

  predicate supportedPrimitiveTypeEvaluation1(Type t, Z3::Sort s) {
    t instanceof BoolType and s instanceof Z3::BoolSort
    or
    t instanceof IntType and s instanceof Z3::IntSort
  }
}

string declarationsForExpr(Expr exp) {
  exists(TerminalVariableAccess v |
    v.forExpr() = exp and
    result = "(declare-const " + v.toId() + " " + z3TypeForQlType(v.getTarget().getType(), v) + ")"
  )
}

class BoundaryAnalyzedFunctionCall extends FunctionCall {
  CodeQLSpecificationCase specCase;

  BoundaryAnalyzedFunctionCall() { getTarget() = specCase.getFunction() }

  CodeQLSpecificationCase forSpecCase() { result = specCase }

  Expr getAValueExpression(Expr fcExpr, ContractParameter cp) {
    getAnActualFormalParameterPair(fcExpr, cp) and
    (
      // an implicit reference that is the most recent one
      result = getAPrefixedVariableReferenceForExpr(fcExpr) and
      isLastVariableReferenceInContext(result)
      or
      // an explicit one
      result = fcExpr
    )
  }

  predicate getAnActualFormalParameterPair(Expr expr, ContractParameter p) {
    p = getTarget().getAParameter() and
    expr = getArgument(p.getIndex())
  }

  float getAUpperBound(Expr exprA, Expr exprB, Parameter p) {
    getAnActualFormalParameterPair(exprB, p) and
    result = getAUpperBound(exprA)
  }

  float getAUpperBound(Expr expr) { result = upperBound(expr.getFullyConverted()) }

  float getALowerBound(Expr exprA, Expr exprB, Parameter p) {
    getAnActualFormalParameterPair(exprB, p) and
    result = getALowerBound(exprA)
  }

  float getALowerBound(Expr expr) { result = lowerBound(expr.getFullyConverted()) }

  string getACategoricalValue(Expr exprA, Expr exprB, Parameter p) {
    getAnActualFormalParameterPair(exprB, p) and
    result = getACategoricalValue(exprA)
  }

  string getACategoricalValue(Expr expr) {
    if
      exists(VariableAccess va |
        va.getParent*() = expr and
        possiblyNull(va)
      )
    then result = any(Z3::MaybeNullOptionNullSortLiteral sl).toString()
    else result = any(Z3::NotNullOptionNullSortLiteral sl).toString()
  }
}

class ContractParameter extends Parameter {
  ContractParameter() {
    // it's part of a contract
    exists(BoundaryAnalyzedFunctionCall bfc | bfc.getTarget().getAParameter() = this)
  }

  string toId() { result = getPrefixForType(z3SortForQlRawType(getType())) + getName() }
}

/**
 * Extracts the terminal variable accesses for an expression.
 */
class TerminalVariableAccess extends VariableAccess {
  Expr exp;

  TerminalVariableAccess() {
    getParent*() = exp and
    not exp instanceof FunctionCall and
    not exists(VariableAccess va | va.getQualifier() = this)
  }

  Expr forExpr() { result = exp }

  string getTypePrefix() { result = getTypePrefix(this) }

  // for the given variable access, substitute the part that matches
  // the anchor to the parameter's name, ignoring the actual type of the
  // value or reference.
  string toId(TerminalVariableAccess anchor, ContractParameter p) {
    exists(string typePrefix, string idWithoutPrefix, string anchorIdWithoutPrefix, string id |
      typePrefix = getTypePrefix() and // if it's a reference or value
      // the entire reference must be subsumed
      idWithoutPrefix = toId(this) and
      anchorIdWithoutPrefix = toId(anchor) and
      idWithoutPrefix.indexOf(anchorIdWithoutPrefix) = 0 and
      // we are talking about the same thing, so replace it with the id of
      // the parameter
      id =
        typePrefix + p.getName() +
          idWithoutPrefix.substring(anchorIdWithoutPrefix.length(), idWithoutPrefix.length()) and
      result = id
    )
  }

  string toId() {
    not this instanceof FieldAccess and result = getTypePrefix() + getTarget().getName()
    or
    // this is the case where it's not a nested type at all
    result = getTypePrefix() + toId(this.getQualifier()) + "_qlcontracts_" + getTarget().getName()
  }

  private string toId(VariableAccess va) {
    not va instanceof FieldAccess and result = va.getTarget().getName()
    or
    result = toId(va.getQualifier()) + "_qlcontracts_" + va.getTarget().getName()
  }

  // irrespective of type, are they the same container?
  predicate refersTo(TerminalVariableAccess va) {
    // this is a substring of that?
    va.stripPrefix(_).indexOf(stripPrefix(_)) = 0 and
    va.getEnclosingFunction() = getEnclosingFunction()
  }

  string stripPrefix(string prefix) {
    exists(string id |
      id = toId() and
      prefix = getAInternalPrefix() and
      id.indexOf(prefix) = 0 and
      result = id.substring(prefix.length(), id.length())
    )
  }

  // checks the prefixes (but not the rest)
  predicate prefixEquals(TerminalVariableAccess va) {
    exists(string idA, string idB, string prefixA, string prefixB |
      idA = stripPrefix(prefixA) and
      idB = va.stripPrefix(prefixB) and
      prefixA = prefixB
    )
  }
}

// POST translation, produces the set of references which
// use the given expr as a basis for deriving their value
TerminalVariableAccess getAPrefixedVariableReferenceForExpr(Expr exp) {
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

TerminalVariableAccess getLastVariableReferenceInContext(TerminalVariableAccess template) {
  exists(TerminalVariableAccess candidate |
    // they are in the same function
    candidate.getEnclosingFunction() = template.getEnclosingFunction() and
    // they share the same id
    candidate.toId() = template.toId() and
    // and there is no other that comes AFTER this
    result = candidate and
    not exists(TerminalVariableAccess mid |
      mid.getEnclosingFunction() = candidate.getEnclosingFunction() and
      mid.toId() = template.toId() and
      candidate.getASuccessor*() = mid
    )
  )
}

predicate isLastVariableReferenceInContext(TerminalVariableAccess candidate) {
  // this holds if there is NOT a successor that is not equal to this id
  not exists(TerminalVariableAccess mid |
    not mid = candidate and
    mid.getEnclosingFunction() = candidate.getEnclosingFunction() and
    mid.toId() = candidate.toId() and
    candidate.getASuccessor*() = mid
  )
}

private string getTypePrefix(VariableAccess va) {
  // this case handles the case where we don't actually know the type
  not exists(z3SortForQlType(va)) and
  exists(Z3::Sort t |
    t instanceof Z3::OpaqueValueSort and
    getPrefixForType(t) = result
  )
  or
  result = getPrefixForType(z3SortForQlType(va))
}

string getAInternalPrefix() { result = "_referenceType__" or result = "_valueType__" }

string getPrefixForType(Z3::Sort sort) {
  if sort = Z3::TOptionNullSort() then result = "_referenceType__" else result = "_valueType__"
}

string implicitExprToZ3(TerminalVariableAccess va) {
  exists(Z3::Sort s |
    s = z3SortForQlType(va.getTarget().getType(), va) and
    (
      // a:int -> (not (= a 0))
      s instanceof Z3::IntSort and result = "(not (= " + va.toId() + " 0))"
      or
      // a:bool -> (not (= a false))
      s instanceof Z3::BoolSort and
      result = "(not (= " + va.toId() + " " + any(Z3::FalseBoolLiteral a) + "))"
      or
      // a:ptr  -> (not (= a MaybeNull))
      s instanceof Z3::OptionNullSort and
      result = "(not (=  " + va.toId() + " " + any(Z3::MaybeNullOptionNullSortLiteral a) + "))"
    )
  )
}

predicate isPointerAccess(VariableAccess va) {
  exists(Z3::Sort s |
    s = z3SortForQlType(va.getTarget().getType(), va) and
    s instanceof Z3::OptionNullSort
  )
}

string logicalOperationToZ3Function(BinaryLogicalOperation blo) {
  blo instanceof LogicalAndExpr and result = "and"
  or
  blo instanceof LogicalOrExpr and result = "or"
}

// Care must be taken when translating binary logical operations.
// Namely, implicitly it is possible to model a null test by
// accessing a variable that is a pointer -- which should be
// translated to a null pointer check. This also applies to checks
// for truthiness of a variable that is an integer.
string logicalExprToZ3(BinaryLogicalOperation blo) {
  exists(string op, string lhs, string rhs |
    // get the operation
    op = logicalOperationToZ3Function(blo) and
    (
      (
        lhs = implicitExprToZ3(blo.getLeftOperand())
        or
        // don't allow this translation for operands that are just varaible accesses
        lhs = explicitExprToZ3(blo.getLeftOperand()) and
        not blo.getLeftOperand() instanceof VariableAccess
      ) and
      (
        rhs = implicitExprToZ3(blo.getRightOperand())
        or
        // don't allow this translation for operands that are just varaible accesses
        rhs = explicitExprToZ3(blo.getRightOperand()) and
        not blo.getRightOperand() instanceof VariableAccess
      )
    ) and
    result = "(" + op + " " + lhs + " " + rhs + ")"
  )
}

string equalityOperationToZ3(EqualityOperation eo) {
  exists(Expr lexp, Expr rexp, string lhs, string rhs |
    lexp = eo.getLeftOperand() and
    rexp = eo.getRightOperand() and
    (
      if isPointerAccess(lexp) and rexp.(Literal).getValue() = "0"
      then
        lhs = explicitExprToZ3(lexp) and
        rhs = any(Z3::MaybeNullOptionNullSortLiteral a).toString()
      else
        if isPointerAccess(rexp) and lexp.(Literal).getValue() = "0"
        then (
          lhs = any(Z3::MaybeNullOptionNullSortLiteral a).toString() and
          rhs = explicitExprToZ3(rexp)
        ) else (
          lhs = explicitExprToZ3(eo.getLeftOperand()) and
          rhs = explicitExprToZ3(eo.getRightOperand())
        )
    ) and
    (
      eo instanceof NEExpr and result = "(not (= " + lhs + " " + rhs + "))"
      or
      eo instanceof EQExpr and result = "(= " + lhs + " " + rhs + ")"
    )
  )
}

string exprToZ3(Expr exp) {
  // if the top level expression is a variable access
  // we do not descend into the expression and instead
  // perform the implicit translation immediately.
  if exp instanceof VariableAccess
  then result = implicitExprToZ3(exp)
  else result = explicitExprToZ3(exp)
}

string explicitExprToZ3(Expr exp) {
  exp.(GEExpr) = exp and
  result =
    "(>= " + explicitExprToZ3(exp.(BinaryOperation).getLeftOperand()) +
      explicitExprToZ3(exp.(BinaryOperation).getRightOperand()) + ") "
  or
  exp.(GTExpr) = exp and
  result =
    "(> " + explicitExprToZ3(exp.(BinaryOperation).getLeftOperand()) +
      explicitExprToZ3(exp.(BinaryOperation).getRightOperand()) + ") "
  or
  exp.(LEExpr) = exp and
  result =
    "(<= " + explicitExprToZ3(exp.(BinaryOperation).getLeftOperand()) +
      explicitExprToZ3(exp.(BinaryOperation).getRightOperand()) + ") "
  or
  exp.(LTExpr) = exp and
  result =
    "(< " + explicitExprToZ3(exp.(BinaryOperation).getLeftOperand()) +
      explicitExprToZ3(exp.(BinaryOperation).getRightOperand()) + ") "
  or
  exp.(AddExpr) = exp and
  result =
    "(+ " + explicitExprToZ3(exp.(BinaryOperation).getLeftOperand()) +
      explicitExprToZ3(exp.(BinaryOperation).getRightOperand()) + ") "
  or
  exp.(SubExpr) = exp and
  result =
    "(- " + explicitExprToZ3(exp.(BinaryOperation).getLeftOperand()) +
      explicitExprToZ3(exp.(BinaryOperation).getRightOperand()) + ") "
  or
  exp.(MulExpr) = exp and
  result =
    "(* " + explicitExprToZ3(exp.(BinaryOperation).getLeftOperand()) +
      explicitExprToZ3(exp.(BinaryOperation).getRightOperand()) + ") "
  or
  exp.(DivExpr) = exp and
  result =
    "(/ " + explicitExprToZ3(exp.(BinaryOperation).getLeftOperand()) +
      explicitExprToZ3(exp.(BinaryOperation).getRightOperand()) + ") "
  or
  exp.(EqualityOperation) = exp and result = equalityOperationToZ3(exp)
  or
  // Uncomment for debugging
  // exp.(BinaryOperation) = exp and result =  preconditionToZ3(exp.(BinaryOperation).getLeftOperand()) + preconditionToZ3(exp.(BinaryOperation).getRightOperand())   or
  exp.(ConditionalExpr) = exp and result = explicitExprToZ3(exp.(ConditionalExpr).getCondition())
  or
  // TODO: need to support negation
  // here we have to differentiate between cases
  // where the LHS or RHS itself is just a variable access.
  //BinaryLogicalOperation //ConditionalExpr
  exp.(NotExpr) = exp and result = "(not " + exprToZ3(exp.(NotExpr).getOperand()) + ")"
  or
  exp.(BinaryLogicalOperation) = exp and result = logicalExprToZ3(exp)
  or
  exists(VariableAccess v |
    v = exp.(VariableAccess) and
    result = " " + v.(TerminalVariableAccess).toId() + " "
  )
  or
  exp = exp.(Literal) and result = " " + exp.(Literal).getValue() + " "
}
