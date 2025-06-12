import cpp
import z3.cpp.contracts.SpecificationCase
import z3.cpp.contracts.style.AnnotatedCAssertStyleSpecifiedElement

from CodeQLSpecificationClauseRequires requires, Expr e, string smt
where
  e = requires.getClauseExpr() and
  isSupported(e) and
  smt = exprToZ3(e)
select requires, e, smt
