import cpp
import z3.cpp.contracts.SpecificationCase
import z3.cpp.contracts.style.AnnotatedCAssertStyleSpecifiedElement

// Checks option types -- also tests our supported mechanism.
from CodeQLSpecificationClauseRequires requires, Expr e, string decl
where
  e = requires.getClauseExpr() and
  isSupported(e) and
  decl = declarationsForExpr(e)
select requires, e, decl
