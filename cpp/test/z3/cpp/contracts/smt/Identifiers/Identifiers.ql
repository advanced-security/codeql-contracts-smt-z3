/**
 * @id cpp/test/SMT/Identifiers
 * @name Identifiers
 * @description Checks how identifiers are encoded in SMT.
 * @kind problem
 * @precision high
 * @problem.severity warning
 */

import cpp
import z3.cpp.contracts.SpecificationCase
import z3.cpp.contracts.SMT
import z3.cpp.contracts.style.AnnotatedCAssertStyleSpecifiedElement

from CodeQLSpecificationClauseRequires requires, Expr e, string decl
where
  e = requires.getClauseExpr() and
  isSupported(e) and
  decl = declarationsForExpr(e)
select requires, e, decl
