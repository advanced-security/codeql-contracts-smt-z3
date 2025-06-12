/**
 * @id cpp/test/SMT/CallSiteNullityToSMT
 * @name CallSiteNullityToSMT
 * @description Detects nullity at callsites.
 * @kind problem
 * @precision high
 * @problem.severity warning
 */

import cpp
import z3.cpp.contracts.SpecificationCase
import z3.cpp.contracts.SMT
import z3.cpp.contracts.style.AnnotatedCAssertStyleSpecifiedElement

// Tests the `getBounds` functionality for each parameter at the call site
// for contract annotated functions
from FunctionCall fc, CodeQLSpecificationCase specCase, string boundary
where
  forall(CodeQLSpecificationClauseRequires requires, Expr pc |
    requires = specCase.getASpecificationClause() and
    pc = requires.getClauseExpr()
  |
    isSupported(pc)
  ) and
  fc.getTarget() = specCase.getFunction() and
  boundary = Contracts::getBounds(specCase, fc)
select fc, boundary
