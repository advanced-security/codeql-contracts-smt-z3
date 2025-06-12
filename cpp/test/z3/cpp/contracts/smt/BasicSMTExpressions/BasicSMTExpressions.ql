/**
 * @id cpp/test/SMT/Identifiers
 * @name Identifiers
 * @description Checks how identifiers are encoded in SMT.
 */

import cpp
import z3.cpp.contracts.SpecificationCase
import z3.cpp.contracts.SMT
import z3.cpp.contracts.style.AnnotatedCAssertStyleSpecifiedElement

from CodeQLSpecificationCase specCase, Expr pc, string pcBody
where
  exists(CodeQLSpecificationClauseRequires requires |
    requires = specCase.getASpecificationClause() and
    pc = requires.getClauseExpr() and
    pcBody = Contracts::assertPreconditionBody(requires)
  )
select specCase, pc, pcBody
