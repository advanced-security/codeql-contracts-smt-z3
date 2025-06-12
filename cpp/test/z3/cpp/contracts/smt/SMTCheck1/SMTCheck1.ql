/**
 * @id cpp/test/SMT/SMTCheck1
 * @name SMT Check 1
 * @description Level 1 SMT Checks
 * @kind problem
 * @precision high
 * @problem.severity warning
 */

import cpp
import z3.cpp.contracts.SpecificationCase
import z3.cpp.contracts.SMT
import z3.cpp.contracts.style.AnnotatedCAssertStyleSpecifiedElement
import z3.Z3

from FunctionCall fc, CodeQLSpecificationCase specCase, string proof, string ce
where
  specCase.getFunction() = fc.getTarget() and
  proof = Contracts::toSMT(specCase, fc) and
  ce = Z3::getModel(proof)
select fc,
  "The $@ at guarding this function call may not be satisfied by this implementation. The SMT Solver found the following model which violates this method's precondition: \n\n"
    + ce, specCase, "specification case"
