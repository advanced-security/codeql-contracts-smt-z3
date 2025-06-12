/**
 * @id cpp/test/SMT/DetectNulls
 * @name DetectsNulls
 * @description Detects nullity 
 * @kind problem
 * @precision high
 * @problem.severity warning
 */

import cpp
import z3.cpp.contracts.SpecificationCase
import z3.cpp.contracts.SMT
import z3.cpp.contracts.style.AnnotatedCAssertStyleSpecifiedElement

// Tests to see if an expression should be considered to be null. 
from CodeQLSpecificationClauseRequires requires, Expr e, VariableAccess va
  where 
      e = requires.getClauseExpr() and 
      isSupported(e) and
      va.getParent*() = e 
      and possiblyNull(va)
select requires, "Within contract $@ is possibly null", va, "this variable"  
  