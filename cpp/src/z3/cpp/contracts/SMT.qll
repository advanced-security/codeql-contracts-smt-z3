import z3.cpp.contracts.SpecificationCase
import semmle.code.cpp.rangeanalysis.SimpleRangeAnalysis

module Contracts {
  bindingset[exp, lb, ub]
  private string boundsToAssert(string exp, float lb, float ub) {
    result = upperBoundsToAssert(exp, ub) + "\n" + lowerBoundsToAssert(exp, lb) + "\n"
  }

  bindingset[exp, ub]
  private string upperBoundsToAssert(string exp, float ub) {
    result = "(assert (<= " + exp + " " + ub + ")) ; establishment of upper bounds"
  }

  bindingset[exp, lb]
  private string lowerBoundsToAssert(string exp, float lb) {
    result = "(assert (>= " + exp + " " + lb + ")) ; establishment of lower bounds"
  }

  bindingset[exp, categoricalValue]
  private string categoricalValueToAssert(string exp, string categoricalValue) {
    result = "(assert (= " + exp + " " + categoricalValue + ")) ; establishment categorical value"
  }

  /**
   * This predicate works differently than the way that preconditions are constructed.
   * In the case of preconditions the scope is limited to the precondition's scope.
   * The constants and declarations however are exposed at the script level. For
   * this reason we must de-duplicate the declarations.
   *
   * There are two types of declarations we include. Those that are directly needed
   * in the scope of the contract and those that are needed in the body of the
   * callsite.
   */
  string extractDeclarations(CodeQLSpecificationCase specCase, FunctionCall fc) {
    // handles the declarations inside of the specified method, including
    // the ones stored in the spec database.
    specCase.getASpecificationClause().getSMTDeclarations() = result
    or
    // handles the declarations possibly needed by injecting scoped
    // variables
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
      result = "(declare-const " + id + " " + z3Sort.toString() + ")"
    )
  }

  string concatDeclarations(CodeQLSpecificationCase specCase, FunctionCall fc) {
    fc.getTarget() = specCase.getFunction() and
    result = concat(string s | s = extractDeclarations(specCase, fc) | s + "\n")
  }

  string assertPreconditionBody(CodeQLSpecificationClause clause) {
    result = concat(CodeQLSpecificationClause c | c = clause | (c.getSMTAsserts() + "\n"))
  }

  string getPrecondition(CodeQLSpecificationCase specCase) {
    exists(int preconditionNumber, string pcBody |
      pcBody =
        rank[preconditionNumber](string pc |
          pc = assertPreconditionBody(specCase.getASpecificationClause())
        |
          pc
        ) and
      result =
        "(define-fun precondition_" + preconditionNumber.toString() + "() Bool \n\t" + pcBody +
          ")\n\n"
    )
  }

  string concatPreconditions(CodeQLSpecificationCase specCase) {
    result = concat(getPrecondition(specCase) + "\n")
  }

  /**
   * Boundary analysis is done on a per argument basis to the function call.
   * We do this by mapping the formal parameter names in SMT to the values
   * produced by range analysis at the call site for its actual parameters.
   */
  string getBounds(CodeQLSpecificationCase specCase, FunctionCall fc) {
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
      // it isn't necessary to break up these cases --
      // we could just take a disjunction but this is presented
      // this way for clarity that we are taking different approaches
      // to value analysis.
      if z3Sort = Z3::TOptionNullSort()
      then
        exists(string categoricalValue |
          bfc.getACategoricalValue(valueExpr, anchorExpr, p) = categoricalValue and
          result = categoricalValueToAssert(id, categoricalValue)
        )
      else
        exists(float lb, float ub |
          bfc.getALowerBound(valueExpr.getParent*(), anchorExpr, p) = lb and
          ub = bfc.getAUpperBound(valueExpr.getParent*(), anchorExpr, p) and
          result = boundsToAssert(id, lb, ub)
        )
    )
  }

  string concatBounds(CodeQLSpecificationCase specCase, FunctionCall fc) {
    fc.getTarget() = specCase.getFunction() and
    result = concat(string s | s = getBounds(specCase, fc) | s + "\n")
  }

  /**
   * The goal of contract checking is not to find an assignment of variables
   * that allows a formula to be true; the goal is to find an assignment wherein
   * the formula is false. Therefore to make this work with a SAT solver
   * (which finds assignments that make a formula true) we use it in reverse
   * and ask the solver for a cases wherein the solver searches for an
   * assignment to an invalid form of the formula.
   *
   * Stated more concisely, for a formula $F$ over variables $V$ a counter
   * example is an assignment of variables $V$ for which $\neg F$ is satisfiable.
   */
  string getCounterExamples(CodeQLSpecificationCase specCase) {
    exists(string preconditionList, int numberOfPreconditions |
      // note -- we translate to the precondition body here because it is
      // possible to have duplicate preconditions. These are automatically
      // filtered out by set equality so to replicate that behavior here,
      // the conversion via `assertPreconditionBody` ensures that the
      // deduplication takes place.
      numberOfPreconditions = count(assertPreconditionBody(specCase.getASpecificationClause())) and
      preconditionList =
        concat(int idx | idx = [1 .. numberOfPreconditions] | "precondition_" + idx.toString() + " ")
            .trim() and
      if numberOfPreconditions = 1
      then result = "(assert (not " + preconditionList + "))"
      else result = "(assert (not (and " + preconditionList + ")))"
    )
  }

  string toSMT(CodeQLSpecificationCase specCase, FunctionCall fc) {
    // scope this down to a single function
    fc.getTarget() = specCase.getFunction() and
    // do the boundary analysis
    result =
      "                     \n" + ";;                            \n" +
        ";; Declarations               \n" +
        "(declare-datatypes () ((OptionNullSort MaybeNull NotNull)))\n\n" +
        concatDeclarations(specCase, fc) + ";;                            \n" +
        ";; Precondition Definition    \n" + concatPreconditions(specCase) +
        ";;                            \n" + ";; Boundary/Context Assertions\n" +
        concatBounds(specCase, fc) + ";;                            \n" +
        ";; Counter Example Assertion  \n" + getCounterExamples(specCase)
  }
}
