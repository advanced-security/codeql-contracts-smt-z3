import cpp
import z3.cpp.contracts.SpecificationCase

/**
 * Describes a C-style assert that has been annotated with a comment indicating
 * it should be treated as a contract specification.
 *
 * For example:
 *
 * ```
 *   /*@ requires @* /
 *   assert(x > 0);
 * ```
 */
class AnnotatedCAssertStyleSpecifiedElement extends SpecifiedElement, MacroInvocation {
  Expr body;
  string keyword;
  string contents;
  Comment exprComment;

  AnnotatedCAssertStyleSpecifiedElement() {
    // model the LHS of a logical or style CAssert
    exists(LogicalOrExpr b |
      body = b.getLeftOperand() and
      b = this.getAGeneratedElement() and
      not exists(LogicalOrExpr e1 |
        not e1 = b and
        b.getParent*() = e1
      )
    ) and
    exprComment.getCommentedElement() = this.getExpr().getEnclosingStmt() and
    (
      // Find comments such as '/*@ requires @*/' or '/*@ ensures @*/'.
      contents =
        exprComment
            .getContents()
            .splitAt("\n")
            .regexpFind("^\\s*\\/\\*@\\s+requires\\s+@\\*\\/$", _, _) and
      keyword = "requires"
      or
      contents =
        exprComment
            .getContents()
            .splitAt("\n")
            .regexpFind("^\\s*\\/\\*@\\s+ensures\\s+@\\*\\/$", _, _) and
      keyword = "ensures"
      or
      contents =
        exprComment
            .getContents()
            .splitAt("\n")
            .regexpFind("^\\s*\\/\\*@\\s+assume\\s+@\\*\\/$", _, _) and
      keyword = "assume"
    )
  }

  override string getSource() { getBody().toString() = result }

  override Expr getBody() { result = body }

  override Function getFunction() { result = getBody().getEnclosingFunction() }

  override predicate hasLocationInfo(
    string filepath, int startline, int startcolumn, int endline, int endcolumn
  ) {
    // for a comment based assert specification the location is essentially
    // the start of the comment to the end of the assert.
    exprComment.getLocation().hasLocationInfo(filepath, startline, startcolumn, _, _) and
    this.(LibcAssert).getLocation().hasLocationInfo(_, _, _, endline, endcolumn)
  }

  string getContents() { result = contents }

  override string getKeyword() { result = keyword }
}
