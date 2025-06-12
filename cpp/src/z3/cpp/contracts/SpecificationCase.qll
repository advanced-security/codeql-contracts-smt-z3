/**
 * A Specification consists of specification cases which in turn consist of
 * specification clauses.
 */

import cpp
import semmle.code.cpp.commons.Assertions
import z3.cpp.Translation

/**
 * A `SpecifiedElement` is an actual program level element that either
 * concretely or synthetically is attached to a specification element.
 *
 * In the case of embedded specifications, they are always attached to the
 * `Function` in which they reside. In the case of others, e.g., macro level
 * assertions, they are attached to the macro. It is important to be careful
 * about this point. We define the rest of our elements so that a single
 * program element can have one or more specification elements attached; this is
 * necessary to be consistent between embedded and non-embedded specifications.
 */
abstract class SpecifiedElement extends Element {
  abstract Expr getBody();

  abstract Function getFunction();

  abstract string getKeyword();

  abstract string getSource();

  abstract predicate hasLocationInfo(
    string filepath, int startline, int startcolumn, int endline, int endcolumn
  );

  // it's worth noting that this is modeled as string mainly because
  // of embedded specifications. The embedded specifications make it hard
  // to store the abstract representations. See `SMT.qll` for some abstract
  // classes for working with SMT expressions.
  string getSMTDeclarations() { result = declarationsForExpr(getBody()) }

  string getSMTAsserts() { result = exprToZ3(getBody()) }
}

/** A SpecificationClause may be one of a set of types of SpecificationClauses. */
private newtype TCodeQLSpecificationClauseType =
  TCodeQLSpecificationClauseRequires(SpecifiedElement e) { e.getKeyword() = "requires" } or
  TCodeQLSpecificationClauseEnsures(SpecifiedElement e) { e.getKeyword() = "ensures" } or
  TCodeQLSpecificationClauseSignals(SpecifiedElement e) { e.getKeyword() = "signals" } or
  TCodeQLSpecificationClauseSignalsOnly(SpecifiedElement e) { e.getKeyword() = "signals_only" } or
  TCodeQLSpecificationClauseWhen(SpecifiedElement e) { e.getKeyword() = "when" } or
  TCodeQLSpecificationClauseAssignable(SpecifiedElement e) { e.getKeyword() = "assignable" } or
  TCodeQLSpecificationClauseCallable(SpecifiedElement e) { e.getKeyword() = "callable" }

/**
 * A SpecificationCase may consist of either a set of SpecificationClauses or a
 * SpecificationCase.
 */
private newtype TCodeQLSpecificationCaseType =
  TCodeQLSingleSpecificationCase(Function f) { exists(SpecifiedElement e | e.getFunction() = f) } or
  TCodeQLEmptySpecificationCase()

abstract class CodeQLSpecificationCase extends TCodeQLSpecificationCaseType {
  Function f;

  abstract CodeQLSpecificationClause getASpecificationClause();

  string toString() { result = "specification of " + f.getName() }

  Function getFunction() { result = f }

  predicate hasLocationInfo(
    string filepath, int startline, int startcolumn, int endline, int endcolumn
  ) {
    f.getLocation().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
  }
}

class CodeQLSingleSpecificationCase extends CodeQLSpecificationCase, TCodeQLSingleSpecificationCase {
  CodeQLSingleSpecificationCase() { this = TCodeQLSingleSpecificationCase(f) }

  override CodeQLSpecificationClause getASpecificationClause() {
    exists(CodeQLSpecificationClause c |
      c.getFunction() = f and
      result = c
    )
  }
}

abstract class CodeQLSpecificationClause extends TCodeQLSpecificationClauseType {
  Function function;
  SpecifiedElement e;

  string toString() { result = getKeyword() + " " + e.getSource() }

  Function getFunction() { result = function }

  Expr getClauseExpr() { result = e.getBody() }

  string getSMTDeclarations() { result = e.getSMTDeclarations() }

  string getSMTAsserts() { result = e.getSMTAsserts() }

  predicate hasLocationInfo(
    string filepath, int startline, int startcolumn, int endline, int endcolumn
  ) {
    e.hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
  }

  string getKeyword() { result = e.getKeyword() }
}

class CodeQLSpecificationClauseRequires extends CodeQLSpecificationClause,
  TCodeQLSpecificationClauseRequires
{
  CodeQLSpecificationClauseRequires() {
    this = TCodeQLSpecificationClauseRequires(e) and
    function = e.getFunction()
  }
}

class CodeQLSpecificationClauseEnsures extends CodeQLSpecificationClause,
  TCodeQLSpecificationClauseEnsures
{
  CodeQLSpecificationClauseEnsures() {
    this = TCodeQLSpecificationClauseEnsures(e) and
    function = e.getFunction()
  }
}

class CodeQLSpecificationClauseSignals extends CodeQLSpecificationClause,
  TCodeQLSpecificationClauseSignals
{
  CodeQLSpecificationClauseSignals() {
    this = TCodeQLSpecificationClauseSignals(e) and
    function = e.getFunction()
  }
}

class CodeQLSpecificationClauseSignalsOnly extends CodeQLSpecificationClause,
  TCodeQLSpecificationClauseSignalsOnly
{
  CodeQLSpecificationClauseSignalsOnly() {
    this = TCodeQLSpecificationClauseSignalsOnly(e) and
    function = e.getFunction()
  }
}

class CodeQLSpecificationClauseWhen extends CodeQLSpecificationClause,
  TCodeQLSpecificationClauseWhen
{
  CodeQLSpecificationClauseWhen() {
    this = TCodeQLSpecificationClauseWhen(e) and
    function = e.getFunction()
  }
}

class CodeQLSpecificationClauseAssignable extends CodeQLSpecificationClause,
  TCodeQLSpecificationClauseAssignable
{
  CodeQLSpecificationClauseAssignable() {
    this = TCodeQLSpecificationClauseAssignable(e) and
    function = e.getFunction()
  }
}

class CodeQLSpecificationClauseCallable extends CodeQLSpecificationClause,
  TCodeQLSpecificationClauseCallable
{
  CodeQLSpecificationClauseCallable() {
    this = TCodeQLSpecificationClauseCallable(e) and
    function = e.getFunction()
  }
}

private newtype TCodeQLSpecificationStmtType =
  TCodeQLSpecificationStmtAssume(SpecifiedElement e) { e.getKeyword() = "assume" }

abstract class CodeQLSpecificationStmt extends TCodeQLSpecificationStmtType {
  Function function;
  SpecifiedElement e;

  string toString() { result = getKeyword() + " " + e.getSource() }

  Function getFunction() { result = function }

  Expr getExpr() { result = e.getBody() }

  string getSMTDeclarations() { result = e.getSMTDeclarations() }

  string getSMTAsserts() { result = e.getSMTAsserts() }

  predicate hasLocationInfo(
    string filepath, int startline, int startcolumn, int endline, int endcolumn
  ) {
    e.hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
  }

  string getKeyword() { result = e.getKeyword() }
}

class CodeQLSpecificationStmtAssume extends CodeQLSpecificationStmt, TCodeQLSpecificationStmtAssume {
  CodeQLSpecificationStmtAssume() {
    this = TCodeQLSpecificationStmtAssume(e) and
    function = e.getFunction()
  }
}
