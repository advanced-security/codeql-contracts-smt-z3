module Z3 {
  /**
   * Basic type modeling for Z3
   */
  newtype TSort =
    TIntSort() or
    TBoolSort() or
    TOptionNullSort() or
    TOpaqueValueSort()

  newtype TLiteral =
    TIntSortLiteral() or
    TFalseBoolSortLiteral() or
    TTrueBoolSortLiteral() or
    TMaybeNullOptionNullSortLiteral() or
    TNotNullOptionNullSortLiteral()

  class Sort extends TSort {
    abstract string toString();
  }

  class IntSort extends Sort, TIntSort {
    override string toString() { result = "Int" }
  }

  class BoolSort extends Sort, TBoolSort {
    override string toString() { result = "Bool" }
  }

  class OptionNullSort extends Sort, TOptionNullSort {
    override string toString() { result = "OptionNullSort" }
  }

  class OpaqueValueSort extends Sort, TOpaqueValueSort {
    override string toString() { result = "OpaqueValueSort" }
  }

  class Literal extends TLiteral {
    string toString() {
      result = this.getValue()
      or
      not exists(this.getValue()) and
      result = "Unknown literal"
    }

    abstract string getValue();
  }

  class TrueBoolLiteral extends Literal, TTrueBoolSortLiteral {
    TrueBoolLiteral() { this = TTrueBoolSortLiteral() }

    override string getValue() { result = "true" }
  }

  class FalseBoolLiteral extends Literal, TFalseBoolSortLiteral {
    FalseBoolLiteral() { this = TFalseBoolSortLiteral() }

    override string getValue() { result = "false" }
  }

  class MaybeNullOptionNullSortLiteral extends Literal, TMaybeNullOptionNullSortLiteral {
    MaybeNullOptionNullSortLiteral() { this = TMaybeNullOptionNullSortLiteral() }

    override string getValue() { result = "MaybeNull" }
  }

  class NotNullOptionNullSortLiteral extends Literal, TNotNullOptionNullSortLiteral {
    NotNullOptionNullSortLiteral() { this = TNotNullOptionNullSortLiteral() }

    override string getValue() { result = "NotNull" }
  }

  private string unsatisfiedOutput() { result = "UNSAT" }

  bindingset[spec]
  private string invokePlugin(string spec) {
    result = QlBuiltins::invokePlugin("z3-plugin.jar:com.github.codeql.z3.Z3Plugin", spec)
  }

  bindingset[spec]
  predicate checkSatisfied(string spec) {
    not invokePlugin(spec) = unsatisfiedOutput()
  }

  bindingset[spec]
  string getModel(string spec) {
    result = invokePlugin(spec) and
    not result = unsatisfiedOutput()
  }


}
