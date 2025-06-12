import z3.Z3

from string spec
where spec =
  "(declare-const x Int)\n" +
  "(declare-const y Int)\n" +
  "(assert (= x y))\n" +
  "(check-sat)\n" +
  "(get-model)\n"
select Z3::getModel(spec)