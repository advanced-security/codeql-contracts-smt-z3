package com.github.codeql.z3;

import com.microsoft.z3.Context;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

public class Z3Plugin {
    public String codeQlPluginEntryPoint(String input) {
        try(
            Context ctx = new Context()) {
            Solver s = ctx.mkSolver();
            s.fromString(input);
            if (s.check() == Status.SATISFIABLE) {
                Model m = s.getModel();
                return m.toString();
            } else {
                return "UNSAT";
            }
        }
    }
}
