package com.github.codeql.z3;

import com.github.codeql.z3.Z3Plugin;

public class Test {
    public static void main(String[] args) {
        Z3Plugin plugin = new Z3Plugin();
        String input = "(declare-fun x () Int)\n" +
                       "(declare-fun y () Int)\n" +
                       "(assert (> x y))\n" +
                       "(check-sat)\n" +
                       "(get-model)";
        String result = plugin.codeQlPluginEntryPoint(input);
        System.out.println(result);
    }
}