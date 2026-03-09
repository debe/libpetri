package org.libpetri.examples.parser;

/**
 * Generates valid Java source strings for stress testing and benchmarking.
 */
final class SyntheticJavaSource {

    private SyntheticJavaSource() {}

    /**
     * Generate a Java source file with the given number of classes and methods per class.
     */
    static String generate(int classCount, int methodsPerClass) {
        var sb = new StringBuilder();
        sb.append("package com.example.generated;\n\n");
        sb.append("import java.util.List;\n");
        sb.append("import java.util.ArrayList;\n");
        sb.append("import java.util.Map;\n\n");

        for (int c = 0; c < classCount; c++) {
            String className = "GeneratedClass" + c;
            sb.append("class ").append(className).append(" {\n\n");

            // Fields
            sb.append("    private int count;\n");
            sb.append("    private String name;\n");
            sb.append("    private List<String> items;\n\n");

            // Constructor
            sb.append("    ").append(className).append("(int count, String name) {\n");
            sb.append("        this.count = count;\n");
            sb.append("        this.name = name;\n");
            sb.append("        this.items = new ArrayList<String>();\n");
            sb.append("    }\n\n");

            // Methods
            for (int m = 0; m < methodsPerClass; m++) {
                generateMethod(sb, m);
            }

            // Nested record
            sb.append("    record Info").append(c).append("(String key, int value) {\n");
            sb.append("        boolean isValid() {\n");
            sb.append("            return key != null && value >= 0;\n");
            sb.append("        }\n");
            sb.append("    }\n\n");

            // Nested enum
            sb.append("    enum Status").append(c).append(" {\n");
            sb.append("        ACTIVE, INACTIVE, PENDING;\n\n");
            sb.append("        boolean isTerminal() {\n");
            sb.append("            return this == INACTIVE;\n");
            sb.append("        }\n");
            sb.append("    }\n\n");

            sb.append("}\n\n");
        }

        return sb.toString();
    }

    private static void generateMethod(StringBuilder sb, int index) {
        sb.append("    String process").append(index).append("(int input) {\n");
        sb.append("        var result = new ArrayList<String>();\n");
        sb.append("        if (input > 0) {\n");
        sb.append("            for (int i = 0; i < input; i++) {\n");
        sb.append("                result.add(String.valueOf(i));\n");
        sb.append("            }\n");
        sb.append("        } else {\n");
        sb.append("            result.add(\"none\");\n");
        sb.append("        }\n");
        sb.append("        int total = result.size();\n");
        sb.append("        String label = \"method_").append(index).append("_\" + total;\n");
        sb.append("        return label;\n");
        sb.append("    }\n\n");
    }

    /** ~5K lines for benchmarking. */
    static String generateForBenchmark() {
        return generate(3, 10);
    }

    /** ~100K lines for stress testing. */
    static String generateForStressTest() {
        return generate(200, 40);
    }
}
