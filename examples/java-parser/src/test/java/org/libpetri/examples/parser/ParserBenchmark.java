package org.libpetri.examples.parser;

import com.sun.source.util.JavacTask;
import org.libpetri.core.Token;
import org.libpetri.examples.parser.compiler.ParseState;
import org.libpetri.examples.parser.lexer.JavaLexer;
import org.libpetri.runtime.NetExecutor;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.OptionsBuilder;

import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.SimpleJavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.ToolProvider;
import java.io.IOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.concurrent.TimeUnit;

/**
 * JMH benchmark comparing the Petri net parser against the JDK javac parser.
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
@Warmup(iterations = 3, time = 2)
@Measurement(iterations = 5, time = 2)
@Fork(1)
public class ParserBenchmark {

    private PetriNetParser parser;
    private JavaCompiler javac;
    private StandardJavaFileManager fileManager;
    private JavaFileObject sourceFile;

    @Param({"simple", "withMethod", "realistic", "selfParse", "synthetic"})
    private String sourceKind;

    private String source;

    // For selfParse: all libpetri source files parsed individually
    private String[] selfParseSources;
    private JavaFileObject[] selfParseSourceFiles;

    private static final String SIMPLE_CLASS = "class Foo {}";

    private static final String CLASS_WITH_METHOD = """
            class Calculator {
                int add(int a, int b) {
                    return a + b;
                }
            }
            """;

    private static final String REALISTIC_FILE = """
            package com.example;

            import java.util.List;
            import java.util.ArrayList;

            public final class StringUtils {
                private static final int MAX_LENGTH = 1024;

                public static String capitalize(String input) {
                    if (input == null || input.isEmpty()) {
                        return input;
                    }
                    return input.substring(0, 1).toUpperCase() + input.substring(1);
                }

                public static List<String> split(String input, char delimiter) {
                    var result = new ArrayList<String>();
                    int start = 0;
                    for (int i = 0; i < input.length(); i++) {
                        if (input.charAt(i) == delimiter) {
                            result.add(input.substring(start, i));
                            start = i + 1;
                        }
                    }
                    result.add(input.substring(start));
                    return result;
                }

                public static boolean isPalindrome(String s) {
                    int left = 0;
                    int right = s.length() - 1;
                    while (left < right) {
                        if (s.charAt(left) != s.charAt(right)) {
                            return false;
                        }
                        left++;
                        right--;
                    }
                    return true;
                }
            }
            """;

    @Setup(Level.Trial)
    public void setup() {
        parser = PetriNetParser.forJava25();
        javac = ToolProvider.getSystemJavaCompiler();
        fileManager = javac.getStandardFileManager(null, null, null);
        if (sourceKind.equals("selfParse")) {
            selfParseSources = readLibpetriSources();
            selfParseSourceFiles = new JavaFileObject[selfParseSources.length];
            for (int i = 0; i < selfParseSources.length; i++) {
                final String src = selfParseSources[i];
                selfParseSourceFiles[i] = new SimpleJavaFileObject(
                    URI.create("string:///File" + i + ".java"), JavaFileObject.Kind.SOURCE
                ) {
                    @Override public CharSequence getCharContent(boolean ignoreErrors) { return src; }
                };
            }
        } else {
            source = switch (sourceKind) {
                case "simple" -> SIMPLE_CLASS;
                case "withMethod" -> CLASS_WITH_METHOD;
                case "realistic" -> REALISTIC_FILE;
                case "synthetic" -> SyntheticJavaSource.generateForBenchmark();
                default -> throw new IllegalArgumentException("Unknown source kind: " + sourceKind);
            };
            sourceFile = new SimpleJavaFileObject(
                URI.create("string:///Test.java"), JavaFileObject.Kind.SOURCE
            ) {
                @Override public CharSequence getCharContent(boolean ignoreErrors) { return source; }
            };
        }
    }

    @Benchmark
    public Object petriNetParse() {
        if (sourceKind.equals("selfParse")) {
            Object last = null;
            for (var src : selfParseSources) last = parser.parse(src);
            return last;
        }
        return parser.parse(source);
    }

    @Benchmark
    public Object netExecutorParse() {
        if (sourceKind.equals("selfParse")) {
            Object last = null;
            for (var src : selfParseSources) last = parseWithNetExecutor(src);
            return last;
        }
        return parseWithNetExecutor(source);
    }

    private Object parseWithNetExecutor(String src) {
        var tokens = JavaLexer.tokenize(src).toArray(org.libpetri.examples.parser.lexer.LexToken[]::new);
        var initialState = ParseState.initial(tokens);
        var compiledNet = parser.compiledNet();
        try (var executor = NetExecutor.create(
                compiledNet.net(),
                Map.of(compiledNet.startPlace(), List.of(new Token<>(initialState, ParseState.EPOCH))))) {
            return executor.run();
        }
    }

    @Benchmark
    public Object javacParse() throws Exception {
        if (sourceKind.equals("selfParse")) {
            var task = (JavacTask) javac.getTask(null, fileManager, null,
                List.of("--enable-preview", "--release", "25"), null, List.of(selfParseSourceFiles));
            return task.parse();
        }
        var task = (JavacTask) javac.getTask(null, fileManager, null,
            List.of("--enable-preview", "--release", "25"), null, List.of(sourceFile));
        return task.parse();
    }


    private static String[] readLibpetriSources() {
        try {
            var root = Path.of("../../java/src/main/java/org/libpetri");
            try (var stream = Files.walk(root)) {
                return stream.filter(p -> p.toString().endsWith(".java"))
                    .filter(p -> !p.toString().endsWith("package-info.java"))
                    .sorted()
                    .map(p -> {
                        try { return Files.readString(p); }
                        catch (IOException e) { throw new RuntimeException(e); }
                    })
                    .toArray(String[]::new);
            }
        } catch (IOException e) {
            throw new RuntimeException("Cannot read libpetri sources", e);
        }
    }

    public static void main(String[] args) throws RunnerException {
        var opt = new OptionsBuilder()
            .include(ParserBenchmark.class.getSimpleName())
            .build();
        new Runner(opt).run();
    }
}
