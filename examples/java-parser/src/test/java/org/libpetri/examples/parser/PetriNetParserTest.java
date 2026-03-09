package org.libpetri.examples.parser;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.libpetri.examples.parser.ast.AstNode;
import org.libpetri.examples.parser.grammar.Java25Grammar;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Integration tests: parse real Java 25 source code through the Petri net parser.
 */
class PetriNetParserTest {

    static PetriNetParser parser;

    @BeforeAll
    static void compileGrammar() {
        parser = PetriNetParser.forJava25();
        System.out.println("Compiled grammar: " + parser.statistics());
    }

    @Test
    void parsesEmptyClass() {
        var result = parser.parse("class Foo {}");
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesClassWithField() {
        var result = parser.parse("class Foo { int x; }");
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesClassWithMethod() {
        var result = parser.parse("""
            class Calculator {
                int add(int a, int b) {
                    return a + b;
                }
            }
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesPublicClassWithModifiers() {
        var result = parser.parse("""
            public final class Config {
                private static final int MAX = 100;
            }
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesRecordDeclaration() {
        var result = parser.parse("record Point(double x, double y) {}");
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesRecordWithInterface() {
        var result = parser.parse("""
            record Circle(double radius) implements Shape {}
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesSealedInterface() {
        var result = parser.parse("""
            sealed interface Shape permits Circle, Rectangle {}
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesEnumDeclaration() {
        var result = parser.parse("""
            enum Color { RED, GREEN, BLUE }
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesIfElseStatement() {
        var result = parser.parse("""
            class Foo {
                void m() {
                    if (x > 0) {
                        return;
                    } else {
                        throw new RuntimeException();
                    }
                }
            }
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesSwitchExpression() {
        var result = parser.parse("""
            class Foo {
                String name(int x) {
                    return switch (x) {
                        case 1 -> "one";
                        case 2 -> "two";
                        default -> "other";
                    };
                }
            }
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesPatternMatching() {
        var result = parser.parse("""
            class Foo {
                void check(Object obj) {
                    if (obj instanceof String s) {
                        System.out.println(s);
                    }
                }
            }
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesLambdaExpression() {
        var result = parser.parse("""
            class Foo {
                void m() {
                    Runnable r = () -> { };
                }
            }
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesForLoop() {
        var result = parser.parse("""
            class Foo {
                void m() {
                    for (int i = 0; i < 10; i++) {
                        x = x + 1;
                    }
                }
            }
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesEnhancedForLoop() {
        var result = parser.parse("""
            class Foo {
                void m() {
                    for (var item : items) {
                        process(item);
                    }
                }
            }
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesTryCatch() {
        var result = parser.parse("""
            class Foo {
                void m() {
                    try {
                        doWork();
                    } catch (Exception e) {
                        handleError(e);
                    } finally {
                        cleanup();
                    }
                }
            }
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesImportStatements() {
        var result = parser.parse("""
            import java.util.List;
            import java.util.*;
            import static java.lang.Math.PI;

            class Foo {}
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesPackageDeclaration() {
        var result = parser.parse("""
            package com.example;

            class Foo {}
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesGenericTypes() {
        var result = parser.parse("""
            class Box<T extends Comparable<T>> {
                T value;
            }
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesAnnotations() {
        var result = parser.parse("""
            class Foo {
                @Override
                public String toString() {
                    return "Foo";
                }
            }
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesShowcaseCode() {
        // The showcase code from the plan — records, sealed, patterns, lambdas, switch
        var result = parser.parse("""
            sealed interface Shape permits Circle, Rectangle {}
            record Circle(double radius) implements Shape {}
            record Rectangle(double w, double h) implements Shape {}
            class Main {
                double area(Shape s) {
                    return switch (s) {
                        case Circle c -> Math.PI * c.radius() * c.radius();
                        case Rectangle r -> r.w() * r.h();
                    };
                }
            }
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesWhileLoop() {
        var result = parser.parse("""
            class Foo {
                void m() {
                    while (x > 0) {
                        x = x - 1;
                    }
                }
            }
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesArrayDeclaration() {
        var result = parser.parse("""
            class Foo {
                int[] arr;
            }
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesMultipleClassesInOneUnit() {
        var result = parser.parse("""
            class Foo {}
            class Bar {}
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void parsesVarDeclaration() {
        var result = parser.parse("""
            class Foo {
                void m() {
                    var x = 42;
                }
            }
            """);
        assertTrue(result.success(), errorMsg(result));
    }

    @Test
    void returnsErrorForInvalidSyntax() {
        var result = parser.parse("class { }");
        assertFalse(result.success(), "Should fail: class name missing");
        assertNotNull(result.errorMessage());
    }

    @Test
    void parseAllMultipleFiles() {
        var results = parser.parseAll(
            "class A {}",
            "class B { int x; }",
            "class C { void m() {} }"
        );
        assertEquals(3, results.size());
        for (int i = 0; i < results.size(); i++) {
            assertTrue(results.get(i).success(), "File " + i + ": " + errorMsg(results.get(i)));
        }
    }

    @Test
    void grammarHasExpectedProductionCount() {
        var grammar = Java25Grammar.create();
        assertTrue(grammar.productions().size() >= 100,
            "Expected >= 100 productions, got " + grammar.productions().size());
    }

    @Test
    void netHasSubstantialScale() {
        var compiled = parser.compiledNet();
        assertTrue(compiled.placeCount() >= 100,
            "Expected >= 100 places, got " + compiled.placeCount());
        assertTrue(compiled.transitionCount() >= 100,
            "Expected >= 100 transitions, got " + compiled.transitionCount());
        System.out.println("Net scale: " + compiled.statistics());
    }

    // ==================== AST Structure Tests ====================

    @Test
    void astRootIsCompilationUnit() {
        var result = parser.parse("class Foo {}");
        assertTrue(result.success(), errorMsg(result));
        assertNotNull(result.ast(), "AST should not be null");
        assertInstanceOf(AstNode.GenericNode.class, result.ast());
        var root = (AstNode.GenericNode) result.ast();
        assertEquals("CompilationUnit", root.kind());
        assertFalse(root.children().isEmpty(), "CompilationUnit should have children");
    }

    @Test
    void astContainsClassDeclarationNode() {
        var result = parser.parse("class Foo {}");
        assertTrue(result.success(), errorMsg(result));
        var root = (AstNode.GenericNode) result.ast();
        // The tree should contain a ClassDeclaration or TypeDeclaration node somewhere
        assertTrue(containsNodeOfKind(root, "ClassDeclaration") ||
                   containsNodeOfKind(root, "TypeDeclaration") ||
                   containsNodeOfKind(root, "NormalClassDeclaration"),
            "AST should contain a class declaration node, got: " + root);
    }

    @Test
    void astContainsIdentifierAndLiteralLeaves() {
        var result = parser.parse("""
            class Foo {
                int x = 1;
            }
            """);
        assertTrue(result.success(), errorMsg(result));
        var root = (AstNode.GenericNode) result.ast();
        assertTrue(containsLeaf(root, "Foo"), "AST should contain identifier 'Foo'");
        assertTrue(containsLeaf(root, "x") || containsLeafByKind(root, AstNode.Identifier.class),
            "AST should contain identifier 'x'");
        assertTrue(containsLeaf(root, "1") || containsLeafByKind(root, AstNode.Literal.class),
            "AST should contain literal '1'");
    }

    @Test
    void astHasTreeStructure() {
        var result = parser.parse("""
            class Foo {
                void bar() {}
            }
            """);
        assertTrue(result.success(), errorMsg(result));
        var root = (AstNode.GenericNode) result.ast();
        // Tree should have depth > 1 (not flat)
        int depth = treeDepth(root);
        assertTrue(depth >= 3, "AST should have depth >= 3, got " + depth);
    }

    private boolean containsNodeOfKind(AstNode node, String kind) {
        if (node instanceof AstNode.GenericNode g) {
            if (g.kind().equals(kind)) return true;
            return g.children().stream().anyMatch(c -> containsNodeOfKind(c, kind));
        }
        return false;
    }

    private boolean containsLeaf(AstNode node, String value) {
        if (node instanceof AstNode.Identifier id) return id.name().equals(value);
        if (node instanceof AstNode.Literal lit) return lit.value().equals(value);
        if (node instanceof AstNode.GenericNode g) {
            return g.children().stream().anyMatch(c -> containsLeaf(c, value));
        }
        return false;
    }

    private boolean containsLeafByKind(AstNode node, Class<? extends AstNode> kind) {
        if (kind.isInstance(node)) return true;
        if (node instanceof AstNode.GenericNode g) {
            return g.children().stream().anyMatch(c -> containsLeafByKind(c, kind));
        }
        return false;
    }

    private int treeDepth(AstNode node) {
        if (node instanceof AstNode.GenericNode g && !g.children().isEmpty()) {
            return 1 + g.children().stream().mapToInt(this::treeDepth).max().orElse(0);
        }
        return 1;
    }

    private String errorMsg(PetriNetParser.ParseResult result) {
        return result.errorMessage() != null ? result.errorMessage() : "Unknown error";
    }
}
