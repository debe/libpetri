package org.libpetri.examples.parser.ast;

import java.util.List;

/**
 * Sealed AST hierarchy for Java 25 syntax.
 * Covers all major syntactic constructs including records, sealed classes,
 * pattern matching, switch expressions, lambdas, and method references.
 */
public sealed interface AstNode {

    // ==================== Top-level ====================

    record CompilationUnit(String packageName, List<AstNode> imports, List<AstNode> declarations) implements AstNode {}
    record PackageDecl(String name) implements AstNode {}
    record ImportDecl(String name, boolean isStatic, boolean isWildcard) implements AstNode {}

    // ==================== Type Declarations ====================

    record ClassDecl(List<String> modifiers, String name, List<AstNode> typeParams,
                     AstNode superClass, List<AstNode> interfaces, List<AstNode> permits,
                     List<AstNode> members) implements AstNode {}
    record InterfaceDecl(List<String> modifiers, String name, List<AstNode> typeParams,
                         List<AstNode> superInterfaces, List<AstNode> permits,
                         List<AstNode> members) implements AstNode {}
    record EnumDecl(List<String> modifiers, String name, List<AstNode> interfaces,
                    List<AstNode> constants, List<AstNode> members) implements AstNode {}
    record RecordDecl(List<String> modifiers, String name, List<AstNode> typeParams,
                      List<AstNode> components, List<AstNode> interfaces,
                      List<AstNode> members) implements AstNode {}
    record AnnotationDecl(List<String> modifiers, String name, List<AstNode> members) implements AstNode {}
    record EnumConstant(String name, List<AstNode> arguments, List<AstNode> members) implements AstNode {}
    record RecordComponent(AstNode type, String name) implements AstNode {}

    // ==================== Members ====================

    record FieldDecl(List<String> modifiers, AstNode type, List<AstNode> declarators) implements AstNode {}
    record MethodDecl(List<String> modifiers, List<AstNode> typeParams, AstNode returnType,
                      String name, List<AstNode> parameters, List<AstNode> throwsTypes,
                      AstNode body) implements AstNode {}
    record ConstructorDecl(List<String> modifiers, String name, List<AstNode> parameters,
                           List<AstNode> throwsTypes, AstNode body) implements AstNode {}
    record CompactConstructor(List<String> modifiers, AstNode body) implements AstNode {}
    record Parameter(List<String> modifiers, AstNode type, boolean varargs, String name) implements AstNode {}
    record VariableDeclarator(String name, List<AstNode> dims, AstNode initializer) implements AstNode {}
    record InitializerBlock(boolean isStatic, AstNode body) implements AstNode {}

    // ==================== Types ====================

    record PrimitiveType(String name) implements AstNode {}
    record ClassType(String name, List<AstNode> typeArgs) implements AstNode {}
    record ArrayType(AstNode componentType, int dimensions) implements AstNode {}
    record TypeParam(String name, List<AstNode> bounds) implements AstNode {}
    record WildcardType(AstNode bound, boolean isUpper) implements AstNode {}
    record VarType() implements AstNode {}

    // ==================== Statements ====================

    record Block(List<AstNode> statements) implements AstNode {}
    record LocalVarDecl(List<String> modifiers, AstNode type, List<AstNode> declarators) implements AstNode {}
    record IfStmt(AstNode condition, AstNode thenBranch, AstNode elseBranch) implements AstNode {}
    record WhileStmt(AstNode condition, AstNode body) implements AstNode {}
    record DoWhileStmt(AstNode body, AstNode condition) implements AstNode {}
    record ForStmt(AstNode init, AstNode condition, List<AstNode> updates, AstNode body) implements AstNode {}
    record ForEachStmt(AstNode variable, AstNode iterable, AstNode body) implements AstNode {}
    record SwitchStmt(AstNode selector, List<AstNode> cases) implements AstNode {}
    record SwitchCase(List<AstNode> labels, boolean isArrow, List<AstNode> statements) implements AstNode {}
    record ReturnStmt(AstNode value) implements AstNode {}
    record ThrowStmt(AstNode value) implements AstNode {}
    record YieldStmt(AstNode value) implements AstNode {}
    record BreakStmt(String label) implements AstNode {}
    record ContinueStmt(String label) implements AstNode {}
    record AssertStmt(AstNode condition, AstNode message) implements AstNode {}
    record TryStmt(List<AstNode> resources, AstNode body, List<AstNode> catches,
                   AstNode finallyBlock) implements AstNode {}
    record CatchClause(AstNode parameter, AstNode body) implements AstNode {}
    record CatchParam(List<String> modifiers, List<AstNode> types, String name) implements AstNode {}
    record SynchronizedStmt(AstNode monitor, AstNode body) implements AstNode {}
    record LabeledStmt(String label, AstNode statement) implements AstNode {}
    record ExpressionStmt(AstNode expression) implements AstNode {}
    record EmptyStmt() implements AstNode {}

    // ==================== Expressions ====================

    record BinaryExpr(AstNode left, String operator, AstNode right) implements AstNode {}
    record UnaryExpr(String operator, AstNode operand, boolean prefix) implements AstNode {}
    record CastExpr(AstNode type, AstNode expression) implements AstNode {}
    record InstanceofExpr(AstNode expression, AstNode typeOrPattern) implements AstNode {}
    record TernaryExpr(AstNode condition, AstNode thenExpr, AstNode elseExpr) implements AstNode {}
    record Assignment(AstNode target, String operator, AstNode value) implements AstNode {}
    record MethodCall(AstNode target, List<AstNode> typeArgs, String name,
                      List<AstNode> arguments) implements AstNode {}
    record FieldAccess(AstNode target, String name) implements AstNode {}
    record ArrayAccess(AstNode array, AstNode index) implements AstNode {}
    record ClassCreation(AstNode type, List<AstNode> typeArgs, List<AstNode> arguments,
                         List<AstNode> members) implements AstNode {}
    record ArrayCreation(AstNode type, List<AstNode> dimensions, AstNode initializer) implements AstNode {}
    record ArrayInit(List<AstNode> elements) implements AstNode {}
    record LambdaExpr(List<AstNode> parameters, AstNode body) implements AstNode {}
    record MethodRef(AstNode target, List<AstNode> typeArgs, String name) implements AstNode {}
    record SwitchExpr(AstNode selector, List<AstNode> cases) implements AstNode {}
    record ParenExpr(AstNode expression) implements AstNode {}

    // ==================== Patterns ====================

    record TypePattern(AstNode type, String name) implements AstNode {}
    record RecordPattern(AstNode type, List<AstNode> components) implements AstNode {}
    record GuardedPattern(AstNode pattern, AstNode guard) implements AstNode {}

    // ==================== Literals & Names ====================

    record Identifier(String name) implements AstNode {}
    record QualifiedName(List<String> parts) implements AstNode {}
    record Literal(String value, LiteralKind kind) implements AstNode {}
    record ThisExpr(AstNode qualifier) implements AstNode {}
    record SuperExpr(AstNode qualifier) implements AstNode {}
    record ClassLiteral(AstNode type) implements AstNode {}

    // ==================== Annotations ====================

    record Annotation(String name, List<AstNode> arguments) implements AstNode {}
    record AnnotationValue(String name, AstNode value) implements AstNode {}

    // ==================== Modules ====================

    record ModuleDecl(boolean isOpen, String name, List<AstNode> directives) implements AstNode {}
    record ModuleRequires(List<String> modifiers, String name) implements AstNode {}
    record ModuleExports(String packageName, List<String> toModules) implements AstNode {}
    record ModuleOpens(String packageName, List<String> toModules) implements AstNode {}
    record ModuleUses(String typeName) implements AstNode {}
    record ModuleProvides(String typeName, List<String> withTypes) implements AstNode {}

    // ==================== Utility ====================

    /** Generic wrapper for grammar nodes not yet fully typed. */
    record GenericNode(String kind, List<AstNode> children) implements AstNode {}

    /** Literal kinds. */
    enum LiteralKind {
        INT, LONG, FLOAT, DOUBLE, CHAR, STRING, TEXT_BLOCK, BOOLEAN, NULL
    }
}
