package org.libpetri.examples.parser.grammar;

import org.libpetri.examples.parser.lexer.TokenType;

import java.util.ArrayList;
import java.util.List;

import static org.libpetri.examples.parser.grammar.GrammarElement.*;

/**
 * Java 25 grammar from JLS Chapter 19, restructured for LL(1) parsing.
 *
 * <p>Key differences from the JLS grammar:
 * <ul>
 *   <li>Left-recursive expression productions rewritten to iterative form</li>
 *   <li>Field/Method declarations left-factored (shared prefix: modifiers type name)</li>
 *   <li>If-then/if-then-else merged (if (expr) stmt [else stmt])</li>
 *   <li>Import declarations left-factored</li>
 *   <li>Shift operators parsed as sequences of '>' tokens (generics compatibility)</li>
 * </ul>
 */
public final class Java25Grammar {

    private Java25Grammar() {}

    public static Grammar create() {
        var prods = new ArrayList<Production>();

        // ==================== Lexical (§3) ====================
        prods.add(prod("Identifier", choice(
            tokenMatch(TokenType.IDENTIFIER),
            terminal("permits"), terminal("when"), terminal("module"),
            terminal("open"), terminal("opens"), terminal("requires"),
            terminal("exports"), terminal("uses"), terminal("provides"),
            terminal("to"), terminal("with"), terminal("transitive")
        )));
        prods.add(prod("TypeIdentifier", tokenMatch(TokenType.IDENTIFIER)));
        prods.add(prod("Literal", choice(
            tokenMatch(TokenType.INT_LITERAL),
            tokenMatch(TokenType.LONG_LITERAL),
            tokenMatch(TokenType.FLOAT_LITERAL),
            tokenMatch(TokenType.DOUBLE_LITERAL),
            tokenMatch(TokenType.STRING_LITERAL),
            tokenMatch(TokenType.TEXT_BLOCK),
            tokenMatch(TokenType.CHAR_LITERAL),
            tokenMatch(TokenType.BOOLEAN_LITERAL),
            tokenMatch(TokenType.NULL_LITERAL)
        )));

        // ==================== Types (§4) ====================
        prods.add(prod("PrimitiveType", choice(
            nonTerminal("NumericType"),
            terminal("boolean")
        )));

        prods.add(prod("NumericType", choice(
            nonTerminal("IntegralType"),
            nonTerminal("FloatingPointType")
        )));

        prods.add(prod("IntegralType", choice(
            terminal("byte"), terminal("short"), terminal("int"),
            terminal("long"), terminal("char")
        )));

        prods.add(prod("FloatingPointType", choice(
            terminal("float"), terminal("double")
        )));

        // ClassOrInterfaceType: Identifier [TypeArguments] {'.' Identifier [TypeArguments]}
        prods.add(prod("ClassOrInterfaceType", seq(
            nonTerminal("Identifier"),
            optional(nonTerminal("TypeArguments")),
            repeat(seq(terminal("."), nonTerminal("Identifier"), optional(nonTerminal("TypeArguments"))))
        )));

        // Type used in declarations (no leading annotations for simplicity)
        prods.add(prod("Type", choice(
            nonTerminal("PrimitiveType"),
            nonTerminal("ClassOrInterfaceType")
        )));

        // Dims: ('[' ']')+
        prods.add(prod("Dims", seq(
            terminal("["), terminal("]"),
            repeat(seq(terminal("["), terminal("]")))
        )));

        prods.add(prod("TypeParameter", seq(
            nonTerminal("TypeIdentifier"),
            optional(nonTerminal("TypeBound"))
        )));

        prods.add(prod("TypeBound", seq(
            terminal("extends"),
            nonTerminal("ClassOrInterfaceType"),
            repeat(seq(terminal("&"), nonTerminal("ClassOrInterfaceType")))
        )));

        prods.add(prod("TypeArguments", seq(
            tokenMatch(TokenType.TYPE_OPEN),
            optional(nonTerminal("TypeArgumentList")),
            tokenMatch(TokenType.TYPE_CLOSE)
        )));

        prods.add(prod("TypeArgumentList", seq(
            nonTerminal("TypeArgument"),
            repeat(seq(terminal(","), nonTerminal("TypeArgument")))
        )));

        prods.add(prod("TypeArgument", choice(
            nonTerminal("Wildcard"),
            nonTerminal("Type")
        )));

        prods.add(prod("Wildcard", seq(
            terminal("?"),
            optional(nonTerminal("WildcardBounds"))
        )));

        prods.add(prod("WildcardBounds", choice(
            seq(terminal("extends"), nonTerminal("Type")),
            seq(terminal("super"), nonTerminal("Type"))
        )));

        // ==================== Annotations (simplified) ====================
        // Annotation: @ QualifiedName optional(( args ))
        // Note: @ is also used in @interface declarations. Since QualifiedName requires
        // Identifier (not KEYWORD), @interface will fail gracefully — the @ is consumed
        // but 'interface' is not an Identifier, routing to error.
        // To prevent this, we use AnnotationName which requires the first token to be
        // an IDENTIFIER (not 'interface' keyword).
        prods.add(prod("Annotation", seq(
            terminal("@"), nonTerminal("QualifiedName"),
            optional(seq(terminal("("),
                optional(nonTerminal("AnnotationArgs")),
                terminal(")")))
        )));

        // Annotation arguments: single value, or comma-separated values.
        // name=value pairs parse as assignment expressions (name = expr).
        // Single values and qualified names like RetentionPolicy.RUNTIME parse as expressions.
        prods.add(prod("AnnotationArgs", seq(
            nonTerminal("ElementValue"),
            repeat(seq(terminal(","), nonTerminal("ElementValue")))
        )));

        prods.add(prod("ElementValue", choice(
            nonTerminal("Annotation"),
            nonTerminal("ElementValueArrayInitializer"),
            nonTerminal("Expression")
        )));

        // Element value array with trailing comma support:
        // { } | { element [, element]* [,] }
        // Uses ElementValueArrayBody to avoid repeat consuming trailing comma
        prods.add(prod("ElementValueArrayInitializer", seq(
            terminal("{"),
            optional(nonTerminal("ElementValueArrayBody")),
            terminal("}")
        )));

        prods.add(prod("ElementValueArrayBody", seq(
            nonTerminal("ElementValue"),
            repeat(nonTerminal("ElementValueArrayTail"))
        )));

        // After each element: , followed by another element, or just trailing ,
        // Dispatches on what follows the comma: } means trailing, else another element
        prods.add(prod("ElementValueArrayTail", seq(
            terminal(","),
            optional(nonTerminal("ElementValue"))
        )));

        prods.add(prod("Annotations", seq(
            nonTerminal("Annotation"),
            repeat(nonTerminal("Annotation"))
        )));

        // ==================== Names (§6) ====================
        prods.add(prod("QualifiedName", seq(
            nonTerminal("Identifier"),
            repeat(seq(terminal("."), nonTerminal("Identifier")))
        )));

        // ==================== Packages (§7) ====================
        prods.add(prod("CompilationUnit", seq(
            optional(nonTerminal("PackageDeclaration")),
            repeat(nonTerminal("ImportDeclaration")),
            repeat(nonTerminal("TypeDeclaration"))
        )));

        prods.add(prod("PackageDeclaration", seq(
            repeat(nonTerminal("Annotation")),
            terminal("package"), nonTerminal("QualifiedName"), terminal(";")
        )));

        // Import: import [static] Identifier {'.' Identifier} ['.' '*'] ';'
        // The QualifiedName consumes as many .Identifier as possible.
        // For on-demand imports, the last segment is '.*' which is handled
        // by ImportSuffix after QualifiedName stops at a non-identifier.
        prods.add(prod("ImportDeclaration", seq(
            terminal("import"),
            optional(terminal("static")),
            nonTerminal("ImportName"),
            terminal(";")
        )));

        // Import name: Identifier {'.' (Identifier | '*')}
        // Handles both java.util.List and java.util.*
        prods.add(prod("ImportName", seq(
            nonTerminal("Identifier"),
            repeat(seq(terminal("."), nonTerminal("ImportNameSegment")))
        )));

        prods.add(prod("ImportNameSegment", choice(
            terminal("*"),
            nonTerminal("Identifier")
        )));

        // Left-factored type declaration:
        // All declarations start with modifiers, then a keyword distinguishes them
        prods.add(prod("TypeDeclaration", choice(
            terminal(";"),
            nonTerminal("ModifiedTypeDeclaration")
        )));

        prods.add(prod("ModifiedTypeDeclaration", seq(
            repeat(nonTerminal("Modifier")),
            nonTerminal("TypeDeclarationKind")
        )));

        prods.add(prod("TypeDeclarationKind", choice(
            nonTerminal("ClassDeclRest"),
            nonTerminal("InterfaceDeclRest"),
            nonTerminal("EnumDeclRest"),
            nonTerminal("RecordDeclRest"),
            // @interface must be handled here since @ is also FIRST(Annotation)
            // and would be consumed by the modifier loop otherwise
            nonTerminal("AnnotationDeclRest")
        )));

        // Standalone declarations (with modifiers) for use in block statements
        prods.add(prod("ClassDeclaration", seq(
            repeat(nonTerminal("Modifier")),
            nonTerminal("ClassDeclRest")
        )));

        // ==================== Classes (§8) ====================
        prods.add(prod("ClassDeclRest", seq(
            terminal("class"), nonTerminal("TypeIdentifier"),
            optional(nonTerminal("TypeParameters")),
            optional(seq(terminal("extends"), nonTerminal("ClassOrInterfaceType"))),
            optional(seq(terminal("implements"), nonTerminal("TypeList"))),
            optional(seq(terminal("permits"), nonTerminal("TypeList"))),
            nonTerminal("ClassBody")
        )));

        prods.add(prod("Modifier", choice(
            nonTerminal("Annotation"),
            terminal("public"), terminal("protected"), terminal("private"),
            terminal("abstract"), terminal("static"), terminal("final"),
            terminal("sealed"), terminal("non-sealed"), terminal("strictfp"),
            terminal("default"), terminal("synchronized"), terminal("native"),
            terminal("transient"), terminal("volatile")
        )));

        prods.add(prod("TypeParameters", seq(
            tokenMatch(TokenType.TYPE_OPEN),
            nonTerminal("TypeParameter"),
            repeat(seq(terminal(","), nonTerminal("TypeParameter"))),
            tokenMatch(TokenType.TYPE_CLOSE)
        )));

        prods.add(prod("TypeList", seq(
            nonTerminal("ClassOrInterfaceType"),
            repeat(seq(terminal(","), nonTerminal("ClassOrInterfaceType")))
        )));

        prods.add(prod("ClassBody", seq(
            terminal("{"),
            repeat(nonTerminal("ClassBodyDeclaration")),
            terminal("}")
        )));

        // Left-factored class body declaration
        // All members start with modifiers, then keyword/type distinguishes them.
        // StaticInitializer is special: 'static' followed by '{'.
        prods.add(prod("ClassBodyDeclaration", choice(
            terminal(";"),
            nonTerminal("ClassBodyMember")
        )));

        // Parse: modifiers, then decide what kind of member
        prods.add(prod("ClassBodyMember", seq(
            repeat(nonTerminal("Modifier")),
            nonTerminal("ClassBodyMemberRest")
        )));

        prods.add(prod("ClassBodyMemberRest", choice(
            // Block: static initializer or instance initializer
            nonTerminal("Block"),
            // Type declarations
            nonTerminal("ClassDeclRest"),
            nonTerminal("InterfaceDeclRest"),
            nonTerminal("EnumDeclRest"),
            nonTerminal("RecordDeclRest"),
            nonTerminal("AnnotationDeclRest"),
            // Field or method (with type and name)
            nonTerminal("FieldOrMethodOrConstructor")
        )));

        // Parse members that start with a type or name:
        //   void name(...) {...}           — void method
        //   Type name = ...; or Type name; — field
        //   Type name(...) {...}           — method
        //   Name(...) {...}                — constructor (Name matches class name)
        //
        // Left-factored: void is unambiguous. For Type/Name, we parse Identifier
        // then decide: if '(' follows, it's a constructor. If Identifier follows,
        // it's field/method with the first Identifier as type.
        prods.add(prod("FieldOrMethodOrConstructor", choice(
            // void method (with optional type parameters: <T> void method())
            seq(terminal("void"), nonTerminal("Identifier"), nonTerminal("MethodRest")),
            // Type (primitive) then name
            seq(nonTerminal("PrimitiveType"), optional(nonTerminal("Dims")),
                nonTerminal("Identifier"), nonTerminal("FieldOrMethodRest")),
            // Identifier-based: could be constructor or ClassType + name
            seq(optional(nonTerminal("TypeParameters")),
                nonTerminal("IdentOrVoidMember"))
        )));

        // After optional TypeParameters: void method, primitive-type method, or Identifier-based member
        prods.add(prod("IdentOrVoidMember", choice(
            seq(terminal("void"), nonTerminal("Identifier"), nonTerminal("MethodRest")),
            // <T> boolean method(), <T> int method(), etc.
            seq(nonTerminal("PrimitiveType"), optional(nonTerminal("Dims")),
                nonTerminal("Identifier"), nonTerminal("FieldOrMethodRest")),
            seq(nonTerminal("Identifier"), nonTerminal("IdentBasedMemberRest"))
        )));

        prods.add(prod("IdentBasedMemberRest", choice(
            // Constructor: Name '(' ... ')'
            seq(terminal("("), optional(nonTerminal("FormalParameterList")), terminal(")"),
                optional(nonTerminal("ThrowsClause")), nonTerminal("Block")),
            // Type continues (qualified or with type args), then field/method name
            seq(nonTerminal("TypeContinuation"),
                nonTerminal("Identifier"), nonTerminal("FieldOrMethodRest")),
            // Direct field/method: simple type name followed by field/method name
            seq(nonTerminal("Identifier"), nonTerminal("FieldOrMethodRest")),
            // Compact constructor (records): Name '{' ... '}'
            nonTerminal("Block")
        )));

        // Continuation of a class type: type args, qualified parts, dims
        prods.add(prod("TypeContinuation", seq(
            optional(nonTerminal("TypeArguments")),
            repeat(seq(terminal("."), nonTerminal("Identifier"),
                       optional(nonTerminal("TypeArguments")))),
            optional(nonTerminal("Dims"))
        )));

        prods.add(prod("FieldOrMethodRest", choice(
            nonTerminal("MethodRest"),
            nonTerminal("FieldRest")
        )));

        prods.add(prod("MethodRest", seq(
            terminal("("),
            optional(nonTerminal("FormalParameterList")),
            terminal(")"),
            optional(nonTerminal("Dims")),
            optional(nonTerminal("ThrowsClause")),
            nonTerminal("MethodBody")
        )));

        prods.add(prod("FieldRest", seq(
            optional(nonTerminal("Dims")),
            optional(seq(terminal("="), nonTerminal("VariableInitializer"))),
            repeat(seq(terminal(","), nonTerminal("VariableDeclarator"))),
            terminal(";")
        )));

        prods.add(prod("MethodBody", choice(
            nonTerminal("Block"),
            // Annotation element default value: default ElementValue ;
            seq(terminal("default"), nonTerminal("ElementValue"), terminal(";")),
            terminal(";")
        )));

        prods.add(prod("FormalParameterList", seq(
            nonTerminal("FormalParameter"),
            repeat(seq(terminal(","), nonTerminal("FormalParameter")))
        )));

        prods.add(prod("FormalParameter", seq(
            repeat(nonTerminal("Modifier")),
            nonTerminal("ParameterType"),
            optional(nonTerminal("Dims")),
            optional(terminal("...")),
            nonTerminal("Identifier"),
            optional(nonTerminal("Dims"))
        )));

        prods.add(prod("ParameterType", choice(
            terminal("var"),
            nonTerminal("Type")
        )));

        prods.add(prod("ThrowsClause", seq(
            terminal("throws"), nonTerminal("TypeList")
        )));

        prods.add(prod("VariableDeclarator", seq(
            nonTerminal("Identifier"),
            optional(nonTerminal("Dims")),
            optional(seq(terminal("="), nonTerminal("VariableInitializer")))
        )));

        prods.add(prod("VariableInitializer", choice(
            nonTerminal("ArrayInitializer"),
            nonTerminal("Expression")
        )));

        prods.add(prod("ArrayInitializer", seq(
            terminal("{"),
            optional(seq(nonTerminal("VariableInitializer"),
                repeat(seq(terminal(","), nonTerminal("VariableInitializer"))))),
            optional(terminal(",")),
            terminal("}")
        )));

        // (ConstructorDeclaration and StaticInitializer are handled inside
        //  ClassBodyMemberRest via FieldOrMethodOrConstructor and Block)

        // ==================== Enums ====================
        prods.add(prod("EnumDeclRest", seq(
            terminal("enum"), nonTerminal("TypeIdentifier"),
            optional(seq(terminal("implements"), nonTerminal("TypeList"))),
            nonTerminal("EnumBody")
        )));

        // Keep standalone EnumDeclaration for use in ClassBodyDeclaration
        prods.add(prod("EnumDeclaration", seq(
            repeat(nonTerminal("Modifier")),
            nonTerminal("EnumDeclRest")
        )));

        prods.add(prod("EnumBody", seq(
            terminal("{"),
            optional(seq(nonTerminal("EnumConstant"),
                repeat(seq(terminal(","), nonTerminal("EnumConstant"))))),
            optional(terminal(",")),
            optional(seq(terminal(";"), repeat(nonTerminal("ClassBodyDeclaration")))),
            terminal("}")
        )));

        prods.add(prod("EnumConstant", seq(
            repeat(nonTerminal("Annotation")),
            nonTerminal("Identifier"),
            optional(seq(terminal("("), optional(nonTerminal("ArgumentList")), terminal(")"))),
            optional(nonTerminal("ClassBody"))
        )));

        // ==================== Records ====================
        prods.add(prod("RecordDeclRest", seq(
            terminal("record"), nonTerminal("TypeIdentifier"),
            optional(nonTerminal("TypeParameters")),
            nonTerminal("RecordHeader"),
            optional(seq(terminal("implements"), nonTerminal("TypeList"))),
            nonTerminal("RecordBody")
        )));

        prods.add(prod("RecordDeclaration", seq(
            repeat(nonTerminal("Modifier")),
            nonTerminal("RecordDeclRest")
        )));

        prods.add(prod("RecordHeader", seq(
            terminal("("),
            optional(seq(nonTerminal("RecordComponent"),
                repeat(seq(terminal(","), nonTerminal("RecordComponent"))))),
            terminal(")")
        )));

        prods.add(prod("RecordComponent", seq(
            repeat(nonTerminal("Annotation")),
            nonTerminal("Type"),
            optional(nonTerminal("Dims")),
            nonTerminal("Identifier")
        )));

        prods.add(prod("RecordBody", seq(
            terminal("{"),
            repeat(nonTerminal("ClassBodyDeclaration")),
            terminal("}")
        )));

        // ==================== Interfaces (§9) ====================
        prods.add(prod("InterfaceDeclRest", seq(
            terminal("interface"), nonTerminal("TypeIdentifier"),
            optional(nonTerminal("TypeParameters")),
            optional(seq(terminal("extends"), nonTerminal("TypeList"))),
            optional(seq(terminal("permits"), nonTerminal("TypeList"))),
            nonTerminal("InterfaceBody")
        )));

        prods.add(prod("InterfaceDeclaration", seq(
            repeat(nonTerminal("Modifier")),
            nonTerminal("InterfaceDeclRest")
        )));

        prods.add(prod("InterfaceBody", seq(
            terminal("{"),
            repeat(nonTerminal("InterfaceBodyDeclaration")),
            terminal("}")
        )));

        // Interface body: same left-factoring as class body
        prods.add(prod("InterfaceBodyDeclaration", choice(
            terminal(";"),
            nonTerminal("ClassBodyMember")
        )));

        prods.add(prod("AnnotationDeclRest", seq(
            terminal("@interface"), nonTerminal("TypeIdentifier"),
            terminal("{"),
            repeat(nonTerminal("InterfaceBodyDeclaration")),
            terminal("}")
        )));

        prods.add(prod("AnnotationDeclaration", seq(
            repeat(nonTerminal("Modifier")),
            nonTerminal("AnnotationDeclRest")
        )));

        // ==================== Blocks & Statements (§14) ====================
        prods.add(prod("Block", seq(
            terminal("{"),
            repeat(nonTerminal("BlockStatement")),
            terminal("}")
        )));

        // Block statements: dispatch by leading token.
        // - Keywords like 'if', 'while', 'for', 'switch', 'try' → Statement
        // - 'final' or annotation → LocalVariableDeclaration (or local class)
        // - Primitive type keyword (int, double, etc.) or 'var' → LocalVariableDeclaration
        // - Identifier → ambiguous: could be variable decl (Type name) or expression stmt
        //   Handled by Statement → LabeledOrExpressionStatement
        // Block statements: Statement is listed first so IDENTIFIER tokens
        // route to expression/labeled statements (not LocalVariableDeclaration).
        // Class-type local variable declarations (e.g. "String s = ...") are
        // handled inside LabelOrExprRest after parsing the type as an expression.
        prods.add(prod("BlockStatement", choice(
            nonTerminal("Statement"),
            nonTerminal("LocalVariableDeclaration")
        )));

        // Local variable: annotations/final prefix distinguishes from expression statements.
        // Primitive types and 'var' also unambiguously start a declaration.
        // Class-type declarations without modifiers are handled by the Expression parser:
        // `Type name = ...` parses as expression but will correctly assign.
        prods.add(prod("LocalVariableDeclaration", seq(
            repeat(nonTerminal("LocalVarModifier")),
            nonTerminal("LocalVarType"),
            optional(nonTerminal("Dims")),
            nonTerminal("VariableDeclarator"),
            repeat(seq(terminal(","), nonTerminal("VariableDeclarator"))),
            terminal(";")
        )));

        prods.add(prod("LocalVarModifier", choice(
            nonTerminal("Annotation"),
            terminal("final")
        )));

        // Only var and primitive types — no ClassOrInterfaceType here.
        // Class-type declarations are handled by LabelOrExprRest (see below).
        prods.add(prod("LocalVarType", choice(
            terminal("var"),
            nonTerminal("PrimitiveType")
        )));

        prods.add(prod("Statement", choice(
            nonTerminal("Block"),
            nonTerminal("IfStatement"),
            nonTerminal("WhileStatement"),
            nonTerminal("DoWhileStatement"),
            nonTerminal("ForStatement"),
            nonTerminal("SwitchStatement"),
            nonTerminal("TryStatement"),
            nonTerminal("ReturnStatement"),
            nonTerminal("ThrowStatement"),
            nonTerminal("BreakStatement"),
            nonTerminal("ContinueStatement"),
            nonTerminal("YieldStatement"),
            nonTerminal("AssertStatement"),
            nonTerminal("SynchronizedStatement"),
            nonTerminal("LabeledOrExpressionStatement"),
            nonTerminal("EmptyStatement"),
            // Local record declaration: record Name(...) { ... }
            nonTerminal("RecordDeclRest"),
            // Local class declaration: class Name { ... }
            nonTerminal("ClassDeclRest"),
            // Local enum declaration: enum Name { ... }
            nonTerminal("EnumDeclRest")
        )));

        // Explicit constructor invocation: this(...) or super(...)
        // These are handled via LabeledOrExpressionStatement since 'this' and 'super'
        // are valid PrimaryBase tokens that parse as expressions followed by ';'.

        prods.add(prod("EmptyStatement", terminal(";")));

        // Merged if-then / if-then-else: if (expr) stmt [else stmt]
        prods.add(prod("IfStatement", seq(
            terminal("if"), terminal("("), nonTerminal("Expression"), terminal(")"),
            nonTerminal("Statement"),
            optional(seq(terminal("else"), nonTerminal("Statement")))
        )));

        prods.add(prod("WhileStatement", seq(
            terminal("while"), terminal("("), nonTerminal("Expression"), terminal(")"),
            nonTerminal("Statement")
        )));

        prods.add(prod("DoWhileStatement", seq(
            terminal("do"), nonTerminal("Statement"),
            terminal("while"), terminal("("), nonTerminal("Expression"), terminal(")"),
            terminal(";")
        )));

        // For: for ( [ForInit] ; [Expr] ; [ForUpdate] ) Stmt
        //    | for ( Modifiers Type Id : Expr ) Stmt
        prods.add(prod("ForStatement", seq(
            terminal("for"), terminal("("),
            nonTerminal("ForContent"),
            terminal(")"),
            nonTerminal("Statement")
        )));

        // For content: left-factored to handle enhanced vs basic.
        // Basic: [init] ; [cond] ; [update]
        // Enhanced: [modifier] type name : expr
        // Both can start with type keywords — disambiguated after name by : vs = or ;
        prods.add(prod("ForContent", choice(
            // Empty init: ; ... (basic for with no init)
            seq(terminal(";"), optional(nonTerminal("Expression")), terminal(";"),
                optional(nonTerminal("ExpressionList"))),
            // Starts with expression or declaration
            nonTerminal("ForContentNonEmpty")
        )));

        // Parse type/name then decide if enhanced (:) or basic (=/,/;)
        prods.add(prod("ForContentNonEmpty", seq(
            repeat(nonTerminal("LocalVarModifier")),
            nonTerminal("ForVarType"),
            nonTerminal("Identifier"),
            nonTerminal("ForContentAfterIdent")
        )));

        prods.add(prod("ForVarType", choice(
            terminal("var"),
            nonTerminal("Type")
        )));

        prods.add(prod("ForContentAfterIdent", choice(
            // Enhanced for: name ':' expr
            seq(terminal(":"), nonTerminal("Expression")),
            // Basic for: variable init rest then ; cond ; update
            seq(optional(seq(terminal("="), nonTerminal("Expression"))),
                repeat(seq(terminal(","), nonTerminal("VariableDeclarator"))),
                terminal(";"),
                optional(nonTerminal("Expression")),
                terminal(";"),
                optional(nonTerminal("ExpressionList")))
        )));

        prods.add(prod("ExpressionList", seq(
            nonTerminal("Expression"),
            repeat(seq(terminal(","), nonTerminal("Expression")))
        )));

        // Switch
        prods.add(prod("SwitchStatement", seq(
            terminal("switch"), terminal("("), nonTerminal("Expression"), terminal(")"),
            nonTerminal("SwitchBlock")
        )));

        prods.add(prod("SwitchBlock", seq(
            terminal("{"),
            repeat(nonTerminal("SwitchEntry")),
            terminal("}")
        )));

        prods.add(prod("SwitchEntry", choice(
            seq(terminal("case"), nonTerminal("CaseExpressionList"),
                nonTerminal("SwitchArrowOrColon")),
            seq(terminal("default"), nonTerminal("SwitchArrowOrColon"))
        )));

        prods.add(prod("CaseExpressionList", seq(
            nonTerminal("CaseExpression"),
            repeat(seq(terminal(","), nonTerminal("CaseExpression")))
        )));

        prods.add(prod("CaseExpression", choice(
            nonTerminal("Pattern"),
            nonTerminal("Expression")
        )));

        prods.add(prod("SwitchArrowOrColon", choice(
            seq(terminal("->"), nonTerminal("SwitchRuleBody")),
            seq(terminal(":"), repeat(nonTerminal("BlockStatement")))
        )));

        prods.add(prod("SwitchRuleBody", choice(
            nonTerminal("Block"),
            seq(nonTerminal("Expression"), terminal(";")),
            seq(terminal("throw"), nonTerminal("Expression"), terminal(";"))
        )));

        // Return, Throw, Break, Continue, Yield
        prods.add(prod("ReturnStatement", seq(
            terminal("return"), optional(nonTerminal("Expression")), terminal(";")
        )));

        prods.add(prod("ThrowStatement", seq(
            terminal("throw"), nonTerminal("Expression"), terminal(";")
        )));

        prods.add(prod("BreakStatement", seq(
            terminal("break"), optional(nonTerminal("Identifier")), terminal(";")
        )));

        prods.add(prod("ContinueStatement", seq(
            terminal("continue"), optional(nonTerminal("Identifier")), terminal(";")
        )));

        prods.add(prod("YieldStatement", seq(
            terminal("yield"), nonTerminal("Expression"), terminal(";")
        )));

        prods.add(prod("AssertStatement", seq(
            terminal("assert"), nonTerminal("Expression"),
            optional(seq(terminal(":"), nonTerminal("Expression"))),
            terminal(";")
        )));

        prods.add(prod("SynchronizedStatement", seq(
            terminal("synchronized"), terminal("("), nonTerminal("Expression"), terminal(")"),
            nonTerminal("Block")
        )));

        // Labeled statement or expression statement
        // Both start with IDENTIFIER: labeled is "id: stmt", expression is "expr ;"
        // We parse as expression, then check for ':'
        prods.add(prod("LabeledOrExpressionStatement", seq(
            nonTerminal("Expression"), nonTerminal("LabelOrExprRest")
        )));

        prods.add(prod("LabelOrExprRest", choice(
            // Label: identifier ':'
            seq(terminal(":"), nonTerminal("Statement")),
            // Expression statement: expr ';'
            terminal(";"),
            // After expression: IDENTIFIER follows — left-factored into AfterExprIdent
            // Handles class-type local var decl, and local record decl
            seq(nonTerminal("Identifier"), nonTerminal("AfterExprIdent")),
            // Array-type class local variable: Type[] name = ...
            seq(nonTerminal("Dims"), nonTerminal("Identifier"),
                optional(nonTerminal("Dims")),
                optional(seq(terminal("="), nonTerminal("VariableInitializer"))),
                repeat(seq(terminal(","), nonTerminal("VariableDeclarator"))),
                terminal(";")),
            // Generic-type class local variable: Type<Args> name = ...
            seq(nonTerminal("TypeArguments"),
                optional(seq(terminal("."), nonTerminal("ClassOrInterfaceType"))),
                optional(nonTerminal("Dims")),
                nonTerminal("Identifier"),
                optional(nonTerminal("Dims")),
                optional(seq(terminal("="), nonTerminal("VariableInitializer"))),
                repeat(seq(terminal(","), nonTerminal("VariableDeclarator"))),
                terminal(";"))
        )));

        // After IDENTIFIER in LabelOrExprRest — dispatches local record decl vs class-type local var
        prods.add(prod("AfterExprIdent", choice(
            // Local record declaration: Name(params) [implements TypeList] { body }
            seq(terminal("("), optional(nonTerminal("FormalParameterList")), terminal(")"),
                optional(seq(terminal("implements"), nonTerminal("TypeList"))),
                nonTerminal("RecordBody")),
            // Class-type local variable: name [dims] [= init] [, more] ;
            seq(optional(nonTerminal("Dims")),
                optional(seq(terminal("="), nonTerminal("VariableInitializer"))),
                repeat(seq(terminal(","), nonTerminal("VariableDeclarator"))),
                terminal(";"))
        )));

        // Try
        prods.add(prod("TryStatement", seq(
            terminal("try"),
            nonTerminal("TryBody")
        )));

        prods.add(prod("TryBody", choice(
            seq(nonTerminal("ResourceSpec"), nonTerminal("Block"),
                optional(nonTerminal("CatchClauses")),
                optional(nonTerminal("FinallyClause"))),
            seq(nonTerminal("Block"), nonTerminal("CatchesOrFinally"))
        )));

        prods.add(prod("CatchesOrFinally", choice(
            seq(nonTerminal("CatchClauses"), optional(nonTerminal("FinallyClause"))),
            nonTerminal("FinallyClause")
        )));

        prods.add(prod("ResourceSpec", seq(
            terminal("("),
            nonTerminal("Resource"),
            repeat(seq(terminal(";"), nonTerminal("Resource"))),
            optional(terminal(";")),
            terminal(")")
        )));

        prods.add(prod("Resource", seq(
            repeat(nonTerminal("Modifier")),
            nonTerminal("ResourceType"),
            nonTerminal("Identifier"),
            terminal("="),
            nonTerminal("Expression")
        )));

        // Resource type: var, primitive, or class type
        prods.add(prod("ResourceType", choice(
            terminal("var"),
            nonTerminal("Type")
        )));

        prods.add(prod("CatchClauses", seq(
            nonTerminal("CatchClause"),
            repeat(nonTerminal("CatchClause"))
        )));

        prods.add(prod("CatchClause", seq(
            terminal("catch"), terminal("("),
            repeat(nonTerminal("Modifier")),
            nonTerminal("CatchType"),
            nonTerminal("Identifier"),
            terminal(")"), nonTerminal("Block")
        )));

        prods.add(prod("CatchType", seq(
            nonTerminal("ClassOrInterfaceType"),
            repeat(seq(terminal("|"), nonTerminal("ClassOrInterfaceType")))
        )));

        prods.add(prod("FinallyClause", seq(
            terminal("finally"), nonTerminal("Block")
        )));

        // Patterns — left-factored since both TypePattern and RecordPattern
        // start with a type name (IDENTIFIER).
        // After parsing modifiers and type, decide:
        //   - IDENTIFIER follows → TypePattern (binding variable)
        //   - '(' follows → RecordPattern (deconstruction)
        //   - neither → type-only pattern (e.g. case x -> ...)
        prods.add(prod("Pattern", seq(
            repeat(nonTerminal("Modifier")),
            nonTerminal("PatternType"),
            optional(nonTerminal("PatternRest"))
        )));

        // Pattern type: var (inferred), or explicit Type
        prods.add(prod("PatternType", choice(
            terminal("var"),
            nonTerminal("Type")
        )));

        prods.add(prod("PatternRest", choice(
            // Binding variable (TypePattern): Type name
            nonTerminal("Identifier"),
            // Record deconstruction (RecordPattern): Type(patterns...)
            seq(terminal("("),
                optional(seq(nonTerminal("Pattern"),
                    repeat(seq(terminal(","), nonTerminal("Pattern"))))),
                terminal(")"))
        )));

        prods.add(prod("Guard", seq(
            terminal("when"), nonTerminal("Expression")
        )));

        // ==================== Expressions (§15) ====================
        // Iterative (left-recursion eliminated) expression hierarchy.

        prods.add(prod("Expression", nonTerminal("AssignmentExpression")));

        prods.add(prod("AssignmentExpression", seq(
            nonTerminal("ConditionalExpression"),
            optional(seq(nonTerminal("AssignmentOperator"), nonTerminal("Expression")))
        )));

        prods.add(prod("AssignmentOperator", choice(
            terminal("="), terminal("+="), terminal("-="), terminal("*="),
            terminal("/="), terminal("%="), terminal("&="), terminal("|="),
            terminal("^="), terminal("<<=")
        )));

        prods.add(prod("ConditionalExpression", seq(
            nonTerminal("ConditionalOrExpression"),
            optional(seq(terminal("?"), nonTerminal("Expression"),
                        terminal(":"), nonTerminal("ConditionalExpression")))
        )));

        prods.add(prod("ConditionalOrExpression", seq(
            nonTerminal("ConditionalAndExpression"),
            repeat(seq(terminal("||"), nonTerminal("ConditionalAndExpression")))
        )));

        prods.add(prod("ConditionalAndExpression", seq(
            nonTerminal("InclusiveOrExpression"),
            repeat(seq(terminal("&&"), nonTerminal("InclusiveOrExpression")))
        )));

        prods.add(prod("InclusiveOrExpression", seq(
            nonTerminal("ExclusiveOrExpression"),
            repeat(seq(terminal("|"), nonTerminal("ExclusiveOrExpression")))
        )));

        prods.add(prod("ExclusiveOrExpression", seq(
            nonTerminal("AndExpression"),
            repeat(seq(terminal("^"), nonTerminal("AndExpression")))
        )));

        prods.add(prod("AndExpression", seq(
            nonTerminal("EqualityExpression"),
            repeat(seq(terminal("&"), nonTerminal("EqualityExpression")))
        )));

        prods.add(prod("EqualityExpression", seq(
            nonTerminal("RelationalExpression"),
            repeat(seq(choice(terminal("=="), terminal("!=")),
                       nonTerminal("RelationalExpression")))
        )));

        prods.add(prod("RelationalExpression", seq(
            nonTerminal("ShiftExpression"),
            repeat(nonTerminal("RelationalSuffix"))
        )));

        prods.add(prod("RelationalSuffix", choice(
            seq(choice(terminal("<"), terminal("<="), terminal(">=")),
                nonTerminal("ShiftExpression")),
            // '>' can be: relational >, right-shift >> (> >), or unsigned right-shift >>> (> > >)
            // After consuming first >, check if another > follows for shift operators
            seq(terminal(">"), nonTerminal("AfterGreaterThan")),
            seq(terminal("instanceof"), nonTerminal("InstanceofTarget"))
        )));

        // After '>': could be relational comparison, >> (shift), or >>> (unsigned shift)
        prods.add(prod("AfterGreaterThan", choice(
            // >> or >>> : next token is '>', left-factor further
            seq(terminal(">"), nonTerminal("AfterDoubleGreaterThan")),
            // plain > : relational comparison (next token is NOT >, it's an expression)
            nonTerminal("ShiftExpression")
        )));

        // After '>>': could be >> (shift) or >>> (unsigned shift)
        prods.add(prod("AfterDoubleGreaterThan", choice(
            // >>> : one more > then additive expression
            seq(terminal(">"), nonTerminal("AdditiveExpression")),
            // >> : just additive expression
            nonTerminal("AdditiveExpression")
        )));

        // Left-factored: parse Type first, then check for pattern binding or record pattern.
        // - "instanceof String s"     → Type + Identifier (TypePattern)
        // - "instanceof Point(x, y)" → Type + "(" ... ")" (RecordPattern)
        // - "instanceof String"       → just Type (type check)
        prods.add(prod("InstanceofTarget", seq(
            nonTerminal("Type"),
            optional(nonTerminal("InstanceofPatternRest"))
        )));

        prods.add(prod("InstanceofPatternRest", choice(
            // Binding variable: Type name
            nonTerminal("Identifier"),
            // Record pattern: Type(patterns...)
            seq(terminal("("),
                optional(seq(nonTerminal("Pattern"),
                    repeat(seq(terminal(","), nonTerminal("Pattern"))))),
                terminal(")"))
        )));

        // Shift expression: only left-shift << is handled at this level.
        // Right-shift >> and >>> are handled in RelationalSuffix where > already lives,
        // since they start with > which conflicts with relational > for LL(1).
        prods.add(prod("ShiftExpression", seq(
            nonTerminal("AdditiveExpression"),
            repeat(seq(terminal("<<"), nonTerminal("AdditiveExpression")))
        )));

        prods.add(prod("AdditiveExpression", seq(
            nonTerminal("MultiplicativeExpression"),
            repeat(seq(choice(terminal("+"), terminal("-")),
                       nonTerminal("MultiplicativeExpression")))
        )));

        prods.add(prod("MultiplicativeExpression", seq(
            nonTerminal("UnaryExpression"),
            repeat(seq(choice(terminal("*"), terminal("/"), terminal("%")),
                       nonTerminal("UnaryExpression")))
        )));

        prods.add(prod("UnaryExpression", choice(
            seq(terminal("++"), nonTerminal("UnaryExpression")),
            seq(terminal("--"), nonTerminal("UnaryExpression")),
            seq(terminal("+"), nonTerminal("UnaryExpression")),
            seq(terminal("-"), nonTerminal("UnaryExpression")),
            seq(terminal("~"), nonTerminal("UnaryExpression")),
            seq(terminal("!"), nonTerminal("UnaryExpression")),
            nonTerminal("PostfixExpression")
        )));

        // Cast expressions are not handled as a separate production to avoid
        // ambiguity with parenthesized expressions (both start with '(').
        // Casts like (int)x parse via LambdaOrParenOrCast + PostParenAction.

        prods.add(prod("PostfixExpression", seq(
            nonTerminal("Primary"),
            repeat(choice(terminal("++"), terminal("--")))
        )));

        // Primary: the core of expressions
        prods.add(prod("Primary", seq(
            nonTerminal("PrimaryBase"),
            repeat(nonTerminal("PrimarySuffix"))
        )));

        prods.add(prod("PrimaryBase", choice(
            nonTerminal("Literal"),
            terminal("this"),
            terminal("super"),
            nonTerminal("NewExpression"),
            nonTerminal("SwitchExpression"),
            nonTerminal("LambdaOrParenOrCast"),
            nonTerminal("NameExpression")
        )));

        // Disambiguate '(' : lambda params, parenthesized expression, or cast
        // Lambda arrow '->' is handled HERE (not in PrimarySuffix) to prevent
        // expressions like `case 1 -> body` from being mis-parsed as lambdas.
        prods.add(prod("LambdaOrParenOrCast", seq(
            terminal("("),
            nonTerminal("ParenContent"),
            terminal(")"),
            optional(nonTerminal("PostParenAction"))
        )));

        // After '(' content ')': lambda arrow or cast target (not +/- to avoid binary op ambiguity)
        prods.add(prod("PostParenAction", choice(
            seq(terminal("->"), nonTerminal("LambdaBody")),
            nonTerminal("UnaryExpressionNotPlusMinus")
        )));

        prods.add(prod("UnaryExpressionNotPlusMinus", choice(
            seq(terminal("~"), nonTerminal("UnaryExpression")),
            seq(terminal("!"), nonTerminal("UnaryExpression")),
            nonTerminal("PostfixExpression")
        )));

        // Inside parens: empty (no-arg lambda), primitive type (cast), or expression list.
        // Primitive types (int, long, etc.) are valid for casts like (int)x.
        // Expression list handles: (expr), (a, b) for multi-param lambdas,
        // and (Type name, Type name) for typed lambda params.
        prods.add(prod("ParenContent", optional(nonTerminal("ParenContentBody"))));

        prods.add(prod("ParenContentBody", choice(
            // Primitive type for casts: (int), (long), etc.
            nonTerminal("PrimitiveType"),
            // Expression (which may be just a type name), followed by:
            // - TypeArguments for generic cast: (Token<T>) or (Map<K,V>)
            // - comma-separated list for multi-param lambdas
            // - nothing for simple parens
            seq(nonTerminal("Expression"),
                optional(nonTerminal("ParenContentSuffix")))
        )));

        // After the first expression inside parens:
        prods.add(prod("ParenContentSuffix", choice(
            // Generic type args for cast: (Token<T>), (Map<K, V>), (List<? extends Foo>)
            seq(nonTerminal("TypeArguments"),
                optional(nonTerminal("Dims")),
                optional(seq(terminal("."), nonTerminal("ClassOrInterfaceType")))),
            // Multi-param lambda: (a, b) -> ... or (Type name, Type name) -> ...
            seq(terminal(","), nonTerminal("LambdaParam"),
                repeat(seq(terminal(","), nonTerminal("LambdaParam"))))
        )));

        // Lambda parameter in multi-param position: can be just name or Type name
        prods.add(prod("LambdaParam", seq(
            repeat(nonTerminal("Modifier")),
            nonTerminal("Expression")
        )));

        // Name-based expressions: identifier, possibly method call, possibly qualified
        // The optional method call handles standalone calls like process(item), doWork()
        prods.add(prod("NameExpression", seq(
            nonTerminal("Identifier"),
            optional(seq(terminal("->"), nonTerminal("LambdaBody"))),
            optional(seq(terminal("("), optional(nonTerminal("ArgumentList")), terminal(")"))),
            repeat(nonTerminal("NameSuffix"))
        )));

        prods.add(prod("NameSuffix", choice(
            // Method call or field access: .name or .name(args)
            seq(terminal("."), nonTerminal("NameSuffixDot")),
            // Array access [expr] or array method reference []::[new|name]
            seq(terminal("["), nonTerminal("BracketSuffix")),
            // Method reference: ::name or ::new
            seq(terminal("::"), nonTerminal("MethodRefTarget"))
        )));

        prods.add(prod("NameSuffixDot", choice(
            // .class literal
            terminal("class"),
            // .this or .super
            terminal("this"),
            terminal("super"),
            // .new
            seq(terminal("new"), nonTerminal("ClassCreatorRest")),
            // .name possibly with type args and method call
            seq(optional(nonTerminal("TypeArguments")),
                nonTerminal("Identifier"),
                optional(seq(terminal("("), optional(nonTerminal("ArgumentList")), terminal(")"))))
        )));

        prods.add(prod("MethodRefTarget", choice(
            terminal("new"),
            nonTerminal("Identifier")
        )));

        prods.add(prod("PrimarySuffix", choice(
            // Method call or field access: .name or .name(args) or .class/.this/.super
            seq(terminal("."), nonTerminal("PrimarySuffixDot")),
            // Array access [expr] or array method reference []::[new|name]
            seq(terminal("["), nonTerminal("BracketSuffix")),
            // Method reference: ::name or ::new
            seq(terminal("::"), optional(nonTerminal("TypeArguments")), nonTerminal("MethodRefTarget")),
            // Direct call: this(args), super(args), or chained calls like expr(args)
            seq(terminal("("), optional(nonTerminal("ArgumentList")), terminal(")"))
            // Note: '->' for lambdas is NOT here — it's in LambdaOrParenOrCast
            // to prevent expressions like `1 -> body` from being parsed as lambdas
        )));

        prods.add(prod("BracketSuffix", choice(
            // Empty bracket: ] — then optional dims and optional method reference
            // Handles both Type[]::method (method ref) and Type[] as array dims suffix
            seq(terminal("]"), optional(nonTerminal("Dims")),
                optional(seq(terminal("::"), optional(nonTerminal("TypeArguments")),
                    nonTerminal("MethodRefTarget")))),
            // Array access: Expression ]
            seq(nonTerminal("Expression"), terminal("]"))
        )));

        prods.add(prod("PrimarySuffixDot", choice(
            terminal("class"),
            terminal("this"),
            terminal("super"),
            seq(terminal("new"), nonTerminal("ClassCreatorRest")),
            seq(optional(nonTerminal("TypeArguments")),
                nonTerminal("Identifier"),
                optional(seq(terminal("("), optional(nonTerminal("ArgumentList")), terminal(")"))))
        )));

        prods.add(prod("LambdaBody", choice(
            nonTerminal("Block"),
            nonTerminal("Expression")
        )));

        prods.add(prod("NewExpression", seq(
            terminal("new"),
            nonTerminal("NewExpressionRest")
        )));

        // Left-factored: after 'new', parse optional type arguments and type,
        // then dispatch based on '(' (class instance) vs '[' (array creation).
        // Primitive types always go to array creation.
        prods.add(prod("NewExpressionRest", choice(
            // Primitive type → always array creation
            seq(nonTerminal("PrimitiveType"), terminal("["), nonTerminal("ArrayCreatorAfterBracket")),
            // Class type → could be instance creation or array creation
            nonTerminal("ClassCreatorRest")
        )));

        prods.add(prod("ClassCreatorRest", seq(
            optional(nonTerminal("TypeArguments")),
            nonTerminal("ClassOrInterfaceType"),
            nonTerminal("NewAfterClassType")
        )));

        // After class type: '(' for instance creation, '<' for diamond then '(',
        // or '[' for array creation
        prods.add(prod("NewAfterClassType", choice(
            // Array creation: new ClassName[expr] or new ClassName[] { init }
            seq(terminal("["), nonTerminal("ArrayCreatorAfterBracket")),
            // Instance creation with diamond: new ClassName<>(...) or new ClassName<Type>(...)
            seq(nonTerminal("TypeArguments"),
                terminal("("), optional(nonTerminal("ArgumentList")), terminal(")"),
                optional(nonTerminal("ClassBody"))),
            // Instance creation without diamond: new ClassName(...)
            seq(terminal("("), optional(nonTerminal("ArgumentList")), terminal(")"),
                optional(nonTerminal("ClassBody")))
        )));

        prods.add(prod("ArrayCreatorAfterBracket", choice(
            // new Type[] { init } or new Type[][] { init }
            seq(terminal("]"), nonTerminal("ArrayCreatorDimsOrInit")),
            // new Type[expr]... possibly followed by empty dims []
            seq(nonTerminal("Expression"), terminal("]"),
                repeat(nonTerminal("ArrayCreatorDimOrEmpty")))
        )));

        prods.add(prod("ArrayCreatorDimsOrInit", seq(
            repeat(seq(terminal("["), terminal("]"))),
            nonTerminal("ArrayInitializer")
        )));

        // After first [expr], each subsequent [ is either [expr] or start of trailing []
        prods.add(prod("ArrayCreatorDimOrEmpty", seq(
            terminal("["),
            nonTerminal("ArrayCreatorDimContent")
        )));

        prods.add(prod("ArrayCreatorDimContent", choice(
            // Empty dim []: ] then optional more []
            seq(terminal("]"), repeat(seq(terminal("["), terminal("]")))),
            // Filled dim [expr]: expression ]
            seq(nonTerminal("Expression"), terminal("]"))
        )));

        // Switch expression
        prods.add(prod("SwitchExpression", seq(
            terminal("switch"), terminal("("), nonTerminal("Expression"), terminal(")"),
            nonTerminal("SwitchBlock")
        )));

        prods.add(prod("ArgumentList", seq(
            nonTerminal("Expression"),
            repeat(seq(terminal(","), nonTerminal("Expression")))
        )));

        return Grammar.of("CompilationUnit", prods);
    }

    private static Production prod(String name, GrammarElement body) {
        return new Production(name, body);
    }
}
