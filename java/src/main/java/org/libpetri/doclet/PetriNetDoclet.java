package org.libpetri.doclet;

import jdk.javadoc.doclet.Doclet;
import jdk.javadoc.doclet.DocletEnvironment;
import jdk.javadoc.doclet.Reporter;

import javax.lang.model.SourceVersion;
import javax.lang.model.element.Element;
import javax.lang.model.element.ElementKind;
import javax.lang.model.element.Modifier;
import javax.lang.model.element.TypeElement;
import javax.lang.model.element.VariableElement;
import javax.tools.Diagnostic;
import java.io.IOException;
import java.io.PrintWriter;
import java.lang.reflect.Field;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;

import org.libpetri.core.NetStructure;
import org.libpetri.core.PetriNet;
import org.libpetri.export.MermaidExporter;

/**
 * Javadoc Doclet that generates Mermaid diagrams for PetriNet structures.
 *
 * <p>This doclet scans for fields annotated with {@link NetStructure} and
 * generates Mermaid flowchart diagrams. The diagrams are written to the
 * output directory and can be embedded in documentation.
 *
 * <h2>Usage</h2>
 * Run with Gradle javadoc task:
 * <pre>
 * javadoc {
 *     options.doclet = 'org.libpetri.doclet.PetriNetDoclet'
 *     options.docletpath = configurations.runtimeClasspath.files.toList()
 * }
 * </pre>
 *
 * <h2>Output</h2>
 * For each {@code @NetStructure} annotated field, generates:
 * <ul>
 *   <li>{@code <ClassName>_<FieldName>.mmd} - Mermaid diagram source</li>
 *   <li>{@code <ClassName>_<FieldName>.html} - HTML page with rendered diagram</li>
 * </ul>
 */
public class PetriNetDoclet implements Doclet {

    private Reporter reporter;
    private String outputDir = ".";

    @Override
    public void init(Locale locale, Reporter reporter) {
        this.reporter = reporter;
    }

    @Override
    public String getName() {
        return "PetriNetDoclet";
    }

    @Override
    public Set<? extends Option> getSupportedOptions() {
        return Set.of(
            new Option("-d", true, "Output directory", "<directory>") {
                @Override
                public boolean process(String option, List<String> arguments) {
                    outputDir = arguments.getFirst();
                    return true;
                }
            }
        );
    }

    @Override
    public SourceVersion getSupportedSourceVersion() {
        return SourceVersion.latest();
    }

    @Override
    public boolean run(DocletEnvironment environment) {
        reporter.print(Diagnostic.Kind.NOTE, "PetriNetDoclet: Scanning for @NetStructure annotations...");

        var outputPath = Path.of(outputDir, "petrinet-diagrams");
        try {
            Files.createDirectories(outputPath);
        } catch (IOException e) {
            reporter.print(Diagnostic.Kind.ERROR, "Cannot create output directory: " + e.getMessage());
            return false;
        }

        int diagramCount = 0;

        for (Element element : environment.getIncludedElements()) {
            if (element.getKind() == ElementKind.CLASS || element.getKind() == ElementKind.INTERFACE) {
                var typeElement = (TypeElement) element;

                // Check class-level annotation
                var classAnnotation = typeElement.getAnnotation(NetStructure.class);
                if (classAnnotation != null) {
                    // Look for static PetriNet fields
                    for (var enclosed : typeElement.getEnclosedElements()) {
                        if (enclosed.getKind() == ElementKind.FIELD) {
                            var field = (VariableElement) enclosed;
                            if (isPetriNetField(field)) {
                                if (generateDiagram(typeElement, field, outputPath)) {
                                    diagramCount++;
                                }
                            }
                        }
                    }
                }

                // Check field-level annotations
                for (var enclosed : typeElement.getEnclosedElements()) {
                    if (enclosed.getKind() == ElementKind.FIELD) {
                        var field = (VariableElement) enclosed;
                        var fieldAnnotation = field.getAnnotation(NetStructure.class);
                        if (fieldAnnotation != null && isPetriNetField(field)) {
                            if (generateDiagram(typeElement, field, outputPath)) {
                                diagramCount++;
                            }
                        }
                    }
                }
            }
        }

        reporter.print(Diagnostic.Kind.NOTE,
            "PetriNetDoclet: Generated " + diagramCount + " diagram(s) in " + outputPath);

        // Generate index
        if (diagramCount > 0) {
            generateIndex(outputPath);
        }

        return true;
    }

    private boolean isPetriNetField(VariableElement field) {
        var modifiers = field.getModifiers();
        return modifiers.contains(Modifier.STATIC)
            && modifiers.contains(Modifier.FINAL)
            && field.asType().toString().contains("PetriNet");
    }

    private boolean generateDiagram(TypeElement type, VariableElement field, Path outputPath) {
        var className = type.getQualifiedName().toString();
        var fieldName = field.getSimpleName().toString();

        reporter.print(Diagnostic.Kind.NOTE,
            "PetriNetDoclet: Processing " + className + "." + fieldName);

        try {
            // Load the class and get the field value
            var clazz = Class.forName(className);
            var javaField = clazz.getDeclaredField(fieldName);
            javaField.setAccessible(true);
            var petriNet = (PetriNet) javaField.get(null);

            if (petriNet == null) {
                reporter.print(Diagnostic.Kind.WARNING,
                    "Field " + fieldName + " is null, skipping");
                return false;
            }

            // Generate Mermaid diagram
            var mermaid = MermaidExporter.export(petriNet);
            var baseName = type.getSimpleName() + "_" + fieldName;

            // Write .mmd file
            var mmdFile = outputPath.resolve(baseName + ".mmd");
            Files.writeString(mmdFile, mermaid);

            // Write HTML file with embedded diagram
            var htmlFile = outputPath.resolve(baseName + ".html");
            Files.writeString(htmlFile, generateHtml(petriNet.name(), mermaid));

            reporter.print(Diagnostic.Kind.NOTE,
                "PetriNetDoclet: Generated " + mmdFile + " and " + htmlFile);

            return true;

        } catch (ClassNotFoundException e) {
            reporter.print(Diagnostic.Kind.WARNING,
                "Cannot load class " + className + ": " + e.getMessage());
        } catch (NoSuchFieldException e) {
            reporter.print(Diagnostic.Kind.WARNING,
                "Cannot find field " + fieldName + ": " + e.getMessage());
        } catch (IllegalAccessException e) {
            reporter.print(Diagnostic.Kind.WARNING,
                "Cannot access field " + fieldName + ": " + e.getMessage());
        } catch (IOException e) {
            reporter.print(Diagnostic.Kind.ERROR,
                "Cannot write diagram: " + e.getMessage());
        }

        return false;
    }

    private String generateHtml(String netName, String mermaid) {
        return """
            <!DOCTYPE html>
            <html>
            <head>
                <meta charset="UTF-8">
                <title>%s - Petri Net Diagram</title>
                <script src="https://cdn.jsdelivr.net/npm/mermaid/dist/mermaid.min.js"></script>
                <style>
                    body {
                        font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
                        max-width: 1200px;
                        margin: 0 auto;
                        padding: 20px;
                        background: #f5f5f5;
                    }
                    h1 {
                        color: #333;
                        border-bottom: 2px solid #007bff;
                        padding-bottom: 10px;
                    }
                    .diagram-container {
                        background: white;
                        border-radius: 8px;
                        padding: 20px;
                        box-shadow: 0 2px 4px rgba(0,0,0,0.1);
                    }
                    .mermaid {
                        display: flex;
                        justify-content: center;
                    }
                    pre {
                        background: #282c34;
                        color: #abb2bf;
                        padding: 15px;
                        border-radius: 8px;
                        overflow-x: auto;
                    }
                    details {
                        margin-top: 20px;
                    }
                    summary {
                        cursor: pointer;
                        font-weight: bold;
                        color: #007bff;
                    }
                </style>
            </head>
            <body>
                <h1>%s</h1>
                <div class="diagram-container">
                    <div class="mermaid">
            %s
                    </div>
                </div>
                <details>
                    <summary>View Mermaid Source</summary>
                    <pre>%s</pre>
                </details>
                <script>
                    mermaid.initialize({ startOnLoad: true, theme: 'default' });
                </script>
            </body>
            </html>
            """.formatted(netName, netName, mermaid, escapeHtml(mermaid));
    }

    private String escapeHtml(String text) {
        return text.replace("&", "&amp;")
            .replace("<", "&lt;")
            .replace(">", "&gt;");
    }

    private void generateIndex(Path outputPath) {
        try {
            var files = Files.list(outputPath)
                .filter(p -> p.toString().endsWith(".html") && !p.getFileName().toString().equals("index.html"))
                .sorted()
                .toList();

            var links = new StringBuilder();
            for (var file : files) {
                var name = file.getFileName().toString().replace(".html", "").replace("_", ".");
                links.append("        <li><a href=\"%s\">%s</a></li>\n"
                    .formatted(file.getFileName(), name));
            }

            var indexHtml = """
                <!DOCTYPE html>
                <html>
                <head>
                    <meta charset="UTF-8">
                    <title>Petri Net Diagrams</title>
                    <style>
                        body {
                            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
                            max-width: 800px;
                            margin: 0 auto;
                            padding: 20px;
                        }
                        h1 { color: #333; }
                        ul { list-style-type: none; padding: 0; }
                        li { margin: 10px 0; }
                        a {
                            color: #007bff;
                            text-decoration: none;
                            font-size: 1.1em;
                        }
                        a:hover { text-decoration: underline; }
                    </style>
                </head>
                <body>
                    <h1>Petri Net Diagrams</h1>
                    <ul>
                %s
                    </ul>
                </body>
                </html>
                """.formatted(links);

            Files.writeString(outputPath.resolve("index.html"), indexHtml);

        } catch (IOException e) {
            reporter.print(Diagnostic.Kind.WARNING,
                "Cannot generate index: " + e.getMessage());
        }
    }

    /**
     * Abstract base for doclet options.
     */
    private abstract static class Option implements Doclet.Option {
        private final String name;
        private final boolean hasArg;
        private final String description;
        private final String parameters;

        Option(String name, boolean hasArg, String description, String parameters) {
            this.name = name;
            this.hasArg = hasArg;
            this.description = description;
            this.parameters = parameters;
        }

        @Override
        public int getArgumentCount() {
            return hasArg ? 1 : 0;
        }

        @Override
        public String getDescription() {
            return description;
        }

        @Override
        public Kind getKind() {
            return Kind.STANDARD;
        }

        @Override
        public List<String> getNames() {
            return List.of(name);
        }

        @Override
        public String getParameters() {
            return parameters;
        }
    }
}
