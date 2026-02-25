/**
 * Javadoc taglets for compile-time Petri net visualization.
 *
 * <h2>Overview</h2>
 * <p>This package provides custom Javadoc taglets that generate Mermaid diagrams
 * from static {@link org.libpetri.core.PetriNet} definitions. The diagrams
 * are embedded directly in the generated Javadoc HTML and rendered via Mermaid.js.
 *
 * <h2>Taglets</h2>
 * <dl>
 *   <dt>{@link org.libpetri.doclet.PetriNetTaglet @petrinet}</dt>
 *   <dd>Auto-generates Mermaid diagram from a static PetriNet field.
 *       Usage: {@code @petrinet FIELD_NAME} or {@code @petrinet ClassName.FIELD_NAME}</dd>
 *
 *   <dt>{@link org.libpetri.doclet.MermaidTaglet @mermaid}</dt>
 *   <dd>Embeds raw Mermaid code in Javadoc. Usage: {@code @mermaid flowchart TB; A --> B}</dd>
 * </dl>
 *
 * <h2>Design Pattern: Static Structure + Runtime Actions</h2>
 * <p>The taglet system enables a clean separation between:
 * <ul>
 *   <li><b>Static structure</b> - Places, transitions, arcs, timing intervals (compile-time)</li>
 *   <li><b>Runtime actions</b> - CDI-injected behavior bound via {@code PetriNet.bindActions()}</li>
 * </ul>
 *
 * <h3>Example</h3>
 * <pre>{@code
 * /**
 *  * Workflow documentation.
 *  * @petrinet STRUCTURE
 *  *{@literal /}
 * @NetStructure
 * public class MyWorkflow {
 *
 *     // Static structure - visible at compile time, analyzable, documentable
 *     public static final PetriNet STRUCTURE = PetriNet.builder("Workflow")
 *         .transitions(
 *             Transition.builder("Process").input(REQUEST).output(RESPONSE).build()
 *         )
 *         .build();
 *
 *     // Runtime binding with CDI-injected services
 *     @Produces
 *     public PetriNet workflow(MyService service) {
 *         return STRUCTURE.bindActions(Map.of(
 *             "Process", (in, out) -> service.process(in.value(REQUEST))
 *                 .thenAccept(r -> out.add(RESPONSE, r))
 *         ));
 *     }
 * }
 * }</pre>
 *
 * <h2>Gradle Configuration</h2>
 * <pre>
 * javadoc {
 *     options {
 *         taglets 'org.libpetri.doclet.MermaidTaglet'
 *         taglets 'org.libpetri.doclet.PetriNetTaglet'
 *         tagletPath = files(sourceSets.main.output.classesDirs, configurations.runtimeClasspath)
 *         addBooleanOption('-allow-script-in-comments', true)
 *         addStringOption('header', '&lt;script src="https://cdn.jsdelivr.net/npm/mermaid@10/dist/mermaid.min.js"&gt;&lt;/script&gt;' +
 *             '&lt;script&gt;mermaid.initialize({startOnLoad:true});&lt;/script&gt;')
 *     }
 *     dependsOn classes
 * }
 * </pre>
 *
 * <h2>Viewing Diagrams</h2>
 * <pre>
 * ./gradlew viewPetriNets   # Generates Javadoc and opens in browser
 * </pre>
 *
 * @see org.libpetri.core.NetStructure
 * @see org.libpetri.core.PetriNet#bindActions
 * @see org.libpetri.export.MermaidExporter
 */
package org.libpetri.doclet;
