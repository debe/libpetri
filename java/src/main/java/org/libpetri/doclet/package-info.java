/**
 * Javadoc taglets for compile-time Petri net visualization.
 *
 * <h2>Overview</h2>
 * <p>This package provides custom Javadoc taglets that generate DOT diagrams
 * from static {@link org.libpetri.core.PetriNet} definitions. The DOT source
 * is embedded in the generated Javadoc HTML alongside the canonical
 * {@code LibpetriViewer} bundle, which renders DOT &rarr; SVG client-side
 * (via an embedded Graphviz WASM build) and wires interactive pan/zoom plus
 * cluster legend, filter, and collapse chrome.
 *
 * <h2>Taglets</h2>
 * <dl>
 *   <dt>{@link org.libpetri.doclet.PetriNetTaglet @petrinet}</dt>
 *   <dd>Auto-generates an interactive diagram from a static PetriNet,
 *       SubnetDef, or Instance field.
 *       Usage: {@code @petrinet FIELD_NAME} or {@code @petrinet ClassName.FIELD_NAME}</dd>
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
 * <h2>Maven Configuration</h2>
 * <pre>{@code
 * <plugin>
 *     <groupId>org.apache.maven.plugins</groupId>
 *     <artifactId>maven-javadoc-plugin</artifactId>
 *     <configuration>
 *         <additionalOptions>--enable-preview --allow-script-in-comments</additionalOptions>
 *         <taglets>
 *             <taglet>
 *                 <tagletClass>org.libpetri.doclet.PetriNetTaglet</tagletClass>
 *             </taglet>
 *         </taglets>
 *         <tagletpath>${project.build.outputDirectory}</tagletpath>
 *     </configuration>
 * </plugin>
 * }</pre>
 *
 * @see org.libpetri.core.NetStructure
 * @see org.libpetri.core.PetriNet#bindActions
 * @see org.libpetri.export.DotExporter
 */
package org.libpetri.doclet;
