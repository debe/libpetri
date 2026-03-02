package org.libpetri.core;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Marks a class or field that defines a static Petri net structure.
 *
 * <p>This annotation enables compile-time visualization of Petri nets.
 * The annotation processor scans for fields annotated with {@code @NetStructure}
 * and generates DOT/SVG diagrams that are embedded in the Javadoc.
 *
 * <h2>Usage</h2>
 * <pre>{@code
 * public class MyWorkflowNet {
 *
 *     public static final Place<Request> REQUEST = Place.of("Request", Request.class);
 *     public static final Place<Response> RESPONSE = Place.of("Response", Response.class);
 *
 *     @NetStructure
 *     public static final PetriNet STRUCTURE = PetriNet.builder("MyWorkflow")
 *         .transitions(
 *             Transition.builder("Process")
 *                 .input(REQUEST)
 *                 .output(RESPONSE)
 *                 .deadline(5000)
 *                 .build()
 *         )
 *         .build();
 * }
 * }</pre>
 *
 * <h2>Generated Documentation</h2>
 * The annotation processor generates:
 * <ul>
 *   <li>An inline SVG diagram in the generated Javadoc</li>
 *   <li>Javadoc snippet that can be included via {@code @include}</li>
 * </ul>
 *
 * <h2>Binding Actions at Runtime</h2>
 * After defining the static structure, use {@link PetriNet#bindActions} to
 * attach runtime behavior:
 * <pre>{@code
 * @Produces
 * public PetriNet myWorkflow(MyService service) {
 *     return MyWorkflowNet.STRUCTURE.bindActions(Map.of(
 *         "Process", (in, out) -> service.process(in.value(REQUEST))
 *             .thenAccept(r -> out.add(RESPONSE, r))
 *     ));
 * }
 * }</pre>
 *
 * @see PetriNet#bindActions
 */
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.FIELD, ElementType.TYPE})
public @interface NetStructure {

    /**
     * Optional name for the generated documentation.
     * Defaults to the field/class name.
     */
    String value() default "";

    /**
     * Description to include in generated documentation.
     */
    String description() default "";
}
