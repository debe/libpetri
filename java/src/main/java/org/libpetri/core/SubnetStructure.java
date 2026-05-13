package org.libpetri.core;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Marks a field that holds a static {@link SubnetDef} or {@link Instance}
 * for documentation tooling (sibling to {@link NetStructure}).
 *
 * <p>This annotation is the entry point for the javadoc taglet's
 * subnet-aware rendering: a {@code SubnetDef<?>} field is drawn with its
 * interface ports highlighted at the cluster boundary; an {@code Instance<?>}
 * field is drawn with the instance prefix label and {@code params()} summary
 * in the cluster header. (The taglet extension itself ships in a later task —
 * this annotation is the marker so users can adopt it incrementally.)
 *
 * <h2>Usage</h2>
 * <pre>{@code
 * public class BoundedBufferLib {
 *
 *     @SubnetStructure
 *     public static final SubnetDef<Void> BOUNDED_BUFFER = SubnetDef.builder("BoundedBuffer")
 *         .transitions(enqueue, dequeue)
 *         .inputPort("put", incomingPlace)
 *         .outputPort("get", outgoingPlace)
 *         .build();
 * }
 * }</pre>
 *
 * @see NetStructure
 * @see SubnetDef
 * @see Instance
 */
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.FIELD)
public @interface SubnetStructure {

    /**
     * Optional name for the generated documentation.
     * Defaults to the field name.
     */
    String value() default "";

    /**
     * Description to include in generated documentation.
     */
    String description() default "";
}
