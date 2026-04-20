package org.libpetri.debug;

import com.fasterxml.jackson.annotation.JsonSubTypes;
import com.fasterxml.jackson.annotation.JsonTypeInfo;
import com.fasterxml.jackson.core.JsonGenerator;
import com.fasterxml.jackson.core.JsonParser;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.DeserializationContext;
import com.fasterxml.jackson.databind.DeserializationFeature;
import com.fasterxml.jackson.databind.JsonDeserializer;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.SerializationFeature;
import com.fasterxml.jackson.databind.SerializerProvider;
import com.fasterxml.jackson.databind.module.SimpleModule;
import com.fasterxml.jackson.databind.ser.std.StdSerializer;
import com.fasterxml.jackson.datatype.jsr310.JavaTimeModule;

import org.libpetri.core.Token;
import org.libpetri.event.NetEvent;

import java.io.IOException;
import java.time.Instant;

/**
 * Jackson-based serializer for {@link NetEvent} records.
 *
 * <p>Uses a Jackson mixin to add polymorphic type information to the sealed NetEvent hierarchy.
 * Uses {@link JavaTimeModule} for {@link java.time.Instant} and {@link java.time.Duration}.
 *
 * <h2>Token value serialization (v3 archive format)</h2>
 * Token values are serialized as structured JSON so readers on the same classpath can
 * reconstruct the original type. The wire shape per token is:
 * <pre>
 *   {"valueType": "&lt;FQN&gt;", "v": &lt;structured JSON&gt;, "createdAt": "&lt;ISO-8601&gt;"}
 * </pre>
 * with these special cases:
 * <ul>
 *   <li>Unit tokens ({@link Token#unit()}): {@code {"valueType": "void", "createdAt": …}} —
 *       no {@code v} field.</li>
 *   <li>Enums: {@code v} is the enum's {@code name()}.</li>
 *   <li>Records / POJOs / primitives / strings: {@code v} is Jackson's default serialization.</li>
 *   <li>Non-structurable values (Jackson throws): fallback
 *       {@code {"valueType": "&lt;simpleName&gt;", "text": "&lt;toString&gt;", "createdAt": …}}.</li>
 * </ul>
 *
 * <h2>Backwards compatibility</h2>
 * The deserializer also accepts the v1/v2 legacy shape
 * {@code {"value": "&lt;toString&gt;", "valueType": "&lt;simpleName&gt;", "createdAt": …}}; such tokens
 * hydrate as {@code Token<String>} carrying the toString text — same behavior as libpetri ≤ 1.7.
 * When the v3 {@code valueType} FQN cannot be resolved on the current classpath (e.g. a Rust-
 * or TypeScript-written archive replayed in a Java-only environment), the deserializer emits
 * {@code Token<JsonNode>} carrying the raw payload tree so downstream display tools still see
 * a faithful rendering.
 *
 * <p>The underlying {@link ObjectMapper} is shared as a static singleton since it is
 * thread-safe once configured and benefits from internal caching (type resolution,
 * serializer lookup).
 *
 * <h2>Usage</h2>
 * <pre>{@code
 * var serializer = new NetEventSerializer();
 * byte[] bytes = serializer.serialize(event);
 * NetEvent deserialized = serializer.deserialize(bytes);
 * }</pre>
 *
 * @implNote v3 deserialization calls {@link Class#forName(String)} on the archive-supplied
 *     {@code valueType} FQN. Archives are trusted inputs in the libpetri debug pipeline
 *     (local sessions, explicitly shared replay files). <strong>Do not deserialize
 *     archives from untrusted network sources</strong> without wrapping the reader in a
 *     classloader allow-list — a hostile writer could pick an FQN whose static
 *     initializer has side effects. See {@link TokenDeserializer}.
 * @see NetEvent
 */
public final class NetEventSerializer {

    /**
     * Mixin that adds polymorphic type info to NetEvent without modifying the original class.
     */
    @JsonTypeInfo(use = JsonTypeInfo.Id.NAME, property = "@type")
    @JsonSubTypes({
        @JsonSubTypes.Type(value = NetEvent.ExecutionStarted.class, name = "ExecutionStarted"),
        @JsonSubTypes.Type(value = NetEvent.ExecutionCompleted.class, name = "ExecutionCompleted"),
        @JsonSubTypes.Type(value = NetEvent.TransitionEnabled.class, name = "TransitionEnabled"),
        @JsonSubTypes.Type(value = NetEvent.TransitionClockRestarted.class, name = "TransitionClockRestarted"),
        @JsonSubTypes.Type(value = NetEvent.TransitionStarted.class, name = "TransitionStarted"),
        @JsonSubTypes.Type(value = NetEvent.TransitionCompleted.class, name = "TransitionCompleted"),
        @JsonSubTypes.Type(value = NetEvent.TransitionFailed.class, name = "TransitionFailed"),
        @JsonSubTypes.Type(value = NetEvent.TransitionTimedOut.class, name = "TransitionTimedOut"),
        @JsonSubTypes.Type(value = NetEvent.ActionTimedOut.class, name = "ActionTimedOut"),
        @JsonSubTypes.Type(value = NetEvent.TokenAdded.class, name = "TokenAdded"),
        @JsonSubTypes.Type(value = NetEvent.TokenRemoved.class, name = "TokenRemoved"),
        @JsonSubTypes.Type(value = NetEvent.LogMessage.class, name = "LogMessage"),
        @JsonSubTypes.Type(value = NetEvent.MarkingSnapshot.class, name = "MarkingSnapshot"),
    })
    private interface NetEventMixin {}

    private static final ObjectMapper SHARED_MAPPER;

    static {
        SHARED_MAPPER = new ObjectMapper();
        SHARED_MAPPER.registerModule(new JavaTimeModule());
        SHARED_MAPPER.disable(SerializationFeature.WRITE_DATES_AS_TIMESTAMPS);
        // Token<?> values may contain arbitrary types — tolerate unknown properties on deserialization
        SHARED_MAPPER.disable(DeserializationFeature.FAIL_ON_UNKNOWN_PROPERTIES);
        SHARED_MAPPER.addMixIn(NetEvent.class, NetEventMixin.class);

        // Disabled mapper-wide because TokenSerializer re-enters this mapper via valueToTree()
        // to project arbitrary token values; opaque domain objects (no public getters) must
        // round-trip as "{}" instead of throwing and aborting the surrounding event. Treat
        // SHARED_MAPPER as reserved for debug payloads — reuse for protocol responses would
        // silently emit empty objects for beans that should have failed loud.
        SHARED_MAPPER.disable(SerializationFeature.FAIL_ON_EMPTY_BEANS);

        var tokenModule = new SimpleModule();
        tokenModule.addSerializer(Token.class, new TokenSerializer());
        tokenModule.addDeserializer(Token.class, new TokenDeserializer());
        SHARED_MAPPER.registerModule(tokenModule);
    }

    /**
     * Writes {@link Token} values in the v3 wire format. See class-level Javadoc for the
     * full wire shape; in short: {@code {valueType: <FQN>, v: <payload>, createdAt: <iso>}}
     * with {@code {valueType: "void"}} for unit tokens and a {@code text} fallback for
     * values Jackson cannot structure.
     *
     * <p>The write path pre-serializes the value into a {@link JsonNode} via
     * {@link ObjectMapper#valueToTree} so that a mid-value Jackson failure does not leave
     * the generator stranded inside an unterminated object. This costs one extra tree
     * allocation per token — acceptable on the archive write path, which is not a
     * benchmarked hot loop.
     */
    private static final class TokenSerializer extends StdSerializer<Token> {
        private TokenSerializer() {
            super(Token.class);
        }

        @Override
        public void serialize(Token token, JsonGenerator gen, SerializerProvider provider) throws IOException {
            Object value = token.value();
            gen.writeStartObject();
            if (value == null) {
                // Unit token — Token.of() requires non-null, so null == Token.unit().
                gen.writeStringField("valueType", "void");
            } else if (value instanceof Enum<?> e) {
                gen.writeStringField("valueType", value.getClass().getName());
                gen.writeStringField("v", e.name());
            } else {
                gen.writeStringField("valueType", value.getClass().getName());
                JsonNode vNode;
                try {
                    vNode = SHARED_MAPPER.valueToTree(value);
                } catch (RuntimeException ex) {
                    vNode = null;
                }
                if (vNode != null) {
                    gen.writeFieldName("v");
                    gen.writeTree(vNode);
                } else {
                    gen.writeStringField("text", String.valueOf(value));
                }
            }
            provider.defaultSerializeField("createdAt", token.createdAt(), gen);
            gen.writeEndObject();
        }
    }

    /**
     * Reads {@link Token} values, accepting every format the project has ever emitted:
     * <ul>
     *   <li><b>v3</b> structured shape ({@code valueType} FQN + {@code v} payload) — reconstructs the
     *       original type when the class is on the classpath.</li>
     *   <li><b>v3 fallback</b> shape ({@code valueType} + {@code text}) — writer could not structure
     *       the value; hydrated as {@code Token<String>}.</li>
     *   <li><b>v1/v2 legacy</b> shape ({@code value} + simple-name {@code valueType}) — hydrated as
     *       {@code Token<String>} carrying the original {@code toString()}.</li>
     *   <li><b>void / null</b> — hydrated as {@link Token#unit()}.</li>
     * </ul>
     *
     * <p>When the FQN in {@code valueType} cannot be resolved (class not on classpath,
     * cross-language archive, shaded renames), the deserializer emits a {@code Token<JsonNode>}
     * so tools can still render the payload without losing information.
     *
     * @implNote Uses {@link Class#forName(String)} on the archive-supplied FQN. See the
     *     {@code @implNote} on {@link NetEventSerializer} for the trust-boundary contract.
     */
    private static final class TokenDeserializer extends JsonDeserializer<Token<?>> {
        @Override
        public Token<?> deserialize(JsonParser p, DeserializationContext ctx) throws IOException {
            JsonNode root = p.readValueAsTree();
            Instant createdAt = readCreatedAt(root);

            // v1/v2 legacy shape: {"value": "<toString>", "valueType": "<simpleName>", ...}
            // New v3 shape never includes a top-level "value" string (structured goes in "v").
            if (root.has("value") && !root.has("v")) {
                var v = root.get("value");
                return new Token<>(v.isNull() ? null : v.asText(), createdAt);
            }

            String valueType = root.hasNonNull("valueType") ? root.get("valueType").asText() : null;
            if (valueType == null || "void".equals(valueType) || "null".equals(valueType)) {
                return new Token<>(null, createdAt);
            }

            // v3 fallback shape: {"valueType": ..., "text": ...} — writer couldn't structure it.
            if (root.has("text") && !root.has("v")) {
                return new Token<>(root.get("text").asText(), createdAt);
            }

            JsonNode vNode = root.get("v");
            if (vNode == null || vNode.isNull()) {
                return new Token<>(null, createdAt);
            }

            try {
                Class<?> cls = Class.forName(valueType);
                if (cls.isEnum()) {
                    @SuppressWarnings({"unchecked", "rawtypes"})
                    Object enumVal = Enum.valueOf((Class<? extends Enum>) cls, vNode.asText());
                    return new Token<>(enumVal, createdAt);
                }
                Object value = SHARED_MAPPER.treeToValue(vNode, cls);
                return new Token<>(value, createdAt);
            } catch (ClassNotFoundException | IllegalArgumentException | JsonProcessingException ex) {
                // Class not on classpath or mapping failed — surface the raw JsonNode so display
                // tools still see a faithful rendering, and replay consumers see a clear type.
                return new Token<>(vNode, createdAt);
            }
        }

        private static Instant readCreatedAt(JsonNode root) {
            if (!root.hasNonNull("createdAt")) return null;
            try {
                return SHARED_MAPPER.treeToValue(root.get("createdAt"), Instant.class);
            } catch (JsonProcessingException e) {
                return null;
            }
        }
    }

    public NetEventSerializer() {
    }

    /**
     * Serializes a NetEvent to JSON bytes.
     *
     * @param event the event to serialize
     * @return JSON bytes
     * @throws NetEventSerializationException if serialization fails
     */
    public byte[] serialize(NetEvent event) {
        try {
            return SHARED_MAPPER.writeValueAsBytes(event);
        } catch (JsonProcessingException e) {
            throw new NetEventSerializationException("Failed to serialize event: " + event.getClass().getSimpleName(), e);
        }
    }

    /**
     * Deserializes a NetEvent from JSON bytes.
     *
     * @param bytes the JSON bytes
     * @return the deserialized event
     * @throws NetEventSerializationException if deserialization fails
     */
    public NetEvent deserialize(byte[] bytes) {
        try {
            return SHARED_MAPPER.readValue(bytes, NetEvent.class);
        } catch (Exception e) {
            throw new NetEventSerializationException("Failed to deserialize event", e);
        }
    }

    /**
     * Serializes a NetEvent directly into the given output stream.
     *
     * <p>Unlike {@link #serialize(NetEvent)}, this avoids an intermediate {@code byte[]} allocation.
     * The stream is flushed but <em>not</em> closed.
     *
     * @param event the event to serialize
     * @param out the output stream to write to
     * @throws NetEventSerializationException if serialization fails
     */
    public void serializeTo(NetEvent event, java.io.OutputStream out) {
        try {
            SHARED_MAPPER.writeValue(out, event);
        } catch (java.io.IOException e) {
            throw new NetEventSerializationException("Failed to serialize: " + event.getClass().getSimpleName(), e);
        }
    }

    /**
     * Deserializes a NetEvent from a region of a byte array.
     *
     * @param bytes the byte array
     * @param offset start offset
     * @param length number of bytes to read
     * @return the deserialized event
     * @throws NetEventSerializationException if deserialization fails
     */
    public NetEvent deserialize(byte[] bytes, int offset, int length) {
        try {
            return SHARED_MAPPER.readValue(bytes, offset, length, NetEvent.class);
        } catch (Exception e) {
            throw new NetEventSerializationException("Failed to deserialize event", e);
        }
    }

    /**
     * Returns the underlying ObjectMapper for testing or advanced use.
     *
     * @return the ObjectMapper
     */
    ObjectMapper mapper() {
        return SHARED_MAPPER;
    }

    /**
     * Exception thrown when serialization or deserialization fails.
     */
    public static class NetEventSerializationException extends RuntimeException {
        public NetEventSerializationException(String message, Throwable cause) {
            super(message, cause);
        }
    }
}
