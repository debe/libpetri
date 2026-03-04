package org.libpetri.debug;

import com.fasterxml.jackson.annotation.JsonSubTypes;
import com.fasterxml.jackson.annotation.JsonTypeInfo;
import com.fasterxml.jackson.core.JsonGenerator;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.DeserializationFeature;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.SerializationFeature;
import com.fasterxml.jackson.databind.SerializerProvider;
import com.fasterxml.jackson.databind.module.SimpleModule;
import com.fasterxml.jackson.databind.ser.std.StdSerializer;
import com.fasterxml.jackson.datatype.jsr310.JavaTimeModule;

import org.libpetri.core.Token;
import org.libpetri.event.NetEvent;

import java.io.IOException;

/**
 * Jackson-based serializer for {@link NetEvent} records.
 *
 * <p>Uses a Jackson mixin to add polymorphic type information to the sealed NetEvent hierarchy.
 * Uses {@link JavaTimeModule} for {@link java.time.Instant} and {@link java.time.Duration}.
 * Token values are serialized via {@code toString()} for pragmatic debug use.
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

        // Token values are serialized via toString() for pragmatic debug use (see class Javadoc).
        // This avoids Jackson failing on domain objects without public getters or annotations.
        var tokenModule = new SimpleModule();
        tokenModule.addSerializer(Token.class, new StdSerializer<Token>(Token.class) {
            @Override
            public void serialize(Token token, JsonGenerator gen, SerializerProvider provider) throws IOException {
                gen.writeStartObject();
                Object value = token.value();
                gen.writeStringField("value", value != null ? value.toString() : null);
                gen.writeStringField("valueType", value != null ? value.getClass().getSimpleName() : "null");
                provider.defaultSerializeField("createdAt", token.createdAt(), gen);
                gen.writeEndObject();
            }
        });
        SHARED_MAPPER.registerModule(tokenModule);
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
