import Libpetri.Spec.Text

requirement_text EVT_025
  id "EVT-025"
  title "Session Archive Format"
  priority SHOULD
  kind F
  body r#"Completed debug sessions can be serialized to a length-prefixed compressed archive (LZ4
for Java, gzip for TypeScript and Rust) for later replay. The archive has a versioned
header followed by one length-prefixed JSON record per event.

Three header versions exist; readers MUST accept all three and dispatch into the matching
sealed variant (`V1`/`V2`/`V3`) so callers can pattern-match on writer guarantees.

**Header format** (the same field names and JSON types in every language; the encoding of time values differs, see below):

| Header | First shipped | Adds over previous |
|---|---|---|
| v1 | libpetri 1.5.x | baseline: `sessionId`, `netName`, `dotDiagram`, `startTime`, `eventCount`, `structure` |
| v2 | libpetri 1.7.x | `endTime`, `tags`, pre-computed `metadata` (event-type histogram, first/last, hasErrors) |
| v3 | libpetri 1.8.0 | same fields as v2; bump signals typed-token event bodies |

**Event body format** (per-language, because each implementation serializes its
own event shape — Java serializes the `NetEvent` record directly, TypeScript and Rust
serialize a `NetEventInfo` debug-protocol projection). Archive bodies are therefore not
byte-compatible across languages, and neither are whole archives: Java compresses with LZ4 and
the others with gzip, and every time value (the header's `startTime` and `endTime`, the event and
token timestamps of the body) is ISO-8601 text in Java and TypeScript and decimal epoch
milliseconds in Rust and Python. The Rust reader rejects an archive whose event timestamps are
ISO-8601 text, and the TypeScript reader reads decimal epoch milliseconds as invalid dates, so an
archive is read correctly only by an implementation of the language that wrote it. All languages
agree on *semantic* content, not wire layout.

- **Java (v3):** `token: {valueType: <FQN>, v: <structured JSON>, createdAt: <iso>}`.
  Special cases: `{valueType: "void", createdAt}` for unit tokens (no `v`);
  `{valueType, text, createdAt}` fallback when Jackson cannot structure the value;
  legacy `{value, valueType: simpleName, createdAt}` from v1/v2 also accepted.
- **TypeScript (v3):** `token: {id, type, value: <String(value)>, structured?: <JSON>, timestamp}`.
  The `value` string is retained alongside the new optional `structured` field so the
  bundled debug UI keeps rendering without change. `type` is `value.constructor.name`
  (simple name — TypeScript has no portable FQN).
- **Rust (v3):** `token: {id, type, value, structured?, timestamp}`, with the field names and
  JSON shapes of TypeScript via a shared `NetEventInfo` camelCase serde contract; the
  `timestamp` is decimal epoch milliseconds where TypeScript writes ISO-8601 text. `type` is
  `std::any::type_name::<T>()` at token-erasure time; `structured` is populated by
  [`TokenProjectorRegistry`](../rust/libpetri-debug/src/token_projector_registry.rs)
  when the token's inner `T` is registered, else falls back to
  `{"type": <type_name>, "text": <Debug repr>}` — parallel to Java's `{valueType, text}`
  shape.

**Key order in an archive is not guaranteed, and [CORE-073]'s canonical order does not reach it.**
A JSON object is an *unordered* collection by definition, so an archive that renders a marking as
one carries no order regardless of what the producer did. Some implementations preserve insertion
order incidentally; JavaScript cannot, because it orders integer-like keys numerically ahead of
every other key whatever the insertion order — a net with a place named `2` reorders itself. The
JSON debug protocol is the same medium and is bound the same way.

This is a bound on the medium, not a defect to fix: canonical order is guaranteed **on the snapshot
form and on the event** ([CORE-073], [EVT-014]), which is where a host that hashes, diffs or
content-addresses should take it. A host needing a byte-stable archive artefact *across
implementations* MUST canonicalise at its own serialization boundary rather than relying on the
object's key order.

What the medium does not excuse is **irreproducibility**. An archive written twice by the same
implementation from identical run data MUST NOT differ ([CORE-073], [EVT-014] AC5). JavaScript's
numeric-first key order is arbitrary but fixed, so it satisfies this; a marking copied through a
per-process-randomised map does not, and an implementation MUST NOT put one on the path to the
archive or the debug protocol. This asks for no change of archive format.

⟦s1|*Where* an implementation provides session archives, *when* its reader reads a well-formed archive of header version 1, 2 or 3 in its own implementation's format (one whose `eventCount` and metadata are those of its body, as its writer writes them), the reader *shall* return the header variant of that version (`V1`, `V2` or `V3`).⟧

⟦s2|*Where* an implementation provides session archives, *if* its reader reads an archive in its own implementation's format whose header version is not 1, 2 or 3, *then* the reader *shall* reject the archive with the error `Unsupported archive version: <version> (reader supports 1..3)`, which names the version it found and the supported range.⟧

⟦s3|*Where* an implementation provides session archives, *when* its reader accepts a well-formed archive in its own implementation's format, it *shall* return the header's `eventCount` unchanged, the header's session fields and metadata as written, and one event for each record of the body, in body order.⟧

⟦s4|*Where* an implementation provides session archives, *when* its writer writes an archive of a session for header version 1, 2 or 3 (`writeV1`, `writeV2`, or `write` for version 3), the header *shall* carry that version and the session's own header fields.⟧

⟦s5|*Where* an implementation provides session archives, *when* its writer writes an archive, the writer *shall* take one snapshot of the event store, the header's `eventCount` *shall* be the number of events in that snapshot, a V1 header *shall* carry no metadata, the V2 and V3 metadata *shall* be computed from that snapshot, and the body *shall* hold one record for each event of that snapshot, in the order of the snapshot.⟧

⟦s6|*Where* an implementation provides session archives, two archives its writer writes for the same header version from identical run data *shall* be identical.⟧

⟦s7|*Where* an implementation provides session archives, its writer *shall* write an archive of any session for each of the header versions 1, 2 and 3 (`writeV1`, `writeV2`, and `write` for version 3), whatever the session's event store holds.⟧

**Acceptance Criteria:**
1. Each language's v3-capable writer defaults to emitting v3; `writeV1` / `writeV2` still
   exist and emit the corresponding header. The event body is always the writer's current
   token shape regardless of header version — byte-identical 1.7.x event bodies are not
   producible from 1.8.0+.
2. Each v3-capable reader reads v1, v2, and v3 archives; an archive with an unknown
   version is rejected with an error/exception that names the encountered version and
   the supported range.
3. Record, enum, boxed primitive, and unit tokens written under Java v3 round-trip with
   their original concrete type when the class is on the reader's classpath.
4. When a Java-side `valueType` FQN cannot be resolved (class not on classpath, shaded,
   cross-language write), the token hydrates as `Token<JsonNode>` — the deserializer
   never throws on unknown types.
5. TypeScript + Rust archives preserve the `structured` JSON payload across a full
   write→read round-trip; replay consumers receive `TokenInfo.structured` (TS) or a
   `ReplayedTokenPayload` on `NetEvent::TokenAdded`/`TokenRemoved` (Rust) carrying the
   same JSON shape the writer emitted.
6. Legacy (`{value, valueType: simpleName}`) tokens continue to hydrate as string-valued
   tokens on any v3-capable reader.
7. TypeScript archives omit the `structured` field entirely when it would be empty or
   unprojectable (wire size is neutral for unstructurable tokens).
8. The header `eventCount` field MUST equal the number of event records that follow in
   the body. Implementations MUST NOT populate `eventCount` from a cumulative lifetime
   counter on the event store; the value reflects retained body length only. After a
   write→read round-trip, `archive.eventCount() == archive.events().size()` for all
   three header versions and across all three language implementations. The writer
   MUST take exactly one snapshot of the event store; header `eventCount`, V2/V3
   metadata, and the event body MUST all derive from that single snapshot.

**Implementation notes:**
- Java: Full implementation — default writer emits v3, deserializer reconstructs original
  token types via `Class.forName`. The V2 and V3 header holds the tags and the metadata histogram
  in ascending code-point order of their keys, so two JVMs write the same header for the same run
  data.
- TypeScript: Full implementation — default writer emits v3, `structured` projection via
  `JSON.parse(JSON.stringify(value))`.
- Rust: Full implementation — default writer emits v3 via a user-supplied
  `TokenProjectorRegistry`; reader hydrates into a `ReplayedTokenPayload` exposing the
  `structured` JSON without attempting to revive the original `T` (Rust has no
  `Class.forName` equivalent).
- Python: `SessionArchiveWriter.write_from_store` writes version 3 through the Rust writer, and
  `write_v1` and `write_v2` write versions 1 and 2. Each archives every event of the store's
  snapshot, whatever its size, and a header whose `structure` lists the net's places and
  transitions. For an empty store the start time is 0 and there is no end time, so two archives of
  the same empty session are identical.

**Cross-language replay:** Java → Java reconstructs typed tokens. TypeScript and Rust
archive bodies share field names and JSON shapes (shared `NetEventInfo` contract) but not the
time encoding, so neither reader reads the other's archives correctly; both preserve `structured` across
a round-trip. Java archive bodies use a different shape
(`NetEvent` direct serialization) and are not interchangeable at the body level — use
language-native archives for full-fidelity replay.

**Security note:** Java v3 deserialization resolves the archive-supplied `valueType`
FQN via `Class.forName`. TypeScript's `structuredValue` uses
`JSON.parse(JSON.stringify(v))` — safe against code execution and prototype pollution,
but respects any `toJSON()` method on the value. Rust's `TokenProjectorRegistry`
projects only user-registered types; unregistered values fall back to `Debug` repr and
never execute arbitrary code. Archives are a trust boundary: **do not deserialize
archives from untrusted network sources** without a guard — in Java because of
static-initializer side effects, in TypeScript because a hostile `toJSON()` override
could return misleading data, and in Rust because a hostile archive could claim any
`type_name` string.

**Test derivation:**
- Java: `SessionArchiveV3Test` (record/enum/primitive/unit round-trip, v2-on-v3
  back-compat, unknown-version rejection) and `NetEventConverterTest.TokenInfoConversion`
  (structured field projection).
- TypeScript: `session-archive-v3.test.ts` (analogous round-trip) and
  `session-archive-v2.test.ts` (explicit v2 emission remains possible).
- Rust: `session_archive_reader::tests::v3_roundtrip_preserves_structured_token` (end-to-end
  writer→reader through `TokenProjectorRegistry`),
  `reader_accepts_v3_archives` (third-party v3 archive hydration), and
  `read_rejects_unsupported_version`."#
