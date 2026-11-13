import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryStore
import Libpetri.Reference.Archive
import Libpetri.Reference.Snapshot
import Libpetri.Spec.Text.EVT_025

set_option linter.missingDocs true

/-!
# EVT-025: Session Archive Format (`spec/08-events-observability.md`)

A session archive is a versioned header followed by one record per event. The requirement is a
predicate over an abstract archive codec `C : ArchiveCodec D E` (glossary in
`Reference/Archive.lean`): the writer, a relation from a store, its history, the operations that
run during the write, the header version asked for and the session's own header fields to the
archives it can write; and the reader, a function from an archive to its result or an error.
Header fields and records are compared up to same content (`SameContent`: the same JSON value,
read as an unordered object), since key order in an archive is not guaranteed.

The lines are the behaviour sentences of the requirement: the reader dispatches every
well-formed archive of versions 1 to 3 into its variant and rejects any other version with a
message naming it; the reader returns the header as written and one event per record, in body
order; the writer writes the version it is asked for and the session's own fields; the header
count, the metadata and the body come from one snapshot of the store; two writes from identical
run data give the same archive; and the writer writes every version for every session. The
bytes, the compression and the per-language token shapes are configuration (kind N) and stay
outside the model.

The witness is the reference codec `refArchive`. The wrong codecs are a reader of the current
version only, a reader that takes version 99 for version 3, a reader that skips records it
cannot hydrate, a writer whose `writeV1` writes the version number 3, a writer that writes
another session's fields, a writer that takes the count from the store's lifetime counter, a
writer that reads the store twice, a writer that renders the header's tags in a per-process
order, and a writer that refuses a store that has evicted (one or more per line). A reader that
loses the metadata, a reader that reverses the events, a writer that writes empty metadata, a
writer that renders a marking in a per-process order, a writer that copies the store through a
bounded store first and a writer of version 3 only are forbidden too; a writer that renders
every marking in one fixed key order and a reader that rejects an archive whose count disagrees
with its body are allowed. Three are the behaviour the runtime defect ledger recorded (RD-17
to RD-19 in `spec/runtime-defects.md`): a header that renders the metadata histogram and the
tags through Java's `Map.copyOf`, whose iteration order changes per JVM, a writer that copies the
store into a debug store of capacity 10,000 before writing, and a binding that offers no
`writeV1` or `writeV2`.
-/

namespace Libpetri.Spec

open Libpetri.Reference

/-! ## EVT-025: Session Archive Format -/

requirement EVT_025
  id "EVT-025"
  title "Session Archive Format"
  kind F
  scope "where an implementation provides session archives: the Java, TypeScript and Rust SessionArchiveWriter and SessionArchiveReader, and Python's, which run Rust's"
  source verbatim "spec/08-events-observability.md"
  covers EVT_025.s1, EVT_025.s2, EVT_025.s3, EVT_025.s4, EVT_025.s5, EVT_025.s6, EVT_025.s7
  reading "For every archive codec C (an implementation's writer and reader) over session header fields D and events E, each with its notion of same content (the same JSON value, read as an unordered object):"
          "for every well-formed archive a (its version is that of a variant w, and its eventCount, its metadata and its body come from one list of events l as the writer forms them), the reader returns a result whose variant is the variant of a's version;"
          "for every archive a whose header version v is not 1, 2 or 3, the reader fails with the message Unsupported archive version: v (reader supports 1..3);"
          "there is one hydration function η such that, whenever the reader returns r for a well-formed archive a, r carries the eventCount of a, the events η applied to each record of a in body order, header fields of the same content as those of a, and the metadata of a;"
          "every archive the writer writes for version w and session fields d carries the number of w as its version and header fields of the same content as d;"
          "for every archive a the writer writes for version w from a store S with history h while the operations dh run, some list l that a call of events() on S returns during the write is the source of all of a: the eventCount of a is the length of l, the metadata of a is that of l for w (none for V1), and the body of a is, record by record, of the same content as l;"
          "two archives the writer writes for the same version and session fields, from the same store and history with no operation during the write, are equal;"
          "for every store, history, operations during the write, version and session fields, the writer writes some archive."
  assumes "The model is an archive codec C : ArchiveCodec D E (glossary in Reference/Archive.lean: Archive codec, Session archive, Same content, Well-formed archive). Its writer is a relation, write S h dh w d a: writing header version w for a session with header fields d, whose event store S has the history h when the write starts and runs the operations dh during the write, can produce the archive a. Its reader is a function, read a. An archive is the header version tag as written (a number, since a reader can meet any number), the session's own header fields (opaque: session id, net name, DOT diagram, start and end time, tags, net structure), eventCount, the V2/V3 metadata and the body. A record is the event it records, as rendered. The store is the glossary's StoreObs, so the lines hold for any store a session has: an in-memory store, the bounded debug store of a debug session (EVT-024), or another."
          "Same content (SameContent) is how the key order sentences ('Key order in an archive is not guaranteed, and [CORE-073]'s canonical order does not reach it.', and a JSON object as an unordered collection) reach the model: two values are the same content when they render the same JSON value read as an unordered object, so a list of key and value entries (a marking in the snapshot form, a tag map) is the same content as any permutation of it, and a value with no object inside is the same content only as itself. Lines 3, 4 and 5 compare header fields and records up to same content, and line 6 compares two archives exactly. So a writer that renders every marking in one fixed key order meets EVT-025 (EVT_025_allows_fixedOrder: JavaScript's numeric-first key order is 'arbitrary but fixed, so it satisfies this'), and a writer that renders it in a per-process order does not (EVT_025_forbids_seededMarking, line 6). Same content is part of the model of the header and event types; the evidence uses equality for numbers and the unit type, and permutation for lists of entries. 'A host needing a byte-stable archive artefact across implementations MUST canonicalise at its own serialization boundary' binds the host, not the implementation: it is an assumption about callers (kind A), not a line."
          "Not modelled, kind N: the bytes (the length prefixes, the JSON text, LZ4 compression in Java and gzip in TypeScript, Rust and Python), I/O and serialization errors, which fields of the header table V1 has and V2 adds beyond the metadata, the encoding of time values, the per-language token shapes of the body, and the security note. The body sentence on the archive's shape, a versioned header followed by one length-prefixed JSON record per event, is lines 4 and 5 without the framing. The metadata is a stand-in (ArchiveMeta: the number of events and the first and last event) for the runtimes' event-type histogram, first and last timestamp and hasErrors flag, which read the event kind and timestamp. Line 5 fixes it to the stand-in of the snapshot (archiveMeta, none for a V1 header), so a writer whose header metadata does not describe its snapshot violates it (EVT_025_forbids_emptyMeta: the reader's empty fallback written into every V2/V3 header), while what the histogram holds beyond the stand-in is configuration."
          "The body sentence that readers MUST accept all three versions and dispatch into the matching sealed variant (V1/V2/V3) is line 1 and the first quoted sentence. Lines 1 and 3 bind the well-formed archives (Archive.WellFormed: the version is 1, 2 or 3, and the count, the metadata and the body come from one list of events, which lines 4 and 5 make true of every archive a writer writes, evt025_written_wf), so a reader may reject an archive whose eventCount disagrees with its body (EVT_025_allows_strictReader); line 2 binds every archive. AC2 is lines 1 and 2 and the first two quoted sentences. The error text of line 2 is the message all three readers produce (rust/libpetri-debug/src/archive/session_archive_reader.rs parse_header, java/src/main/java/org/libpetri/debug/archive/SessionArchiveReader.java readHeader, typescript/src/debug/archive/session-archive-reader.ts parseHeader); it fixes the exact text where AC2 asks only that the error name the version and the supported range, an added requirement that no runtime fails. Python raises it as a ValueError from Rust's reader. Errors of a truncated or corrupt byte stream are outside the model, which has no bytes."
          "Line 3 is the third quoted sentence: the reader returns the header as written (eventCount unchanged, the session fields up to same content, the metadata), so a reader that loses the metadata of a V2/V3 header violates it (EVT_025_forbids_dropsMetadata: a Java header record component renamed away from its wire name and read as null, since the header mapper ignores unknown properties), and the events are the records, each hydrated by one function η of the reader, in body order (EVT_025_forbids_reversedEvents). Hydration is lossy by design (a Java Token<JsonNode>, a Rust ReplayedTokenPayload), so line 3 fixes the number and order of the events, not their content. 'the header's session fields and metadata as written' and 'in body order' are new text: the markdown said that the reader dispatches into the variant and, in AC8, that the count matches the events (map evt-c, EVT-025). Every reader meets them: each returns the header it parsed and reads the records in sequence."
          "AC1 is lines 4 and 7. Line 7, the seventh quoted sentence, says that the writer writes every header version for every session and store: writeV1 and writeV2 exist (EVT_025_forbids_v3Only), and a writer that refuses a store that has evicted, instead of counting what it retained, violates it (EVT_025_mutant_refuses: the 1.8.2 lifetime-counter bug of rust/libpetri-debug/src/archive/session_archive_writer.rs write_v1 'fixed' with a guard). Line 4 says that writeV1 and writeV2 write the header of their version and write (writeV3) version 3 (EVT_025_mutant_currentHeader), and that the header carries the session's own fields (EVT_025_mutant_wrongSession). That the default writer is the version 3 one is the naming of the API, and that the event body has the writer's current token shape whatever the header version is the token shape; both are kind N, since a record is the event, not its token shape."
          "AC8 is lines 3 and 5. Line 5 is the AC's 'the writer MUST take exactly one snapshot of the event store; header eventCount, V2/V3 metadata, and the event body MUST all derive from that single snapshot': one list l that a call of events() returns during the write gives the count (its length), the metadata (archiveMeta of the version and l) and the body (l, record by record up to same content). The operations dh during the write stand for another thread still appending (the debug stores take appends from the executor while a writer runs); without them one read and two reads could not be told apart. A writer that takes the header from one read and the body from a later one violates line 5 even when the two reads have the same length (EVT_025_mutant_twoReads, on the bounded store). 'Implementations MUST NOT populate eventCount from a cumulative lifetime counter' is line 5 too: on the bounded debug store the count of every append ever made overstates the retained events (EVT_025_mutant_lifetime; the write_v1 bug of libpetri 1.8.2 and earlier). The round trip archive.eventCount() == archive.events().size() for all three header versions is the consequence evt025_roundtrip of lines 1, 3, 4 and 5, and evt025_bounded shows that an archive of the bounded store never counts more than its capacity."
          "Line 5's 'in the order of the snapshot' and 'a V1 header shall carry no metadata' are new text: the body's 'one length-prefixed JSON record per event' fixed the number of records and not their order, and the header table says that V1 has no metadata only by listing what v2 adds (map evt-c, EVT-025). Every writer meets them, since each walks the one list it took (write_framed in Rust, writeFramed in Java and TypeScript) and writes its V1 header without metadata."
          "AC3, AC4, AC5, AC6 and AC7 are kind N: they fix the per-language token shapes and how a reader hydrates them (AC3 Java's typed round trip, AC4 its Token<JsonNode> fallback, AC5 the structured payload TypeScript and Rust preserve, AC6 legacy {value, valueType} tokens read as strings, AC7 TypeScript omitting an empty structured field). Line 3 keeps of them that hydration gives one event per record, in body order, whatever the token shape (AC4: the Java deserializer never throws on an unknown type). The model cannot tell a typed token from a JSON node; a reader that skips the records it cannot hydrate violates line 3 (EVT_025_mutant_skips)."
          "The reproducibility paragraph is line 6. 'An archive written twice by the same implementation from identical run data MUST NOT differ' is line 6: identical run data are the same store, history and session fields with no operation during the write, and the writer is a relation so that a writer whose output depends on something outside the run data, such as a per-process hash seed, is a codec too. That an implementation MUST NOT put a per-process-randomised map on the path to the archive is line 6 for the archive: a writer that renders a marking inside an event in a per-process order (EVT_025_forbids_seededMarking) or a map of the header in a per-process order (EVT_025_mutant_seededTags) writes two archives from one run's data. Rendering in one fixed order is not that (EVT_025_allows_fixedOrder). The debug protocol half of that sentence (MUST NOT put a per-process-randomised map on the path to the debug protocol), with the sentence before it that the JSON debug protocol is the same medium and is bound the same way, is kind Q: the model has an archive codec and no debug protocol, so no line states it, and no other block does (EVT-014's assumes and CORE-073's hand renderings to this block). It is tested in Rust, by the libpetri-debug rendering-order tests (marking_bearing_frames_render_places_in_ascending_order, event_details_render_in_ascending_key_order and session_tags_render_in_ascending_key_order in the debug_response module, net_structure_lists_places_in_ascending_name_order in rust/libpetri-debug/src/debug_session_registry.rs, computed_state_is_ordered_independently_of_the_process in rust/libpetri-debug/src/marking_cache.rs), and in Java, by NetEventConverterTest, DebugSessionRegistryTest and DebugProtocolSubnetTest; TypeScript builds these records as insertion-ordered object literals. Java sorts the event details (NetEventInfo) and the session tags (SessionSummary) by code point where each record is built, as Rust's BTreeMap orders them, DebugSessionRegistry.tagsFor hands a sorted copy, and SubnetInstanceInfo keeps its name sets in build order. A Map.of, Map.copyOf or Set.copyOf left on that path would hand Jackson an order salted per JVM (the behaviour RD-36 and RD-45 recorded)."
          "The header table's 'identical across languages', 'only headers are' byte-compatible, and TypeScript and Rust bodies being wire-compatible are reworded under ruling D29 (a) (clashes evt-c#5 and evt-c#6): headers, and TypeScript and Rust bodies, share field names and JSON types but not the encoding of time values (ISO-8601 text in Java and TypeScript, decimal epoch milliseconds in Rust and Python), so an archive is read correctly only by the language that wrote it. No line compares archives across languages, and lines 1 to 3 bind a reader on archives in its own implementation's format only: the codec C is one implementation's, and an archive of another language's compression or time encoding is outside the lines (Java's reader cannot decompress a gzip archive, Rust's reader rejects ISO-8601 event timestamps, and TypeScript's reads decimal epoch milliseconds as invalid dates)."
          "Priority is SHOULD while the body says MUST, so every quoted sentence reads 'Where an implementation provides session archives' (ruling D20, EVT-C11 (a) item 5). Java, TypeScript, Rust and Python provide them."
          "The Java and Python writers meet the lines where the runtime defect ledger recorded gaps (spec/runtime-defects.md, RD-17 to RD-20). Java's V2/V3 header and SessionMetadata keep the tags and the metadata histogram as maps sorted by code point (CodePointOrder.sortedCopy in the canonical constructors of SessionMetadata and of SessionArchive's V2 and V3), so Jackson writes them in one order on every JVM (line 6; SessionArchiveV3Test). Rendering them through Map.copyOf, whose iteration order is randomised per JVM, is EVT_025_mutant_seededTags on the tags (RD-17). Python's write_from_store archives the store's snapshot through a debug store sized to that snapshot, so no event is evicted before the write (line 5); a copy through a store of capacity 10,000 is EVT_025_forbids_copyThroughBounded, with capacity 1 (RD-18). Python offers write_v1 and write_v2 next to write_from_store, which writes version 3 (line 7, AC1); a writer of version 3 only is EVT_025_forbids_v3Only (RD-19). For a store with no events Python takes start time 0 and no end time rather than the wall clock, so two archives of the same empty session are identical (line 6, RD-20). python/tests/test_archive.py tests the three Python points (rust/libpetri-py/src/archive.rs)."
          "The test derivation (round trips, unknown-version rejection, explicit v2 emission) is EVT_025_nonvacuous on the reference: a version 3 archive of a bounded store after an eviction counts its two retained events, not the three appends, and reads back as V3 with that count, its metadata and two events; a version 2 archive carries version 2 and its metadata; an archive of version 99 is rejected with the message naming 99."
  signoff "2026-11-13 40cba61c02bfb8b6 ai"
  statement : ∀ {D E : Type} [SameContent D] [SameContent E], ArchiveCodec D E → Prop :=
    fun {D E} [SameContent D] [SameContent E] C =>
      (∀ a : Archive D E, a.WellFormed →
        ∃ r, C.read a = .ok r ∧ r.variant.toNat = a.version) ∧
      (∀ a : Archive D E, a.version ∉ [1, 2, 3] →
        C.read a = .error (unsupportedMsg a.version)) ∧
      (∃ η : E → E, ∀ (a : Archive D E) (r : ArchiveRead D E), a.WellFormed → C.read a = .ok r →
        r.eventCount = a.eventCount ∧ r.events = a.recs.map η ∧
          SameContent.same r.data a.data ∧ r.metadata = a.metadata) ∧
      (∀ (S : StoreObs E) (h dh : List (StoreOp E)) (w : ArchiveVer) (d : D) (a : Archive D E),
        C.write S h dh w d a → a.version = w.toNat ∧ SameContent.same a.data d) ∧
      (∀ (S : StoreObs E) (h dh : List (StoreOp E)) (w : ArchiveVer) (d : D) (a : Archive D E),
        C.write S h dh w d a →
          ∃ l, ReadDuring S h dh l ∧ a.eventCount = l.length ∧ a.metadata = archiveMeta w l ∧
            SameRecs a.recs l) ∧
      (∀ (S : StoreObs E) (h : List (StoreOp E)) (w : ArchiveVer) (d : D) (a a' : Archive D E),
        C.write S h [] w d a → C.write S h [] w d a' → a = a') ∧
      (∀ (S : StoreObs E) (h dh : List (StoreOp E)) (w : ArchiveVer) (d : D),
        ∃ a, C.write S h dh w d a)

/- The pinned readable form of EVT-025: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_025 : {D E : Type} → [SameContent D] → [SameContent E] → ArchiveCodec D E → Prop :=
fun {D E} [SameContent D] [SameContent E] C =>
  (∀ (a : Archive D E), a.WellFormed → ∃ r, C.read a = Except.ok r ∧ r.variant.toNat = a.version) ∧
    (∀ (a : Archive D E), a.version ∉ [1, 2, 3] → C.read a = Except.error (unsupportedMsg a.version)) ∧
      (∃ η,
          ∀ (a : Archive D E) (r : ArchiveRead D E),
            a.WellFormed →
              C.read a = Except.ok r →
                r.eventCount = a.eventCount ∧
                  r.events = List.map η a.recs ∧ SameContent.same r.data a.data ∧ r.metadata = a.metadata) ∧
        (∀ (S : StoreObs E) (h dh : List (StoreOp E)) (w : ArchiveVer) (d : D) (a : Archive D E),
            C.write S h dh w d a → a.version = w.toNat ∧ SameContent.same a.data d) ∧
          (∀ (S : StoreObs E) (h dh : List (StoreOp E)) (w : ArchiveVer) (d : D) (a : Archive D E),
              C.write S h dh w d a →
                ∃ l, ReadDuring S h dh l ∧ a.eventCount = l.length ∧ a.metadata = archiveMeta w l ∧ SameRecs a.recs l) ∧
            (∀ (S : StoreObs E) (h : List (StoreOp E)) (w : ArchiveVer) (d : D) (a a' : Archive D E),
                C.write S h [] w d a → C.write S h [] w d a' → a = a') ∧
              ∀ (S : StoreObs E) (h dh : List (StoreOp E)) (w : ArchiveVer) (d : D), ∃ a, C.write S h dh w d a
-/
#guard_msgs in #print EVT_025

/-! ### The seven lines, one definition each -/

section Lines

variable {D E : Type} [SameContent D] [SameContent E] (C : ArchiveCodec D E)

/-- Line 1: every well-formed archive of versions 1, 2 and 3 dispatches into its variant. -/
def Evt025Dispatch : Prop :=
  ∀ a : Archive D E, a.WellFormed → ∃ r, C.read a = .ok r ∧ r.variant.toNat = a.version

/-- Line 2: any other version is rejected with the message naming it. -/
def Evt025Reject : Prop :=
  ∀ a : Archive D E, a.version ∉ [1, 2, 3] → C.read a = .error (unsupportedMsg a.version)

/-- Line 3: the reader returns the header as written and one event per record, in body order. -/
def Evt025ReadBack : Prop :=
  ∃ η : E → E, ∀ (a : Archive D E) (r : ArchiveRead D E), a.WellFormed → C.read a = .ok r →
    r.eventCount = a.eventCount ∧ r.events = a.recs.map η ∧
      SameContent.same r.data a.data ∧ r.metadata = a.metadata

/-- Line 4: the writer writes the version it is asked for and the session's own fields. -/
def Evt025Header : Prop :=
  ∀ (S : StoreObs E) (h dh : List (StoreOp E)) (w : ArchiveVer) (d : D) (a : Archive D E),
    C.write S h dh w d a → a.version = w.toNat ∧ SameContent.same a.data d

/-- Line 5: count, metadata and body come from one read of the store made during the write. -/
def Evt025OneRead : Prop :=
  ∀ (S : StoreObs E) (h dh : List (StoreOp E)) (w : ArchiveVer) (d : D) (a : Archive D E),
    C.write S h dh w d a →
      ∃ l, ReadDuring S h dh l ∧ a.eventCount = l.length ∧ a.metadata = archiveMeta w l ∧
        SameRecs a.recs l

/-- Line 6: two writes from identical run data give the same archive. -/
def Evt025Reproducible : Prop :=
  ∀ (S : StoreObs E) (h : List (StoreOp E)) (w : ArchiveVer) (d : D) (a a' : Archive D E),
    C.write S h [] w d a → C.write S h [] w d a' → a = a'

/-- Line 7: the writer writes every version for every session and store. -/
def Evt025Total : Prop :=
  ∀ (S : StoreObs E) (h dh : List (StoreOp E)) (w : ArchiveVer) (d : D),
    ∃ a, C.write S h dh w d a

/-- EVT-025 is the conjunction of its seven lines (by definition). -/
theorem evt025_iff :
    EVT_025 C ↔ Evt025Dispatch C ∧ Evt025Reject C ∧ Evt025ReadBack C ∧ Evt025Header C ∧
      Evt025OneRead C ∧ Evt025Reproducible C ∧ Evt025Total C :=
  Iff.rfl

/-- The reader lines (1 to 3) of a codec whose reader is the reference reader. -/
theorem evt025_reader_ref (h : C.read = refArchiveRead) :
    Evt025Dispatch C ∧ Evt025Reject C ∧ Evt025ReadBack C := by
  refine ⟨fun a ha => ?_, fun a ha => ?_, ⟨id, fun a r _ hr => ?_⟩⟩
  · rw [h]
    obtain ⟨w, l, hv, -⟩ := ha
    exact refArchiveRead_mem a (by rw [hv]; exact ArchiveVer.toNat_mem w)
  · rw [h]; exact refArchiveRead_not_mem a ha
  · rw [h] at hr
    obtain ⟨h1, h2, h3, h4⟩ := refArchiveRead_ok hr
    refine ⟨h1, by rw [h2, List.map_id], ?_, h4⟩
    rw [h3]; exact SameContent.equiv.refl _

/-- The writer lines (4 to 7) of a codec whose writer is the reference writer. -/
theorem evt025_writer_ref (h : C.write = refArchive.write) :
    Evt025Header C ∧ Evt025OneRead C ∧ Evt025Reproducible C ∧ Evt025Total C := by
  refine ⟨fun S h' dh w d a ha => ?_, fun S h' dh w d a ha => ?_,
    fun S h' w d a a' ha ha' => ?_, fun S h' dh w d => ?_⟩
  · rw [h] at ha
    obtain ⟨l, -, rfl⟩ := ha
    exact ⟨rfl, SameContent.equiv.refl d⟩
  · rw [h] at ha
    obtain ⟨l, hl, rfl⟩ := ha
    exact ⟨l, hl, rfl, rfl, SameRecs.refl l⟩
  · rw [h] at ha ha'
    rw [refArchive_write_nil.mp ha, refArchive_write_nil.mp ha']
  · rw [h]
    exact ⟨_, S.read h' [], ⟨0, Nat.zero_le _, by simp⟩, rfl⟩

end Lines

/-! ### The reference -/

/-- The reference codec satisfies EVT-025, whatever same content its header fields and events
have: its reader dispatches versions 1 to 3 and rejects the others with `unsupportedMsg`,
returning the header as written and the records as the events; its writer writes the version and
the session fields asked for, forms the whole archive from one read of the store, and writes for
every store and version. -/
@[evidence holds EVT_025]
theorem EVT_025_reference {D E : Type} [SameContent D] [SameContent E] :
    EVT_025 (refArchive (D := D) (E := E)) := by
  obtain ⟨h1, h2, h3⟩ := evt025_reader_ref (refArchive (D := D) (E := E)) rfl
  obtain ⟨h4, h5, h6, h7⟩ := evt025_writer_ref (refArchive (D := D) (E := E)) rfl
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- The reference writer writes an archive for every store, history, version and session: a
write call always has an outcome. -/
@[evidence total EVT_025]
theorem EVT_025_total {D E : Type} (S : StoreObs E) (h dh : List (StoreOp E)) (w : ArchiveVer)
    (d : D) : ∃ a, (refArchive (D := D) (E := E)).write S h dh w d a :=
  ⟨_, S.read h [], ⟨0, Nat.zero_le _, by simp⟩, rfl⟩

/-! ### Consequences -/

/-- Every archive a codec meeting EVT-025 writes is well formed (lines 4 and 5), so its own
reader is bound by lines 1 and 3 on it. -/
theorem evt025_written_wf {D E : Type} [SameContent D] [SameContent E] {C : ArchiveCodec D E}
    (hC : EVT_025 C) {S : StoreObs E} {h dh : List (StoreOp E)} {w : ArchiveVer} {d : D}
    {a : Archive D E} (hw : C.write S h dh w d a) : a.WellFormed := by
  obtain ⟨-, -, -, h4, h5, -, -⟩ := hC
  obtain ⟨l, -, hc, hm, hr⟩ := h5 S h dh w d a hw
  exact ⟨w, l, (h4 S h dh w d a hw).1, hc, hm, hr⟩

/-- AC8's round trip: an archive a codec meeting EVT-025 writes reads back as the variant of the
version asked for, with as many events as its header counts. -/
theorem evt025_roundtrip {D E : Type} [SameContent D] [SameContent E] {C : ArchiveCodec D E}
    (hC : EVT_025 C) {S : StoreObs E} {h dh : List (StoreOp E)} {w : ArchiveVer} {d : D}
    {a : Archive D E} (hw : C.write S h dh w d a) :
    ∃ r, C.read a = .ok r ∧ r.variant = w ∧ r.eventCount = r.events.length := by
  have hwf := evt025_written_wf hC hw
  obtain ⟨h1, -, ⟨η, h3⟩, h4, h5, -, -⟩ := hC
  obtain ⟨r, hr, hrv⟩ := h1 a hwf
  have hv := (h4 S h dh w d a hw).1
  obtain ⟨l, -, hc, -, hrecs⟩ := h5 S h dh w d a hw
  obtain ⟨hrc, hre, -, -⟩ := h3 a r hwf hr
  refine ⟨r, hr, ArchiveVer.toNat_inj (hrv.trans hv), ?_⟩
  rw [hrc, hre, List.length_map, hc, SameRecs.length_eq hrecs]

/-- An archive of the bounded store of capacity `c`, written with no operation during the write,
never counts more than `c` events, however many were appended: the count is the retained body,
not a lifetime counter. -/
theorem evt025_bounded {D E : Type} [SameContent D] [SameContent E] {C : ArchiveCodec D E}
    (hC : EVT_025 C) (c : Nat) {h : List (StoreOp E)} {w : ArchiveVer} {d : D}
    {a : Archive D E} (hw : C.write (refBoundedStore c) h [] w d a) : a.eventCount ≤ c := by
  obtain ⟨-, -, -, -, h5, -, -⟩ := hC
  obtain ⟨l, hl, hc, -, -⟩ := h5 _ h [] w d a hw
  rw [readDuring_nil.mp hl] at hc
  rw [hc]
  simp only [refBoundedStore, List.length_drop]
  omega

/-! ### Wrong readers -/

/-- A reader of the current version only: it rejects versions 1 and 2. -/
def evt025_currentOnlyRead {D E : Type} (a : Archive D E) : Except String (ArchiveRead D E) :=
  if a.version = 3 then .ok ⟨.v3, a.data, a.eventCount, a.metadata, a.recs⟩
  else .error (unsupportedMsg a.version)

/-- The reference writer with the current-version-only reader. -/
def evt025_currentOnly {D E : Type} : ArchiveCodec D E := ⟨refArchive.write, evt025_currentOnlyRead⟩

/-- The reading of EVT-025 without line 1. -/
def Evt025WithoutDispatch {D E : Type} [SameContent D] [SameContent E] (C : ArchiveCodec D E) :
    Prop :=
  Evt025Reject C ∧ Evt025ReadBack C ∧ Evt025Header C ∧ Evt025OneRead C ∧
    Evt025Reproducible C ∧ Evt025Total C

/-- ✗ A reader that reads the current version only meets every line but line 1 and violates
EVT-025: the well-formed empty archive of version 1 is rejected. -/
@[evidence mutant EVT_025]
theorem EVT_025_mutant_currentOnly :
    Evt025WithoutDispatch (evt025_currentOnly (D := Unit) (E := Nat)) ∧
      ¬ EVT_025 (evt025_currentOnly (D := Unit) (E := Nat)) := by
  obtain ⟨h4, h5, h6, h7⟩ := evt025_writer_ref (evt025_currentOnly (D := Unit) (E := Nat)) rfl
  refine ⟨⟨fun a ha => ?_, ⟨id, fun a r _ hr => ?_⟩, h4, h5, h6, h7⟩, fun h => ?_⟩
  · have h3 : a.version ≠ 3 := fun e => ha (by simp [e])
    simp [evt025_currentOnly, evt025_currentOnlyRead, h3]
  · simp only [evt025_currentOnly, evt025_currentOnlyRead] at hr
    split at hr
    · cases hr; exact ⟨rfl, (List.map_id _).symm, rfl, rfl⟩
    · cases hr
  · obtain ⟨r, hr, -⟩ := h.1 ⟨1, (), 0, none, []⟩ ⟨.v1, [], rfl, rfl, rfl, trivial⟩
    simp [evt025_currentOnly, evt025_currentOnlyRead] at hr

/-- A lenient reader: it takes every version above 3 for version 3. -/
def evt025_lenientRead {D E : Type} (a : Archive D E) : Except String (ArchiveRead D E) :=
  match ArchiveVer.ofNat? a.version with
  | some w => .ok ⟨w, a.data, a.eventCount, a.metadata, a.recs⟩
  | none =>
    if 3 ≤ a.version then .ok ⟨.v3, a.data, a.eventCount, a.metadata, a.recs⟩
    else .error (unsupportedMsg a.version)

/-- The reference writer with the lenient reader. -/
def evt025_lenient {D E : Type} : ArchiveCodec D E := ⟨refArchive.write, evt025_lenientRead⟩

/-- The reading of EVT-025 without line 2. -/
def Evt025WithoutReject {D E : Type} [SameContent D] [SameContent E] (C : ArchiveCodec D E) :
    Prop :=
  Evt025Dispatch C ∧ Evt025ReadBack C ∧ Evt025Header C ∧ Evt025OneRead C ∧
    Evt025Reproducible C ∧ Evt025Total C

/-- ✗ A reader that takes version 99 for version 3 meets every line but line 2 and violates
EVT-025: it accepts an archive it cannot know. -/
@[evidence mutant EVT_025]
theorem EVT_025_mutant_lenient :
    Evt025WithoutReject (evt025_lenient (D := Unit) (E := Nat)) ∧
      ¬ EVT_025 (evt025_lenient (D := Unit) (E := Nat)) := by
  obtain ⟨h4, h5, h6, h7⟩ := evt025_writer_ref (evt025_lenient (D := Unit) (E := Nat)) rfl
  refine ⟨⟨fun a ha => ?_, ⟨id, fun a r _ hr => ?_⟩, h4, h5, h6, h7⟩, fun h => ?_⟩
  · obtain ⟨w, l, hv, -⟩ := ha
    have hw : ArchiveVer.ofNat? a.version = some w := ArchiveVer.ofNat?_eq_some.mpr hv.symm
    exact ⟨⟨w, a.data, a.eventCount, a.metadata, a.recs⟩,
      by simp [evt025_lenient, evt025_lenientRead, hw], hv.symm⟩
  · simp only [evt025_lenient, evt025_lenientRead] at hr
    split at hr
    · cases hr; exact ⟨rfl, (List.map_id _).symm, rfl, rfl⟩
    · split at hr
      · cases hr; exact ⟨rfl, (List.map_id _).symm, rfl, rfl⟩
      · cases hr
  · have := h.2.1 ⟨99, (), 0, none, []⟩ (by decide)
    simp [evt025_lenient, evt025_lenientRead, ArchiveVer.ofNat?] at this

/-- A reader that skips the records it cannot hydrate (here: the event `0`). -/
def evt025_skipsRead (a : Archive Unit Nat) : Except String (ArchiveRead Unit Nat) :=
  (refArchiveRead a).map fun r => { r with events := r.events.filter (· ≠ 0) }

/-- The reference writer with the skipping reader. -/
def evt025_skips : ArchiveCodec Unit Nat := ⟨refArchive.write, evt025_skipsRead⟩

/-- The reading of EVT-025 without line 3. -/
def Evt025WithoutReadBack {D E : Type} [SameContent D] [SameContent E] (C : ArchiveCodec D E) :
    Prop :=
  Evt025Dispatch C ∧ Evt025Reject C ∧ Evt025Header C ∧ Evt025OneRead C ∧
    Evt025Reproducible C ∧ Evt025Total C

/-- ✗ A reader that skips the records it cannot hydrate meets every line but line 3 and
violates EVT-025: an archive of one record reads back with no event. -/
@[evidence mutant EVT_025]
theorem EVT_025_mutant_skips :
    Evt025WithoutReadBack evt025_skips ∧ ¬ EVT_025 evt025_skips := by
  obtain ⟨h4, h5, h6, h7⟩ := evt025_writer_ref evt025_skips rfl
  refine ⟨⟨fun a ha => ?_, fun a ha => ?_, h4, h5, h6, h7⟩, fun h => ?_⟩
  · obtain ⟨w, l, hv, -⟩ := ha
    have hw : ArchiveVer.ofNat? a.version = some w := ArchiveVer.ofNat?_eq_some.mpr hv.symm
    exact ⟨_, by simp [evt025_skips, evt025_skipsRead, refArchiveRead, hw, Except.map]; rfl,
      hv.symm⟩
  · simp [evt025_skips, evt025_skipsRead, refArchiveRead, ArchiveVer.ofNat?_of_not_mem ha,
      Except.map]
  · obtain ⟨η, h3⟩ := h.2.2.1
    have := (h3 (refForm .v3 () [0]) ⟨.v3, (), 1, some ⟨1, some 0, some 0⟩, []⟩
      (refForm_wellFormed _ _ _) rfl).2.1
    simp [refForm] at this

/-- A reader that loses the V2/V3 metadata: a Java header record component renamed away from its
wire name is read as null, since the header mapper ignores unknown properties. -/
def evt025_dropsMetadataRead (a : Archive Unit Nat) : Except String (ArchiveRead Unit Nat) :=
  (refArchiveRead a).map fun r => { r with metadata := none }

/-- ✗ A reader that loses the metadata violates EVT-025 (line 3): a version 3 archive of one event
reads back without the metadata its header holds. -/
@[evidence forbids EVT_025]
theorem EVT_025_forbids_dropsMetadata :
    ¬ EVT_025 (⟨refArchive.write, evt025_dropsMetadataRead⟩ : ArchiveCodec Unit Nat) := by
  intro h
  obtain ⟨η, h3⟩ := h.2.2.1
  have := (h3 (refForm .v3 () [7]) ⟨.v3, (), 1, none, [7]⟩ (refForm_wellFormed _ _ _) rfl).2.2.2
  revert this
  decide

/-- A reader that returns the events in reverse body order. -/
def evt025_reversedRead (a : Archive Unit Nat) : Except String (ArchiveRead Unit Nat) :=
  (refArchiveRead a).map fun r => { r with events := r.events.reverse }

/-- ✗ A reader that reverses the events violates EVT-025 (line 3): no hydration function maps the
records `[1]` to the events `[1]` and the records `[1, 2]` to the events `[2, 1]`. -/
@[evidence forbids EVT_025]
theorem EVT_025_forbids_reversedEvents :
    ¬ EVT_025 (⟨refArchive.write, evt025_reversedRead⟩ : ArchiveCodec Unit Nat) := by
  intro h
  obtain ⟨η, h3⟩ := h.2.2.1
  have e1 := (h3 (refForm .v3 () [1]) ⟨.v3, (), 1, some ⟨1, some 1, some 1⟩, [1]⟩
    (refForm_wellFormed _ _ _) rfl).2.1
  have e2 := (h3 (refForm .v3 () [1, 2]) ⟨.v3, (), 2, some ⟨2, some 1, some 2⟩, [2, 1]⟩
    (refForm_wellFormed _ _ _) rfl).2.1
  simp [refForm] at e1 e2
  omega

/-! ### Wrong writers -/

/-- A writer whose `writeV1` and `writeV2` write the version number 3 into a header that is
otherwise of their version. -/
def evt025_currentHeader {D E : Type} : ArchiveCodec D E where
  write S h dh w d a :=
    ∃ l, ReadDuring S h dh l ∧ a = ⟨3, d, l.length, archiveMeta w l, l⟩
  read := refArchiveRead

/-- The reading of EVT-025 without line 4. -/
def Evt025WithoutHeader {D E : Type} [SameContent D] [SameContent E] (C : ArchiveCodec D E) :
    Prop :=
  Evt025Dispatch C ∧ Evt025Reject C ∧ Evt025ReadBack C ∧ Evt025OneRead C ∧
    Evt025Reproducible C ∧ Evt025Total C

/-- ✗ A writer whose `writeV1` writes the version number 3 meets every line but line 4 and
violates EVT-025 (AC1: `writeV1` emits the v1 header). -/
@[evidence mutant EVT_025]
theorem EVT_025_mutant_currentHeader :
    Evt025WithoutHeader (evt025_currentHeader (D := Unit) (E := Nat)) ∧
      ¬ EVT_025 (evt025_currentHeader (D := Unit) (E := Nat)) := by
  obtain ⟨h1, h2, h3⟩ := evt025_reader_ref (evt025_currentHeader (D := Unit) (E := Nat)) rfl
  refine ⟨⟨h1, h2, h3, fun S h dh w d a ha => ?_, fun S h w d a a' ha ha' => ?_,
    fun S h dh w d => ?_⟩, fun h => ?_⟩
  · obtain ⟨l, hl, rfl⟩ := ha
    exact ⟨l, hl, rfl, rfl, SameRecs.refl l⟩
  · obtain ⟨l, hl, rfl⟩ := ha
    obtain ⟨l', hl', rfl⟩ := ha'
    rw [readDuring_nil.mp hl, readDuring_nil.mp hl']
  · exact ⟨_, S.read h [], ⟨0, Nat.zero_le _, by simp⟩, rfl⟩
  · have := (h.2.2.2.1 refMemStore [] [] .v1 () ⟨3, (), 0, none, []⟩
      ⟨[], ⟨0, Nat.zero_le _, rfl⟩, rfl⟩).1
    simp [ArchiveVer.toNat] at this

/-- A writer that writes the header fields of another session (here: the session `0`) whatever
session it is asked to archive. -/
def evt025_wrongSession {E : Type} : ArchiveCodec Nat E where
  write S h dh w _ a := refArchive.write S h dh w 0 a
  read := refArchiveRead

/-- ✗ A writer that writes another session's header fields meets every line but line 4 and
violates EVT-025: the archive of session `1` carries the fields of session `0`. -/
@[evidence mutant EVT_025]
theorem EVT_025_mutant_wrongSession :
    Evt025WithoutHeader (evt025_wrongSession (E := Nat)) ∧
      ¬ EVT_025 (evt025_wrongSession (E := Nat)) := by
  obtain ⟨h1, h2, h3⟩ := evt025_reader_ref (evt025_wrongSession (E := Nat)) rfl
  obtain ⟨-, h5, h6, h7⟩ := evt025_writer_ref (refArchive (D := Nat) (E := Nat)) rfl
  refine ⟨⟨h1, h2, h3, fun S h dh w d a ha => h5 S h dh w 0 a ha,
    fun S h w d a a' ha ha' => h6 S h w 0 a a' ha ha', fun S h dh w d => h7 S h dh w 0⟩,
    fun h => ?_⟩
  have := (h.2.2.2.1 refMemStore [] [] .v3 1 (refForm .v3 0 [])
    ⟨[], ⟨0, Nat.zero_le _, rfl⟩, rfl⟩).2
  have h01 : (0 : Nat) = 1 := this
  exact absurd h01 (by decide)

/-- A writer that takes the header's count from the store's lifetime counter (every append made
before the write, evicted or not) and everything else from one read: the `write_v1` of libpetri
1.8.2 and earlier. -/
def evt025_lifetime {D E : Type} : ArchiveCodec D E where
  write S h dh w d a :=
    ∃ l, ReadDuring S h dh l ∧ a = { refForm w d l with eventCount := (appended h).length }
  read := refArchiveRead

/-- The reading of EVT-025 without line 5. -/
def Evt025WithoutOneRead {D E : Type} [SameContent D] [SameContent E] (C : ArchiveCodec D E) :
    Prop :=
  Evt025Dispatch C ∧ Evt025Reject C ∧ Evt025ReadBack C ∧ Evt025Header C ∧
    Evt025Reproducible C ∧ Evt025Total C

/-- ✗ A writer that counts the lifetime appends meets every line but line 5 and violates EVT-025:
after two appends to a bounded store of capacity 1 its header counts 2 events over a body of
one. -/
@[evidence mutant EVT_025]
theorem EVT_025_mutant_lifetime :
    Evt025WithoutOneRead (evt025_lifetime (D := Unit) (E := Nat)) ∧
      ¬ EVT_025 (evt025_lifetime (D := Unit) (E := Nat)) := by
  obtain ⟨h1, h2, h3⟩ := evt025_reader_ref (evt025_lifetime (D := Unit) (E := Nat)) rfl
  refine ⟨⟨h1, h2, h3, fun S h dh w d a ha => ?_, fun S h w d a a' ha ha' => ?_,
    fun S h dh w d => ?_⟩, fun h => ?_⟩
  · obtain ⟨l, -, rfl⟩ := ha
    exact ⟨rfl, rfl⟩
  · obtain ⟨l, hl, rfl⟩ := ha
    obtain ⟨l', hl', rfl⟩ := ha'
    rw [readDuring_nil.mp hl, readDuring_nil.mp hl']
  · exact ⟨_, S.read h [], ⟨0, Nat.zero_le _, by simp⟩, rfl⟩
  · have hw : (evt025_lifetime (D := Unit) (E := Nat)).write (refBoundedStore 1)
        [.append 1, .append 2] [] .v1 () ⟨1, (), 2, none, [2]⟩ :=
      ⟨[2], readDuring_nil.mpr (by decide), rfl⟩
    obtain ⟨l, hl, hc, -, -⟩ := h.2.2.2.2.1 _ _ _ _ _ _ hw
    rw [readDuring_nil.mp hl] at hc
    revert hc
    decide

/-- A writer that reads the store twice: the header (count and metadata) from a read when the
write starts, the body from a read when it ends. -/
def evt025_twoReads {D E : Type} : ArchiveCodec D E where
  write S h dh w d a := a = { refForm w d (S.read h []) with recs := S.read (h ++ dh) [] }
  read := refArchiveRead

/-- ✗ A writer that reads the store twice meets every line but line 5 and violates EVT-025: on a
bounded store of capacity 1 that takes one append during the write, the two reads have the same
length but not the same event, and the header's metadata describes an event the body does not
hold. -/
@[evidence mutant EVT_025]
theorem EVT_025_mutant_twoReads :
    Evt025WithoutOneRead (evt025_twoReads (D := Unit) (E := Nat)) ∧
      ¬ EVT_025 (evt025_twoReads (D := Unit) (E := Nat)) := by
  obtain ⟨h1, h2, h3⟩ := evt025_reader_ref (evt025_twoReads (D := Unit) (E := Nat)) rfl
  refine ⟨⟨h1, h2, h3, fun S h dh w d a ha => ?_, fun S h w d a a' ha ha' => ?_,
    fun S h dh w d => ⟨_, rfl⟩⟩, fun h => ?_⟩
  · subst ha; exact ⟨rfl, rfl⟩
  · show a = a'
    have e1 : a = _ := ha
    have e2 : a' = _ := ha'
    rw [e1, e2]
  · have hw : (evt025_twoReads (D := Unit) (E := Nat)).write (refBoundedStore 1)
        [.append 1] [.append 2] .v2 () ⟨2, (), 1, some ⟨1, some 1, some 1⟩, [2]⟩ := by
      show (_ : Archive Unit Nat) = _
      decide
    obtain ⟨l, -, -, hm, hr⟩ := h.2.2.2.2.1 _ _ _ _ _ _ hw
    have hl : [2] = l := (SameRecs.eq_iff (fun _ _ => Iff.rfl)).mp hr
    subst hl
    revert hm
    decide

/-- A writer whose V2/V3 header carries the reader's empty fallback metadata (no events) instead
of the metadata of its snapshot: `emptyMetadata()` in place of `computeMetadata(events)` in
TypeScript's `writeV2` and `writeV3`. -/
def evt025_emptyMeta {D E : Type} : ArchiveCodec D E where
  write S h dh w d a := ∃ l, ReadDuring S h dh l ∧
    a = { refForm w d l with metadata := match w with | .v1 => none | _ => some ⟨0, none, none⟩ }
  read := refArchiveRead

/-- ✗ A writer that writes empty metadata violates EVT-025 (line 5): its V2 header of one event
claims none. -/
@[evidence forbids EVT_025]
theorem EVT_025_forbids_emptyMeta : ¬ EVT_025 (evt025_emptyMeta (D := Unit) (E := Nat)) := by
  intro h
  have hw : (evt025_emptyMeta (D := Unit) (E := Nat)).write refMemStore [.append 7] [] .v2 ()
      ⟨2, (), 1, some ⟨0, none, none⟩, [7]⟩ :=
    ⟨[7], readDuring_nil.mpr rfl, rfl⟩
  obtain ⟨l, hl, -, hm, -⟩ := h.2.2.2.2.1 _ _ _ _ _ _ hw
  rw [readDuring_nil.mp hl] at hm
  revert hm
  decide

/-- A writer that copies the store's events into a bounded store of capacity 1 and archives
that copy: a writer that copies through a debug store of capacity 10,000 (the behaviour RD-18
recorded), at capacity 1. -/
def evt025_copyThroughBounded {D E : Type} : ArchiveCodec D E where
  write S h dh w d a := ∃ l, ReadDuring S h dh l ∧ a = refForm w d (l.drop (l.length - 1))
  read := refArchiveRead

/-- ✗ A writer that archives a bounded copy of the store violates EVT-025 (line 5): of an
in-memory store holding two events it archives one, so the body is not the snapshot it took. -/
@[evidence forbids EVT_025]
theorem EVT_025_forbids_copyThroughBounded :
    ¬ EVT_025 (evt025_copyThroughBounded (D := Unit) (E := Nat)) := by
  intro h
  have hw : (evt025_copyThroughBounded (D := Unit) (E := Nat)).write refMemStore
      [.append 1, .append 2] [] .v3 () (refForm .v3 () [2]) :=
    ⟨[1, 2], readDuring_nil.mpr (by decide), rfl⟩
  obtain ⟨l, hl, -, -, hr⟩ := h.2.2.2.2.1 _ _ _ _ _ _ hw
  rw [readDuring_nil.mp hl] at hr
  have := SameRecs.length_eq hr
  revert this
  decide

/-- A writer that renders the header's tags (here: the session fields, a list of key and value
pairs in rendering order) in a per-process order: either order, depending on a seed that is not
part of the run data. A header built with Java's `Map.copyOf` over the tags does this (the
behaviour RD-17 recorded). -/
def evt025_seededTags {E : Type} : ArchiveCodec (List (String × String)) E where
  write S h dh w d a :=
    ∃ seed : Bool, ∃ l, ReadDuring S h dh l ∧ a = refForm w (if seed then d.reverse else d) l
  read := refArchiveRead

/-- The reading of EVT-025 without line 6. -/
def Evt025WithoutReproducible {D E : Type} [SameContent D] [SameContent E]
    (C : ArchiveCodec D E) : Prop :=
  Evt025Dispatch C ∧ Evt025Reject C ∧ Evt025ReadBack C ∧ Evt025Header C ∧ Evt025OneRead C ∧
    Evt025Total C

/-- ✗ A writer that renders the tags in a per-process order meets every line but line 6 (either
order is the same content) and violates EVT-025: one session with two tags is written two
ways. -/
@[evidence mutant EVT_025]
theorem EVT_025_mutant_seededTags :
    Evt025WithoutReproducible (evt025_seededTags (E := Nat)) ∧
      ¬ EVT_025 (evt025_seededTags (E := Nat)) := by
  obtain ⟨h1, h2, h3⟩ := evt025_reader_ref (evt025_seededTags (E := Nat)) rfl
  refine ⟨⟨h1, h2, h3, fun S h dh w d a ha => ?_, fun S h dh w d a ha => ?_,
    fun S h dh w d => ?_⟩, fun h => ?_⟩
  · obtain ⟨seed, l, -, rfl⟩ := ha
    refine ⟨rfl, ?_⟩
    cases seed
    · exact SameContent.equiv.refl d
    · exact List.reverse_perm d
  · obtain ⟨_, l, hl, rfl⟩ := ha
    exact ⟨l, hl, rfl, rfl, SameRecs.refl l⟩
  · exact ⟨_, false, S.read h [], ⟨0, Nat.zero_le _, by simp⟩, rfl⟩
  · have := h.2.2.2.2.2.1 refMemStore [] .v3 [("a", "1"), ("b", "2")]
      (refForm .v3 [("a", "1"), ("b", "2")] []) (refForm .v3 [("b", "2"), ("a", "1")] [])
      ⟨false, [], ⟨0, Nat.zero_le _, rfl⟩, rfl⟩ ⟨true, [], ⟨0, Nat.zero_le _, rfl⟩, rfl⟩
    revert this
    decide

/-- A writer that copies an event's marking through a per-process-randomised map before writing
it: the marking's entries come out in either order, depending on a seed that is not part of the
run data. Events here carry a marking in the snapshot form of [CORE-073]; the count and the
metadata read the event, not its rendering. -/
def evt025_seededMarking : ArchiveCodec Unit (QSnap String Nat) where
  write S h dh w d a :=
    ∃ seed : Bool, ∃ l, ReadDuring S h dh l ∧
      a = ⟨w.toNat, d, l.length, archiveMeta w l, l.map fun e => if seed then e.reverse else e⟩
  read := refArchiveRead

/-- ✗ A writer that renders a marking in a per-process order violates EVT-025 (line 6): for an
event carrying the snapshot of a marking of two places, it writes two different archives from
one run's data. -/
@[evidence forbids EVT_025]
theorem EVT_025_forbids_seededMarking : ¬ EVT_025 evt025_seededMarking := by
  intro h
  have hs : refSnapshot snapExF = [("a", [1]), ("c", [7, 8])] := by decide
  have := h.2.2.2.2.2.1 refMemStore [.append (refSnapshot snapExF)] .v3 () _ _
    ⟨false, [refSnapshot snapExF], readDuring_nil.mpr rfl, rfl⟩
    ⟨true, [refSnapshot snapExF], readDuring_nil.mpr rfl, rfl⟩
  rw [hs] at this
  revert this
  decide

/-- A writer that renders every marking in one fixed key order (here: the reverse of the snapshot
form), as JavaScript renders integer-like keys first: arbitrary but fixed. -/
def evt025_fixedOrder : ArchiveCodec Unit (QSnap String Nat) where
  write S h dh w d a :=
    ∃ l, ReadDuring S h dh l ∧ a = ⟨w.toNat, d, l.length, archiveMeta w l, l.map List.reverse⟩
  read := refArchiveRead

/-- ✓ EVT-025 allows a writer that renders every marking in one fixed key order: each record is
the same content as its event, and two writes from identical run data agree. -/
@[evidence allows EVT_025]
theorem EVT_025_allows_fixedOrder : EVT_025 evt025_fixedOrder := by
  obtain ⟨h1, h2, h3⟩ := evt025_reader_ref evt025_fixedOrder rfl
  refine ⟨h1, h2, h3, fun S h dh w d a ha => ?_, fun S h dh w d a ha => ?_,
    fun S h w d a a' ha ha' => ?_, fun S h dh w d => ?_⟩
  · obtain ⟨l, -, rfl⟩ := ha
    exact ⟨rfl, SameContent.equiv.refl d⟩
  · obtain ⟨l, hl, rfl⟩ := ha
    exact ⟨l, hl, rfl, rfl, SameRecs.map (fun x => List.reverse_perm x) l⟩
  · obtain ⟨l, hl, rfl⟩ := ha
    obtain ⟨l', hl', rfl⟩ := ha'
    rw [readDuring_nil.mp hl, readDuring_nil.mp hl']
  · exact ⟨_, S.read h [], ⟨0, Nat.zero_le _, by simp⟩, rfl⟩

/-- A reader that also checks the header against the body: it rejects an archive of a supported
version whose `eventCount` is not the number of its records. -/
def evt025_strictRead (a : Archive Unit Nat) : Except String (ArchiveRead Unit Nat) :=
  if a.eventCount = a.recs.length then refArchiveRead a else
    match ArchiveVer.ofNat? a.version with
    | some _ => .error "eventCount does not match the body"
    | none => .error (unsupportedMsg a.version)

/-- ✓ EVT-025 allows a reader that rejects an archive whose `eventCount` disagrees with its body:
lines 1 and 3 bind the well-formed archives only, and line 2 still names an unsupported
version. -/
@[evidence allows EVT_025]
theorem EVT_025_allows_strictReader :
    EVT_025 (⟨refArchive.write, evt025_strictRead⟩ : ArchiveCodec Unit Nat) := by
  obtain ⟨h4, h5, h6, h7⟩ :=
    evt025_writer_ref (⟨refArchive.write, evt025_strictRead⟩ : ArchiveCodec Unit Nat) rfl
  refine ⟨fun a ha => ?_, fun a ha => ?_, ⟨id, fun a r _ hr => ?_⟩, h4, h5, h6, h7⟩
  · obtain ⟨w, l, hv, hc, -, hr⟩ := ha
    have hn : a.eventCount = a.recs.length := by rw [hc, SameRecs.length_eq hr]
    simp only [evt025_strictRead, hn, if_true]
    exact refArchiveRead_mem a (by rw [hv]; exact ArchiveVer.toNat_mem w)
  · simp only [evt025_strictRead, ArchiveVer.ofNat?_of_not_mem ha]
    split <;> simp [refArchiveRead_not_mem a ha]
  · simp only [evt025_strictRead] at hr
    split at hr
    · obtain ⟨h1, h2, h3, h4⟩ := refArchiveRead_ok hr
      exact ⟨h1, by rw [h2, List.map_id], h3, h4⟩
    · split at hr <;> cases hr

/-- A writer that refuses a store whose snapshot is shorter than its lifetime count (a bounded
store that has evicted, or a cleared one) instead of archiving what it retained: the 1.8.2
lifetime-counter bug of Rust's `write_v1` "fixed" with a guard. -/
def evt025_refuses {D E : Type} : ArchiveCodec D E where
  write S h dh w d a := ∃ j, j ≤ dh.length ∧
    (S.read (h ++ dh.take j) []).length = (appended (h ++ dh.take j)).length ∧
    a = refForm w d (S.read (h ++ dh.take j) [])
  read := refArchiveRead

/-- The reading of EVT-025 without line 7. -/
def Evt025WithoutTotal {D E : Type} [SameContent D] [SameContent E] (C : ArchiveCodec D E) :
    Prop :=
  Evt025Dispatch C ∧ Evt025Reject C ∧ Evt025ReadBack C ∧ Evt025Header C ∧ Evt025OneRead C ∧
    Evt025Reproducible C

/-- ✗ A writer that refuses a store that has evicted meets every line but line 7 and violates
EVT-025: a bounded store of capacity 1 after two appends cannot be archived at all. -/
@[evidence mutant EVT_025]
theorem EVT_025_mutant_refuses :
    Evt025WithoutTotal (evt025_refuses (D := Unit) (E := Nat)) ∧
      ¬ EVT_025 (evt025_refuses (D := Unit) (E := Nat)) := by
  obtain ⟨h1, h2, h3⟩ := evt025_reader_ref (evt025_refuses (D := Unit) (E := Nat)) rfl
  refine ⟨⟨h1, h2, h3, fun S h dh w d a ha => ?_, fun S h dh w d a ha => ?_,
    fun S h w d a a' ha ha' => ?_⟩, fun h => ?_⟩
  · obtain ⟨j, -, -, rfl⟩ := ha
    exact ⟨rfl, rfl⟩
  · obtain ⟨j, hj, -, rfl⟩ := ha
    exact ⟨_, ⟨j, hj, rfl⟩, rfl, rfl, SameRecs.refl _⟩
  · obtain ⟨j, -, -, rfl⟩ := ha
    obtain ⟨j', -, -, rfl⟩ := ha'
    simp
  · obtain ⟨a, j, hj, hlen, -⟩ := h.2.2.2.2.2.2 (refBoundedStore 1) [.append 1, .append 2] [] .v1 ()
    have : j = 0 := by simpa using hj
    subst this
    revert hlen
    decide

/-- A writer of header version 3 only: a binding whose `write_from_store` has no `writeV1` or
`writeV2` beside it (the behaviour RD-19 recorded). -/
def evt025_v3Only {D E : Type} : ArchiveCodec D E where
  write S h dh w d a := w = .v3 ∧ refArchive.write S h dh w d a
  read := refArchiveRead

/-- ✗ A writer of version 3 only violates EVT-025 (line 7): it writes no version 1 archive. -/
@[evidence forbids EVT_025]
theorem EVT_025_forbids_v3Only : ¬ EVT_025 (evt025_v3Only (D := Unit) (E := Nat)) := by
  intro h
  obtain ⟨a, hv, -⟩ := h.2.2.2.2.2.2 refMemStore [] [] .v1 ()
  cases hv

/-! ### Non-vacuity: the test derivation on the reference -/

/-- The test derivation on the reference: a version 3 archive of a bounded store of capacity 2
after three appends counts the two retained events (not the three appends) and reads back as V3
with that count, its metadata and two events; a version 2 archive of one event carries version 2
and its metadata; an archive of version 99 is rejected with the message naming 99. -/
@[evidence nonvacuous EVT_025]
theorem EVT_025_nonvacuous :
    (refArchive (D := Unit) (E := Nat)).write (refBoundedStore 2)
        [.append 1, .append 2, .append 3] [] .v3 () (refForm .v3 () [2, 3]) ∧
    (refArchive (D := Unit) (E := Nat)).read (refForm .v3 () [2, 3]) =
        .ok ⟨.v3, (), 2, some ⟨2, some 2, some 3⟩, [2, 3]⟩ ∧
    (appended [StoreOp.append (1 : Nat), .append 2, .append 3]).length = 3 ∧
    (refArchive (D := Unit) (E := Nat)).write refMemStore [.append 1] [] .v2 ()
        ⟨2, (), 1, some ⟨1, some 1, some 1⟩, [1]⟩ ∧
    (refArchive (D := Unit) (E := Nat)).read ⟨99, (), 3, none, [1, 2, 3]⟩ =
        .error "Unsupported archive version: 99 (reader supports 1..3)" := by
  refine ⟨⟨[2, 3], readDuring_nil.mpr (by decide), rfl⟩, rfl, rfl,
    ⟨[1], readDuring_nil.mpr rfl, rfl⟩, ?_⟩
  decide

end Libpetri.Spec
