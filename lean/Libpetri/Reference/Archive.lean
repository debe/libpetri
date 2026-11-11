import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryStore

set_option linter.missingDocs true

/-!
# RefArchive: session archives without bytes

The witness model of [EVT-025] (`spec/08-events-observability.md`), on the store vocabulary of
`Spec/GlossaryStore.lean`. A session archive is a header followed by one record per event. The
model keeps what the requirement's behaviour sentences talk about and drops the wire format:

* **The archive** (`Archive D E`): the header version tag as written (`version`, a number,
  since a reader can meet any number), the session's own header fields (`data : D`, opaque:
  session id, net name, DOT diagram, start and end time, tags, net structure), the header's
  `eventCount`, the V2/V3 metadata (`metadata`, `none` in a V1 header) and the body (`recs`). A
  record is the event it records: the length prefixes, the JSON text, the compression (LZ4 in
  Java, gzip elsewhere), the time encodings and the per-language token shapes are not modelled.
* **The metadata** (`ArchiveMeta E`) stands in for the V2/V3 metadata: the number of events
  and the first and last event. The runtimes' event-type histogram (whose counts sum to the
  number of events), first and last timestamp and `hasErrors` flag read the event kind and
  timestamp, which the store tier does not model. `archiveMeta w l` is the metadata of the
  events `l` in a header of version `w`: none for V1, which has no metadata.
* **Same content** (`SameContent α`): when two values render the same JSON value, read as an
  unordered object. A list of key and value entries (a marking in the snapshot form, a tag map)
  renders as a JSON object, so two such lists are the same content when one is a permutation of
  the other; a value with no object inside is the same content only as itself. Key order in an
  archive is not guaranteed, so the requirement compares the header fields and the records with
  the events up to same content (`SameRecs` for lists of records, position by position).
* **A well-formed archive** (`Archive.WellFormed`): its version is one of the three, and its
  count, metadata and body come from one list of events, as a writer's do.
* **The reader's result** (`ArchiveRead D E`): the header variant it dispatched into
  (`ArchiveVer`: `V1`, `V2` or `V3`), the header fields it returns, and the events it hydrated
  from the body. Hydration is lossy by design (a Rust `ReplayedTokenPayload`, a Java
  `Token<JsonNode>`), so the events are of the record type and a requirement compares their
  number and order, not their content.
* **A codec** (`ArchiveCodec D E`): an implementation's writer and reader, observed.
  `write S h dh w d a` says that writing header version `w` for a session with header fields `d`,
  whose event store `S` has the operation history `h` when the write starts and runs the further
  operations `dh` while the write runs (another thread still appending), can produce the archive
  `a`. It is a relation so that a writer that reads the store twice, or renders a map in a
  per-process order, is a codec too. `read a` is the reader's result or its error message.
* **A read during the write** (`ReadDuring S h dh l`): `l` is the list a call of `events()` on
  `S` returns at some moment of the write, after `h` and a prefix of `dh`.

## The reference (`refArchive`)

The reference writer takes one snapshot of the store, at some moment during the write, and
derives the whole archive from it, for every version it is asked for: the version tag, the
session fields as given,
`eventCount` the length of the snapshot, the metadata of the snapshot (none for V1) and the
snapshot as the body (`refForm`). This is what all three writers do: one call of `events()` feeds
the header and the body (rust/libpetri-debug/src/archive/session_archive_writer.rs `write_v1`,
`write_v2`, `write_v3`; java/src/main/java/org/libpetri/debug/archive/SessionArchiveWriter.java
`writeV1` to `writeV3`; typescript/src/debug/archive/session-archive-writer.ts, which copies the
live array once and freezes it).

The reference reader dispatches on the version tag: 1, 2 and 3 into `V1`, `V2` and `V3`, with
the header's fields as written and one event per record, in body order; any other number fails
with the message all
three readers produce, `Unsupported archive version: <v> (reader supports 1..3)`
(`session_archive_reader.rs` `parse_header`, `SessionArchiveReader.java` `readHeader`,
`session-archive-reader.ts` `parseHeader`).
-/

namespace Libpetri.Spec

/-! ## Vocabulary -/

/-- The three header versions a reader dispatches into (the sealed variants `V1`, `V2`, `V3`). A
writer is asked for one of them (`writeV1`, `writeV2`, and `write` or `writeV3` for version 3). -/
inductive ArchiveVer where
  /-- Header version 1 (libpetri 1.5.x): no end time, tags or metadata. -/
  | v1
  /-- Header version 2 (libpetri 1.7.x): adds end time, tags and metadata. -/
  | v2
  /-- Header version 3 (libpetri 1.8.0): the fields of version 2; signals typed token bodies. -/
  | v3
  deriving DecidableEq, Repr, Inhabited

namespace ArchiveVer

/-- The version number a header of this variant carries. -/
def toNat : ArchiveVer → Nat
  | v1 => 1
  | v2 => 2
  | v3 => 3

/-- The variant a version number dispatches into, if it is one of the three. -/
def ofNat? : Nat → Option ArchiveVer
  | 1 => some v1
  | 2 => some v2
  | 3 => some v3
  | _ => none

/-- Every variant's number is one of the three supported. -/
theorem toNat_mem (w : ArchiveVer) : w.toNat ∈ [1, 2, 3] := by
  cases w <;> decide

/-- The number of a variant is the number of no other variant. -/
theorem toNat_inj {w w' : ArchiveVer} (h : w.toNat = w'.toNat) : w = w' := by
  cases w <;> cases w' <;> first | rfl | (simp [toNat] at h)

/-- `ofNat?` finds exactly the variant whose number it is given. -/
theorem ofNat?_eq_some {n : Nat} {w : ArchiveVer} : ofNat? n = some w ↔ w.toNat = n := by
  constructor
  · intro h
    match n, h with
    | 1, h => cases h; rfl
    | 2, h => cases h; rfl
    | 3, h => cases h; rfl
  · intro h
    subst h
    cases w <;> rfl

/-- A supported number has a variant. -/
theorem ofNat?_of_mem {n : Nat} (h : n ∈ [1, 2, 3]) : ∃ w, ofNat? n = some w := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact ⟨v1, rfl⟩
  · exact ⟨v2, rfl⟩
  · exact ⟨v3, rfl⟩

/-- Any other number has none. -/
theorem ofNat?_of_not_mem {n : Nat} (h : n ∉ [1, 2, 3]) : ofNat? n = none := by
  cases hw : ofNat? n with
  | none => rfl
  | some w =>
    rw [ofNat?_eq_some] at hw
    exact absurd (hw ▸ toNat_mem w) h

end ArchiveVer

/-- The stand-in for the V2/V3 metadata: the number of events, and the first and last event (the
runtimes keep an event-type histogram, the first and last timestamp and a `hasErrors` flag). -/
structure ArchiveMeta (E : Type) where
  /-- The number of events. -/
  count : Nat
  /-- The first event, if any. -/
  first : Option E
  /-- The last event, if any. -/
  last : Option E
  deriving DecidableEq, Repr

/-- **Glossary: Session archive** (proposed term). A session archive as written, without bytes:
the header (version tag, the session's own fields, `eventCount`, the V2/V3 metadata) and the
body, one record per event. -/
structure Archive (D E : Type) where
  /-- The header's version tag, as written. -/
  version : Nat
  /-- The session's own header fields (session id, net name, DOT diagram, times, tags,
  structure). -/
  data : D
  /-- The header's `eventCount`. -/
  eventCount : Nat
  /-- The V2/V3 metadata; `none` in a V1 header. -/
  metadata : Option (ArchiveMeta E)
  /-- The body: one record per event, in body order. -/
  recs : List E
  deriving DecidableEq, Repr

/-- What a reader returns for an archive it accepts: the header variant it dispatched into, the
header fields, and the events it hydrated from the body. -/
structure ArchiveRead (D E : Type) where
  /-- The sealed header variant (`V1`, `V2` or `V3`). -/
  variant : ArchiveVer
  /-- The session's own header fields. -/
  data : D
  /-- The header's `eventCount`, as the reader returns it. -/
  eventCount : Nat
  /-- The V2/V3 metadata, as the reader returns it. -/
  metadata : Option (ArchiveMeta E)
  /-- The events hydrated from the body. -/
  events : List E
  deriving DecidableEq, Repr

/-- The error message of a reader that meets a header version it does not support: it names the
version and the supported range. All three runtimes produce this text. -/
def unsupportedMsg (v : Nat) : String :=
  s!"Unsupported archive version: {v} (reader supports 1..3)"

/-- **Glossary: Same content** (proposed term). `same x y`: `x` and `y` render the same JSON value,
read as an unordered object (a JSON object is an unordered collection, so key order is not part
of the content). It is an equivalence. -/
class SameContent (α : Type) where
  /-- `x` and `y` render the same JSON value. -/
  same : α → α → Prop
  /-- Same content is an equivalence. -/
  equiv : Equivalence same

/-- Same content for a type with no JSON object inside: equality. -/
@[reducible] def SameContent.byEq (α : Type) : SameContent α :=
  ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩

instance : SameContent Unit := SameContent.byEq Unit
instance : SameContent Nat := SameContent.byEq Nat
instance : SameContent String := SameContent.byEq String

/-- A list of key and value entries renders as a JSON object, so two such lists are the same
content when one is a permutation of the other (a marking in the snapshot form, a tag map). -/
instance {K V : Type} : SameContent (List (K × V)) :=
  ⟨List.Perm, ⟨List.Perm.refl, List.Perm.symm, List.Perm.trans⟩⟩

/-- Two lists of records are the same content position by position: as many records, the `i`-th
of one the same content as the `i`-th of the other. -/
def SameRecs {E : Type} [SameContent E] : List E → List E → Prop
  | [], [] => True
  | x :: xs, y :: ys => SameContent.same x y ∧ SameRecs xs ys
  | _, _ => False

/-- Every list of records is the same content as itself. -/
theorem SameRecs.refl {E : Type} [SameContent E] : (l : List E) → SameRecs l l
  | [] => trivial
  | x :: xs => ⟨SameContent.equiv.refl x, SameRecs.refl xs⟩

/-- Lists of records of the same content have the same length. -/
theorem SameRecs.length_eq {E : Type} [SameContent E] :
    {xs ys : List E} → SameRecs xs ys → xs.length = ys.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => congrArg (· + 1) (SameRecs.length_eq h.2)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- For records whose same content is equality, same content of lists is equality. -/
theorem SameRecs.eq_iff {E : Type} [SameContent E]
    (hE : ∀ x y : E, SameContent.same x y ↔ x = y) : {xs ys : List E} → (SameRecs xs ys ↔ xs = ys)
  | [], [] => by simp [SameRecs]
  | x :: xs, y :: ys => by simp [SameRecs, hE, SameRecs.eq_iff hE (xs := xs) (ys := ys)]
  | [], _ :: _ => by simp [SameRecs]
  | _ :: _, [] => by simp [SameRecs]

/-- Each record mapped by a function that keeps its content is the same content as the record. -/
theorem SameRecs.map {E : Type} [SameContent E] {f : E → E}
    (hf : ∀ x, SameContent.same (f x) x) : (l : List E) → SameRecs (l.map f) l
  | [] => trivial
  | x :: xs => ⟨hf x, SameRecs.map hf xs⟩

/-- The metadata of the events `l` in a header of version `w`: none for a V1 header (version 1
has no metadata); for V2 and V3 the number of events and the first and last event. -/
def archiveMeta {E : Type} (w : ArchiveVer) (l : List E) : Option (ArchiveMeta E) :=
  match w with
  | .v1 => none
  | _ => some ⟨l.length, l.head?, l.getLast?⟩

/-- **Glossary: Well-formed archive** (proposed term). An archive whose header agrees with its
body: its version is that of some variant `w`, and its `eventCount`, its metadata and its body
come from one list of events `l` (the count is the length of `l`, the metadata that of `l` for
`w`, the body the same content as `l`). Every archive a writer meeting [EVT-025] writes is well
formed. -/
def Archive.WellFormed {D E : Type} [SameContent E] (a : Archive D E) : Prop :=
  ∃ w : ArchiveVer, ∃ l : List E, a.version = w.toNat ∧ a.eventCount = l.length ∧
    a.metadata = archiveMeta w l ∧ SameRecs a.recs l

/-- `l` is what a call of `events()` on `S` returns at some moment of a write that starts after
the history `h` and during which the operations `dh` run: after `h` and the first `j` of `dh`. -/
def ReadDuring {E : Type} (S : StoreObs E) (h dh : List (StoreOp E)) (l : List E) : Prop :=
  ∃ j, j ≤ dh.length ∧ l = S.read (h ++ dh.take j) []

/-- **Glossary: Archive codec** (proposed term). An implementation's session archive writer and
reader, observed:

* `write S h dh w d a`: writing header version `w` for a session with header fields `d`, whose
  event store `S` has the history `h` when the write starts and runs `dh` during the write, can
  produce the archive `a`;
* `read a`: what the reader returns for `a`, or its error message. -/
structure ArchiveCodec (D E : Type) where
  /-- The writer, as a relation (it may read the store at a moment of its choice). -/
  write : StoreObs E → List (StoreOp E) → List (StoreOp E) → ArchiveVer → D → Archive D E → Prop
  /-- The reader. -/
  read : Archive D E → Except String (ArchiveRead D E)

/-- With no operation during the write, the one moment to read at is after `h`. -/
theorem readDuring_nil {E : Type} {S : StoreObs E} {h : List (StoreOp E)} {l : List E} :
    ReadDuring S h [] l ↔ l = S.read h [] := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    simp
  · rintro rfl
    exact ⟨0, Nat.le_refl 0, by simp⟩

end Libpetri.Spec

namespace Libpetri.Reference

open Libpetri.Spec

variable {D E : Type}

/-! ## The reference codec -/

/-- The archive the reference writer forms from one snapshot `l`: version `w`, the session fields
as given, `eventCount` the length of `l`, the metadata of `l`, and `l` as the body. -/
def refForm (w : ArchiveVer) (d : D) (l : List E) : Archive D E :=
  ⟨w.toNat, d, l.length, archiveMeta w l, l⟩

/-- The reference reader: versions 1, 2 and 3 dispatch into `V1`, `V2` and `V3` with the
header's fields as written and the body's records as the events, in body order; any other
version fails with `unsupportedMsg`. -/
def refArchiveRead (a : Archive D E) : Except String (ArchiveRead D E) :=
  match ArchiveVer.ofNat? a.version with
  | some w => .ok ⟨w, a.data, a.eventCount, a.metadata, a.recs⟩
  | none => .error (unsupportedMsg a.version)

/-- **The reference codec** ([EVT-025]): the writer forms the archive from one read of the store
made during the write (`refForm`), the reader is `refArchiveRead`. -/
def refArchive : ArchiveCodec D E where
  write S h dh w d a := ∃ l, ReadDuring S h dh l ∧ a = refForm w d l
  read := refArchiveRead

#spec_witness refArchive

/-! ## Lemmas on the reference reader -/

/-- The reference reader accepts every supported version, into the variant of that number. -/
theorem refArchiveRead_mem (a : Archive D E) (h : a.version ∈ [1, 2, 3]) :
    ∃ r, refArchiveRead a = .ok r ∧ r.variant.toNat = a.version := by
  obtain ⟨w, hw⟩ := ArchiveVer.ofNat?_of_mem h
  exact ⟨⟨w, a.data, a.eventCount, a.metadata, a.recs⟩, by simp [refArchiveRead, hw],
    ArchiveVer.ofNat?_eq_some.mp hw⟩

/-- The reference reader rejects every other version with `unsupportedMsg`. -/
theorem refArchiveRead_not_mem (a : Archive D E) (h : a.version ∉ [1, 2, 3]) :
    refArchiveRead a = .error (unsupportedMsg a.version) := by
  simp [refArchiveRead, ArchiveVer.ofNat?_of_not_mem h]

/-- What the reference reader returns carries the header's fields as written (`eventCount`, the
session fields, the metadata) and the body's records as its events. -/
theorem refArchiveRead_ok {a : Archive D E} {r : ArchiveRead D E}
    (h : refArchiveRead a = .ok r) :
    r.eventCount = a.eventCount ∧ r.events = a.recs ∧ r.data = a.data ∧
      r.metadata = a.metadata := by
  unfold refArchiveRead at h
  split at h
  · cases h; exact ⟨rfl, rfl, rfl, rfl⟩
  · cases h

/-- The archive the reference writer forms is well formed. -/
theorem refForm_wellFormed [SameContent E] (w : ArchiveVer) (d : D) (l : List E) :
    (refForm w d l).WellFormed :=
  ⟨w, l, rfl, rfl, rfl, SameRecs.refl l⟩

/-- With no operation during the write, the reference writer's archive is the form of the one
read after `h`. -/
theorem refArchive_write_nil {S : StoreObs E} {h : List (StoreOp E)} {w : ArchiveVer} {d : D}
    {a : Archive D E} :
    refArchive.write S h [] w d a ↔ a = refForm w d (S.read h []) := by
  show (∃ l, ReadDuring S h [] l ∧ a = refForm w d l) ↔ _
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [readDuring_nil.mp hl]
  · rintro rfl
    exact ⟨_, readDuring_nil.mpr rfl, rfl⟩

end Libpetri.Reference
