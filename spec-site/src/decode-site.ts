/**
 * Decoders for every type of `model.ts`. Each constant is annotated with its model type, so the
 * compiler fails when the model and the decoder disagree (a missing field, a wrong type).
 * The object decoders are exact at run time, so an extra field fails too.
 *
 * The app decodes `SiteData` once at start (`app/data.ts`). Generator input modules reuse the
 * pieces (`situation`, `replayResult`, ...) where their input already has the model shape.
 */
import {
  arr,
  bool,
  type Decoder,
  int,
  lazy,
  lit,
  nullable,
  num,
  obj,
  oneOf,
  rec,
  str,
  tagged,
} from './decode.js';
import {
  type BlockNote,
  type BlockReason,
  type BlockStatus,
  type BodyParagraph,
  type Citation,
  type CorpusNet,
  type CoverageRow,
  type Defect,
  type DefectStatus,
  type Edge,
  EVIDENCE_ROLES,
  type Evidence,
  type GlossaryTerm,
  type InputArc,
  type LeanBlock,
  type LeanProof,
  type Marking,
  NOT_REPLAYED,
  type NetProperty,
  type NetTransition,
  type OutputSpec,
  PRIORITIES,
  REQ_KINDS,
  type ReasonArc,
  type ReplayResult,
  type ReplayStep,
  RUNTIMES,
  type RuleLink,
  type Signoff,
  SITUATION_GROUPS,
  STEP_EXPECTS,
  type SiteCounts,
  type SiteData,
  type SiteLinks,
  type Situation,
  type SituationEntry,
  type SituationRule,
  type SituationStep,
  type SpecBlock,
  type SpecFile,
  type SpecSection,
  type TestCoverage,
  type Timing,
} from './model.js';

const strs = arr(str);
const priority = oneOf(PRIORITIES);
const reqKind = oneOf(REQ_KINDS);
const evidenceRole = oneOf(EVIDENCE_ROLES);
const runtime = oneOf(RUNTIMES);

export const specSection: Decoder<SpecSection> = obj({ title: str, ids: strs });

export const specFile: Decoder<SpecFile> = obj({
  file: str,
  number: str,
  title: str,
  prefixes: strs,
  sections: arr(specSection),
});

export const blockStatus: Decoder<BlockStatus> = tagged('state', {
  active: obj({ state: lit('active') }),
  proposed: obj({ state: lit('proposed') }),
  removed: obj({ state: lit('removed') }),
});

export const bodyParagraph: Decoder<BodyParagraph> = tagged('kind', {
  prose: obj({ kind: lit('prose'), text: str }),
  shall: obj({ kind: lit('shall'), text: str }),
  code: obj({ kind: lit('code'), text: str }),
});

export const blockNote: Decoder<BlockNote> = obj({ label: str, text: str });

export const specBlock: Decoder<SpecBlock> = obj({
  id: str,
  title: str,
  file: str,
  line: int,
  section: nullable(str),
  priority: nullable(priority),
  kind: nullable(reqKind),
  status: blockStatus,
  body: arr(bodyParagraph),
  acceptance: strs,
  notes: arr(blockNote),
  dependsOn: strs,
  mentions: strs,
  testDerivation: nullable(str),
  terms: strs,
});

export const glossaryTerm: Decoder<GlossaryTerm> = obj({
  term: str,
  slug: str,
  group: str,
  text: str,
  refs: strs,
});

export const evidence: Decoder<Evidence> = obj({
  theorem: str,
  role: evidenceRole,
  module: str,
  doc: nullable(str),
});

export const signoff: Decoder<Signoff> = tagged('state', {
  pending: obj({ state: lit('pending') }),
  signed: obj({ state: lit('signed'), date: str, hash: str, by: oneOf(['person', 'ai'] as const) }),
});

export const leanBlock: Decoder<LeanBlock> = obj({
  id: str,
  title: str,
  decl: str,
  module: str,
  kind: reqKind,
  sourceRef: str,
  source: str,
  scope: str,
  quotes: strs,
  reading: strs,
  assumes: strs,
  statement: str,
  signoff,
  hash: str,
  evidence: arr(evidence),
});

export const citation: Decoder<Citation> = obj({ id: str, theorem: str, module: str, fragment: str });

export const leanProof: Decoder<LeanProof> = obj({ theorem: str, fragment: str });

export const testCoverage: Decoder<TestCoverage> = tagged('state', {
  tested: obj({ state: lit('tested'), refs: strs }),
  untested: obj({ state: lit('untested') }),
});

export const coverageRow: Decoder<CoverageRow> = obj({
  id: str,
  leanProofs: arr(leanProof),
  leanRef: bool,
  tests: obj({ java: testCoverage, typescript: testCoverage, rust: testCoverage, python: testCoverage }),
});

export const defectStatus: Decoder<DefectStatus> = tagged('state', {
  open: obj({ state: lit('open') }),
  fixed: obj({ state: lit('fixed'), version: nullable(str) }),
});

export const defect: Decoder<Defect> = obj({
  id: str,
  title: str,
  requirements: strs,
  runtimes: arr(runtime),
  text: str,
  evidence: strs,
  evidenceText: str,
  fix: nullable(str),
  status: defectStatus,
});

export const inputArc: Decoder<InputArc> = tagged('kind', {
  one: obj({ kind: lit('one'), place: str }),
  exactly: obj({ kind: lit('exactly'), place: str, n: int }),
  all: obj({ kind: lit('all'), place: str }),
  atLeast: obj({ kind: lit('atLeast'), place: str, n: int }),
});

export const outputSpec: Decoder<OutputSpec> = tagged('type', {
  place: obj({ type: lit('place'), place: str }),
  and: obj({ type: lit('and'), children: arr(lazy(() => outputSpec)) }),
  xor: obj({ type: lit('xor'), children: arr(lazy(() => outputSpec)) }),
  timeout: obj({ type: lit('timeout'), afterMs: num, child: lazy(() => outputSpec) }),
  forward: obj({ type: lit('forward'), from: str, to: str }),
});

export const timing: Decoder<Timing> = obj({
  kind: oneOf(['immediate', 'unconstrained', 'deadline', 'delayed', 'window', 'exact']),
  earliestMs: nullable(num),
  latestMs: nullable(num),
});

export const netTransition: Decoder<NetTransition> = obj({
  name: str,
  inputs: arr(inputArc),
  inhibitors: strs,
  reads: strs,
  resets: strs,
  output: nullable(outputSpec),
  priority: int,
  timing: nullable(timing),
});

export const netProperty: Decoder<NetProperty> = tagged('type', {
  'deadlock-free': obj({ type: lit('deadlock-free'), id: str, sinks: strs }),
  'terminates-at-sink': obj({ type: lit('terminates-at-sink'), id: str, sinks: strs }),
  'place-bound': obj({ type: lit('place-bound'), id: str, place: str, bound: int }),
  'mutual-exclusion': obj({ type: lit('mutual-exclusion'), id: str, places: strs }),
  unreachable: obj({ type: lit('unreachable'), id: str, places: strs }),
  'quiescent-count': obj({ type: lit('quiescent-count'), id: str, places: strs, min: int, max: nullable(int) }),
});

export const marking: Decoder<Marking> = rec(int);

export const corpusNet: Decoder<CorpusNet> = obj({
  places: strs,
  marking,
  transitions: arr(netTransition),
  properties: arr(netProperty),
});

export const situationStep: Decoder<SituationStep> = obj({
  fire: str,
  branch: int,
  timeout: bool,
  text: nullable(str),
  expect: oneOf(STEP_EXPECTS),
});

const situationGroup = oneOf(SITUATION_GROUPS);
const notReplayed = nullable(oneOf(NOT_REPLAYED));

export const situation: Decoder<Situation> = obj({
  slug: str,
  title: str,
  text: str,
  group: situationGroup,
  cites: strs,
  replay: bool,
  notReplayed,
  net: corpusNet,
  steps: arr(situationStep),
});

export const reasonArc: Decoder<ReasonArc> = obj({
  kind: oneOf(['one', 'exactly', 'all', 'atLeast']),
  n: nullable(int),
});

export const blockReason: Decoder<BlockReason> = tagged('kind', {
  unknownTransition: obj({ kind: lit('unknownTransition') }),
  inputShort: obj({ kind: lit('inputShort'), place: str, arc: reasonArc, need: int, have: int }),
  inhibitorMarked: obj({ kind: lit('inhibitorMarked'), place: str, count: int }),
  readEmpty: obj({ kind: lit('readEmpty'), place: str }),
  noSuchBranch: obj({ kind: lit('noSuchBranch'), branch: int, timeout: bool }),
});

export const replayStep: Decoder<ReplayStep> = tagged('kind', {
  fired: obj({ kind: lit('fired'), index: int, fire: str, branch: int, timeout: bool, marking }),
  blocked: obj({
    kind: lit('blocked'),
    index: int,
    fire: str,
    branch: int,
    timeout: bool,
    reason: blockReason,
    requirement: str,
    message: str,
  }),
});

export const replayResult: Decoder<ReplayResult> = obj({
  slug: str,
  reference: str,
  initial: marking,
  complete: bool,
  steps: arr(replayStep),
});

export const ruleLink: Decoder<RuleLink> = tagged('kind', {
  cited: obj({ kind: lit('cited') }),
  step: obj({ kind: lit('step'), index: int }),
  exercised: obj({ kind: lit('exercised') }),
});

export const situationRule: Decoder<SituationRule> = obj({ id: str, links: arr(ruleLink) });

export const situationEntry: Decoder<SituationEntry> = obj({
  slug: str,
  title: str,
  text: str,
  group: situationGroup,
  cites: strs,
  replay: bool,
  notReplayed,
  net: corpusNet,
  steps: arr(situationStep),
  rules: arr(situationRule),
  result: nullable(replayResult),
  diagram: bool,
});

export const edge: Decoder<Edge> = tagged('kind', {
  'depends-on': obj({ kind: lit('depends-on'), from: str, to: str }),
  mentions: obj({ kind: lit('mentions'), from: str, to: str }),
  evidence: obj({ kind: lit('evidence'), from: str, to: str, role: evidenceRole }),
  cites: obj({ kind: lit('cites'), from: str, to: str }),
  'uses-term': obj({ kind: lit('uses-term'), from: str, to: str }),
  exercises: obj({ kind: lit('exercises'), from: str, to: str }),
  breaks: obj({ kind: lit('breaks'), from: str, to: str }),
});

export const siteCounts: Decoder<SiteCounts> = obj({
  specFiles: int,
  activeIds: int,
  removedIds: int,
  proposedIds: int,
  leanBlocks: int,
  leanIds: int,
  signedBlocks: int,
  citedIds: int,
  openDefects: int,
  situations: int,
  replayed: int,
  glossaryTerms: int,
  untestedIds: int,
});

export const siteLinks: Decoder<SiteLinks> = obj({ repo: str, blob: str, proofGraph: str, home: str });

export const siteData: Decoder<SiteData> = obj({
  schema: lit(1),
  contentHash: str,
  counts: siteCounts,
  links: siteLinks,
  files: arr(specFile),
  blocks: arr(specBlock),
  glossary: arr(glossaryTerm),
  lean: rec(arr(leanBlock)),
  citations: arr(citation),
  coverage: rec(coverageRow),
  defects: arr(defect),
  situations: arr(situationEntry),
  edges: arr(edge),
});
