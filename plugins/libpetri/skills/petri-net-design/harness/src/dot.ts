/**
 * DOT export of a design candidate. Uses the library's own exporter with its default configuration,
 * so the text is byte-identical to what Java `DotExporter.export(net)`, Rust `dot_export(&net, None)`,
 * Python `libpetri.dot_export(net)` and TS `dotExport(net)` produce for the same net (EXP-014).
 */
import type { PetriNet } from 'libpetri';
import { dotExport } from 'libpetri/export';

export function candidateDot(net: PetriNet): string {
  return dotExport(net);
}
