/**
 * Tests for the doclet plugin's subnet-aware rendering pipeline. Mirrors
 * `java/src/test/java/org/libpetri/doclet/SubnetTagletTest.java`.
 *
 * The Java tests stub a `javax.lang.model.element.Element` and run the
 * taglet end-to-end through reflection. TypeScript has no equivalent
 * reflection layer; instead, we exercise the same code paths the plugin
 * dispatches to (`subnet-dot-export`, `subnet-header`, `diagram-renderer`,
 * `net-resolver`'s `classify`) directly with in-memory fixtures.
 *
 * The combined coverage is structurally equivalent — a regression in any
 * of the above components surfaces here.
 */

import { describe, expect, it } from 'vitest';
import { producer, boundedBuffer } from '../fixtures/subnet-fixtures.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { fullBody, interfaceOnly } from '../../src/doclet/subnet-dot-export.js';
import { forSubnetDef, forInstance } from '../../src/doclet/subnet-header.js';
import { renderSvg, renderSubnetSvg } from '../../src/doclet/diagram-renderer.js';
import { resolveNet } from '../../src/doclet/net-resolver.js';
import { dotExport } from '../../src/export/dot-exporter.js';

describe('doclet/subnet plugin', () => {
  describe('subnet-dot-export', () => {
    it('full-body restyles port places with the interface-port category', () => {
      // Producer has one output port "output" → port place id is "p_output".
      // In the body DOT, that node is rendered with the default place style
      // (fillcolor="#FFFFFF"); after restyleNode, fillcolor must be the
      // interface-port colour "#e7f1ff".
      const def = producer();
      const dot = fullBody(def);

      // The port node must carry the interface-port fillcolor.
      // We assert on the substring "p_output [" line with the new fill.
      const portLineStart = dot.indexOf('p_output [');
      expect(portLineStart).toBeGreaterThan(0);
      const portLineEnd = dot.indexOf('];', portLineStart);
      const portLine = dot.substring(portLineStart, portLineEnd);
      expect(portLine).toContain('fillcolor="#e7f1ff"');
      expect(portLine).toContain('color="#1d4ed8"');
      // The interface-port style adds the `dashed` modifier.
      expect(portLine).toContain('"filled,dashed"');
    });

    it('full-body wraps port places in a `cluster_iface_<name>` block', () => {
      const def = producer();
      const dot = fullBody(def);

      expect(dot).toContain('subgraph cluster_iface_Producer {');
      expect(dot).toContain('label="interface";');
      // Port node id must appear inside the cluster block.
      const ifaceStart = dot.indexOf('cluster_iface_Producer {');
      const ifaceEnd = dot.indexOf('}', ifaceStart);
      const ifaceBlock = dot.substring(ifaceStart, ifaceEnd);
      expect(ifaceBlock).toContain('p_output;');
    });

    it('interface-only diagram emits port nodes + stub but NOT body transitions', () => {
      // Producer's body transition is "produce" → node id "t_produce".
      const def = producer();
      const dot = interfaceOnly(def);

      expect(dot).toContain('digraph Producer {');
      expect(dot).toContain('rankdir=LR;');
      // Port place nodes are present.
      expect(dot).toContain('p_output [');
      // Stub node with the "(internals omitted)" marker.
      expect(dot).toContain('stub_Producer [');
      expect(dot).toContain('(internals omitted)');
      // Body transition MUST NOT appear (interface-only filters it out).
      expect(dot).not.toContain('t_produce ');
      // The "nextItem" internal place must NOT appear either.
      expect(dot).not.toContain('p_nextItem ');
    });

    it('interface-only handles bounded-buffer (input + output ports)', () => {
      // boundedBuffer(2) names the def "BoundedBuffer-2"; sanitize() turns
      // the '-' into '_' for the stub node id and digraph id.
      const def = boundedBuffer(2);
      const dot = interfaceOnly(def);

      // Both ports present.
      expect(dot).toContain('p_put [');
      expect(dot).toContain('p_get [');
      // Stub (sanitized "BoundedBuffer-2" → "BoundedBuffer_2").
      expect(dot).toContain('stub_BoundedBuffer_2 [');
      // Edge from input → stub and stub → output.
      expect(dot).toContain('p_put -> stub_BoundedBuffer_2');
      expect(dot).toContain('stub_BoundedBuffer_2 -> p_get');
      // No body transitions.
      expect(dot).not.toContain('t_enqueue ');
      expect(dot).not.toContain('t_dequeue ');
    });
  });

  describe('subnet-header', () => {
    it('forSubnetDef emits header div with subnet name and per-port badges', () => {
      // boundedBuffer(2) yields name "BoundedBuffer-2" — assert on the
      // exact value the fixture produces.
      const def = boundedBuffer(2);
      const html = forSubnetDef(def, /* interfaceOnly */ false);

      expect(html).toContain('<div class="subnet-header">');
      expect(html).toContain('<span class="subnet-header-label">subnet</span>');
      expect(html).toContain('<span class="subnet-header-name">BoundedBuffer-2</span>');
      // Both port direction badges are rendered.
      expect(html).toContain('interface-port-badge-input');
      expect(html).toContain('interface-port-badge-output');
      expect(html).toContain('put');
      expect(html).toContain('get');
      // Without the interfaceOnly flag, no "interface only" badge.
      expect(html).not.toContain('interface only');
    });

    it('forSubnetDef adds the "interface only" badge when the flag is set', () => {
      const def = producer();
      const html = forSubnetDef(def, /* interfaceOnly */ true);

      expect(html).toContain('subnet-header-badge-interface');
      expect(html).toContain('interface only');
    });

    it('forInstance emits prefix + def name in the header', () => {
      const def = producer();
      const inst = def.instantiate('p1');
      const html = forInstance(inst);

      expect(html).toContain('<span class="subnet-header-label">instance</span>');
      // Prefix appears as a name span.
      expect(html).toContain('>p1<');
      // "of" connective + def name.
      expect(html).toContain('>of<');
      expect(html).toContain('Producer');
      // Interface badges still rendered.
      expect(html).toContain('interface-port-badge-output');
    });
  });

  describe('diagram-renderer', () => {
    it('renderSvg emits the petrinet-diagram wrapper without subnet-diagram class', () => {
      const html = renderSvg('PlainNet', 'digraph PlainNet { }');

      expect(html).toContain('class="petrinet-diagram"');
      expect(html).not.toContain('petrinet-diagram subnet-diagram');
      expect(html).toContain('PlainNet');
      // The canonical viewer renders chrome (legend + filter strip) itself
      // when mounted with `chrome: true`. The doclet HTML must therefore
      // NOT carry the pre-existing empty placeholder divs from the old
      // `PetriNetDiagrams` shim.
      expect(html).not.toContain('class="diagram-legend"');
      expect(html).not.toContain('class="diagram-filter-strip"');
      expect(html).not.toContain('btn-toggle-clusters');
      expect(html).not.toContain('PetriNetDiagrams.');
      // The mount container carries the DOT source as a data attribute and
      // the marker the init script uses to find it.
      expect(html).toContain('data-libpetri-diagram="true"');
      expect(html).toContain('data-dot="digraph PlainNet { }"');
    });

    it('renderSubnetSvg emits the subnet-diagram wrapper with header block', () => {
      const headerHtml = '<div class="subnet-header">HEADER</div>';
      const html = renderSubnetSvg('Sub', headerHtml, 'digraph Sub { }');

      expect(html).toContain('class="petrinet-diagram subnet-diagram"');
      expect(html).toContain('HEADER');
      expect(html).toContain('Sub');
      expect(html).toContain('data-libpetri-diagram="true"');
    });

    it('inlines the resource CSS and JS', () => {
      const html = renderSvg('X', 'digraph X { }');

      // CSS class declared in petrinet-diagrams.css.
      expect(html).toContain('.petrinet-diagram');
      // The new canonical viewer exposes its API on globalThis as
      // `LibpetriViewer`. Assert on the namespace assignment so we catch
      // any future bundle drift.
      expect(html).toContain('LibpetriViewer');
      // Idempotency guard so multiple `@petrinet` tags on one page only
      // inline the IIFE once.
      expect(html).toContain('_libpetriViewerInit');
      // Per-diagram init snippet calls mount() with chrome enabled.
      expect(html).toContain('LibpetriViewer.mount');
      expect(html).toContain('chrome:true');
    });

    it('escapes the DOT source inside the data-dot attribute', () => {
      // A DOT body containing `"`, `<`, `&`, and `'` must be encoded so the
      // attribute parses correctly — otherwise the embedded HTML breaks.
      const trickyDot = 'digraph T { a [label="a&b <c> \'d\""] }';
      const html = renderSvg('Tricky', trickyDot);

      // Every special character must be encoded as an entity.
      expect(html).not.toContain('data-dot="digraph T { a [label="a&b');
      expect(html).toContain('&amp;');
      expect(html).toContain('&lt;');
      expect(html).toContain('&gt;');
      expect(html).toContain('&quot;');
      expect(html).toContain('&#39;');
    });
  });

  describe('net-resolver classification', () => {
    it('resolveNet classifies a SubnetDef from a same-file fixture export', async () => {
      // Use this very test file — it re-exports `__fixture_subnet` below so
      // the dynamic-import resolver can find it on disk.
      const here = __filename();
      const result = await resolveNet('#__fixture_subnet', here);

      expect(result).not.toBeNull();
      expect(result!.kind).toBe('subnet');
      expect(result!.title).toBe('Producer');
    });

    it('resolveNet classifies a PetriNet from a same-file fixture export', async () => {
      const here = __filename();
      const result = await resolveNet('#__fixture_net', here);

      expect(result).not.toBeNull();
      expect(result!.kind).toBe('net');
      expect(result!.title).toBe('PlainNet');
    });

    it('resolveNet classifies an Instance from a same-file fixture export', async () => {
      const here = __filename();
      const result = await resolveNet('#__fixture_instance', here);

      expect(result).not.toBeNull();
      expect(result!.kind).toBe('instance');
      // Instance title is "<defName> :: <prefix>".
      expect(result!.title).toBe('Producer :: p1');
    });

    it('resolveNet returns null for unknown export name', async () => {
      const here = __filename();
      const result = await resolveNet('#nope_does_not_exist', here);
      expect(result).toBeNull();
    });
  });

  describe('cluster markup smoke test (composed net)', () => {
    it('full-body DOT for a composed net carries `subgraph cluster_<prefix>`', () => {
      // Compose a producer instance into a host net; the resulting DOT
      // (via the standard dotExport pipeline that the @petrinet renderer
      // calls for `kind === 'net'`) must carry the cluster block — this is
      // the input the runtime JS uses to discover clusters.
      const inst = producer().instantiate('p1');
      const host = PetriNet.builder('Host').compose(inst, new Map()).build();
      const dot = dotExport(host);

      expect(dot).toContain('subgraph cluster_p1');
    });
  });
});

// ============================================================
//  Fixtures exported from this module so resolveNet can import them.
//  (resolveNet uses dynamic import; same-file references work because
//  vitest exposes the test module's compiled URL.)
// ============================================================

export const __fixture_subnet = producer();
export const __fixture_instance = __fixture_subnet.instantiate('p1');

const __plain_in = place<string>('IN');
const __plain_out = place<string>('OUT');
const __plain_t = Transition.builder('Process')
  .inputs(one(__plain_in))
  .outputs(outPlace(__plain_out))
  .build();
export const __fixture_net: PetriNet = PetriNet.builder('PlainNet')
  .transition(__plain_t)
  .build();

/** Returns the absolute path of this test module. ESM doesn't expose
 * `__filename` natively, so we derive it from `import.meta.url`. */
function __filename(): string {
  return new URL(import.meta.url).pathname;
}
