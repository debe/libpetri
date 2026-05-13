/**
 * Prefix-derivation helpers for subnet-instance-aware export and debug
 * tooling, per `spec/11-modular-composition.md` **MOD-040** (export
 * grouping) and **MOD-041** (debug protocol subnet instances).
 *
 * The `"/"` character is the prefix separator established by **MOD-010**:
 * a node named `"outer/inner/leaf"` belongs to the cluster tree
 * `outer -> outer/inner`, with `"leaf"` as the un-prefixed final segment.
 *
 * This module is observability-only — it never inspects {@link
 * import('../core/subnet-def').SubnetDef} or {@link
 * import('../core/instance').Instance} objects, only the resulting
 * prefixed names that survived composition. That keeps consumers (DOT
 * exporter, debug protocol handler) decoupled from the modular-composition
 * layer per **MOD-023**.
 *
 * @module export/subnet-prefixes
 */

/**
 * Returns the instance prefix carried by the given node name, or `undefined`
 * when the name has no `/` (i.e. is not part of any composed subnet
 * instance).
 *
 * The prefix is the substring up to (but not including) the **last** `/`
 * — so `"producer1/internal"` returns `"producer1"` and
 * `"outer/inner/leaf"` returns `"outer/inner"`. The bare segment after the
 * last `/` is the original (un-prefixed) place or transition name.
 *
 * @param nodeName the prefixed-or-flat node name
 * @returns the prefix, or `undefined` for flat names
 */
export function instancePrefixOf(nodeName: string | null | undefined): string | undefined {
  if (nodeName == null) return undefined;
  const idx = nodeName.lastIndexOf('/');
  if (idx <= 0) return undefined;
  return nodeName.substring(0, idx);
}

/**
 * Returns the parent prefix of a given prefix, or `undefined` if the prefix
 * is top-level (single segment, no `/`).
 *
 * Used by the debug protocol's {@code SubnetInstance.parentPrefix} field
 * per **MOD-041** for nested instances.
 *
 * @param prefix an instance prefix string (e.g. `"outer/inner"`)
 * @returns the parent prefix (e.g. `"outer"`), or `undefined` for top-level
 */
export function parentOf(prefix: string | null | undefined): string | undefined {
  if (prefix == null || prefix.length === 0) return undefined;
  const idx = prefix.lastIndexOf('/');
  if (idx <= 0) return undefined;
  return prefix.substring(0, idx);
}

/**
 * Returns the last (leaf) segment of a prefix, used as the cluster label per
 * **MOD-040**. For top-level prefixes the input itself is returned unchanged.
 *
 * @param prefix an instance prefix string
 * @returns the trailing segment after the last `/` (or the input when there
 *          is no `/`)
 */
export function leafSegment(prefix: string | null | undefined): string | null | undefined {
  if (prefix == null || prefix.length === 0) return prefix;
  const idx = prefix.lastIndexOf('/');
  return idx < 0 ? prefix : prefix.substring(idx + 1);
}
