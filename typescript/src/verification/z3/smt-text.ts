/**
 * @module smt-text
 *
 * Text-level helpers shared by the transport, the Spacer runner, the certificate
 * check and the counterexample decoder (VER-013). Byte-for-byte mirrors of the Rust
 * `z3_process` / `smt_verifier` helpers and the Java `SmtText` class.
 */

/**
 * The first trimmed stdout line that is a `(check-sat)` answer, or `null`. The answer
 * is a LINE anywhere in the reply, not the first bytes: a build is free to print a
 * warning first, and a HORN script that asks for both a proof and a model always gets
 * one `(error …)` line back.
 */
export function classifyFirstLine(stdout: string): 'sat' | 'unsat' | 'unknown' | null {
  for (const raw of stdout.split('\n')) {
    const line = raw.trim();
    if (line === 'sat' || line === 'unsat' || line === 'unknown') return line;
  }
  return null;
}

/** True when z3's `-T` backstop fired: it prints the single line `timeout`. */
export function timeoutLine(stdout: string): boolean {
  return stdout.split('\n').some((l) => l.trim() === 'timeout');
}

/** The first `(error …)` line in a z3 stream, trimmed; `null` if none. */
export function errorLine(text: string): string | null {
  for (const raw of text.split('\n')) {
    const line = raw.trim();
    if (line.startsWith('(error')) return line;
  }
  return null;
}

/**
 * Returns the index one past the `)` matching the `(` at `start`, or `-1` when the
 * expression is unbalanced. Paren counting skips string literals (`"…"`, with `""`
 * escapes) and quoted symbols (`|…|`).
 */
export function sexprEnd(s: string, start: number): number {
  let depth = 0;
  let inString = false;
  let inSymbol = false;
  for (let i = start; i < s.length; i++) {
    const c = s[i]!;
    if (inString) {
      if (c === '"') inString = false;
    } else if (inSymbol) {
      if (c === '|') inSymbol = false;
    } else if (c === '"') {
      inString = true;
    } else if (c === '|') {
      inSymbol = true;
    } else if (c === '(') {
      depth++;
    } else if (c === ')') {
      depth--;
      if (depth === 0) return i + 1;
    }
  }
  return -1;
}

/**
 * Every complete `(define-fun …)` s-expression in `output`, in order. A truncated
 * (unbalanced) definition is dropped rather than half-captured.
 */
export function extractDefineFuns(output: string): string[] {
  const defs: string[] = [];
  let from = 0;
  for (;;) {
    const pos = output.indexOf('(define-fun', from);
    if (pos < 0) break;
    const end = sexprEnd(output, pos);
    if (end < 0) break;
    defs.push(output.slice(pos, end));
    from = end;
  }
  return defs;
}

/**
 * The inductive invariant of a `sat` reply: every `(define-fun …)` of the
 * `(get-model)` block joined with newlines, or `null` when no model was printed.
 */
export function extractInvariant(output: string): string | null {
  const defs = extractDefineFuns(output);
  return defs.length === 0 ? null : defs.join('\n');
}
