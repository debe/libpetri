import { describe, expect, it } from 'vitest';
import { decode } from '../src/decode.js';
import { siteData } from '../src/decode-site.js';
import { generate } from '../src/gen/build.js';
import { REPO_ROOT } from '../src/gen/paths.js';
import { SITE_DATA_ELEMENT_ID } from '../src/model.js';

describe('build', () => {
  it('is deterministic and embeds data the app decoder accepts', async () => {
    const first = await generate(REPO_ROOT);
    const second = await generate(REPO_ROOT);
    expect(second.html).toBe(first.html);

    const match = new RegExp(`<script type="application/json" id="${SITE_DATA_ELEMENT_ID}">([^<]*)</script>`).exec(first.html);
    expect(match).not.toBeNull();
    const embedded: unknown = JSON.parse(match?.[1] ?? 'null');
    expect(decode(siteData, embedded)).toEqual(first.data);
  });

  it('writes no timestamps or local paths', async () => {
    const { html } = await generate(REPO_ROOT);
    expect(html).not.toContain(REPO_ROOT);
    expect(html).not.toMatch(/20\d\d-\d\d-\d\dT\d\d:/);
  });
});
