//! HTML wrapper for rustdoc-embedded Petri net diagrams.
//!
//! Mirrors `org.libpetri.doclet.DiagramRenderer` (Java) and
//! `typescript/src/doclet/diagram-renderer.ts` (TypeScript): inlines the
//! canonical viewer bundle (`petrinet-diagrams.{css,js}`) into the generated
//! HTML so the rustdoc output is fully self-contained and the bundled
//! `window.LibpetriViewer.mount(...)` API renders SVG client-side from a
//! DOT source embedded as a `data-dot` attribute.
//!
//! The CSS and JS are byte-equivalent to the Java/TS resources and live at
//! `rust/libpetri-docgen/resources/petrinet-diagrams.{css,js}`. They are
//! build outputs of `typescript/src/viewer/` — do not hand-edit.
//!
//! ## Old vs new contract
//!
//! The previous implementation embedded a pre-rendered Graphviz SVG and
//! relied on a hand-written `window.PetriNetDiagrams` IIFE that
//! auto-discovered diagrams via DOM-ready and wired up cluster collapse /
//! filter / fullscreen handlers. The new viewer:
//!
//! - exposes `window.LibpetriViewer.mount(dot, container, { chrome: true })`
//!   instead of auto-init,
//! - renders the SVG from DOT client-side (no pre-rendered SVG required),
//! - injects its own legend + filter chrome when `chrome: true` is passed.

/// Inlined CSS — byte-equivalent to the Java/TS resource.
const INLINE_CSS: &str = include_str!("../resources/petrinet-diagrams.css");

/// Inlined JS — byte-equivalent to the Java/TS resource. Exposes
/// `window.LibpetriViewer`.
const INLINE_JS: &str = include_str!("../resources/petrinet-diagrams.js");

/// Renders the wrapper HTML for a plain (non-subnet) diagram. The viewer
/// renders the SVG from the embedded `dot_source` client-side.
pub fn render_svg(title: Option<&str>, dot_source: &str) -> String {
    render_internal(title, None, dot_source)
}

/// Renders the wrapper HTML for a subnet- or instance-aware diagram.
/// Identical to [`render_svg`] apart from the additional `header_html` block
/// (the port/channel/params badge bar) above the diagram, plus the
/// `subnet-diagram` CSS class on the wrapper.
pub fn render_subnet_svg(title: &str, header_html: &str, dot_source: &str) -> String {
    render_internal(Some(title), Some(header_html), dot_source)
}

fn render_internal(
    title: Option<&str>,
    header_html: Option<&str>,
    dot_source: &str,
) -> String {
    let title_html = match title {
        Some(t) => format!("<h4>{}</h4>\n", escape_html(t)),
        None => String::new(),
    };
    let summary_text = if title.is_some() { "View DOT Source" } else { "View Source" };
    let diagram_class = if header_html.is_some() {
        "petrinet-diagram subnet-diagram"
    } else {
        "petrinet-diagram"
    };
    let header_block = header_html.unwrap_or("");

    // The init script (inlined once per page, alongside the viewer JS) walks
    // every `.diagram-container[data-dot]` that has not yet been mounted and
    // calls `LibpetriViewer.mount(dot, container, { chrome: true })`. It is
    // idempotent: subsequent invocations (e.g. on SPA-style re-mount) skip
    // containers already tagged with `data-libpetri-mounted`.
    //
    // Kept in lockstep with the Java taglet (`DiagramRenderer.java`) and the
    // TypeScript doclet (`diagram-renderer.ts` mountScript). Three things it
    // has to get right: `data-libpetri-viewer` records the bundle version so a
    // page drawn by an old viewer is identifiable without comparing pixels; a
    // rejected `mount()` paints a visible error rather than leaving an empty
    // box; and the poll for the bundle is bounded, because a viewer that never
    // arrives must not look like a diagram that simply has no edges.
    //
    // `el` is bound with `let` on purpose: under `var` the whole loop shares
    // one binding, so every `.then` callback would write the handle of the
    // last container.
    let init_script = "(function(){\
        function fail(el,e){\
            console.error('[libpetri] viewer mount failed',e);\
            var p=document.createElement('p');\
            p.className='libpetri-diagram-error';\
            p.textContent='Diagram render failed: '+(e&&e.message?e.message:e);\
            el.textContent='';el.appendChild(p);\
        }\
        var tries=0;\
        function boot(){\
            var nodes=document.querySelectorAll('.diagram-container[data-dot]');\
            if(!window.LibpetriViewer||typeof window.LibpetriViewer.mount!=='function'){\
                if(++tries>100){\
                    for(var j=0;j<nodes.length;j++){\
                        fail(nodes[j],new Error('viewer bundle did not load'));\
                    }\
                    return;\
                }\
                return setTimeout(boot,30);\
            }\
            for(var i=0;i<nodes.length;i++){\
                let el=nodes[i];\
                if(el.dataset.libpetriMounted==='true')continue;\
                el.dataset.libpetriMounted='true';\
                el.dataset.libpetriViewer=window.LibpetriViewer.VERSION||'unknown';\
                try{\
                    Promise.resolve(window.LibpetriViewer.mount(el.dataset.dot,el,{chrome:true}))\
                        .then(function(h){el.__libpetriHandle=h;})\
                        .catch(function(e){fail(el,e);});\
                }catch(e){fail(el,e);}\
            }\
        }\
        if(document.readyState==='loading'){\
            document.addEventListener('DOMContentLoaded',boot);\
        }else{boot();}\
    })();";

    format!(
        "<style>{css}</style>\n\
<script>if(!window._libpetriViewerInit){{window._libpetriViewerInit=true;\n\
{js}\n\
}}</script>\n\
<script>{init}</script>\n\
<div class=\"{class}\">\n\
{title}{header}<div class=\"diagram-container\" data-dot=\"{dot_attr}\">\n\
<div class=\"diagram-controls\">\n\
<button class=\"diagram-btn btn-toggle-clusters\" title=\"Collapse / expand all clusters\" style=\"display:none\">Collapse all</button>\n\
<button class=\"diagram-btn btn-reset\" title=\"Reset zoom\">Reset</button>\n\
<button class=\"diagram-btn btn-fullscreen\" title=\"Toggle fullscreen\">Fullscreen</button>\n\
</div>\n\
</div>\n\
<details>\n\
<summary>{summary}</summary>\n\
<pre><code>{dot}</code></pre>\n\
</details>\n\
</div>\n",
        css = INLINE_CSS,
        js = INLINE_JS,
        init = init_script,
        class = diagram_class,
        title = title_html,
        header = header_block,
        dot_attr = escape_html_attr(dot_source),
        summary = summary_text,
        dot = escape_html(dot_source),
    )
}

/// Escapes HTML special characters for safe embedding in HTML *text* content.
pub fn escape_html(text: &str) -> String {
    text.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

/// Escapes a string for safe embedding inside a double-quoted HTML *attribute*
/// value. The attribute value is delimited by `"`, so we must escape `&`,
/// `<`, `>`, `"`, and newline / carriage-return characters (which would
/// otherwise be preserved literally and corrupt the surrounding tag layout
/// when round-tripped through some serializers).
pub fn escape_html_attr(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for ch in text.chars() {
        match ch {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            '\n' => out.push_str("&#10;"),
            '\r' => out.push_str("&#13;"),
            other => out.push(other),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn css_and_js_inlined() {
        // CSS and JS resources must be present (compile-time include_str!
        // guarantees this, but we sanity-check that they aren't empty and
        // that the new viewer global is exposed).
        assert!(!INLINE_CSS.is_empty());
        assert!(!INLINE_JS.is_empty());
        assert!(INLINE_JS.contains("LibpetriViewer"));
    }

    #[test]
    fn css_byte_equivalent_to_java_resource() {
        // Byte-equivalence with the Java doclet's resource is required so the
        // visual output matches. The build-time include_str! pulls our local
        // copy; here we cross-check that the resource on disk hasn't drifted
        // from Java's by reading both relative to CARGO_MANIFEST_DIR.
        let manifest_dir = env!("CARGO_MANIFEST_DIR");
        let local =
            std::fs::read_to_string(format!("{manifest_dir}/resources/petrinet-diagrams.css")).unwrap();
        let java = std::fs::read_to_string(format!(
            "{manifest_dir}/../../java/src/main/resources/javadoc/petrinet-diagrams.css"
        ));
        if let Ok(java) = java {
            assert_eq!(local, java, "CSS must be byte-equivalent to Java resource");
        }
    }

    #[test]
    fn js_byte_equivalent_to_java_resource() {
        let manifest_dir = env!("CARGO_MANIFEST_DIR");
        let local =
            std::fs::read_to_string(format!("{manifest_dir}/resources/petrinet-diagrams.js")).unwrap();
        let java = std::fs::read_to_string(format!(
            "{manifest_dir}/../../java/src/main/resources/javadoc/petrinet-diagrams.js"
        ));
        if let Ok(java) = java {
            assert_eq!(local, java, "JS must be byte-equivalent to Java resource");
        }
    }

    #[test]
    fn render_svg_includes_inlined_assets_and_mount_init() {
        let html = render_svg(Some("Test"), "digraph G { a -> b }");
        assert!(html.contains("<style>"));
        assert!(html.contains("<script>"));
        // New idempotency guard (replaces the old _petriNetDiagramsInit).
        assert!(html.contains("_libpetriViewerInit"));
        // New API surface — init script must reference the canonical mount.
        assert!(html.contains("LibpetriViewer.mount"));
        // Container must carry data-dot so the init script can find it.
        assert!(html.contains("data-dot=\""));
        // chrome:true is requested so the bundled viewer renders legend +
        // filter strip; the renderer no longer emits placeholders for them.
        assert!(html.contains("chrome:true"));
        assert!(!html.contains("class=\"diagram-legend\""));
        assert!(!html.contains("class=\"diagram-filter-strip\""));
        // No reference to the retired hand-written global.
        assert!(!html.contains("PetriNetDiagrams"));
        // Fullscreen button must NOT carry an inline handler — the new
        // viewer wires controls itself via the chrome it injects.
        assert!(!html.contains("onclick=\""));
        // Plain (non-subnet) — should NOT carry the subnet class.
        assert!(!html.contains("subnet-diagram"));
    }

    #[test]
    fn render_subnet_svg_carries_subnet_class_and_dot_attr() {
        let html = render_subnet_svg(
            "Foo",
            "<div class=\"subnet-header\"></div>",
            "digraph Foo {}",
        );
        assert!(html.contains("subnet-diagram"));
        assert!(html.contains("subnet-header"));
        assert!(html.contains("data-dot=\""));
        assert!(html.contains("LibpetriViewer.mount"));
    }

    #[test]
    fn escape_html_handles_specials() {
        assert_eq!(escape_html("<a href=\"x\">"), "&lt;a href=&quot;x&quot;&gt;");
        assert_eq!(escape_html("a&b"), "a&amp;b");
    }

    #[test]
    fn escape_html_attr_handles_specials() {
        // Quotes, angle brackets, ampersands, and newlines must all be
        // entity-encoded so a DOT source can survive embedding in a
        // double-quoted HTML attribute.
        let raw = "digraph G {\n  \"a\" -> \"b\" [label=\"x < y & z\"]\n}";
        let attr = escape_html_attr(raw);
        assert!(!attr.contains('"'), "raw quotes survived: {attr}");
        assert!(!attr.contains('\n'), "raw newline survived: {attr}");
        assert!(!attr.contains('<'), "raw < survived: {attr}");
        assert!(attr.contains("&quot;"));
        assert!(attr.contains("&#10;"));
        assert!(attr.contains("&lt;"));
        assert!(attr.contains("&amp;"));
    }

    #[test]
    fn render_embeds_dot_source_in_attribute() {
        let dot = "digraph G { \"a\" -> \"b\" }";
        let html = render_svg(None, dot);
        // The DOT source appears entity-escaped inside data-dot, and verbatim
        // inside the <pre><code> details block.
        assert!(html.contains("data-dot=\"digraph G { &quot;a&quot; -&gt; &quot;b&quot; }\""));
        assert!(html.contains("digraph G { &quot;a&quot; -&gt; &quot;b&quot; }"));
    }

    // ---- viewer bundle drift gate ----------------------------------------
    //
    // `typescript/src/viewer/` is the single source of truth, but this crate
    // ships a *copy* of the built bundle in `resources/`, as do the Java
    // javadoc taglet and the TypeScript doclet. `scripts/build-viewer.sh`
    // distributes all three and records the canonical digests in
    // `spec/viewer-bundle.sha256`.
    //
    // Nothing forced a rebuild before, so a consumer could sit on an old
    // bundle indefinitely and quietly render an old viewer. That is how a
    // generated doc page ends up with Graphviz-routed diagonal edges long
    // after the ELK orthogonal routing shipped, with nothing on the page to
    // say so.
    //
    // When this fails, the fix is `scripts/build-viewer.sh`. The files under
    // `resources/` are build outputs and must never be hand-edited.

    /// Resolves the checksum file upward from this crate's manifest directory.
    fn locate_checksums() -> std::path::PathBuf {
        let mut dir: Option<&std::path::Path> =
            Some(std::path::Path::new(env!("CARGO_MANIFEST_DIR")));
        while let Some(d) = dir {
            let candidate = d.join("spec").join("viewer-bundle.sha256");
            if candidate.is_file() {
                return candidate;
            }
            dir = d.parent();
        }
        panic!(
            "could not locate spec/viewer-bundle.sha256 upward from {}",
            env!("CARGO_MANIFEST_DIR")
        );
    }

    /// Parses the `<sha256>  <filename>` lines written by build-viewer.sh.
    fn canonical_digest(filename: &str) -> String {
        let path = locate_checksums();
        let contents = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("reading {}: {e}", path.display()));
        for line in contents.lines() {
            let mut parts = line.split_whitespace();
            let (Some(digest), Some(name)) = (parts.next(), parts.next()) else {
                continue;
            };
            if name == filename {
                return digest.to_string();
            }
        }
        panic!("spec/viewer-bundle.sha256 has no entry for {filename}");
    }

    fn sha256_hex(bytes: &[u8]) -> String {
        use sha2::{Digest, Sha256};
        let mut hasher = Sha256::new();
        hasher.update(bytes);
        hasher
            .finalize()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect()
    }

    #[test]
    fn bundled_js_matches_canonical_digest() {
        assert_eq!(
            canonical_digest("petrinet-diagrams.js"),
            sha256_hex(INLINE_JS.as_bytes()),
            "resources/petrinet-diagrams.js is stale — run scripts/build-viewer.sh \
             (do not hand-edit build outputs)"
        );
    }

    #[test]
    fn bundled_css_matches_canonical_digest() {
        assert_eq!(
            canonical_digest("petrinet-diagrams.css"),
            sha256_hex(INLINE_CSS.as_bytes()),
            "resources/petrinet-diagrams.css is stale — run scripts/build-viewer.sh \
             (do not hand-edit build outputs)"
        );
    }

    /// Cheap canary independent of the digests: the orthogonal edge routing
    /// draws ELK's own routes under Graphviz `nop2`. A bundle predating that
    /// renders ELK-placed nodes joined by diagonal splines, which reads as a
    /// styling preference rather than a stale build.
    #[test]
    fn bundle_ships_orthogonal_routing() {
        assert!(
            INLINE_JS.contains("nop2"),
            "viewer bundle predates orthogonal edge routing"
        );
    }
}
