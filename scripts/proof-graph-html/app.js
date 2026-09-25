// Interactive view of lean/graph/proof-graph.json. Plain JS + SVG, no library, no network.
// Inlined into lean/graph/index.html by scripts/proof-graph.py. Layouts are computed here,
// deterministically (sorted order, no randomness), so the page itself carries no layout data.
(function () {
  "use strict";
  var SVGNS = "http://www.w3.org/2000/svg"; // XML namespace identifier, not fetched
  var raw = JSON.parse(document.getElementById("graph-data").textContent);
  var files = raw.files;
  var nodes = raw.nodes.map(function (a, i) {
    return { i: i, name: a[0], kind: a[1], file: a[2], line: a[3], locked: a[4] === 1,
             specs: a[5], axioms: a[6], external: a[7], deps: [], users: [] };
  });
  raw.edges.forEach(function (e) { nodes[e[0]].deps.push(e[1]); nodes[e[1]].users.push(e[0]); });
  var fileCount = files.map(function () { return 0; });
  nodes.forEach(function (n) { fileCount[n.file]++; });
  var specs = [];
  nodes.forEach(function (n) { n.specs.forEach(function (s) { if (specs.indexOf(s) < 0) specs.push(s); }); });
  specs.sort();

  var $ = function (id) { return document.getElementById(id); };
  var svg = $("svg"), panel = $("panel"), results = $("results");
  var specClosure = null; // Set of node indices in the selected spec's proof tree, or null

  function colour(f) {
    var h = Math.round(f * 360 / Math.max(files.length, 1));
    return "hsl(" + h + ",60%," + (f % 2 ? 60 : 42) + "%)";
  }
  function short(name) {
    var parts = name.split(".");
    return parts.slice(Math.max(parts.length - 2, 0)).join(".");
  }
  function el(tag, attrs, parent) {
    var e = document.createElementNS(SVGNS, tag);
    for (var k in attrs) e.setAttribute(k, attrs[k]);
    if (parent) parent.appendChild(e);
    return e;
  }
  function h(tag, text, cls) {
    var e = document.createElement(tag);
    if (text !== undefined) e.textContent = text;
    if (cls) e.className = cls;
    return e;
  }
  function nodeLink(i) {
    var n = nodes[i];
    var b = h("button", (n.locked ? "🔒 " : "") + n.name, "link");
    b.title = n.kind + " — " + files[n.file] + ":" + n.line;
    b.onclick = function () { showNode(i); };
    var li = h("li");
    var sw = h("span", "", "sw");
    sw.style.background = colour(n.file);
    li.appendChild(sw);
    li.appendChild(b);
    return li;
  }
  function closureOf(roots) {
    var seen = new Set(), stack = roots.slice();
    while (stack.length) {
      var u = stack.pop();
      if (seen.has(u)) continue;
      seen.add(u);
      nodes[u].deps.forEach(function (v) { stack.push(v); });
    }
    return seen;
  }

  // ------------------------------------------------------------------ sidebar

  $("stats").textContent = nodes.length + " declarations, " + raw.edges.length + " edges, " +
    files.length + " files, " + specs.length + " spec IDs";
  specs.forEach(function (s) { var o = h("option", s); o.value = s; $("spec").appendChild(o); });
  files.forEach(function (f, i) {
    var li = h("li");
    var sw = h("span", "", "sw");
    sw.style.background = colour(i);
    var b = h("button", f + " (" + fileCount[i] + ")", "link");
    b.onclick = function () { showFile(i); };
    li.appendChild(sw);
    li.appendChild(b);
    $("legend").appendChild(li);
  });

  function refreshResults() {
    var q = $("search").value.trim().toLowerCase();
    results.textContent = "";
    var spec = $("spec").value;
    if (spec) {
      var roots = nodes.filter(function (n) { return n.specs.indexOf(spec) >= 0; });
      results.appendChild(h("li", "Theorems carrying " + spec + ":", "muted"));
      roots.forEach(function (n) { results.appendChild(nodeLink(n.i)); });
      results.appendChild(h("li", "Proof tree: " + specClosure.size + " declarations" +
        (q ? " — matches below" : " (search to list them)"), "muted"));
    }
    if (!q) return;
    var hits = nodes.filter(function (n) {
      return n.name.toLowerCase().indexOf(q) >= 0 && (!specClosure || specClosure.has(n.i));
    });
    hits.slice(0, 200).forEach(function (n) { results.appendChild(nodeLink(n.i)); });
    if (hits.length > 200) results.appendChild(h("li", "… " + (hits.length - 200) + " more", "muted"));
    if (!hits.length) results.appendChild(h("li", "no match", "muted"));
  }
  $("search").oninput = refreshResults;
  $("spec").onchange = function () {
    var spec = $("spec").value;
    specClosure = spec ? closureOf(nodes.filter(function (n) { return n.specs.indexOf(spec) >= 0; })
                                         .map(function (n) { return n.i; })) : null;
    refreshResults();
    showModules();
  };
  $("home").onclick = showModules;

  // ------------------------------------------------------------------ module overview

  function showModules() {
    $("view-title").textContent = specClosure
      ? "Files (highlighted: used by " + $("spec").value + ")" : "Files: arrow = a declaration uses one in the other file";
    svg.textContent = "";
    var W = 1000, H = 760, cx = W / 2, cy = H / 2, R = 300;
    svg.setAttribute("viewBox", "0 0 " + W + " " + H);
    var pos = files.map(function (f, i) {
      var a = 2 * Math.PI * i / files.length - Math.PI / 2;
      return [cx + R * Math.cos(a), cy + R * Math.sin(a), a];
    });
    var inSpec = files.map(function () { return false; });
    if (specClosure) specClosure.forEach(function (i) { inSpec[nodes[i].file] = true; });
    var fe = new Map();
    raw.edges.forEach(function (e) {
      var a = nodes[e[0]].file, b = nodes[e[1]].file;
      if (a !== b) fe.set(a + "," + b, true);
    });
    fe.forEach(function (_, k) {
      var ab = k.split(",").map(Number);
      var p = pos[ab[0]], q = pos[ab[1]];
      el("path", { d: "M" + p[0] + "," + p[1] + " Q" + cx + "," + cy + " " + q[0] + "," + q[1],
                   "class": "edge" + (specClosure && !(inSpec[ab[0]] && inSpec[ab[1]]) ? " dim" : "") }, svg);
    });
    files.forEach(function (f, i) {
      var g = el("g", { "class": "node" + (specClosure && !inSpec[i] ? " dim" : "") }, svg);
      el("circle", { cx: pos[i][0], cy: pos[i][1], r: 4 + Math.sqrt(fileCount[i]) * 1.6,
                     fill: colour(i), stroke: "#333" }, g);
      var t = el("title", {}, g);
      t.textContent = f + " (" + fileCount[i] + ")";
      var left = Math.cos(pos[i][2]) < 0;
      var tx = el("text", { x: pos[i][0] + (left ? -12 : 12), y: pos[i][1] + 4,
                            "text-anchor": left ? "end" : "start" }, g);
      tx.textContent = f.replace(/^Libpetri\//, "").replace(/\.lean$/, "");
      g.onclick = function () { showFile(i); };
    });
  }

  function showFile(f) {
    panel.textContent = "";
    panel.appendChild(h("h1", files[f]));
    panel.appendChild(h("p", fileCount[f] + " declarations", "muted"));
    var ul = h("ul");
    nodes.forEach(function (n) { if (n.file === f) ul.appendChild(nodeLink(n.i)); });
    panel.appendChild(ul);
  }

  // ------------------------------------------------------------------ neighbourhood view

  var CAP = 60;
  function showNode(i) {
    var n = nodes[i];
    $("view-title").textContent = n.name;
    svg.textContent = "";
    var left = n.users.slice(0, CAP), right = n.deps.slice(0, CAP);
    var rows = Math.max(left.length, right.length, 1);
    var W = 1000, H = Math.max(500, rows * 22 + 60);
    svg.setAttribute("viewBox", "0 0 " + W + " " + H);
    var cx = W / 2, cy = H / 2, xl = 170, xr = W - 170;
    function place(list, x) {
      var gap = (H - 40) / Math.max(list.length, 1);
      return list.map(function (j, k) { return [j, x, 20 + gap * (k + 0.5)]; });
    }
    var L = place(left, xl), Rt = place(right, xr);
    L.forEach(function (p) {
      el("path", { d: "M" + p[1] + "," + p[2] + " C" + (p[1] + 150) + "," + p[2] + " " + (cx - 150) + "," + cy + " " + cx + "," + cy,
                   "class": "edge hl" }, svg);
    });
    Rt.forEach(function (p) {
      el("path", { d: "M" + cx + "," + cy + " C" + (cx + 150) + "," + cy + " " + (p[1] - 150) + "," + p[2] + " " + p[1] + "," + p[2],
                   "class": "edge hl" }, svg);
    });
    function drawNode(j, x, y, anchor, big) {
      var m = nodes[j];
      var g = el("g", { "class": "node" }, svg);
      el("circle", { cx: x, cy: y, r: big ? 12 : 6, fill: colour(m.file),
                     stroke: m.locked ? "#b8860b" : "#333", "stroke-width": m.locked ? 3 : 1 }, g);
      var t = el("title", {}, g);
      t.textContent = (m.locked ? "🔒 locked — " : "") + m.name + " (" + m.kind + ")";
      var dx = anchor === "end" ? -10 : anchor === "start" ? 10 : 0;
      var tx = el("text", { x: x + dx, y: big ? y - 18 : y + 4, "text-anchor": anchor,
                            "font-weight": big ? "bold" : "normal" }, g);
      tx.textContent = (m.locked ? "🔒 " : "") + (big ? m.name : short(m.name));
      g.onclick = function () { showNode(j); };
    }
    L.forEach(function (p) { drawNode(p[0], p[1], p[2], "end", false); });
    Rt.forEach(function (p) { drawNode(p[0], p[1], p[2], "start", false); });
    drawNode(i, cx, cy, "middle", true);
    el("text", { x: xl, y: 14, "text-anchor": "middle" }, svg).textContent =
      "used by (" + n.users.length + (n.users.length > CAP ? ", first " + CAP + " drawn" : "") + ")";
    el("text", { x: xr, y: 14, "text-anchor": "middle" }, svg).textContent =
      "uses (" + n.deps.length + (n.deps.length > CAP ? ", first " + CAP + " drawn" : "") + ")";
    showPanel(n);
  }

  function showPanel(n) {
    panel.textContent = "";
    var title = h("h1", n.name);
    panel.appendChild(title);
    if (n.locked) panel.appendChild(h("p", "🔒 locked theorem (statement lock of the gate)", "lock"));
    var dl = h("p");
    dl.appendChild(document.createTextNode("kind: " + n.kind));
    dl.appendChild(h("br"));
    dl.appendChild(document.createTextNode(files[n.file] + ":" + n.line));
    panel.appendChild(dl);
    function section(label, items, render) {
      panel.appendChild(h("h2", label + " (" + items.length + ")"));
      var ul = h("ul");
      if (!items.length) ul.appendChild(h("li", "none", "muted"));
      items.forEach(function (x) { ul.appendChild(render(x)); });
      panel.appendChild(ul);
    }
    function codeItem(x) { var li = h("li"); li.appendChild(h("code", x)); return li; }
    section("Spec IDs", n.specs, codeItem);
    section("Axioms", n.axioms, codeItem);
    section("Uses (dependencies)", n.deps, nodeLink);
    section("Used by (dependents)", n.users, nodeLink);
    section("External constants (Lean core / Mathlib, not expanded)", n.external, codeItem);
  }

  showModules();
})();
