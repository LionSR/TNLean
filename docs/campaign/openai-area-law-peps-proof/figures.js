/* Stage figures for the area-law and PEPS board.

   Each entry draws one schematic into an empty <svg>; a stage names its entry
   in config.json (`figure`) and gives the caption (`caption`). The figures
   follow Tufte's rules for small explanatory graphics: hairline range frames
   instead of boxed axes, labels written next to what they name instead of a
   legend, small multiples for anything that changes in steps, and colour only
   where it carries meaning (blue for the object of the stage, orange for a
   cut). Curves show shapes, not data: the constants are chosen for legibility. */
window.campaignFigures = (function () {
  "use strict";
  const NS = "http://www.w3.org/2000/svg";
  const add = (p, tag, attrs = {}, cls) => {
    const n = document.createElementNS(NS, tag);
    for (const [k, v] of Object.entries(attrs)) n.setAttribute(k, v);
    if (cls) n.setAttribute("class", cls);
    p.append(n);
    return n;
  };
  const view = (svg, w, h) => svg.setAttribute("viewBox", `0 0 ${w} ${h}`);
  const line = (p, x1, y1, x2, y2, cls = "h") => add(p, "line", { x1, y1, x2, y2 }, cls);
  const pts = q => q.map((v, i) => (i ? "L" : "M") + v[0].toFixed(1) + "," + v[1].toFixed(1)).join("");
  const path = (p, d, cls = "a") => add(p, "path", { d }, cls);
  const rect = (p, x, y, width, height, cls, extra = {}) => add(p, "rect", { x, y, width, height, ...extra }, cls);
  const dot = (p, cx, cy, r, cls = "fa") => add(p, "circle", { cx, cy, r }, cls);
  // Text with light markup: ^{..} superscript, _{..} subscript, *..* italic.
  const text = (p, x, y, s, cls = "", anchor = "start") => {
    const t = add(p, "text", { x, y, "text-anchor": anchor }, cls);
    let shift = 0;
    for (const tok of s.split(/(\^\{[^}]*\}|_\{[^}]*\}|\*[^*]+\*)/).filter(Boolean)) {
      const ts = add(t, "tspan");
      const sup = tok.startsWith("^{"), sub = tok.startsWith("_{"), it = tok.startsWith("*");
      const target = sup ? -4.5 : sub ? 3 : 0;
      if (target !== shift) { ts.setAttribute("dy", target - shift); shift = target; }
      if (sup || sub) ts.setAttribute("font-size", "72%");
      if (it) ts.setAttribute("font-style", "italic");
      ts.textContent = sup || sub ? tok.slice(2, -1) : it ? tok.slice(1, -1) : tok;
    }
    return t;
  };
  const scale = (d0, d1, r0, r1, log) => {
    const f = log ? Math.log : v => v;
    return v => r0 + (f(v) - f(d0)) / (f(d1) - f(d0)) * (r1 - r0);
  };
  // Tufte range frame: the axis runs only between the extreme ticks.
  const xFrame = (p, X, y, ticks) => {
    line(p, X(ticks[0][0]), y, X(ticks[ticks.length - 1][0]), y);
    for (const [v, lab] of ticks) { line(p, X(v), y, X(v), y + 3); text(p, X(v), y + 13, lab, "", "middle"); }
  };
  const yFrame = (p, Y, x, ticks) => {
    line(p, x, Y(ticks[0][0]), x, Y(ticks[ticks.length - 1][0]));
    for (const [v, lab] of ticks) { line(p, x - 3, Y(v), x, Y(v)); text(p, x - 6, Y(v) + 3.5, lab, "", "end"); }
  };
  const sample = (f, a, b, n = 80) => Array.from({ length: n + 1 }, (_, i) => f(a + (b - a) * i / n));
  const jitter = i => { const s = Math.sin(i * 12.9898 + 78.233) * 43758.5453; return s - Math.floor(s); };
  const brace = (p, x1, x2, y, label, cls = "h", up = true) => {
    const d = up ? -4 : 4;
    path(p, pts([[x1, y], [x1, y + d], [x2, y + d], [x2, y]]), cls);
    text(p, (x1 + x2) / 2, y + (up ? -8 : 15), label, "", "middle");
  };

  return {
    /* Area law, stage 1: log-log entropy bounds for a box of side r. */
    "box-exponent"(svg) {
      view(svg, 320, 200);
      const X = scale(2, 64, 44, 236, true), Y = scale(2, 4096, 160, 16, true);
      const curve = (k, cls, lab, dy = 0) => {
        line(svg, X(2), Y(2 ** k), X(64), Y(64 ** k), cls);
        text(svg, X(64) + 6, Y(64 ** k) + 4 + dy, lab, cls === "a" ? "t" : "");
      };
      curve(2, "h", "volume, *r*^{2}");
      curve(1.5, "a", "this stage, *r*^{1+e₀}");
      curve(1, "h dash", "area, *r*");
      xFrame(svg, X, 172, [[2, "2"], [4, "4"], [8, "8"], [16, "16"], [32, "32"], [64, "64"]]);
      text(svg, X(8), 198, "box side *r*, log scale", "", "middle");
      text(svg, 44, 10, "entropy bound, log scale");
    },

    /* Area law, stage 2: the spectral window chi and the decay of its Fourier transform f.
       Area-law manuscript, eq:quasilocal-centered-filter: chi(0) = 1 and chi vanishes on
       every excited energy, so averaging h_i over time against f keeps only its ground part. */
    filter(svg) {
      view(svg, 320, 175);
      const base = 132, e0 = 22, gap = 44;
      for (let i = 0; i < 46; i++) line(svg, e0 + gap + 84 * Math.pow(jitter(i), 0.8), base, e0 + gap + 84 * Math.pow(jitter(i), 0.8), base - 6, "h");
      line(svg, e0, base, e0, base - 10, "k");
      line(svg, 12, base, 150, base);
      const smooth = u => u <= 0 ? 0 : u >= 1 ? 1 : u * u * u * (u * (6 * u - 15) + 10);
      path(svg, pts(sample(x => [x, base - 74 * (1 - smooth((x - e0) / (gap / 2)))], e0, 150)), "a");
      text(svg, e0 - 4, base - 1, "*E*_{0}", "m", "end");
      brace(svg, e0, e0 + gap, base + 7, "", "h", false);
      text(svg, e0 + gap / 2, base + 24, "gap Δ", "", "middle");
      text(svg, 108, base + 13, "spectrum of *H*", "", "middle");
      text(svg, e0 + 6, base - 80, "χ = 1 at *E*_{0}", "t");
      text(svg, 150, base - 14, "χ = 0 on excited levels", "", "end");
      // Fourier transform of the filter on a log scale.
      const T = scale(0, 30, 182, 296), L = scale(1e-8, 1, 132, 22, true);
      const str = t => Math.exp(-1.5 * Math.pow(t, 0.7)), pow = t => Math.pow(1 + t, -4);
      path(svg, pts(sample(t => [T(t), L(pow(t))], 0, 30)), "h dash");
      path(svg, pts(sample(t => [T(t), L(str(t))], 0, 30)), "a");
      text(svg, T(9), L(pow(9)) + 14, "power law", "", "middle");
      text(svg, T(30) - 2, L(str(30)) + 12, "stretched exp.", "t", "end");
      xFrame(svg, T, base + 6, [[0, "0"], [30, "large *t*"]]);
      text(svg, 182, 14, "|*f*(*t*)|, log scale");
    },

    /* Area law, stage 3: per-copy log-norm converging as the number of replicas grows. */
    replicas(svg) {
      view(svg, 320, 196);
      const X = scale(1, 16, 50, 250), Y = scale(0, 1.3, 150, 30);
      const lim = 0.32, v = k => lim + 0.9 / Math.pow(k, 0.85);
      line(svg, X(1), Y(lim), X(16) + 6, Y(lim), "h dash");
      text(svg, X(16) + 10, Y(lim) + 4, "limit:", "t");
      text(svg, X(16) + 10, Y(lim) + 17, "entropies");
      path(svg, pts(Array.from({ length: 16 }, (_, i) => [X(i + 1), Y(v(i + 1))])), "h");
      for (let k = 1; k <= 16; k++) dot(svg, X(k), Y(v(k)), 2.4, "fa");
      text(svg, X(3) + 6, Y(v(3)) - 6, "−(1/*k*) log ‖filtered state‖^{2}", "t");
      xFrame(svg, X, 162, [[1, "1"], [4, "4"], [8, "8"], [12, "12"], [16, "16"]]);
      text(svg, X(8.5), 192, "number of copies *k*", "", "middle");
      // the m copies, drawn once
      for (let i = 0; i < 7; i++) { const c = add(svg, "circle", { cx: 60 + i * 13, cy: 14, r: 4.5 }, "k"); c.setAttribute("stroke-width", "1"); }
      text(svg, 60 + 7 * 13, 18, "… Ω̃^{⊗k}");
    },

    /* Area law, stage 4: small multiples of the partition sweeping a collar. */
    "collar-scan"(svg) {
      view(svg, 320, 172);
      const pos = [0.18, 0.74, 0.42, 0.9, 0.58], w = 52, h = 112, top = 26, cl = 14, cr = 42;
      pos.forEach((p, k) => {
        const x = 8 + k * 62;
        rect(svg, x, top, cl, h, "fa", { "fill-opacity": 0.22 });
        rect(svg, x + cl, top, cr - cl, h, "fs");
        line(svg, x + cl, top, x + cl, top + h, "h");
        line(svg, x + cr, top, x + cr, top + h, "h");
        line(svg, x, top, x + w, top, "g");
        line(svg, x, top + h, x + w, top + h, "g");
        const q = [];
        for (let j = 0; j <= 8; j++) q.push([x + cl + (cr - cl) * Math.min(0.97, Math.max(0.03, p + (jitter(10 * k + j) - 0.5) * 0.3)), top + j * h / 8]);
        path(svg, pts(q), "c");
        text(svg, x + w / 2, top + h + 16, String(k + 1), "", "middle");
      });
      text(svg, 8 + cl / 2, top + h / 2 + 4, "*X*", "m t", "middle");
      brace(svg, 8 + cl, 8 + cr, top - 4, "collar");
      text(svg, 160, 168, "steps of the randomized schedule", "", "middle");
    },

    /* Area law, stage 5: leaked information against collar width. */
    amplify(svg) {
      view(svg, 320, 180);
      const X = scale(0, 1, 74, 250), Y = scale(1, -4.6, 22, 150);
      const e = u => 0.8 - 5.4 * Math.pow(u, 0.75);
      for (const k of [0, -1, -2, -3, -4]) line(svg, X(0), Y(k), X(1), Y(k), "g");
      path(svg, pts(sample(u => [X(u), Y(e(u))], 0, 1)), "a");
      dot(svg, X(0), Y(e(0)), 3, "fa");
      dot(svg, X(1), Y(e(1)), 3, "fa");
      text(svg, X(0) + 8, Y(e(0)) - 4, "after the scan: *C n*^{1−ε}", "t");
      text(svg, X(1) + 6, Y(e(1)) - 6, "below", "t");
      text(svg, X(1) + 6, Y(e(1)) + 6, "*n*^{−M}");
      yFrame(svg, Y, 66, [[1, "*n*"], [0, "1"], [-1, "*n*^{−1}"], [-2, "*n*^{−2}"], [-3, "*n*^{−3}"], [-4, "*n*^{−4}"]]);
      xFrame(svg, X, 160, [[0, "*n*^{1−ε}"], [1, "+ sublinear"]]);
      text(svg, X(0.5), 176, "collar width", "", "middle");
      text(svg, 20, 10, "information leaked, log scale");
    },

    /* PEPS, stage 1: a buffer tapering linearly toward a point. */
    angular(svg) {
      view(svg, 320, 180);
      const top = 12, bot = 140, mid = 160, wide = 52, narrow = 6;
      const lt = [mid - wide, top], lb = [mid - narrow, bot], rt = [mid + wide, top], rb = [mid + narrow, bot];
      path(svg, pts([[16, top], lt, lb, [mid - narrow, bot + 18], [16, bot + 18]]) + "Z", "fa op");
      path(svg, pts([[304, top], rt, rb, [mid + narrow, bot + 18], [304, bot + 18]]) + "Z", "fl op");
      path(svg, pts([lt, lb, [mid - narrow, bot + 18], [mid + narrow, bot + 18], rb, rt]) + "Z", "fs");
      line(svg, ...lt, ...lb, "k"); line(svg, ...rt, ...rb, "k");
      line(svg, mid - narrow, bot, mid - narrow, bot + 18, "k"); line(svg, mid + narrow, bot, mid + narrow, bot + 18, "k");
      text(svg, 60, 80, "*X*", "m t big", "middle");
      text(svg, 260, 80, "*E*", "m t big", "middle");
      text(svg, mid, 40, "buffer", "t", "middle");
      text(svg, mid + 30, 100, "tapers", "", "start");
      text(svg, mid + 30, 112, "linearly", "", "start");
      line(svg, mid - narrow, bot + 24, mid + narrow, bot + 24, "c");
      text(svg, mid, bot + 36, "width ≥ *K* log *L*", "", "middle");
      text(svg, 16, bot + 36, "*I*(*X* : *E*) ≤ *L*^{−p}", "t");
    },

    /* PEPS, stage 2: nested squares and the inside ranks of the subspaces. */
    patch(svg) {
      view(svg, 320, 178);
      const cx = 78, cy = 88;
      [136, 100, 64].forEach((s, i) => rect(svg, cx - s / 2, cy - s / 2, s, s, i ? "h" : "g"));
      rect(svg, cx - 12, cy - 12, 24, 24, "fa", { "fill-opacity": 0.55 });
      text(svg, cx, cy + 82, "nested squares", "", "middle");
      line(svg, cx, cy - 12, cx, cy - 70);
      text(svg, cx, cy - 74, "side ~ log *L*", "t", "middle");
      const d = [9, 6, 6, 4, 3, 3, 2, 2, 1, 1, 1];
      const bx = 180, base = 148;
      d.forEach((v, j) => rect(svg, bx + j * 11, base - v * 9, 6, v * 9, "fa"));
      line(svg, bx, base + 3, bx + 10 * 11 + 6, base + 3);
      text(svg, bx, base + 16, "subspaces *j*");
      text(svg, bx, base - 98, "inside rank *d*_{j}", "t");
      text(svg, bx, base - 86, "Σ *d*_{j} ≤ *C L*^{c}");
    },

    /* PEPS, stage 4: small multiples of the dyadic hierarchy. */
    dyadic(svg) {
      view(svg, 320, 118);
      const s = 64;
      for (let k = 0; k < 4; k++) {
        const x = 8 + k * 78, y = 10, n = 2 ** k, c = s / n;
        for (let i = 1; i < n; i++) { line(svg, x + i * c, y, x + i * c, y + s, "g"); line(svg, x, y + i * c, x + s, y + i * c, "g"); }
        rect(svg, x, y, s, s, "h");
        if (k) rect(svg, x, y, 2 * c, 2 * c, "k");
        for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) dot(svg, x + (i + 0.5) * c, y + (j + 0.5) * c, Math.max(1.6, 4.5 - k), i < 2 && j < 2 && k ? "fa" : "fm");
        text(svg, x + s / 2, y + s + 16, `${n * n} part${n > 1 ? "ies" : "y"}`, "", "middle");
      }
      text(svg, 160, 112, "a party works only with parties at its own or the next scale", "", "middle");
    },

    /* PEPS, stage 6: links between dyadic parties routed along rows and columns. */
    routing(svg) {
      view(svg, 320, 190);
      const n = 8, s = 20, x0 = 14, y0 = 14;
      const load = new Map();
      const key = (a, b) => a < b ? a + "|" + b : b + "|" + a;
      const step = (p, q) => { const k = key(p.join(), q.join()); load.set(k, (load.get(k) || 0) + 1); };
      const centre = (i, j, sz) => [i + Math.max(0, sz / 2 - 1), j + Math.max(0, sz / 2 - 1)];
      const parties = [];
      for (let sz = n; sz >= 2; sz /= 2) for (let i = 0; i < n; i += sz) for (let j = 0; j < n; j += sz) {
        const p = centre(i, j, sz);
        parties.push([p, sz]);
        for (const [di, dj] of [[0, 0], [sz / 2, 0], [0, sz / 2], [sz / 2, sz / 2]]) {
          const q = centre(i + di, j + dj, sz / 2);
          let cur = [...p];
          while (cur[0] !== q[0]) { const nx = [cur[0] + Math.sign(q[0] - cur[0]), cur[1]]; step(cur, nx); cur = nx; }
          while (cur[1] !== q[1]) { const nx = [cur[0], cur[1] + Math.sign(q[1] - cur[1])]; step(cur, nx); cur = nx; }
        }
      }
      const P = ([i, j]) => [x0 + i * s, y0 + j * s];
      for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
        if (i < n - 1) line(svg, ...P([i, j]), ...P([i + 1, j]), "g");
        if (j < n - 1) line(svg, ...P([i, j]), ...P([i, j + 1]), "g");
      }
      let max = 0;
      for (const [k, v] of load) {
        max = Math.max(max, v);
        const [a, b] = k.split("|").map(t => t.split(",").map(Number));
        const l = line(svg, ...P(a), ...P(b), "a");
        l.setAttribute("stroke-width", (0.9 + 2.4 * (v - 1)).toFixed(2));
        l.setAttribute("stroke-linecap", "round");
      }
      for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) dot(svg, ...P([i, j]), 1.6, "fm");
      for (const [p, sz] of parties) { const c = add(svg, "circle", { cx: P(p)[0], cy: P(p)[1], r: 1.5 + Math.log2(sz) * 1.3 }, "k"); c.style.fill = "var(--surface)"; }
      const tx = x0 + (n - 1) * s + 22;
      text(svg, tx, 30, "rings: parties", "t");
      text(svg, tx, 42, "larger ring, coarser");
      text(svg, tx, 54, "dyadic square");
      text(svg, tx, 80, "stroke width: links", "t");
      text(svg, tx, 92, "routed through");
      text(svg, tx, 104, `each edge (here ≤ ${max})`);
      text(svg, x0 + (n - 1) * s / 2, y0 + (n - 1) * s + 20, `${n} × ${n} grid`, "", "middle");
    },

    /* Foundations: a finite domain with a hole, a region and its boundary edges. */
    domain(svg) {
      view(svg, 320, 170);
      const cols = 15, rows = 7, s = 20, x0 = 12, y0 = 12;
      const inL = (c, r) => c >= 0 && r >= 0 && c < cols && r < rows && !(c >= 10 && c <= 11 && r >= 2 && r <= 3) && !(c >= 13 && r <= 1);
      const inA = (c, r) => inL(c, r) && c >= 2 && c <= 7 && r >= 1 && r <= 5 && !(c === 7 && r === 5) && !(c === 2 && r === 1);
      const P = (c, r) => [x0 + c * s, y0 + r * s];
      let cut = 0;
      for (let r = 0; r < rows; r++) for (let c = 0; c < cols; c++) for (const [dc, dr] of [[1, 0], [0, 1]]) {
        if (!inL(c, r) || !inL(c + dc, r + dr)) continue;
        const crossing = inA(c, r) !== inA(c + dc, r + dr);
        if (crossing) cut++;
        line(svg, ...P(c, r), ...P(c + dc, r + dr), crossing ? "c" : "g");
      }
      for (let r = 0; r < rows; r++) for (let c = 0; c < cols; c++) if (inL(c, r)) dot(svg, ...P(c, r), inA(c, r) ? 3.6 : 2, inA(c, r) ? "fa" : "fm");
      text(svg, ...P(4.5, 3.75), "*A*", "m t big halo", "middle");
      text(svg, ...P(10.5, 2.7), "hole", "", "middle");
      text(svg, ...P(13.5, 0.7), "edge of Λ", "", "middle");
      text(svg, x0, y0 + rows * s + 6, `orange: the ${cut} edges of ∂_{Λ}*A*`, "t");
    }
  };
})();
