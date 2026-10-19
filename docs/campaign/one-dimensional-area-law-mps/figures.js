/* Stage figures for the one-dimensional board.

   Each entry draws one schematic into an empty <svg>; a stage names its entry
   in config.json (`figure`) and gives the caption (`caption`). The style is
   that of the two-dimensional board: hairlines, labels next to what they name,
   blue for the object of the stage and orange for a cut. Curves show shapes,
   not data. */
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
  const rect = (p, x, y, width, height, cls) => add(p, "rect", { x, y, width, height }, cls);
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

  return {
    /* The surprisal distribution of an interval: concentrated around S(X), with thin tails. */
    tail(svg) {
      view(svg, 360, 150);
      const x0 = 20, x1 = 340, base = 118, mid = 180, width = 26;
      const X = t => x0 + (x1 - x0) * t;
      const f = x => 82 * Math.exp(-Math.abs(x - mid) / width) * (1 - 0.25 * Math.exp(-(((x - mid) / 18) ** 2)));
      const curve = [];
      for (let i = 0; i <= 160; i++) { const x = X(i / 160); curve.push([x, base - f(x)]); }
      const w = 62;
      for (const [a, b] of [[x0, mid - w], [mid + w, x1]]) {
        const part = curve.filter(([x]) => x >= a && x <= b);
        path(svg, pts([[a, base], ...part, [b, base]]) + "Z", "fc op");
      }
      path(svg, pts(curve), "a");
      line(svg, x0, base, x1, base);
      line(svg, mid, base, mid, 30, "k dash");
      text(svg, mid, 24, "*S*(*X*)", "m t", "middle");
      line(svg, mid - w, base, mid - w, base + 5);
      line(svg, mid + w, base, mid + w, base + 5);
      path(svg, pts([[mid, base + 12], [mid + w, base + 12]]), "h");
      text(svg, mid + w / 2, base + 26, "*w*", "m", "middle");
      text(svg, x1, 50, "shaded weight ≤ 2e^{e/2} e^{−w/32s}", "", "end");
      text(svg, x1, base + 26, "−log *p*", "m", "end");
    },

    /* An interval X with m nested shells of width R on both sides. */
    shells(svg) {
      view(svg, 360, 172);
      const n = 31, x0 = 18, step = 10.8, y = 96, m = 4, R = 2;
      const xs = i => x0 + i * step;
      const lo = 11, hi = 19; // X = [lo, hi]
      for (let j = m; j >= 1; j--) {
        const a = lo - j * R, b = hi + j * R, h = 14 + 9 * j;
        rect(svg, xs(a) - 4.5, y - h, xs(b) - xs(a) + 9, 2 * h, "fs");
        add(svg, "rect", { x: xs(a) - 4.5, y: y - h, width: xs(b) - xs(a) + 9, height: 2 * h, rx: 4 }, "g");
        text(svg, xs(b) + 2, y - h - 3, `*X*_{${j}}`, "m");
      }
      add(svg, "rect", { x: xs(lo) - 5, y: y - 12, width: xs(hi) - xs(lo) + 10, height: 24, rx: 4 }, "a");
      line(svg, xs(0), y, xs(n - 1), y, "h");
      for (let i = 0; i < n; i++) {
        const inX = i >= lo && i <= hi, inT = !inX && i >= lo - m * R && i <= hi + m * R;
        dot(svg, xs(i), y, inX ? 3.6 : 2.6, inX ? "fa" : inT ? "fk" : "fm");
      }
      text(svg, (xs(lo) + xs(hi)) / 2, y + 4, "*X*", "m on big", "middle");
      text(svg, xs(lo - m * R), y + 70, "buffer *T*: the shells outside *X*, 2*mR* sites", "", "start");
    },

    /* Sequential truncation: the number of kept Schmidt vectors at each cut of a chain. */
    truncation(svg) {
      view(svg, 360, 150);
      const L = 6, x0 = 40, step = 56, y = 112;
      const xs = i => x0 + i * step;
      const kept = [2, 4, 5, 4, 3];
      const cap = 5.5;
      line(svg, xs(0), y, xs(L - 1), y, "k");
      for (let k = 0; k < L - 1; k++) {
        const xm = (xs(k) + xs(k + 1)) / 2, h = 13 * kept[k];
        rect(svg, xm - 7, y - 16 - h, 14, h, "fa op");
        add(svg, "rect", { x: xm - 7, y: y - 16 - h, width: 14, height: h }, "a");
        line(svg, xm, y - 9, xm, y + 9, "c");
      }
      const capY = y - 16 - 13 * cap;
      line(svg, xs(0), capY, xs(L - 1), capY, "h dash");
      text(svg, xs(L - 1), capY - 5, "exp(*C*_{int} + *w*)", "", "end");
      for (let i = 0; i < L; i++) {
        add(svg, "rect", { x: xs(i) - 8, y: y - 8, width: 16, height: 16, rx: 3 }, "fk");
        line(svg, xs(i), y + 8, xs(i), y + 18, "k");
      }
      text(svg, xs(0), y + 32, "one tensor per site", "", "start");
      text(svg, xs(L - 1), y + 32, "cuts in orange", "", "end");
    }
  };
})();
