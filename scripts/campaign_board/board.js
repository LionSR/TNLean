/* Campaign board: renders a snapshot produced by collect.py and merged by render.py.
   Everything campaign-specific comes from D.config (the campaign's config.json),
   D.gaps (its gaps.json) and the campaign's intro HTML. */
(function () {
  "use strict";
  const D = JSON.parse(document.getElementById("data").textContent);
  const C = D.config;

  /* ---------- vocabulary ---------- */
  const STATUS = { done: "Closed", landed: "Partly landed", review: "In review", draft: "Draft PR", ready: "Unblocked, no PR", blocked: "Blocked" };
  const ORDER = ["done", "landed", "review", "draft", "ready", "blocked"];
  const RANK = { blocked: 0, ready: 1, draft: 2, review: 3, landed: 4, done: 5 };
  const GAP_KIND = {
    error: ["Error in the paper", "A printed claim fails as stated. It needs a correction and possibly a new argument."],
    "missing-step": ["Missing step", "The paper omits a nontrivial step. The claim may hold, but the argument is incomplete."],
    narrower: ["Lean narrower than the paper", "Lean currently proves a restricted version. The paper's argument appears sound, and the remaining work is formalization."],
    convention: ["Convention", "A degenerate case, such as a zero dimension or an empty set, is read as the authors evidently intend."]
  };
  const GAP_STATUS = { open: ["Open", "st-draft"], "resolved-pending": ["Resolved in an open PR", "st-review"], resolved: ["Resolved", "st-done"] };

  /* ---------- time ---------- */
  const generated = new Date(D.generatedAt);
  const now = new Date(Math.max(Date.now(), +generated));
  const age = iso => { const h = Math.max(0, (now - new Date(iso)) / 36e5); return h < 1 ? "<1 h" : h < 48 ? Math.round(h) + " h" : Math.round(h / 24) + " d"; };
  // The snapshot is regenerated hourly; reload an open page when it is next viewed after 20 minutes.
  setTimeout(() => {
    const reload = () => { if (document.visibilityState === "visible") location.reload(); };
    reload();
    document.addEventListener("visibilitychange", reload);
  }, 20 * 60 * 1000);

  /* ---------- DOM helpers ---------- */
  const $ = id => document.getElementById(id);
  const el = (tag, attrs = {}, ...kids) => {
    const n = document.createElement(tag);
    for (const [k, v] of Object.entries(attrs)) {
      if (k === "class") n.className = v; else if (k === "text") n.textContent = v; else if (k === "html") n.innerHTML = v; else n.setAttribute(k, v);
    }
    for (const c of kids) if (c != null) n.append(c);
    return n;
  };
  const NS = "http://www.w3.org/2000/svg";
  const sv = (tag, attrs = {}) => { const n = document.createElementNS(NS, tag); for (const [k, v] of Object.entries(attrs)) n.setAttribute(k, v); return n; };
  const ext = (href, text, cls) => el("a", { href, target: "_blank", rel: "noopener", text, ...(cls ? { class: cls } : {}) });
  const kfmt = n => Math.abs(n) >= 10000 ? (n / 1000).toFixed(0) + "k" : Math.abs(n) >= 1000 ? (n / 1000).toFixed(1) + "k" : String(n);

  /* ---------- repositories ---------- */
  const REPO = Object.fromEntries(C.repos.map(r => [r.name, r]));
  const PRIMARY = C.repos.find(r => r.primary);
  const issueUrl = n => `https://github.com/${PRIMARY.slug}/issues/${n}`;
  const prUrl = p => `https://github.com/${REPO[p.repo].slug}/pull/${p.number}`;
  const prLabel = p => (REPO[p.repo].prefix || "#") + p.number;
  const prTitle = t => t.replace(/^[a-z]+(\([^)]*\))?!?:\s*/i, "").replace(/^./, c => c.toUpperCase());
  const issueTitle = t => t.replace(/^[^:]{1,40}:\s+/, "");

  /* ---------- derived state ---------- */
  const byNum = new Map(D.issues.map(i => [i.number, i]));
  const streams = D.streams.map((s, k) => ({ ...s, lane: k }));
  const streamOf = new Map(streams.map(s => [s.issue, s]));
  const isTracker = n => n === C.tracker || streamOf.has(n) || ((byNum.get(n) || {}).subIssues || []).length > 0;

  for (const p of D.prs) {
    p.kind = p.state === "MERGED" ? "merged" : p.state === "CLOSED" ? "closed" : p.isDraft ? "draft" : "review";
    p.open = p.kind === "review" || p.kind === "draft";
    p.attention = p.open && (p.mergeable === "CONFLICTING" || p.ci === "FAILURE" || p.ci === "ERROR");
    p.work = [...new Set([...(p.closes || []), ...(p.refs || [])])].filter(n => byNum.has(n) && !isTracker(n));
  }
  for (const i of D.issues) i.prs = [];
  for (const p of D.prs) for (const n of p.work) byNum.get(n).prs.push(p);
  for (const i of D.issues) {
    i.stream = streamOf.get(i.parent) || null;
    if (i.state === "CLOSED") i.status = "done";
    else if (i.prs.some(p => p.kind === "merged")) i.status = "landed";
    else if (i.prs.some(p => p.kind === "review")) i.status = "review";
    else if (i.prs.some(p => p.kind === "draft")) i.status = "draft";
    else if (i.blockedBy.every(b => (byNum.get(b) || {}).state === "CLOSED")) i.status = "ready";
    else i.status = "blocked";
  }
  const leaves = D.issues.filter(i => i.stream);
  const leastStatus = nums => nums.map(n => byNum.get(n)).filter(Boolean).reduce((a, i) => RANK[i.status] < RANK[a] ? i.status : a, "done");

  /* ---------- blocking graph ---------- */
  const preds = n => ((byNum.get(n) || {}).blockedBy || []).filter(b => byNum.has(b));
  const succ = new Map(leaves.map(i => [i.number, []]));
  for (const i of leaves) for (const b of preds(i.number)) if (succ.has(b)) succ.get(b).push(i.number);
  const closure = (start, next) => {
    const seen = new Set(), stack = [start];
    while (stack.length) for (const y of next(stack.pop())) if (!seen.has(y)) { seen.add(y); stack.push(y); }
    return seen;
  };
  const chainMemo = new Map();
  /** Longest chain of open issues ending at n, n included when open. */
  const openChain = n => {
    if (chainMemo.has(n)) return chainMemo.get(n);
    chainMemo.set(n, []);
    let best = [];
    for (const b of preds(n)) { const c = openChain(b); if (c.length > best.length) best = c; }
    const chain = byNum.get(n).state === "CLOSED" ? best : [...best, n];
    chainMemo.set(n, chain);
    return chain;
  };

  /* ---------- shared widgets ---------- */
  const meter = items => {
    const m = el("div", { class: "meter" });
    for (const s of ORDER) {
      const c = items.filter(i => i.status === s).length;
      if (!c) continue;
      const seg = el("span", { title: `${STATUS[s]}: ${c}` });
      seg.style.width = (100 * c / Math.max(1, items.length)) + "%";
      seg.style.background = `var(--s-${s})`;
      m.append(seg);
    }
    return m;
  };
  const countLine = items => ORDER.map(s => [s, items.filter(i => i.status === s).length]).filter(([, c]) => c).map(([s, c]) => `${c} ${STATUS[s].toLowerCase()}`).join(" · ");
  const prChip = p => {
    const cls = p.kind === "merged" ? "st-done" : p.kind === "closed" ? "st-closed" : p.attention ? "st-bad" : p.kind === "review" ? "st-review" : "st-draft";
    const a = ext(prUrl(p), prLabel(p), "chip " + cls);
    a.title = `${p.repo}: ${p.title} (${p.kind}${p.attention ? ", needs a fix" : ""})`;
    return a;
  };
  const prRef = (repo, n) => { const p = D.prs.find(q => q.repo === repo && q.number === n); return p ? prChip(p) : ext(`https://github.com/${REPO[repo].slug}/pull/${n}`, (REPO[repo].prefix || "#") + n, "chip st-closed"); };
  const issueRef = n => { const j = byNum.get(n); const a = ext(issueUrl(n), "#" + n, "blk" + (j && j.state === "CLOSED" ? " closed" : "")); a.title = j ? j.title : ""; return a; };
  const tile = (big, label, sub) => el("div", { class: "tile" }, el("div", { class: "eyebrow", text: label }), el("div", { class: "big", text: big }), el("div", { class: "sub", text: sub }));
  const statusPill = s => el("span", { class: "pill st-" + s, text: STATUS[s] });

  /* ---------- masthead ---------- */
  document.title = C.pageTitle;
  $("crumbs").append(...[["../", PRIMARY.name], ["../blueprint/", "Blueprint"], ["../paper-gaps/", "Paper-gap notes"]].flatMap(([h, t], k) => [k ? " · " : "", el("a", { href: h, text: t })]));
  $("heading").textContent = C.heading;
  $("lede").textContent = C.lede;
  $("stamp").append(
    el("span", {}, "Updated ", el("b", { text: generated.toLocaleString(undefined, { dateStyle: "medium", timeStyle: "short" }) }), ` (${age(D.generatedAt)} ago)`),
    el("span", {}, `${PRIMARY.name} main at `, el("b", { class: "mono", text: D.mainCommit })),
    el("span", {}, "Tracker ", ext(issueUrl(C.tracker), "#" + C.tracker)),
    C.sources ? el("span", {}, ext(C.sources, "Pinned sources")) : null
  );

  /* ---------- the libraries doing the work ---------- */
  const libs = C.repos.filter(r => r.homepage);
  if (libs.length) {
    $("libs").append("Formalized in the open-source Lean 4 libraries ",
      ...libs.flatMap((r, k) => [k ? " and " : "", el("a", { href: r.homepage, text: r.name }), " (", ext(`https://github.com/${r.slug}`, "GitHub"), ")"]),
      ".");
    for (const r of libs) $("libcards").append(el("div", { class: "libcard" },
      el("h3", {}, el("a", { href: r.homepage, text: r.name })),
      el("p", { text: r.description || "" }),
      el("div", { class: "links" },
        el("a", { href: r.homepage, text: "Project site" }), el("a", { href: r.homepage + "blueprint/", text: "Blueprint" }),
        el("a", { href: r.homepage + "docs/", text: "API docs" }), ext(`https://github.com/${r.slug}`, "GitHub"))));
  } else $("libraries").hidden = true;

  /* ---------- headline cards from the intro ---------- */
  const statementPR = C.statementPR && D.prs.find(p => p.repo === PRIMARY.name && p.number === C.statementPR);
  for (const card of document.querySelectorAll(".thm[data-target]")) {
    const n = +card.dataset.target, target = byNum.get(n);
    const dl = card.querySelector(".tdl");
    if (!target || !dl) continue;
    const all = [...[...closure(n, preds)].map(k => byNum.get(k)), target];
    dl.before(meter(all));
    dl.append(
      el("dt", { text: "Proved in Lean" }), el("dd", { text: target.state === "CLOSED" ? "Yes" : "Not yet" }),
      el("dt", { text: "Prerequisites" }), el("dd", { text: `${all.length} issues: ${countLine(all)}` }),
      el("dt", { text: "Longest open chain" }), el("dd", { text: `${openChain(n).length} issues in sequence` }),
      statementPR ? el("dt", { text: "Lean statement" }) : null,
      statementPR ? el("dd", {}, prChip(statementPR), ` ${statementPR.kind === "merged" ? "merged" : statementPR.kind === "draft" ? "is a draft" : "is in review"}${statementPR.attention ? " and needs a fix" : ""}`) : null
    );
    const trace = card.querySelector(".trace");
    if (trace) trace.addEventListener("click", () => { select(n); $("map").scrollIntoView({ behavior: "smooth", block: "center" }); });
  }

  /* ---------- headline tiles ---------- */
  const merged = D.prs.filter(p => p.kind === "merged");
  const open = D.prs.filter(p => p.open);
  const byRepo = ps => C.repos.map(r => `${ps.filter(p => p.repo === r.name).length} ${r.name}`).join(" · ");
  const withWork = D.results.filter(r => RANK[leastStatus(r.issues)] >= RANK.draft).length;
  $("tiles").append(
    tile(`${withWork} / ${D.results.length}`, "Paper results with work", "named results whose issues have a pull request or are closed"),
    tile(`${leaves.filter(i => i.status === "done").length} / ${leaves.length}`, "Work issues closed", `${leaves.filter(i => i.status === "landed").length} more have merged pieces`),
    tile(String(merged.length), "Pull requests merged", byRepo(merged)),
    tile(String(open.length), "Pull requests open", `${open.filter(p => p.kind === "review").length} ready for review · ${open.filter(p => p.attention).length} need a fix`)
  );
  $("legend").append(el("span", { text: "Status:" }), ...ORDER.map(s => el("span", {}, el("i", { class: "sw st-" + s }), STATUS[s])));

  /* ---------- gaps ---------- */
  const G = D.gaps || { entries: [], checked: [] };
  const isOpenGap = g => (g.status || "open") === "open";
  // Notes are identified by repository and path; two repositories may use the same file name.
  const gapKey = (repo, path) => `${repo || PRIMARY.name}:${path}`;
  const noteFor = g => (D.gapNotes || []).find(n => gapKey(n.repo, n.path) === gapKey(g.repo, g.id));
  (function renderGaps() {
    const curated = new Set(G.entries.map(g => gapKey(g.repo, g.id)));
    const pending = (D.gapNotes || []).filter(n => !curated.has(gapKey(n.repo, n.path)));
    const openCount = k => G.entries.filter(g => g.kind === k && isOpenGap(g)).length;
    const serious = openCount("error") + openCount("missing-step");
    const plural = (n, word) => `${n} ${word}${n === 1 ? "" : "s"}`;
    const verdict = serious > 0
      ? `${plural(openCount("error"), "open error")} and ${plural(openCount("missing-step"), "open missing step")} in the papers.`
      : pending.length
        ? `No open errors or missing steps among the classified notes. ${plural(pending.length, "new note")} still to be classified.`
        : "No open errors or missing steps in either paper.";
    const counts = el("div", { class: "counts" }, el("span", { class: "muted", text: "Open:" }),
      ...Object.keys(GAP_KIND).map(k => el("span", {}, el("span", { class: "pill k-" + k, text: String(openCount(k)) }), " " + GAP_KIND[k][0].toLowerCase())));
    const done = G.entries.filter(g => !isOpenGap(g)).length;
    if (done) counts.append(el("span", {}, el("span", { class: "pill st-done", text: String(done) }), " resolved"));
    if (pending.length) counts.append(el("span", {}, el("span", { class: "pill st-draft", text: String(pending.length) }), ` new note${pending.length > 1 ? "s" : ""} awaiting a summary`));
    $("gapsum").append(el("div", { class: "verdict", text: verdict }), counts);
    $("kinds").append(...Object.entries(GAP_KIND).map(([k, [name, desc]]) => el("div", {}, el("dt", {}, el("span", { class: "pill k-" + k, text: name })), el("dd", { text: desc }))));

    const order = { error: 0, "missing-step": 1, narrower: 2, convention: 3 };
    const list = $("gaplist");
    for (const g of [...G.entries].sort((a, b) => (isOpenGap(b) - isOpenGap(a)) || order[a.kind] - order[b.kind])) {
      const note = noteFor(g);
      const [statusName, statusCls] = GAP_STATUS[g.status || "open"];
      list.append(el("article", { class: "gap" },
        el("div", { class: "where" }, el("span", { class: "pill k-" + g.kind, text: GAP_KIND[g.kind][0] }), el("span", { class: "pill " + statusCls, text: statusName }),
          el("span", { text: `${(C.papers[g.paper] || {}).name || ""} · ${g.result}` })),
        el("h3", { text: g.title }),
        el("dl", {},
          el("div", {}, el("dt", { text: "The paper says" }), el("dd", { text: g.claims })),
          el("div", {}, el("dt", { text: "What the formalization found" }), el("dd", { text: g.found })),
          el("div", {}, el("dt", { text: "Does it threaten the theorem?" }), el("dd", { text: g.impact })),
          el("div", {}, el("dt", { text: "Next step" }), el("dd", { text: g.plan }))),
        el("div", { class: "links" }, g.issue ? issueRef(g.issue) : null,
          ...Object.entries(g.prs || {}).flatMap(([repo, ns]) => ns.map(n => prRef(repo, n))),
          note ? el("span", { class: "muted mono", text: `${note.path.split("/").pop()} · note status: ${note.status || "unstated"}` }) : null)));
    }
    for (const n of pending) list.append(el("article", { class: "gap" },
      el("div", { class: "where" }, el("span", { class: "pill st-draft", text: "New note, summary pending" }), n.kind ? el("span", { text: `marked ${n.kind} by its author` }) : null),
      el("h3", { text: n.title || n.path }),
      el("div", { class: "links" }, ...n.prs.map(p => prRef(n.repo, p.number)), el("span", { class: "muted mono", text: n.path.split("/").pop() }))));
    if (!list.children.length) list.append(el("p", { class: "muted", text: "No paper-gap notes yet." }));

    const box = $("gapchecked");
    if ((G.checked || []).length) {
      box.append(el("h3", { class: "charttitle", text: "Checked against the paper with no gap reported" }),
        el("ul", { class: "checked" }, ...G.checked.map(c => el("li", {}, el("b", { text: c.result }), `: ${c.what}. `, el("span", { class: "muted" }, c.note + " ", prRef(c.repo, c.pr))))));
    }
    if (G.reviewedAt) box.append(el("p", { class: "note", text: `Summaries last reviewed ${new Date(G.reviewedAt).toLocaleString(undefined, { dateStyle: "medium", timeStyle: "short" })}. They paraphrase the paper-gap notes, which are authoritative.` }));
  })();

  /* ---------- proof routes ---------- */
  (function renderRoutes() {
    const assigned = new Set();
    for (const route of C.routes) {
      const container = el("div", { class: "route" });
      $("routes").append(el("section", { class: "part" },
        el("header", {}, el("div", { class: "eyebrow", text: route.eyebrow }), el("h2", { text: route.heading }), route.intro ? el("p", { html: route.intro }) : null),
        container));
      route.stages.forEach((st, idx) => {
        const items = st.issues.map(n => byNum.get(n)).filter(Boolean);
        const status = leastStatus(st.issues);
        const furthest = items.reduce((a, i) => RANK[i.status] > RANK[a] ? i.status : a, "blocked");
        const results = D.results.filter(r => r.paper === route.paper && !assigned.has(r.paper + r.label) && r.issues.some(n => st.issues.includes(n)));
        results.forEach(r => assigned.add(r.paper + r.label));
        const sections = [...new Set(results.map(r => +r.num.split(".")[0]))].sort((a, b) => a - b);
        const prs = [...new Set(items.flatMap(i => i.prs))];
        const landed = prs.filter(p => p.kind === "merged").sort((a, b) => new Date(a.mergedAt) - new Date(b.mergedAt));
        const inflight = prs.filter(p => p.open);
        const gapBadges = G.entries.filter(g => st.issues.includes(g.issue) && g.kind !== "convention" && isOpenGap(g))
          .map(g => { const a = el("a", { href: "#gaps", class: "pill k-" + g.kind, text: `${GAP_KIND[g.kind][0]}: ${g.result}` }); a.title = g.title; return a; });

        const resultList = el("ul", { class: "results" }, ...results.map(r => {
          const rs = leastStatus(r.issues);
          const name = r.name || (C.resultNames || {})[r.label] || r.label;
          const li = el("li", {}, el("i", { class: "rd st-" + rs, title: STATUS[rs] }), el("span", {}, r.url ? ext(r.url, name) : name, " ", el("span", { class: "rn", text: `${r.kind} ${r.num}` })));
          if (r.gate) li.title = r.gate;
          return li;
        }));
        const landedList = el("ul", { class: "landed" },
          ...landed.slice(-6).map(p => el("li", {}, prChip(p), el("span", { text: prTitle(p.title) }))),
          landed.length > 6 ? el("li", {}, el("span"), el("span", { class: "muted", text: `and ${landed.length - 6} earlier` })) : null,
          landed.length ? null : el("li", {}, el("span"), el("span", { class: "muted", text: "Nothing merged yet." })));
        container.append(el("div", { class: "stage" },
          el("div", { class: "rail" }, el("div", { class: "dot st-" + furthest, text: route.stages.length > 1 ? String(idx + 1) : "·" }), el("div", { class: "line" })),
          el("div", { class: "body" },
            el("div", { class: "head" }, el("h3", { text: st.title }),
              sections.length ? el("span", { class: "secs", text: sections.length > 1 ? `§§${sections[0]}–${sections[sections.length - 1]}` : `§${sections[0]}` }) : null,
              statusPill(status), ...gapBadges),
            el("p", { class: "phys", html: st.physics }),
            el("p", { class: "out", html: "<b>Delivers.</b> " + st.delivers }),
            el("div", { class: "meta" },
              el("div", { class: "box" }, el("h4", { text: results.length ? `Paper results (${results.length})` : "Paper results" }),
                results.length ? resultList : el("span", { class: "muted", text: "Shared definitions; no named result." })),
              el("div", { class: "box" }, el("h4", { text: `Landed (${landed.length})` }), landedList)),
            el("div", { class: "foot" }, meter(items), el("span", { text: `${items.length} issue${items.length === 1 ? "" : "s"}:` }),
              ...items.map(i => { const a = issueRef(i.number); a.classList.add("chip", "st-" + i.status); return a; }),
              inflight.length ? el("span", { text: `· ${inflight.length} PR${inflight.length === 1 ? "" : "s"} open` }) : null))));
      });
    }
  })();

  /* ---------- next actions ---------- */
  (function renderActions() {
    const card = (title, blurb, rows) => $("actions").append(el("div", { class: "act" },
      el("h3", {}, el("span", { text: title }), el("span", { class: "mono", text: String(rows.length) })), el("p", { text: blurb }),
      el("ul", {}, ...(rows.length ? rows : [el("li", {}, el("span"), el("span", { class: "muted", text: "Nothing here right now." }))]))));
    const forIssues = p => p.work.length ? el("span", { class: "why", text: " → " + p.work.map(n => "#" + n).join(" ") }) : null;
    card("Ready to merge", "Out of draft, CI passing, and GitHub reports no conflicts.",
      open.filter(p => p.kind === "review" && p.ci === "SUCCESS" && p.mergeable === "MERGEABLE").map(p => el("li", {}, prChip(p), el("span", {}, prTitle(p.title), forIssues(p)))));
    card("Needs a fix", "Merge conflict or failing CI.",
      open.filter(p => p.attention).map(p => el("li", {}, prChip(p), el("span", {}, prTitle(p.title),
        el("span", { class: "why", text: " · " + [p.mergeable === "CONFLICTING" ? "conflicts" : "", p.ci === "FAILURE" || p.ci === "ERROR" ? "CI failing" : ""].filter(Boolean).join(", ") })))));
    card("Can start now", "Every blocker is closed and no pull request exists yet.",
      leaves.filter(i => i.status === "ready").map(i => el("li", {}, issueRef(i.number), el("span", { text: issueTitle(i.title) }))));
    const unlocks = leaves.filter(i => i.state !== "CLOSED").map(i => [i, closure(i.number, x => succ.get(x) || []).size]).sort((a, b) => b[1] - a[1]).slice(0, 6);
    card("Biggest unlocks", "Open issues with the most work downstream.",
      unlocks.map(([i, k]) => el("li", {}, issueRef(i.number), el("span", {}, issueTitle(i.title), el("span", { class: "why", text: ` · ${k} issues wait on it` })))));
  })();

  /* ---------- blocking map ---------- */
  const svg = $("map"), nodes = new Map(), edges = [];
  (function renderMap() {
    const depth = new Map();
    const dep = n => {
      if (depth.has(n)) return depth.get(n);
      depth.set(n, 0);
      const ps = preds(n).filter(b => succ.has(b));
      const d = ps.length ? 1 + Math.max(...ps.map(dep)) : 0;
      depth.set(n, d);
      return d;
    };
    leaves.forEach(i => dep(i.number));
    if (!leaves.length) return;
    const ncol = Math.max(...depth.values()) + 1;
    const cell = streams.map(() => Array.from({ length: ncol }, () => []));
    for (const i of leaves) cell[i.stream.lane][depth.get(i.number)].push(i);
    const NW = 168, NH = 54, CW = 206, RH = 62, PADX = 16, TOP = 28, LANEGAP = 30;
    const laneRows = cell.map(lane => Math.max(1, ...lane.map(c => c.length)));
    const laneY = []; { let y = TOP; streams.forEach((s, k) => { laneY[k] = y + LANEGAP - 8; y += LANEGAP + laneRows[k] * RH; }); }
    const pos = new Map();
    const place = () => cell.forEach(lane => lane.forEach(col => col.forEach((i, y) => pos.set(i.number, y))));
    cell.forEach(lane => lane.forEach(col => col.sort((a, b) => a.number - b.number)));
    place();
    const absY = n => laneY[byNum.get(n).stream.lane] + pos.get(n) * RH;
    for (let pass = 0; pass < 4; pass++) {
      for (let x = 1; x < ncol; x++) for (const lane of cell) {
        const bary = i => { const ps = preds(i.number).filter(b => pos.has(b)); return ps.length ? ps.reduce((a, b) => a + absY(b), 0) / ps.length : absY(i.number); };
        lane[x].sort((a, b) => bary(a) - bary(b));
      }
      place();
    }
    const W = PADX * 2 + (ncol - 1) * CW + NW;
    const H = laneRows.reduce((a, r) => a + LANEGAP + r * RH, TOP) + 6;
    svg.setAttribute("viewBox", `0 0 ${W} ${H}`); svg.setAttribute("width", W); svg.setAttribute("height", H);
    for (let x = 0; x < ncol; x++) { const t = sv("text", { x: PADX + x * CW, y: 16, class: "colhead" }); t.textContent = x === 0 ? "NO BLOCKERS" : "DEPTH " + x; svg.append(t); }
    streams.forEach((s, k) => {
      const y = laneY[k] - 14;
      svg.append(sv("line", { x1: PADX, x2: W - PADX, y1: y - 10, y2: y - 10, class: "laneline" }));
      const t = sv("text", { x: PADX, y: y + 2, class: "lane" }); t.textContent = s.name.toUpperCase(); t.style.fill = `var(--lane-${k % 3})`; svg.append(t);
    });
    const xy = new Map(leaves.map(i => [i.number, [PADX + depth.get(i.number) * CW, absY(i.number)]]));
    const edgeLayer = sv("g"); svg.append(edgeLayer);
    for (const i of leaves) for (const b of preds(i.number)) {
      if (!xy.has(b)) continue;
      const [x1, y1] = xy.get(b), [x2, y2] = xy.get(i.number);
      const sx = x1 + NW, sy = y1 + NH / 2, tx = x2, ty = y2 + NH / 2, mx = (sx + tx) / 2;
      const path = sv("path", { d: `M${sx},${sy} C${mx},${sy} ${mx},${ty} ${tx},${ty}`, class: "edge" });
      path.dataset.a = b; path.dataset.b = i.number;
      edgeLayer.append(path); edges.push(path);
    }
    const twoLines = (text, max) => {
      const out = [""];
      for (const w of text.split(/\s+/)) {
        const cur = out[out.length - 1];
        if ((cur + " " + w).trim().length <= max) out[out.length - 1] = (cur + " " + w).trim();
        else if (out.length < 2) out.push(w);
        else { out[1] = out[1].replace(/\s*\S*$/, "") + "…"; break; }
      }
      if (out[1] && out[1].length > max) out[1] = out[1].slice(0, max - 1) + "…";
      return out;
    };
    for (const i of leaves) {
      const [x, y] = xy.get(i.number);
      const g = sv("g", { class: "node", transform: `translate(${x},${y})`, tabindex: "0", role: "button" });
      const box = sv("rect", { class: "box", width: NW, height: NH, rx: 7 });
      box.style.fill = `var(--s-${i.status}-bg)`; box.style.stroke = `var(--s-${i.status})`;
      if (i.status === "ready") box.setAttribute("stroke-dasharray", "4 3");
      const num = sv("text", { x: 9, y: 14, class: "nnum" }); num.textContent = "#" + i.number + (i.prs.length ? `  ·  ${i.prs.length} PR` : "");
      g.append(box, num);
      twoLines(issueTitle(i.title), 25).forEach((line, k) => { const t = sv("text", { x: 9, y: 30 + k * 14, class: "ntitle" }); t.textContent = line; g.append(t); });
      const tip = sv("title"); tip.textContent = `#${i.number} ${i.title} (${STATUS[i.status]})`; g.append(tip);
      g.addEventListener("click", e => { e.stopPropagation(); select(i.number); });
      g.addEventListener("keydown", e => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); select(i.number); } });
      svg.append(g); nodes.set(i.number, g);
    }
    svg.addEventListener("click", () => select(null));
  })();

  const detailIdle = () => $("detail").replaceChildren(el("span", { class: "note", text: "Select an issue in the map, or use “Trace its prerequisites” on a theorem card." }));
  detailIdle();
  function select(n) {
    nodes.forEach(g => g.classList.remove("on", "sel", "crit"));
    edges.forEach(e => e.classList.remove("on", "crit"));
    if (n == null || !nodes.has(n)) { svg.classList.remove("focus"); detailIdle(); return; }
    const up = closure(n, preds), down = closure(n, x => succ.get(x) || []);
    const upN = new Set([n, ...up]), downN = new Set([n, ...down]);
    svg.classList.add("focus");
    [...upN, ...downN].forEach(k => nodes.has(k) && nodes.get(k).classList.add("on"));
    nodes.get(n).classList.add("sel");
    edges.forEach(e => { const a = +e.dataset.a, b = +e.dataset.b; if ((upN.has(a) && upN.has(b)) || (downN.has(a) && downN.has(b))) e.classList.add("on"); });
    const chain = openChain(n);
    chain.forEach(k => nodes.has(k) && nodes.get(k).classList.add("crit"));
    for (let k = 1; k < chain.length; k++) edges.forEach(e => { if (+e.dataset.a === chain[k - 1] && +e.dataset.b === chain[k]) e.classList.add("crit"); });
    const i = byNum.get(n);
    const row = (k, ...v) => el("div", { class: "row" }, el("span", { class: "k", text: k }), ...v);
    const none = t => [el("span", { class: "muted", text: t })];
    const arrows = ks => ks.flatMap((k, j) => j ? [el("span", { class: "muted", text: "→" }), issueRef(k)] : [issueRef(k)]);
    $("detail").replaceChildren(
      el("h4", {}, ext(issueUrl(n), "#" + n), " " + i.title + " ", statusPill(i.status)),
      row("Blocked by", ...(i.blockedBy.length ? i.blockedBy.map(issueRef) : none("nothing"))),
      row("Upstream", el("span", { text: `${[...up].filter(k => byNum.get(k).state !== "CLOSED").length} of ${up.size} prerequisites still open` })),
      row("Longest open chain", ...(chain.length ? arrows(chain) : none("none"))),
      row("Unlocks", ...((succ.get(n) || []).length ? succ.get(n).map(issueRef) : none("nothing directly"))),
      row("Pull requests", ...(i.prs.length ? i.prs.map(prChip) : none("none yet"))));
  }

  /* ---------- charts ---------- */
  /** Cumulative step chart. Each series is {label, color, dash?, thin?, events: [{t: Date, v: number}]}. */
  function stepChart(target, series, t0, t1) {
    const W = 900, H = 260, L = 52, R = 170, T = 14, B = 36;
    target.setAttribute("viewBox", `0 0 ${W} ${H}`);
    // Running sums can rise and fall (a deletion-heavy merge), so scale from their extremes.
    const sorted = series.map(s => [...s.events].sort((a, b) => a.t - b.t));
    const prefixes = sorted.map(evs => { let c = 0; return evs.map(e => (c += e.v)); });
    const totals = prefixes.map(ps => ps.length ? ps[ps.length - 1] : 0);
    const all = [0, ...prefixes.flat()];
    const span = Math.max(1, Math.max(...all) - Math.min(...all));
    const mag = Math.pow(10, Math.floor(Math.log10(span)));
    const step = span / mag > 5 ? 2 * mag : span / mag > 2 ? mag : Math.max(1, mag / 2);
    const ytop = Math.max(step, Math.ceil(Math.max(...all) / step) * step);
    const ybot = Math.min(0, Math.floor(Math.min(...all) / step) * step);
    const X = t => L + (W - L - R) * (t - t0) / Math.max(1, t1 - t0);
    const Y = v => T + (H - T - B) * (ytop - v) / (ytop - ybot);
    for (let v = ybot; v <= ytop + 1e-9; v += step) {
      target.append(sv("line", { x1: L, x2: W - R, y1: Y(v), y2: Y(v), class: Math.abs(v) < 1e-9 ? "axis" : "grid" }));
      const t = sv("text", { x: L - 8, y: Y(v) + 4, "text-anchor": "end" }); t.textContent = kfmt(Math.round(v)); target.append(t);
    }
    const hours = (t1 - t0) / 36e5, tick = hours > 96 ? 48 : hours > 48 ? 24 : hours > 24 ? 12 : 6;
    for (let t = new Date(Math.ceil(t0 / (tick * 36e5)) * tick * 36e5); t <= t1; t = new Date(+t + tick * 36e5)) {
      target.append(sv("line", { x1: X(t), x2: X(t), y1: H - B, y2: H - B + 4, class: "grid" }));
      const lb = sv("text", { x: X(t), y: H - B + 17, "text-anchor": "middle" });
      lb.textContent = t.toLocaleString(undefined, { month: "short", day: "numeric", hour: "2-digit" });
      target.append(lb);
    }
    const ends = series.map((s, k) => {
      let c = 0, d = `M${X(t0)},${Y(0)}`;
      for (const e of sorted[k]) { c += e.v; d += ` H${X(e.t)} V${Y(c)}`; }
      d += ` H${X(t1)}`;
      const path = sv("path", { d }); path.style.fill = "none"; path.style.stroke = s.color; path.style.strokeWidth = s.thin ? "1.6" : "2.4";
      if (s.dash) path.setAttribute("stroke-dasharray", s.dash);
      const dot = sv("circle", { cx: X(t1), cy: Y(c), r: 3.5 }); dot.style.fill = s.color;
      target.append(path, dot);
      return { y: Y(c), text: `${s.label} ${kfmt(totals[k])}`, color: s.color };
    }).sort((a, b) => a.y - b.y);
    for (let k = 1; k < ends.length; k++) if (ends[k].y - ends[k - 1].y < 14) ends[k].y = ends[k - 1].y + 14;
    for (const e of ends) { const t = sv("text", { x: W - R + 10, y: e.y + 4, class: "lbl" }); t.textContent = e.text; t.style.fill = e.color; target.append(t); }
  }

  (function renderStatus() {
    const leanNet = p => (p.leanAdd || 0) - (p.leanDel || 0);
    const sum = (ps, f) => ps.reduce((a, p) => a + f(p), 0);
    const bp = D.blueprint || [];
    const bsum = f => bp.reduce((a, c) => a + c[f], 0);
    const sorryMain = (D.sorryOnMain || []).reduce((a, h) => a + h.count, 0);
    const sorryOpen = sum(open, p => p.sorryAdded || 0);
    $("fstiles").append(
      tile(kfmt(sum(merged, leanNet)), "Lean lines merged", C.repos.map(r => `${kfmt(sum(merged.filter(p => p.repo === r.name), leanNet))} ${r.name}`).join(" · ")),
      tile(kfmt(sum(open, p => p.leanAdd || 0)), "Lean lines in open PRs", `across ${open.filter(p => p.leanAdd).length} pull requests`),
      tile(String(bsum("proved")), "\\leanok statements on main", `${bp.length} blueprint chapters · ${bsum("stated")} stated without proof · ${bsum("notready")} not ready`),
      tile(String(sum(open, p => p.leanokAdded || 0)), "\\leanok tags in open PRs", "statement and proof tags counted separately"),
      tile(String(sorryMain + sorryOpen), "sorry", `${sorryMain} on main in campaign files · ${sorryOpen} added by open PRs`));
    const tbody = document.querySelector("#bptable tbody");
    for (const c of [...bp].sort((a, b) => a.repo.localeCompare(b.repo) || b.proved - a.proved)) tbody.append(el("tr", {},
      el("td", { text: c.repo }),
      el("td", { class: "t" }, ext(`https://github.com/${REPO[c.repo].slug}/blob/main/${c.path}`, c.title.replace(/\\[a-zA-Z]+\{([^}]*)\}/g, "$1"))),
      ...["proved", "stated", "unformalized", "notready"].map(f => el("td", { class: "mono", text: String(c[f]) }))));
    if (!bp.length) tbody.append(el("tr", {}, el("td", { colspan: "6", class: "muted", text: "No campaign chapters on main yet." })));

    const created = D.prs.map(p => new Date(p.createdAt));
    if (!created.length) return;
    const t0 = new Date(Math.floor(Math.min(...created) / 36e5) * 36e5);
    const mergedEvents = (f, ps = merged) => ps.filter(p => p.mergedAt).map(p => ({ t: new Date(p.mergedAt), v: f(p) }));
    const laneColor = k => `var(--lane-${k % 3})`;
    stepChart($("chart"), [
      { label: "Opened, all", color: "var(--muted)", dash: "5 4", events: D.prs.map(p => ({ t: new Date(p.createdAt), v: 1 })) },
      { label: "Merged, all", color: "var(--ink)", events: mergedEvents(() => 1) },
      ...C.repos.map((r, k) => ({ label: `Merged, ${r.name}`, color: laneColor(k + 1), thin: true, events: mergedEvents(() => 1, merged.filter(p => p.repo === r.name)) }))
    ], t0, now);
    stepChart($("locchart"), [
      { label: "All files", color: "var(--muted)", dash: "5 4", events: mergedEvents(p => p.additions - p.deletions) },
      { label: "Lean, all", color: "var(--ink)", events: mergedEvents(leanNet) },
      ...C.repos.map((r, k) => ({ label: `Lean, ${r.name}`, color: laneColor(k + 1), thin: true, events: mergedEvents(leanNet, merged.filter(p => p.repo === r.name)) }))
    ], t0, now);
  })();

  /* ---------- issue and pull-request tables ---------- */
  (function renderTables() {
    let query = "";
    const matches = (...fields) => !query || fields.join(" ").toLowerCase().includes(query);
    const issueRow = i => el("tr", {},
      el("td", {}, ext(issueUrl(i.number), "#" + i.number, "mono")), el("td", { class: "t", text: issueTitle(i.title) }),
      el("td", {}, statusPill(i.status)), el("td", {}, el("div", { class: "chips" }, ...i.blockedBy.map(issueRef))),
      el("td", {}, el("div", { class: "chips" }, ...i.prs.map(prChip))));
    const itb = document.querySelector("#issues tbody");
    function renderIssues() {
      itb.replaceChildren();
      for (const s of streams) {
        const all = leaves.filter(i => i.stream === s);
        const shown = all.filter(i => matches("#" + i.number, i.title, STATUS[i.status], ...i.prs.map(prLabel)));
        if (!shown.length) continue;
        const stripe = el("span", { class: "stripe" }); stripe.style.background = `var(--lane-${s.lane % 3})`;
        const bar = meter(all); bar.classList.add("gbar");
        itb.append(el("tr", { class: "grp" }, el("td", { colspan: "5" }, stripe, ext(issueUrl(s.issue), s.name), el("span", { class: "gcount", text: ` #${s.issue} · ${all.length} issues · ${countLine(all)}` }), bar)));
        shown.forEach(i => itb.append(issueRow(i)));
      }
      const others = D.issues.filter(i => !i.stream && !isTracker(i.number) && matches("#" + i.number, i.title));
      if (others.length) { itb.append(el("tr", { class: "grp" }, el("td", { colspan: "5", text: "Outside the streams" }))); others.forEach(i => itb.append(issueRow(i))); }
      if (!itb.children.length) itb.append(el("tr", {}, el("td", { colspan: "5", class: "muted", text: "No issues match the filter." })));
    }

    const FILTERS = [["all", "All", () => true], ["review", "Ready for review", p => p.kind === "review"], ["draft", "Draft", p => p.kind === "draft"],
      ["fix", "Needs a fix", p => p.attention], ["merged", "Merged", p => p.kind === "merged"]];
    const REPOS = [["all", "All repositories"], ...C.repos.map(r => [r.name, r.name])];
    const remembered = key => { try { return localStorage.getItem(`${C.slug}-${key}`); } catch (e) { return null; } };
    const remember = (key, v) => { try { localStorage.setItem(`${C.slug}-${key}`, v); } catch (e) { /* storage unavailable */ } };
    let filter = remembered("filter") || "all", repo = remembered("repo") || "all";
    const bar = $("prfilters"), ptb = document.querySelector("#prs tbody");
    const KIND_ORDER = { review: 0, draft: 1, merged: 2, closed: 3 };
    function renderPRs() {
      bar.querySelectorAll("button").forEach(b => b.setAttribute("aria-pressed", String(b.dataset.f === filter || b.dataset.r === repo)));
      const keep = (FILTERS.find(f => f[0] === filter) || FILTERS[0])[2];
      const rows = D.prs.filter(keep).filter(p => repo === "all" || p.repo === repo).filter(p => matches(prLabel(p), "#" + p.number, p.title, ...p.work.map(n => "#" + n)))
        .sort((a, b) => (b.attention - a.attention) || KIND_ORDER[a.kind] - KIND_ORDER[b.kind] || a.repo.localeCompare(b.repo) || b.number - a.number);
      ptb.replaceChildren(...rows.map(p => {
        const [cls, text] = p.kind === "merged" ? ["st-done", `Merged ${age(p.mergedAt)} ago`] : p.kind === "closed" ? ["st-closed", "Closed"] : p.kind === "review" ? ["st-review", "Ready for review"] : ["st-draft", "Draft"];
        const ci = !p.open ? "" : p.ci === "SUCCESS" ? "passing" : p.ci === "FAILURE" || p.ci === "ERROR" ? "failing" : p.ci === "PENDING" ? "running" : "none";
        return el("tr", {},
          el("td", {}, prChip(p)),
          el("td", { class: "t" }, ext(prUrl(p), p.title), REPO[p.repo].primary ? null : el("span", { class: "muted", text: `  · ${p.repo}` })),
          el("td", {}, el("span", { class: "pill " + cls, text }), p.open && p.mergeable === "CONFLICTING" ? el("div", {}, el("span", { class: "pill st-bad", text: "Conflicts" })) : null),
          el("td", {}, ci ? el("span", { class: "pill " + { passing: "st-done", failing: "st-bad", running: "st-draft", none: "st-closed" }[ci], text: ci }) : null),
          el("td", {}, el("span", { class: "delta" }, el("span", { class: "p", text: "+" + p.additions }), " ", el("span", { class: "m", text: "−" + p.deletions }))),
          el("td", {}, el("div", { class: "chips" }, ...p.work.map(issueRef))),
          el("td", { class: "mono", text: age(p.createdAt) }));
      }));
      if (!rows.length) ptb.append(el("tr", {}, el("td", { colspan: "7", class: "muted", text: "No pull requests match this filter." })));
    }
    for (const [k, label, keep] of FILTERS) {
      const b = el("button", { type: "button", text: `${label} ${D.prs.filter(keep).length}` }); b.dataset.f = k;
      b.addEventListener("click", () => { filter = k; remember("filter", k); renderPRs(); });
      bar.append(b);
    }
    bar.append(el("span", { class: "sep" }));
    for (const [k, label] of REPOS) {
      const b = el("button", { type: "button", text: label }); b.dataset.r = k;
      b.addEventListener("click", () => { repo = k; remember("repo", k); renderPRs(); });
      bar.append(b);
    }
    $("q").addEventListener("input", e => { query = e.target.value.trim().toLowerCase(); renderIssues(); renderPRs(); });
    renderIssues(); renderPRs();
  })();

  /* ---------- files, glossary, footer ---------- */
  $("filesnote").append(`Lean files under ${(C.leanDirs || []).join(" and ")} on ${PRIMARY.name} main. Merged work elsewhere is counted in the pull-request table.`);
  if (!D.mainFiles.length) $("files").append(el("div", { class: "muted", text: "No campaign Lean files on main yet." }));
  for (const f of D.mainFiles) $("files").append(el("div", {}, el("span", { text: f.path }), el("span", { text: `${f.lines} lines · ${f.sorry} sorry` })));

  if ((C.glossary || []).length) $("glossary").append(...C.glossary.map(([term, def]) => el("div", {}, el("dt", { text: term }), el("dd", { html: def }))));
  else $("glossarysection").hidden = true;

  const meta = D.meta || {};
  $("footer").append(
    "This page is regenerated every hour from GitHub",
    meta.workflowUrl ? el("span", {}, " by the ", ext(meta.workflowUrl, "campaign-board workflow")) : null,
    ", and an open page reloads itself. The raw snapshot is ", el("a", { href: "data.json", text: "data.json" }), ". ",
    "A partly landed issue is one with at least one merged pull request that is still open. A stage or paper result takes the least advanced status among its issues. ",
    "The stage texts paraphrase each manuscript's own proof outline. ",
    meta.gapsUrl ? el("span", {}, "The gap summaries are maintained in ", ext(meta.gapsUrl, meta.gapsPath), ", and the paper-gap notes themselves are authoritative.") : null);
})();
