# tenkz 0.6 worklist — ranked after RMP tranche-2 merge (2026-07-17)

Input: 31 tranche-2 verdicts. Tally: 3 clean (t2_mpublock, t2_renorm13,
t2_olvert), 16 clean-with-noted-gap, 12 still-blocked. Gaps deduped across
verdicts; ranked by unblock count (still-blocked figures a gap is named a
blocker for, primaries first; noted-gap upgrades as tie-break). Known 0.5
gaps (WHATS-NEW-0.5.md §Gaps) folded in with code-verified status.

## 0.5 gap status

| 0.5 gap | Status | Evidence |
|---|---|---|
| Per-side boundary control | **LANDED** | `west=`/`east=` choice keys, tex/tenkz/tenkz-grid.code.tex lines 120–196; t2_lassodef_v2 re-audit: "the west=/east= per-side policy … is now consulted by the renderer", .tnlog signatures balance. Successor gap: per-row-per-side (item 8). |
| Bare identity-wire atom | open | t2_mpucond: all-empty wire row emits no ink and a scalar signature (item 11). |
| `combined=` on `wires=k` | open | t2_sptgh_box, t2_purifyO (item 10). |
| Inter-sheet closures | **LANDED** | Four lattice sides accept `cup` / `cup=M` for the exact `sheets={ket,bra}` role stack; each sitewise virtual contraction emits a cup event and consumes its boundary endpoints. Same-sheet periodic closure remains separate. |
| Directed signatures | open, zero tranche-2 demand | tenkz-grid.code.tex lines 248–250: "deferred to the next audit revision" (tail item). |
| Mirrored `tri=` closures | open, zero tranche-2 demand | `tri=l\|r` skins only, tenkz-grid.code.tex lines 373–380; no closure key (tail item). |

Also confirmed landed by tranche 2: the 1x1-grid "Missing number" failure
(t2_renorm13, fixed by the concurrent extension) and
`chain axis=south` + `periodic style=hooks` (t2_olvert, exact match).

## Ranked worklist

### 1. Operator-hued `\tnjoin` (wire-style key, free tier)
Named blocker for 3 still-blocked figures, cited by 6 total — the largest
single-primitive win.
- Blocks: t2_eq50_pull, t2_eq54_ginj (cleared outright), t2_sptmpo_cross
  (primary; parallelogram skin remains as noted gap).
- Upgrades: t2_pentagon4, t2_idempotent, t2_seljbraid (red string carried
  only by geometry).
- Evidence: tenkz-free.code.tex lines 120/166/172 — `\l__tenkz_jstyle_tl`
  resolves only to `bond` / `fused bond`. Suggested key:
  `/tenkz/join/operator` or a wire-style option on `\tnjoin`.

### 2. `/tenkz/lattice/physical/updown`
1 sole-blocker clear + 1 secondary; acceptance test already written.
- Blocks: t2_probe_pepoupdown / sec2fig5PEPO (sole blocker — probe fails
  with pgfkeys "Choice 'updown' unknown", becomes the acceptance test);
  t2_wrap9a (secondary, PEPO sheets).
- Evidence: tenkz-lattice.code.tex lines 128–130 — `physical=` choice stops
  at `up|none`. Unchanged by the concurrent extension (probe verdict).

### 3. Multi-wire glyph leg completeness
Named for 3 still-blocked figures (1 primary + 2 co-blockers).
- Per-spanned-column pairing for wide `legs at=` glyphs at a PAIRED
  interface: t2_hamil_gate (primary — second spanned column's partner leg
  dropped; its `\tnskip` secondary is item 12).
- Per-spanned-row legs on `wires=k` bricks: t2_twoshift (co-blocker), and
  t2_mpuflow / sec2fig9a per its tranche-1 record.

### 4. Per-atom / per-site / per-wire hue keys
Co-blocker for 2 still-blocked, upgrades 5 — the hue system beyond `\tnjoin`.
- Co-blocks: t2_twoshift (per-wire hue key: blue right-mover vs red
  left-mover IS the content), t2_braidpat1 (per-site hue/species slot on
  `\tnsite`).
- Upgrades: t2_mpubrick (per-atom red/blue sub-tensor hues), t2_gs2d_lasso
  (A/B side split), t2_lassodef_v2 (A-side red vs B-side gray),
  t2_idempotent (hue skin on `\tnput`), t2_ared_loop (periodic racetrack
  should inherit the traced row's `operator bond` hue instead of neutral
  `trace` black).

### 5. Inter-sheet closures: `east=cup` at the lattice tier — LANDED
All four lattice sides now accept `cup` / `cup=M` for the exact ket--bra
role stack.  The renderer draws one virtual ket--bra closure per complete
boundary pair, records it separately from physical pairing, and seals the
consumed side.  Numeric and operator stacks warn rather than inventing a
contraction.  Same-sheet periodic virtual closure is a different topology.

### 6. tenkzlattice annotation layer
1 primary blocker + 2 noted-gap upgrades, all lattice-tier labels/styles.
- `label=<text>` on `\tnsite`: t2_lhsrhs6 primary (A/B vs B/C tile labels
  are the load-bearing difference; secondary removed-site mode in item 13).
- Leg/edge label key (eight group labels g_i, g_1 g_4^{-1}, …), squiggle
  physical-index mark on `\tnedge`, boundary-leg length override (0.30 vs
  0.27 pitch): t2_tcprimal_v2, t2_tcdual_v2.
- `\tnedge` edge-style option honored (e.g. `\tnedge[dashed]` — currently
  parses but ignores its option slot): t2_tcdual_v2.

### 7. Per-bond suppression in tenkzlattice
1 primary clear.
- Blocks: t2_czx — auto-drawn nearest-neighbour bonds appear INSIDE each
  blocked 2x2 blob. Exact key: `\tnbond[none]{(r,c)-(r,c+1)}` or a
  blocked-site key. Secondary (circular blob region) in item 14.

### 8. Per-row-per-side boundary suffix
1 primary clear; cheap successor to the landed `west=`/`east=` plumbing.
- Blocks: t2_mpusplit — split factors need east-only (u) / west-only (v)
  stubs; `rows=` suffix seals both sides, picture-level `west=`/`east=`
  apply to all rows. Exact spelling: `rows={op:west none, op:east none}`.

### 9. Entangled-pair blob site + projection-arrow physical leg
1 primary clear.
- Blocks: t2_pairs / sec2fig1 — `site=blob` (ellipse enclosing one ancilla
  dot per incident bond) + `physical=arrow` to a detached spin dot; plain
  sheet reads as ordinary PEPS, not the projection construction.

### 10. `combined=` on `wires=k` glyphs (0.5 carry-over)
2 noted-gap upgrades.
- t2_sptgh_box (gh MPO tensor cannot sit on the combined west wire
  in-picture; juxtaposed panels, split signature), t2_purifyO (`combined=`
  on wires=2 pill glyphs; plus fuse capsule skin, item 15).

### 11. Bare identity-wire atom (0.5 carry-over)
1 noted-gap upgrade, verified failure mode.
- t2_mpucond: RHS bare identity wire unrenderable — an all-empty vertical
  wire row emits no ink and a SCALAR signature; identity written as "I".

### 12. `\tnskip` robustness bugs
Secondary blocker for 1, workaround-papered in 1.
- t2_hamil_gate: skip holes sprout spurious west/east virtual stubs on the
  gate row. t2_lhsrhs3: trailing-column `\tnskip` bridged by `close east`
  (hole silently closed into the boundary loop; `\tnghost` workaround).

### 13. Routing gaps: cup-apex physical stub, hole-end turn-up, removed-site leg
- t2_lhsrhs2 + t2_lhsrhs3: hole's open virtual ends drawn horizontal, not
  turned up; boundary tensor's escaping physical leg emitted down from the
  bra-row pill instead of over the cup bend (cup-apex stub also noted as
  deferred in tenkz-grid.code.tex ~line 228). t2_lhsrhs6 secondary:
  removed-site mode that keeps the physical leg.

### 14. Non-rectilinear region shapes / free strings / crossing gaps
- Region shapes: t2_gs2d_lasso (filled ellipse vs rounded rectilinear;
  \bar R exterior float), t2_czx secondary (circular blob).
- Off-lattice string primitive with over/under crossing gaps: t2_braidpat1
  co-blocker (half-braid loop inexpressible; `\tnedge` only marks lattice
  bonds), t2_seljbraid (crossings render as plain intersections).

### 15. Skin pack (cosmetic, no figure hinges solely on these)
- Sheared/parallelogram skin in `\tnput`: t2_sptmpo_cross (secondary),
  t2_idempotent. Per-cell in-glyph reroute skin
  (`reroute={north-east, west-south; …}`): t2_twoshift co-blocker.
- Fuse capsule skin (tall rounded capsule, interior label): t2_purifyO.
- Gray-disc junction beads + `\tntree` direction barbs: t2_pentagon5,
  t2_pentagon4. Oblique product-bead legs + square-bracket closure style:
  t2_rgfp4. Cut half-gates at window edges (a brick is whole): t2_mpubrick.

### Tail (no tranche-2 demand)
- Directed boundary signatures (0.5 carry-over): code-deferred,
  tenkz-grid.code.tex lines 248–250.
- Mirrored `tri=` closures (0.5 carry-over): no verdict cites them.
