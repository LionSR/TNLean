# Retiring the legacy fixture corpus

The four legacy front ends — `tenkz-cd`, `tenkz-free`, `tenkz-lattice`,
`tenkz-grid` — are sentenced by the 1.0 contract (`LANGUAGE-1.0.md` §10) and
delete once their consumers are gone (issue #4699, tracked on #4709). The
blueprint consumers are migrating separately. What remains is the standalone
fixture corpus: the 264 top-level files under `tests/tenkz/` whose `.tnlog`
event streams are pinned by `tests/tenkz/golden-events.sha256`. That baseline
exists to prove the internal rebuild kept event streams byte-identical; it is
not, by itself, a reason to keep a fixture whose language is being deleted.

This document answers the question that gates the deletion: **which behaviours
do the legacy fixtures exercise that the kernel suites
(`tests/tenkz/kernel/`) and the 130-case RMP corpus (`tests/tenkz/rmp/`) do
not?** Every behaviour the legacy corpus carries is classified three ways:

- **dies** — the behaviour is a spelling the contract tombstones
  (`LANGUAGE-1.0.md` §10), an alias with a 1.0 sunset, or a construct whose
  retirement holds a verdict in `docs/tenkz/SHRINK.md`. The coverage is of
  something that will not exist; no replacement is needed.
- **covered** — the behaviour survives under a kernel spelling and a named
  kernel or RMP case already exercises it.
- **gap** — the behaviour survives and nothing outside the legacy corpus
  exercises it. Each gap names the replacement fixture that must land before
  the deletion.

Migration codes per fixture (preserve/codemod/redraw) are the separate ledger
in `DISPOSITIONS.md`; this document classifies coverage, not migration.

## 1. Method

Three measurements, each reproducible from the tracked tree:

1. **Construct and key inventory.** Every fixture in the three corpora was
   scanned for environment openings, command occurrences, and option keys with
   their values, using the comment-stripping and balanced-group scanners in
   `scripts/tenkzlib/texcase.py`, following local `\input` dependencies
   (`modes_suite.inc`). The compared suites are the 264 top-level fixtures
   against `tests/tenkz/kernel/*.tex` (12), `kernel/regression/` (127),
   `kernel/sugar/` (20), and `tests/tenkz/rmp/*/cases/` (130). The 108
   `kernel/negative/` fixtures pin diagnostics, not behaviours, and were kept
   out of the coverage side.
2. **Full-corpus compile.** All 264 fixtures were compiled with the
   `HACKING.md` invocation; all succeed, and every emitted `.tnlog` was
   parsed for its event kinds and `picture` language fields.
3. **Spot verification.** Every "covered" claim below names its covering
   case, checkable with one `grep` in the named file.

## 2. Corpus census

By the language of the picture events each fixture emits when compiled:

| Surface | Fixtures | Event vocabulary |
|---|---:|---|
| dying dialect (`lang=lattice` 59, `free` 40, `cd` 14; overlapping) | 104 | `lattice` `site` `edge` `region` `trace` `cup` `hooks` `hole` `surface` `pairtrace` `join` `cdcell` `cdarrow` `tree` … |
| 0.7 grid only (`lang=grid`, no kernel switch) | 143 | `bond` `boundary` `faceports` `pairleg` `phtrace` `span` `label-use` `bbox` … |
| kernel (`\tenkzkernel`: `fig21d_cubic.tex`, `fig21d_cubic_v2.tex`) | 2 | `atom` `wire` `kernel-boundary` `frame` |
| no picture event (command-only and geometry probes) | 15 | `tree` (`\tntree`-only sources), `geomprobe`, or none |

At source level, 104 fixtures open a dying dialect environment
(`tenkzcd`/`tenkzfree`/`tenkzlattice`/`tenkzplanes`, directly or through a
local input), 140 open only the 0.7 `tenkz` grid environment, 2 carry the
kernel switch, and 18 open no tenkz environment. Warnings are emitted by 17
fixtures with the codes `combined-attach`, `plane-tall-window`,
`planes-interleave`, `sheet-coincide`, `plane-rise-low`, `plane-slant-band`,
`sheet-role`, and `interface-range`.

The whole dialect event vocabulary above dies with the front ends: the kernel
model emits only kernel records (`atom`, `wire`, `mark`, `string`,
`kernel-boundary`, `check`, geometry records), pinned by the kernel suite's own
ledgers `tests/tenkz/kernel/golden.sha256` and `golden-pixels.sha256`. The
coverage question is therefore not about event kinds but about the behaviours
behind them, classified next.

## 3. Behaviour ledger

Carrier counts are fixtures using the spelling; representative carriers are
named. Evidence for **dies** is the contract or ledger line; evidence for
**covered** is the covering case. Paths: `r_*` are
`tests/tenkz/kernel/regression/`, `n_*` are `kernel/negative/`, `s*` are
`kernel/sugar/`, `k_*` are `kernel/`, `rmp-*` are `tests/tenkz/rmp/*/cases/`.

### 3.1 Environments and surfaces

| # | Behaviour | Carriers | Verdict | Evidence |
|---|---|---|---|---|
| 1 | `tenkzcd` typed-map grids (`maps`, `polygon=`, `radius=`, `column sep=`, `row sep=`, `\tnarrow`) | 14 (`cd_test`, `p4067_*`, `pentagon_corrected`, `p3_corner`, `p3_slidecd`, `p3_sliding`) | dies | §10: commutative diagrams belong to tikz-cd, outside this language |
| 2 | `tenkzcd`/grid fusion-tree content (`\tntree`) | 16 (`tree_test`, `gr_t2_fsymbol`, `p3_eq5_*`, `t2_fusion`, `t2_pentagon5`) | covered | `rmp-iii-a-fusion-tensor`, `rmp-iii-a-pentagon-peps` |
| 3 | `tenkzfree` irregular typed graphs (`\tnput`/`\tnjoin` placement) | 40 (`free*`, `gr_t4_lasso`, `t2_peps`, …) | dies | §10: redrawn as addressed `\tn`/`\tnwire`/`\tnmark` records; addressed-graph coverage is rows 40–43, 47–49 |
| 4 | `tenkzlattice` spatial lattices, sheets, regions | 53 (`lattice_test`, `notch`, `t2_tc*`, `fig21d_expect`, …) | dies | §10: `tenkz` with `lattice=` sugar or a declared basis; content coverage in §3.2, §3.5 |
| 5 | `tenkzplanes` two-sheet preset | 11 (`plane_test`, `ease_test`, `xyz_*`, …) | dies | §10; the preset is the `planes` sugar row: `s9_sugar.tex` |
| 6 | 0.7 grid open-by-default sides and `boundary=none` sealing | 140 grid fixtures | dies | §14.6: the kernel side default is `none`; default pinned by `r_side_default_none.tex` |

### 3.2 Picture keys

| # | Behaviour | Carriers | Verdict | Evidence |
|---|---|---|---|---|
| 7 | `periodic` bare flag | 38 | dies | alias, sunset 1.0 (registry); `boundary=periodic` covered by `s2_sugar.tex` |
| 8 | `boundary legs` | 36 | dies | alias, sunset 1.0; `boundary=open` covered by `r_side_default_none.tex`, `rmp-ii-boundary-region` |
| 9 | `chain axis=` | 3 | dies | alias, sunset 1.0; frame words covered by `k_plane.tex` |
| 10 | `tensor style=` | 50 | dies | §10 → `skin=`; `r_exact_glyph_faces.tex`, `r_ink_semantics.tex` |
| 11 | `inline`, `compact` metric profiles | 17 (`smoke`, `audit2`, `p3_*` probes) | dies | §10 → math-style sensing + `size=`; sensing is unimplemented — see gap G3 |
| 12 | picture-scope `pitch=` | 3 (`p3_pitch_probe`, …) | dies | 0.7 spelling; document metric via `\tnset{pitch=}` covered by `r_basis_spacing.tex` |
| 13 | `west label=`, `east label=` | 11 fixtures | dies | SHRINK verdict (wave note: consumers respell onto a station on the cup arc); the station is `r_onwire_cup_arc.tex` |
| 14 | `bond label=` | 17 | dies | SHRINK verdict: dies at S4 with the 0.7 picture ledger; wire-point label marks covered by `r_dot_label_carriers.tex` |
| 15 | `bond dir=` | 4 | dies | 0.7 spelling; `dir=` covered by `r_physical_dir.tex`, `r_dir_open_bearings.tex` |
| 16 | `trace style=racetrack\|hooks` | 6 | dies | §10: closure depth follows the selection the closure clears; `r_cup.tex`, `r_one_sided_trace.tex` |
| 17 | `layer sep=` | 4 (`cups_*`) | dies | 0.7 spelling; concentric order is doctrine: `r_cup_both.tex`, `r_nested_regions.tex` |
| 18 | `site=none` | 4 | dies | lattice spelling; the invisible junction is `skin=none`: `r_exact_glyph_faces.tex`, `r_physical_leg_lane_plan.tex` |
| 19 | `sheets=` count and role lists | 10 | dies | §10: a sheet is a basis member of one frame; `k_plane.tex`, `r_planes_doubled_scaffold.tex`, `s9_sugar.tex` |
| 20 | `pairing` sheet flag | 3 | dies | ket-bra pairing is frame-typed in the kernel: `r_transverse_pairing.tex`, `rmp-ii-peps-marginal` |
| 21 | `outer legs=` | 2 (`sheets_*`) | dies | plane physical policy: `r_plane_transverse_physical.tex` |
| 22 | `sheet sep=`, `plane lean=`, `plane rise=`, `plane slant=` | 6 | dies | escape rows die with the dialect; plane ratios are house metrics, spacing guarded by `r_basis_spacing.tex` |
| 23 | `col vector=`, `row vector=`, `sheet vector=` | 3 (`xyz_test`, `t2_condensanyon`) | dies | §10 → `frame=plane` with a declared basis: `r_basis_plane.tex`, `k_plane.tex` |
| 24 | `frame=vertical\|rotate\|oblique\|slab` words | ~30 | dies | §10: `flat`, `plane`, `circle` only; `r_plane_projection.tex`, orientation from placement `k_ring.tex`, `r_label_carriers_affine.tex` |
| 25 | `sandwich` | 38 | covered | `s1_sugar.tex`, `r_false_flags.tex` |
| 26 | `physical=up\|down\|updown` policy | 86 | covered | `r_physical_policy.tex`, `r_atom_physical_answer.tex`, `k_blocking.tex` |
| 27 | `boundary=open\|none` | 9 | covered | `r_side_default_none.tex`, `rmp-ii-peps-marginal` |
| 28 | side words `open`/`none`/`trace`/`cup` on `west=`…`south=` | 60+ | covered | `r_cup_label.tex`, `r_closure_implicit_virtual.tex`, `r_bond_restated.tex` |
| 29 | labelled cup with matrix atom (`west={cup=$X$}`) | 14 (`p_newcup`, `channel_test`, `cups_*`, …) | covered | `r_cup_label.tex`, `s10_kernel.tex` (atom `at=on cup-west-1-2 0.5`) |
| 30 | `open=`/`trace=` cell selections | 10 | covered | `r_cell_policy.tex`, `r_cell_policy_typed_ports.tex` |
| 31 | `trace=physical` | 8 | covered | `r_affine_physical_trace.tex`, `rmp-ii-zcl-mpdo` |
| 32 | `align=` | 1 | covered | `r_equation_policy.tex` |
| 33 | `rows=`/`cols=` topology | 164 | covered | throughout; `r_tall_grid.tex`, `r_wide_chain.tex` |

### 3.3 Atom keys and commands

| # | Behaviour | Carriers | Verdict | Evidence |
|---|---|---|---|---|
| 34 | skin flags `dot`/`box`/`pill`/`mpo`/`ring`/`circle`/`boundary`/`tri=l\|r` | 60+ | dies | 0.7 flag spellings; `skin=` values covered: `r_exact_glyph_faces.tex`, `r_pill_skin_prelude.tex`, `r_mpo_skin_prelude.tex`, `r_tri_apex_mirror.tex` (tri and triwest), `s10_kernel.tex` (ring) |
| 35 | `up=`/`down=` port-label keys | 30 | dies | §10 → `ports=`; port labels covered by `rmp-ii-blocking`, `r_closure_port_labels.tex` |
| 36 | `up at=`/`down at=`/`west at=`/`east at=`/`combined=`/`span=` | 23 | dies | SHRINK verdicts (fold into the ports grammar); slotted ports covered by `rmp-ii-blocking` (`90@1`), `r_route_typed_ports.tex`, `r_index_pair_scaling.tex` |
| 37 | `legs at=`, fusion `rows=` alias | 9 | dies | aliases, sunset 1.0 |
| 38 | `no legs` | 12 | dies | 0.7 spelling; the refusal is `physical=none`: `r_atom_physical_answer.tex` |
| 39 | site `removed=` | 11 | dies | lattice spelling; `void=sealed` covered by `r_sealed_void.tex` |
| 40 | `\tnput`, `\tnsite` placement | 45 | dies | §10 → `\tn[at=…]`: `r_explicit_at.tex`, `r_midway.tex` |
| 41 | `\tnghost` invisible anchors | 41 | dies | §10: addresses reference empty cells directly; string ends on empty wire cells in `k_torus.tex` |
| 42 | `\tnX` on-wire map | 34 | dies | SHRINK verdict: tombstoned, migrates to `\tn[skin=ring]`; `s10_kernel.tex` |
| 43 | `\tnfuse` fusion atom | 34 | dies | SHRINK verdict: demoted to a prelude-declared atom; declarations covered by `r_declare_atom.tex`, trees by `rmp-iii-a-fusion-tensor` |
| 44 | `\tndots` elision | 33 | covered | `rmp-ii-tangent-projector` (command), `k_blocking.tex` (`skin=dots`); sentenced to fold into `\tn[skin=dots]` at the language landing |
| 45 | `\tnskip` open hole | 11 (`hole` event emitters) | **gap G1** | the kernel target `void=open` has no surviving fixture; see §5 |
| 46 | atom-scope `physical=` answers | 14 | covered | `r_atom_physical_answer.tex` (`none`, `up` against an `updown` row; the atom-scope `updown` answer of `t2_twoshift` folds into G1's fixture) |
| 47 | typed `ports=` lists (free dialect) | 11 | covered | `r_closure_typed_ports.tex`, `r_authored_port_default_type.tex` |
| 48 | `wide=`/`wires=` spans | 40+ | covered | `k_roperator.tex`, `r_tall_grid.tex`, `r_basis_member_wide.tex` |
| 49 | `role=`, object `size=`, `label pos=` | 20+ | covered | `s6_sugar.tex`, `r_ink_semantics.tex`, `r_label_turn.tex`, `rmp-ii-staircase` |
| 50 | site `label=`, atom `frame=rotate` | 2 | dies | lattice spelling and §10 frame tombstone |

### 3.4 Wire keys and commands

| # | Behaviour | Carriers | Verdict | Evidence |
|---|---|---|---|---|
| 51 | `\tnjoin`, `\tnedge` connections | 45 | dies | §10 → `\tnwire`; `r_bond_restated.tex` and throughout |
| 52 | `\tnarrow` directed maps | 6 | dies | died with `tenkzcd`; a directed index is `\tnwire[dir=to]`: `r_physical_dir.tex` |
| 53 | `out=`/`in=` arc angles | 23 | dies | §10 → `route=arc`: `rmp-iv-ground-space-1d`, `r_onwire_cup_arc.tex` |
| 54 | `route=hv\|vh\|curve` | 7 | dies | migration-only values; `route=orth` `k_roperator.tex`, `route=arc` `rmp-iv-ground-space-1d` |
| 55 | connection `label=` | 18 | dies | 0.7 spelling; port labels and wire-point marks: `r_closure_port_labels.tex`, `r_dot_label_carriers.tex` |
| 56 | `fused` doubled strands | 2 | dies | §10: the port type decides the stroke; `r_physical_wire_stroke.tex` |
| 57 | connection `none` flag | 1 | dies | §10: omit the record; `void=sealed` removes a site (`r_sealed_void.tex`) |
| 58 | `distinguished`, edge `style=`, edge `role=` | 7 | dies | lattice spellings; semantic ink is `species=`: `r_ink_semantics.tex`, `r_parallel_lanes.tex` |
| 59 | typed-endpoint mismatch checking (free joins) | 4 | covered | kernel port typing: `r_authored_port_default_type.tex`; negatives `n_port_type.tex` family |

### 3.5 Marks, regions, annotations

| # | Behaviour | Carriers | Verdict | Evidence |
|---|---|---|---|---|
| 60 | `\tnregion` semantic enclosures | 32 | dies | §10 → `\tnmark[form=enclosure]`: `r_region_staircase.tex`, `r_region_complement.tex`, `k_czx.tex` |
| 61 | `\tncut` connection cut | 7 | dies | §10: `form=cut` fails tenure outright, no successor owed |
| 62 | `\tnspan` braces above/below | 16 | dies | SHRINK verdict; the kernel states ranges through mark addresses: `r_mark_bracket_range.tex` |
| 63 | `slot=selected`, `slot=secondary` | 25 | covered | `r_region_staircase.tex`, `r_region_complement.tex`, 13 `slot=selected` uses across `k_*` and RMP |
| 64 | `slot=complement\|collar\|neutral` | 5 (`lattice_test`, `notch`, `feat`, `t2_gs2d_lasso`, `t2_tcdual`) | **gap G2** | live kernel enum words (`tenkz-kernel.code.tex` line 1222) with no surviving fixture; see §5 |
| 65 | region `name=` | 4 | **gap G2** | `name` is a registered kernel mark key with no surviving fixture; folded into G2's replacement |
| 66 | `outline` flag | 17 | dies | 0.7 spelling; a kernel enclosure strokes only, `tint` adds the paper: `r_region_staircase.tex` |
| 67 | `inset=` nested regions | 6 | covered | `rmp-iv-ground-space-2d`; concentric order doctrine `r_nested_regions.tex` (the key itself is sentenced by the amendments) |
| 68 | `label at=` | 9 | dies | alias, sunset 1.0; `label pos=` covered by `r_label_turn.tex` |
| 69 | free region `group=` membership | 5 | dies | free spelling; enclosure over a named selection: `k_czx.tex` (member selection) |

### 3.6 Addresses and selectors

| # | Behaviour | Carriers | Verdict | Evidence |
|---|---|---|---|---|
| 70 | hyphen cell ranges `(1-3,1-3)` and `+` union | 30+ | dies | §10: a hyphen cannot be told from a generated name; `..` ranges and braced unions covered by `r_region_staircase.tex`, `r_basis_range_empty.tex` |
| 71 | lattice selector subtraction | 10 | covered | `r_selector_subtraction.tex`, `r_region_complement.tex` |

### 3.7 Diagnostics, event stream, embedding

| # | Behaviour | Carriers | Verdict | Evidence |
|---|---|---|---|---|
| 72 | dialect event vocabulary (§2 table) | 262 | dies | the kernel emits kernel records only, pinned by `tests/tenkz/kernel/golden.sha256` |
| 73 | `combined-attach` warning | 6 | dies | dies with `combined=` (row 36) |
| 74 | `planes-interleave`, `sheet-coincide` warnings | 5 | dies | superseded by the §4 basis-spacing diagnostic: `r_basis_spacing.tex`, `n_geom_singular_basis.tex` |
| 75 | `plane-tall-window` warning | 2 | covered | `r_plane_warning.tex` |
| 76 | `plane-rise-low`, `plane-slant-band`, `sheet-role`, `interface-range` warnings | 7 | dies | attached to escape and role spellings that die (rows 19–22) |
| 77 | `.tnlog` header framing (`hdr.tex`) | 1 | covered | kernel golden gate; `scripts/test_tnlog.py` schema tests |
| 78 | grid boundary audit (`audit1`–`audit4`, `audit_open`, `boundary` events) | 5 | dies | grid `boundary` records die; the kernel boundary signature and equation audit are `r_physical_port_signature_equiv.tex`, `r_equation_policy.tex`, `r_check_scope_nested.tex` |
| 79 | savebox embedding (`lrbox_probe`) | 1 | covered | `r_declaration_whitespace.tex` (kernel pictures measured in saveboxes) |
| 80 | inline-math embedding and density profiles (`modes_test`, `modes_dot_baseline`, `\tnpic` carriers) | 12 | **gap G3** | conditional on contract work; see §5 |
| 81 | document and group `\tnset` scoping | 4 | covered | `r_setup_persistence.tex`, `r_kernel_scope.tex` |
| 82 | species cycle and derived ink (`p_species`) | 1 | covered | `r_ink_semantics.tex`, `k_skin_pairings.tex` |
| 83 | fraction-placed atoms on the production render path (`zz_renderslice`) | 1 | covered | `r_onwire_cup_arc.tex`, `r_wire_on_curve.tex`, `r_midway.tex` |
| 84 | vertical draw-prune guard (`zz_vertprune`) | 1 | dies | guards `frame=vertical` closure derivation, dead with row 24 |
| 85 | figure-level RMP drafts (`hard01`–`hard12` and versions, `t2_*`, `p3_*`, `gr_t*`, `p4067_*`, `pentagon_corrected`, `rmpfig2_test`) | ~140 | covered | each figure's benchmark form is an RMP case of the same subject (`rmp-ii-mpu-two-shift` for `t2_twoshift`, `rmp-app-czx-state` for `t2_czx`, `rmp-app-toric-dual` for `t2_tcdual`, `rmp-iii-b-self-braiding` for `t2_seljbraid`, `rmp-ii-zcl-mpdo` for `hard12_zcl`, `rmp-ii-reduced-density` for `hard03_rdm`, …); the figure-level classification of every one of these fixtures is codemod or redraw in `DISPOSITIONS.md` |

## 4. Counts

Classifying the 85 ledger rows: **55 die** with their dialect, **26 are
covered** by a named kernel or RMP case, and **4 rows are gaps**, forming
three distinct gaps (G1 and G2 immediate — G2 spans rows 64 and 65 — and G3
conditional). Nothing else in the legacy corpus's construct inventory,
key-value inventory, or event census falls outside these rows.

## 5. The gaps

### G1 — `void=open` (write before deletion)

The eleven fixtures that call `\tnskip` are the only tests of an open hole:
they emit the grid `hole` event and pin that a removed object preserves its
open indices. The kernel implements the surviving spelling —
`void={open,sealed}` is a registered choice in `tenkz-kernel.code.tex` — but
`r_sealed_void.tex` covers only `void=sealed`. Deleting the corpus leaves
`void=open` untested.

**Replacement:** `tests/tenkz/kernel/regression/r_void_open.tex`. One chain
(`rows={wire}`, `cols=3`, `physical=up`) whose middle cell is
`\tn[void=open]{}`. Pin structurally: the void cell contributes no glyph
record; the frame bonds incident to the hole and the hole's preserved indices
match the `void=open` contract (§2.3: a hole that preserves indices, against
`void=sealed`, which removes the site and its bonds — count wire records and
compare the boundary signature against the sealed variant in a second
picture). Include one atom answering `physical=updown` at atom scope, the one
policy-answer value `r_atom_physical_answer.tex` does not spell.

### G2 — mark slot words and mark names (write before deletion)

The kernel mark slot alphabet is `{selected, secondary, complement, collar,
neutral}` (`tenkz-kernel.code.tex` line 1222), and marks accept `name=` (line
1227). Surviving suites exercise only `selected` (13 uses) and `secondary`
(`r_region_complement.tex`). The words `complement`, `collar`, and `neutral`
and the mark `name=` key are exercised solely by five legacy lattice fixtures
(`lattice_test`, `notch`, `feat`, `t2_gs2d_lasso`, `t2_tcdual`).

**Replacement:** `tests/tenkz/kernel/regression/r_region_slot_words.tex`. One
grid with three enclosures carrying `slot=complement`, `slot=collar`,
`slot=neutral`, one of them `name=R`. Pin: each slot resolves to its own
semantic ink (the theme maps `collar` to its dedicated hue,
`tenkz-kernel.code.tex` line 15385) and the named mark is accepted and
recorded. If the deferred slot-for-species exchange
(`LANGUAGE-1.0.md` §14.5) lands first and retires `slot=`, the fixture pins
the `species=` respelling instead and the three words join the tombstones.

### G3 — inline embedding and math-style sensing (conditional on contract work)

A dozen fixtures (`modes_test`, `modes_dot_baseline`, `smoke`, `rv_probe`,
the `adv_*` family, `audit2`, `part_B8`, `gallery` among them) are the only
tests that place
pictures in inline math and running text and the only tests of metric response
to math context — today through the 0.7 `inline`/`compact` profiles and the
`\tnpic` command, all of which die (§10). The surviving contract spellings are
the `\tnpic` sugar row over the picture environment (§9) and math-style
sensing (§7.2). Neither exists in `tenkz-kernel.code.tex` yet (no `tnpic`
binding, no math-style branch), so no replacement fixture can be written
today, and nothing presently testable is lost by the deletion.

**Requirement instead of a fixture:** the change that implements the `\tnpic`
sugar row and math-style sensing must land its sugar-pair fixture
(`kernel/sugar/` class, as §9 already mandates for every sugar row) and a
sensing regression in the same change. The deletion PR must reference the
tracking issue for that S4 work so the requirement is not lost with the
fixtures that used to state it.

## 6. Collateral the deletion must handle

- `tests/tenkz/golden-events.sha256` — re-pin (`scripts/tenkz_golden.sh`)
  after the corpus shrinks; the ledger currently holds all 264 hashes.
- `tests/tenkz/kernel/regression/r_sheet_coincide_plan.tex` and
  `r_sheet_coincide_removed.tex` — these two kernel-suite fixtures open
  `tenkzlattice` and die with the lattice front end. Their subject — spacing
  diagnostics over stacked sheets and removed sites — survives as the §4
  basis-spacing check, covered by `r_basis_spacing.tex` and
  `n_geom_singular_basis.tex`; site removal is `r_sealed_void.tex`. Delete
  them with the dialect and re-pin `tests/tenkz/kernel/golden.sha256` and
  `golden-pixels.sha256`.
- `tests/tenkz/PROVENANCE.tsv`, `tests/tenkz/LOCAL_FIXTURES.tsv` — drop the
  deleted rows; `scripts/test_tenkz_corpus_provenance.py` enforces agreement.
- `tests/tenkz/pixelpair-sources.txt` — all six listed fixtures (`gallery`,
  `gr_t1_fusion`, `gr_t3_action`, `gr_t8_sum`, `p3_eq3_fusion`,
  `p3_eq8_action`) are legacy; the pixel-pair command expires with the redraw
  campaign (`HACKING.md`), so retire the manifest with the fixtures.
- `tests/tenkz/modes_suite.inc` — shared input of `modes_test` and
  `modes_dot_baseline` only; dies with them.
- `scripts/tenkz_corpus.sh` — the special-case list at line 296 names
  `geom.tex`, `p_pitch.tex`, `p_species.tex`, `plane_experiment.tex`; update
  it for whichever of these the deletion removes.
- `docs/tenkz/DISPOSITIONS.md` and `scripts/check_tenkz_dispositions.py` —
  the fixture tables and counts are checked against the tracked tree and must
  shrink with it.
- `scripts/test_tenkz_cubic.py` — depends on `fig21d_cubic.tex` and
  `fig21d_cubic_v2.tex`, which are kernel fixtures and stay.

## 7. Survivors

Fixtures the deletion does not touch: the five with no tenkz construct
(`geom`, `plane_experiment`, `zz_geomdag`, `zz_geomframe`, `zz_geomsupport` —
geometry-stage probes emitting `geomprobe` events), the five pure-kernel-grid
preserves (`iso_h`, `p3_probe_opop`, `rv4061_flatonly`, `trace_warn`,
`zz_wirescan`), and the two kernel-switch fixtures (`fig21d_cubic`,
`fig21d_cubic_v2`). Everything else — 252 fixtures — either dies or is
respelled according to its `DISPOSITIONS.md` code, and either way leaves the
corpus safely once G1 and G2 land, with G3's requirement recorded on the S4
tracking issue.
