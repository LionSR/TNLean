# Blueprint chapters 9–13 + Lean: structural consolidation roadmap

Date: 2026-05-30. Scope: the canonical-form → BNT → after-blocking → Fundamental
Theorem arc. Compiled-chapter ↔ file map (verified against `content.tex`):

| Compiled | Title | File |
|---|---|---|
| Ch 9 | Canonical Form Reduction | `blueprint/src/chapter/ch08_canonical.tex` |
| Ch 10 | Block Permutation and Separation | `blueprint/src/chapter/ch09_block_perm.tex` |
| Ch 11 | Basis of Normal Tensors | `blueprint/src/chapter/ch10_bnt.tex` |
| Ch 12 | Canonical-form reductions after blocking | `blueprint/src/chapter/ch11b_after_blocking.tex` |
| Ch 13 | Proof of the Fundamental Theorem | `blueprint/src/chapter/ch11_fundamental_theorem_proof.tex` |

This roadmap synthesizes two read-only audits (one blueprint-structural, one
Lean-predicate). The complaint it answers: the logical development across these
chapters is repetitive, oddly ordered, and hard to read — and that mirrors
duplicated predicates and parallel proof routes in the Lean code.

## Root cause

Three activities — (A) *defining* canonical-form predicates, (B) *performing*
the reduction, and (C) *building* the BNT/sector machinery — are each smeared
across several chapters, with the base sector type and one canonical-form
predicate physically located in chapters that *depend on* them rather than
*define* them. The same concept is therefore defined 2–6 times.

## Duplication clusters (blueprint label / Lean decl)

### 1. "normal tensor" — two formulations, two constants, no formalized bridge
- `def:normal` / `MPSTensor.IsNormal` — **algebraic** (eventual `L₀`-block
  injectivity / full matrix span). The workhorse: ~212 refs across Wielandt /
  FT / RFP / ParentHamiltonian.
- `def:nt_cpsv` / `MPSTensor.IsNormalTensor` — **spectral** (no nontrivial
  invariant projection + peripheral spectrum `{1}`). Paper-faithful; **no Lean
  consumers**; the spectral↔algebraic equivalence (Sanz2010 Prop 3) is
  deliberately *not* formalized.
- Decision needed: keep both as paper-vs-working with an explicit (currently
  informal) equivalence remark, or formalize the bridge and alias one onto the
  other. **Do not silently conflate** — the equivalence is a real, unproved
  implication.

### 2. "basis of normal tensors" — Definition 4.2 stated twice
- `def:bnt_cpsv` / `IsCPSVBasisOfNormalTensors` (Ch9, spectral-normal blocks).
- `def:bnt` / `IsBNT` (Ch11, algebraic-normal blocks).
- Both bypassed in the actual FT proof by the richer
  `IsBNTCanonicalForm` (over a `SectorDecomposition`). `IsCPSVBasisOfNormalTensors`
  has **no Lean consumers**.

### 3. "canonical form" — 4 live predicates + 2 documentary (now 1, after cleanup)
- `def:canonical_form` / `CanonicalForm` — bare data carrier (keep).
- `def:is_normal_canonical_form` / `IsNormalCanonicalForm` — **core** strong
  predicate (~24 refs). Hub.
- `def:is_canonical_form` / `IsCanonicalForm` — **mis-filed in Ch10**
  (Block Permutation); injective + overlap→1 variant. Belongs with the CF
  predicates.
- `def:sector_bnt_cf` / `IsBNTCanonicalForm` — the **workhorse** BNT-CF over a
  `SectorDecomposition` (~119 refs / 19 files).
- `def:normal_cf_bnt` / `IsNormalCanonicalFormBNT` — strict-order one-copy
  surface; dead-ended (its `→ IsBNT` path is unused).
- `def:cf_cpsv` / `IsCPSVCanonicalForm` — **vestigial, REMOVED** (PR on
  `codex/cpsv-cf-single-source`).
- `def:pgvwc07_positive_length_witness` / `PGVWC07PositiveLengthWitness` —
  isolated to §9.13 (see readability item R1).

### 4. "sector / phase-class decomposition" — base type defined last, used first
- `def:sector_weight_data` / `SectorDecomposition` (+ `SectorWeightData`) — the
  **base type**, currently defined in **Ch13** but `\uses`'d in Ch9 and Ch11.
- `def:trivial_sector_decomp` (Ch9) and `def:mpv_phase_class_data` (Ch13) — the
  two real constructors (granular vs phase-collapse).
- `def:norm_class_grouping*` (Ch9) — no Lean, superseded; **REMOVED**.
- Two **parallel matching routes** that never cross-consume: overlap-span
  (`SectorBasisMatching`/`...PreMatching`/`...OverlapSpan`, Ch13) vs
  copy-weight (`SectorBNTCopyWeightMatching` / `ProportionalMatch`, Ch10). Both
  reach "matched sector decompositions" by different means.

## Worst ordering / readability edges (with labels)

- **O1** (worst): `def:sector_weight_data` defined in Ch13 but used in Ch9/Ch11.
- **O2**: Ch9 forward-depends on Ch12 (`thm:tp_gauge_arbitrary` `\uses`
  `def:zero_mps_tensor` and `thm:zero_block_separation`, both in Ch12).
- **O3**: Ch9 `thm:canonical_from_primitive` `\uses` `def:is_canonical_form`,
  defined in Ch10.
- **O4**: the reduction is split Ch9 §9.7–9.11 **and** Ch12, with duplicated
  period-removal / TP-gauge / normal-CF theorems; Ch11 (BNT, self-contained) is
  interposed between them.
- **R1**: §9.13 "Source-faithful PGVWC07 intermediate steps" (~370 lines) is a
  self-declared dead-end ("not used by the canonical-form reduction in the proof
  of the FT").
- **R2** (DONE): §9.12 distinct-modulus one-copy subcase scaffolding (no Lean) —
  removed.
- **R3**: the one-copy scope/gap disclaimer is repeated ~6×; the equal-MPV
  narrative is told ~3×; literature is restated in both Ch9 and Ch13.

## Staged plan (risk-ordered)

- **Stage 0 — pure deletions.** DONE on `codex/cpsv-cf-single-source`: removed
  the §9.12 no-Lean subcase scaffolding (`thm:bnt_sorted_*`, `thm:bnt_trivial_sector`,
  `def:norm_class_grouping*`) and the vestigial `IsCPSVCanonicalForm` /
  `CPSVCanonicalFormData` / `def:cf_cpsv`. (Audit-flagged `IsVerticalCF` and the
  two `IsBNT` producers turned out blueprint-tagged/consumed — correctly kept.)
- **Stage 1 — unify the BNT duplicate (#2).** Make `def:bnt` / `IsBNT` the single
  source; reduce `def:bnt_cpsv` / `IsCPSVBasisOfNormalTensors` to the paper
  statement of the same Definition 4.2 (it has no Lean consumers). Fix the
  mis-pointed conclusion of `thm:paperbnt_supplier_prepared` (claims `def:bnt_cpsv`
  but targets `IsBNTCanonicalForm`). Coordinated ch08+ch10 edits.
- **Stage 4 — quarantine §9.13 (R1).** Move `sec:pgvwc07_intermediates`
  (`def:pgvwc07_positive_length_witness` + the `thm:pgvwc07_*` ladder) into a
  late "Source-faithful PGVWC07 recordings" chapter; keep only the headline
  `thm:pgvwc07_ti_canonical_form` in the main text. Blueprint-only; all `\lean`
  tags stay valid. Lean: optionally move the `exists_pgvwc07_*` ladder to its own
  namespace/file.
- **Stage 3 — relocate the sector type (O1).** Move `def:sector_weight_data` and
  the matching/phase-cover apparatus (`def:sector_basis_matching`,
  `def:mpv_block_phase_equiv`, `def:mpv_common_phase_cover`) out of Ch13 into the
  BNT chapter (Ch11), so Ch13 only consumes named BNT theorems. Lean is
  import-only — low risk; mostly blueprint.
- **Stage 2 — unify normality (#1).** Decide paper-vs-working and, if unifying,
  formalize the spectral↔algebraic equivalence first. Higher effort.
- **Stage 5 — merge Ch9-reduction + Ch12 (O2,O4); re-home `def:is_canonical_form`
  out of Ch10 (O3); demote Ch10 to a pre-FT toolbox.** Heaviest; touches the most
  `\lean`-tagged chapters. Pick one of each duplicated reduction theorem (prefer
  the Ch12 forms the FT actually `\uses`).

## Target arc

`canonical-form predicates + reduction (Ch9-core + Ch12 merged)` →
`block-perm toolbox (Ch10 minus the mis-filed CF predicate)` →
`BNT + sector machinery (Ch11 + sector type/matching pulled from Ch13)` →
`FT proof (consumers only)` → `appendix: PGVWC07 recordings`,
with every cross-edge pointing strictly backward.

## Load-bearing — do NOT break (looks redundant but isn't)
- `IsNormal` (algebraic) ≠ `IsNormalTensor` (spectral): no formalized bridge.
- `SectorBasisMatching` (whole-sector) ≠ `SectorBNTCopyWeightMatching`
  (copy-within-matched-sector): different granularity, complementary.
- `IsCanonicalForm` (#3): only non-trivial external consumers (RFP), backs the
  live injective-block FT route.
- `HasBNTSectorData`: untagged but a field of `IsBNTCanonicalForm`.
- The CPSV definition layer (`IsNormalTensor`, `IsCPSVBasisOfNormalTensors`):
  `\leanok`-tagged paper-faithful nodes — keep as documentation; do not delete as
  "dead code".
