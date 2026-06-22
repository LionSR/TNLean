# Canonical-form / BNT / FT blueprint + Lean audit (2026-05-30)

Cross-check of the canonical-form/BNT/fundamental-theorem blueprint cluster against
its Lean backing, the CPSV16 source (arXiv:1606.00608v4), Erickson's
`blueprint/comments202605/` analysis, and the `docs/` + `.github` prose/blueprint
standards. Produced by an 8-agent read-only audit fleet.

## Headline

**No chapter needs a full rewrite.** Erickson's May-13 documents in
`comments202605/` are **stale**: they describe the one-copy `IsCanonicalFormBNT`
predicate (with `mu_strict_anti` / `mu_dom_norm_one`) and the broken non-dominant
projection / Plan-A roadmap, all of which have since been **deleted** and replaced
by the multi-copy sector structure (`SectorDecomposition` + `IsBNTCanonicalForm`
carrying the global unit witness). Driving rewrites from those docs would re-introduce
retired architecture.

This file is now annotated with resolution status rather than left as a list of
live blockers. The single current item-by-item ledger is
`blueprint/comments202605/STATUS_erickson_items_20260530.md`. On current
`main`, B1 is resolved, B2 is recorded as a documented scope restriction, and
M1--M2 are resolved. Other findings below remain audit candidates unless they
are separately marked as resolved.

Original severity histogram (blueprint): 2 blocker, 4 major, 40 minor.

---

## Resolved or documented blockers (ch10_bnt)

### B1: resolved, `def:bnt` now tags the abstract BNT declaration  (ch10-01)
The audit found that `def:bnt` displayed the abstract three-clause Definition 4.2
BNT but tagged the stronger multi-copy canonical-form predicate. Current
`ch10_bnt.tex` tags this entry as `\lean{MPSTensor.IsBNT}`, matching the prose:
each block is normal, the total MPV lies in the span of the block MPVs, and the
block MPVs are eventually linearly independent.

**Resolution:** `def:bnt` is the single blueprint entry for `MPSTensor.IsBNT`.
`def:sector_bnt_cf` remains the single blueprint entry for
`MPSTensor.IsBNTCanonicalForm`.

### B2: documented, per-sector vs global unit-modulus witness  (ch10-02 / ch10-07; mirrored ch11 F3/F4)
Four equal-MPV / matching theorems carry **per-sector** unit-modulus hypotheses
`∀ j ∃ q ‖μ_{j,q}‖ = 1` (and `∀ k` for the Q side) — `StrongMatch.lean:132,270`,
`FundamentalCoord.lean:644`:
- `thm:sector_bnt_forall_unit_k_exists_j_nondecaying_overlap_of_sameMPV` (884)
- `thm:sector_bnt_bijective_match_of_sameMPV` (965)
- `thm:sector_bnt_equal_global_gauge` (1376)
- `thm:sector_bnt_equal_mps_gaugeEquiv_literal` (1442), the most exposed; calls itself
  "the normalized BNT form of Corollary II.2".

CPSV16 §II.C line 246 (and Cor II.2, line 1182) states only a **single global**
existential `∃ (j*,q*) |μ_{j*,q*}| = 1`. The per-sector form is strictly stronger and
absent from the source. Per the CLAUDE.md Faithfulness rule, these are
scope-restricted theorems, not unrestricted formalizations of the source
theorem. The core structure `IsBNTCanonicalForm`
(`Basic.lean:152-161`, `weight_unit_exists`) faithfully carries the **global** witness;
ch08's BNT supplier also correctly carries only the global witness (confirmed clean).

**Resolution:** the gap and elimination plan are recorded in
`docs/paper-gaps/cpsv16_global_vs_persector_unit_witness.tex`. Chapter 10
states the per-sector hypotheses in the theorem prose and keeps the paper-gap
path in LaTeX comments, as required by `docs/prose_style.md`. The `\leanok`
tags are retained because the blueprint statements state the per-sector
hypotheses that the Lean declarations actually assume.

---

## Majors

### M1: resolved, ch08 fixed-point statement  (C08-01)
The audit found that `thm:pgvwc07_ti_canonical_form` stated "$\Id$ is the only
fixed point of $\E_{A_k}$". Current `ch08_canonical.tex` states the correct
fixed-point space: every fixed point is a scalar multiple of $\Id$, matching
`WeightNormalization.lean`.

### M2: resolved, ch10 bibliographic edition / line numbers  (ch10-03 / FT-08)
The audit found line-range citations in the sector-BNT section pointing to the
Annals edition while using arXiv line numbers. Current `ch10_bnt.tex` uses
`Cirac2016MPDO_arXiv` for the CPSV16 line-range references, matching the Lean
docstrings and the local source file.

### M3 — ch11b: hidden hypothesis on a conditional theorem  (F-A-01)
`thm:after_blocking_common_primitive_irreducible_blocks_reindexed` (ch11b:751–799)
reduces a real Lean hypothesis (`CommonSectorRelabelingHypothesis`, a `SameMPV₂`
between the directly-blocked weighted family and the reindexed common-sector family)
to the vague phrase "can be identified with the common blocked alphabet". The
hypothesis is dischargeable — `unconditional_commonPrimitiveIrreducibleBlocks`
(`CommonSectorTransport.lean:536`) exists and is its own ch11 entry.
**Fix:** display the assumed `SameMPV₂` equality, cross-reference the unconditional
version; or retarget the entry's `\lean` to the unconditional theorem.

### M4 — ch11b: untagged graph-orphan theorem  (F-A-02)
`thm:zero_tail_common_flat_of_blocked_word_comparison` (ch11b:651–704) is a
`\begin{theorem}` with full statement + proof but **no** `\lean`/`\leanok`/`\notready`
— a dependency-graph orphan bundling "three equivalent hypothesis forms" (file-local
lemmas) with a verbal proof and an em-dash narrative. Cited by `\uses` at 884, 919.
**Fix:** attach `\lean{MPSTensor.zeroTail_commonFlat_of_blockwise}`
(`CommonSectorTransport.lean:79`) + `\leanok` displaying the blockwise hypothesis; or
demote to `\begin{remark}` and reroute the two `\uses` edges to the file-local lemmas.
Remove the em-dash list; display the contraction identity in the proof.

---

## Minor themes (40 findings; representative)

- **Formula-first proof sketches** (B-category): ch11 `thm:unit_modulus_phase_tp_prim_irred`
  (F1) hand-waves "peripheral spectrum = {1}"; the Lean uses the self-overlap scaling
  identity $O_{BB}(N) = |\zeta|^{2N} O_{AA}(N)$ with $O_{AA},O_{BB}\to 1 \Rightarrow |\zeta|=1$.
  ch08 BNT supplier (C08-07) should display $\|\zeta_{j,q}\|=1$ and the sector-weight
  identity. ch11b proofs F-A-03/04/05 should display the fixed-point uniqueness chain,
  the $\phi_u$ algebra-iso properties, and the length-zero identity $D = D_0 + \sum_k D_k$.
- **Prose / Lean-jargon leaks**: "SectorBNT" namespace in ch11 prose (F2 → "BNT"),
  "the matched basis" ch10:400 (ch10-04 → "paired basis tensors"), "assembly" as a
  prose noun ch10:788,1257 (ch10-05 → "construction"), "granular sector decomposition"
  ch08 (C08-03 → "single-copy sector decomposition").
- **Indexing drift**: ch08 CPSV definitions use 1-based $k=1,\ldots,r$ (C08-02); should
  be 0-based / `Fin r`. Lambda/Lambda clash in the ch08 headline (C08-06).
- **Status hygiene**: 7 untagged blueprint-only ch08 entries (C08-04) need
  `\notready`-or-delete (several duplicate the ch10 SectorBNT grouping); undefined
  symbol `P` in `thm:bnt_trivial_sector`. ch08 `thm:cyclic_sector_decomp_after_blocking`
  tag-without-`\leanok` limbo (C08-05). ch11 `lem:ft_equal_same_structure` ambiguous
  status (F4).
- **Scope `\path{}` markers** missing on scope-restricted entries: ch09 block-separation
  (ch09-01), ch11 equal-structure (F3) — both have governing paper-gap notes but cite
  them only in LaTeX comments, not reader-facing `\path{}`.
- **NeZero / positive-bond-dimension** hypotheses to surface: ch09-02, ch10-06, ch11 F7.
- **Section preambles** missing in ch09 (ch09-03). **One-copy mis-advertisement** of
  ch11's own multi-copy lemmas (F5). **Overlap-clause inconsistency** ch08 (C08-09).
- **Positive confirmations** (no action): ch09 all `\leanok`/`\uses` accurate;
  ch11 both source theorems correctly `\notready` (no smuggled source `\leanok`); FT-04
  injectivity-from-`basis_distinct` clean; ch08 BNT supplier carries only the global
  witness.

---

## Lean N=0 / degenerate-case cleanup (current branch)

FT-05: most genuinely-wasted N=0 effort (the Plan-A projection workaround, the one-copy
predicate) is **already deleted**. The retired `Full/` directory is empty. The
zero-tail / length-zero ($D = D_0 + \sum_k D_k$) handling in ch11b is **source-faithful
CPSV16 content** (all-zero irreducible blocks contribute only at N=0), **not** bloat.

Remaining, localized to the current branch's modified files:
- **F1** `SectorComparison/CommonSectorTransport.lean`
  (`afterBlocking_commonPrimitiveIrreducibleBlocks`, ~456,490–537): the N=0 zero-tail
  identity is threaded as an **unused** `_hZeroCanon`; only `SameMPV2Pos` is used; the
  A/B blocks re-derive zero-vanishing twice (~9 lines each). Cleanup: drop the `Fin 0`
  threading, recover N=0 via `toSameMPV2_of_bondDim_eq`, factor the duplicated A/B
  blocks into one lemma (~90 lines saved).
- **F2** `SectorComparison/CommonSectorData.lean` (85–87, 152–154; unused `_hZero` 261):
  the `Fin 0` zero-tail conjunct is dropped unused by the consumer; pure N=0 bookkeeping
  is just a dimension equation. Cleanup: drop the `Fin 0` conjunct, expose the nat dim
  equation if needed.

NOTE: this Lean N=0 pass was the thinnest agent result; a deeper pass over the active
`SectorComparison/` files is warranted before committing the cleanup, since the branch
is actively reworking exactly these files.

---

## Genuinely-open mathematics (not blueprint fixes; tracked separately)

1. **Per-sector → global unit witness** (B2): eliminate the per-sector hypothesis by
   deriving it from the global one (or the all-strict-modulus dominant-block split).
2. **Proportional matched-coefficient identity** (FT-02): the proportional
   ($c_N \ne 1$) FT still takes $c_N^{(\beta(k))}(P) = \zeta_k^N c_N^{(k)}(Q)$ as a
   hypothesis rather than deriving it; this is the load-bearing remaining input,
   tracked by issue #1749. The two CPSV16 source theorems (Cor II.1, Cor II.2) are
   correctly `\notready`.

These are real formalization work; the blueprint already flags them honestly via
`\notready` / scope prose. The audit's blueprint fixes make the *documentation* of
these gaps rubric-compliant; they do not close the gaps.
