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

The current chapters are good-to-strong. The defects are surgical: 2 blockers,
4 majors, 40 minors, plus a modest Lean N=0 cleanup localized to the current branch.

Severity histogram (blueprint): 2 blocker, 4 major, 40 minor.

---

## Blockers (both in ch10_bnt)

### B1 — `def:bnt` tags the wrong Lean declaration  (ch10-01)
`def:bnt` (ch10:18–43) displays the abstract 3-clause Definition 4.2 BNT (each block
normal; the MPV lies in the span of the block MPVs; the block MPVs are eventually
linearly independent). That prose matches `MPSTensor.IsBNT` (`BNT/Basic.lean:75`).
But the entry tags `\lean{MPSTensor.IsBNTCanonicalForm}` — the 10-field much stronger
structure already (correctly) tagged by `def:sector_bnt_cf` (ch10:517). Statement
`\leanok` is therefore invalid, and the abstract BNT definition is left unlinked.

**Fix:** retarget `def:bnt` → `\lean{MPSTensor.IsBNT}`, keep the 3-clause prose. The
downstream `lem:cf_bnt_is_bnt_split` and `lem:normal_cf_bnt_is_bnt` already conclude
`IsBNT`, so their `\uses{def:bnt}` becomes correct. Leave `def:sector_bnt_cf` as the
sole entry for `IsBNTCanonicalForm`. Re-run `leanblueprint checkdecls`.

### B2 — per-sector vs global unit-modulus witness: faithfulness-rule violation  (ch10-02 / ch10-07; mirrored ch11 F3/F4)
Four equal-MPV / matching theorems carry **per-sector** unit-modulus hypotheses
`∀ j ∃ q ‖μ_{j,q}‖ = 1` (and `∀ k` for the Q side) — `StrongMatch.lean:132,270`,
`FundamentalCoord.lean:644`:
- `thm:sector_bnt_forall_unit_k_exists_j_nondecaying_overlap_of_sameMPV` (884)
- `thm:sector_bnt_bijective_match_of_sameMPV` (965)
- `thm:sector_bnt_equal_global_gauge` (1376)
- `thm:sector_bnt_equal_mps_gaugeEquiv_literal` (1442) — most exposed; calls itself
  "the normalized BNT form of Corollary II.2".

CPSV16 §II.C line 246 (and Cor II.2, line 1182) states only a **single global**
existential `∃ (j*,q*) |μ_{j*,q*}| = 1`. The per-sector form is strictly stronger and
absent from the source. Per the CLAUDE.md Faithfulness rule, these are scope-restricted
theorems; bearing `\leanok` against the source labels without a paper-gap note is the
"smuggled hypothesis" antipattern. The core structure `IsBNTCanonicalForm`
(`Basic.lean:152-161`, `weight_unit_exists`) faithfully carries the **global** witness;
ch08's BNT supplier also correctly carries only the global witness (confirmed clean).
No existing note covers this gap (`ft_one_copy_scope_restriction.tex` is the r_j=1
case; `cpsv16_two_layer_sector_refinement.tex` only remarks the factorization).

**Fix:** write `docs/paper-gaps/cpsv16_global_vs_persector_unit_witness.tex` (global
line-246 existential vs the per-sector Lean hypotheses; elimination plan: derive the
per-sector witness from the global one inside the line-1182 matching argument, or
split off all-strict-modulus sectors via the dominant-block argument). Add a complete
`\path{}` sentence to the four entries above + the two proportional
`..._global_gauge_of_...` theorems, modeled on ch07 `cor:uniform_injective_blocking`
and ch10 `def:normal_cf_bnt` (144–148). Keep `\leanok` (Lean statements match the
per-sector form); ensure none is presented as the unrestricted source theorem.

---

## Majors

### M1 — ch08: false "only fixed point" claim  (C08-01)
`thm:pgvwc07_ti_canonical_form` headline (ch08:63) writes "$\Id$ is the only fixed
point of $\E_{A_k}$". False: every $c\,\Id$ is fixed by a unital map. Lean
(`WeightNormalization.lean:389-391`) says the fixed-point space is spanned by $\Id$:
`∀ X, transferMap (blocks k) X = X → ∃ c, X = c • 1`.
**Fix:** "the only fixed points of $\E_{A_k}$ are scalar multiples of $\Id$"; display
$\E_{A_k}(X) = X \Rightarrow X = c\,\Id$.

### M2 — ch10: inconsistent bibliographic edition / line numbers  (ch10-03 / FT-08)
The sector-BNT section (ch10:505+) pins ~41 line-range citations to
`Cirac2017MPDO_AnnPhys` (Annals pagination), whose line numbers differ from
arXiv:1606.00608v4 — the edition the Lean docstrings use (`Basic.lean:152` "CPSV16
§II.C line 246"). A reviewer cannot verify line 246 / line 1182 against the cited
edition. **Fix:** pin every line-range citation to `Cirac2016MPDO_arXiv`, verify each
range (246, 264–279, 1080–1091, 1121–1132, 1167–1170, 1182, 1184–1192) resolves there,
collapse the three keys to the two papers actually used.

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
