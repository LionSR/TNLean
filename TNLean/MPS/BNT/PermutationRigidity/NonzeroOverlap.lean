import TNLean.MPS.FundamentalTheorem.Proportional
import TNLean.Spectral.SpectralGapRect
import TNLean.Spectral.SpectralGapNT
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.Overlap.CastDecay

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# Permutation rigidity for basis-of-normal-tensors (BNT) decompositions — Theorem 4.4
(paper hypotheses, no span-equality)

This module replaces the extra span-equality hypothesis used in
`PermutationRigidityPrimitive.lean` with the **paper-style** hypotheses from Theorem 4.4
(arXiv:2011.12127 / 1606.00608, primitive branch): proportionality of the full MPV
families together with explicit decompositions into BNT families.

It contains both directions of the key nonvanishing-overlap step and the resulting
full permutation / gauge-phase matching theorems, in both the injective and
irreducible trace-preserving settings.

The overlap arguments follow the Appendix-A strategy: take overlaps of the
proportional full states with individual block states and use the asymptotic
orthogonality inside each BNT family.

In canonical-form applications one first normalizes by the dominant weights, so the relevant
coefficient arrays are `(μ j / μ 0)^N`; the discarded dominant factors are absorbed into the
proportionality constant.

## Paper-faithfulness note

Both `exists_nonzero_overlap_of_proportional_decomp` and the `_left` companion take the
**full symmetric hypothesis set** — A-side and B-side dominant-block normalization
(`a_top_norm_one`, `b_top_norm_one`), uniform sub-dominant bounds (`a_norm_le_one`,
`b_norm_le_one`), per-side asymptotic block-orthonormality (`hA_self`, `hA_off`,
`hB_self`, `hB_off`), per-`N` nonzero proportionality (`hc_ne`), and the BNT
decomposition identities. This matches CPSV16's hypothesis "$A$ and $B$ in canonical
form" (arXiv:1606.00608, statement of Theorem `thm1`) — the paper's CF concept
implicitly carries the dominant-block normalization and the per-block primitivity that
gives asymptotic orthonormality. The Lean theorems unbundle these into explicit
per-side hypotheses; no hypothesis is added beyond what the paper provides.
-/

open scoped BigOperators Matrix
open Filter Finset

namespace MPSTensor

/-! ## Helper lemmas for the CPSV16 lines 1170–1192 lower-bound argument -/

/-- Dominant-block lower bound on the total-vs-block overlap.

Source: arXiv:1606.00608, lines 1170–1192. Used in the proof of Theorem `thm1`
to anchor the dominant block's overlap with the total tensor away from zero,
which propagates through proportionality to constrain the proportionality
scalar `c N`.

Eventually `‖mpvOverlap total (block_dom) N‖ ≥ 1/2` whenever the dominant
coefficient stays at unit norm, the off-diagonal coefficients are uniformly
bounded by `1`, and the within-family overlaps are asymptotically orthonormal.

**Sorry:** to be discharged via `mpvOverlap_eq_sum_of_decomp_left` plus
triangle inequality from `hSelf k` and `hOff k k'`. Tracked in #1559 Stage C. -/
private lemma mpvOverlap_total_block_eventually_ge_half
    {d g : ℕ} {dim : Fin g → ℕ} {Dtot : ℕ}
    (X : (k : Fin g) → MPSTensor d (dim k))
    (X_total : MPSTensor d Dtot)
    (xCoeff : ℕ → Fin g → ℂ)
    (hX_decomp : ∀ N (σ : Fin N → Fin d),
      mpv X_total σ = ∑ k : Fin g, (xCoeff N k) * mpv (X k) σ)
    (k : Fin g)
    (xCoeff_at_k_norm_one : ∀ N, ‖xCoeff N k‖ = 1)
    (_xCoeff_norm_le_one : ∀ N k', ‖xCoeff N k'‖ ≤ 1)
    (_hSelf : Tendsto (fun N => mpvOverlap (d := d) (X k) (X k) N) atTop (nhds (1 : ℂ)))
    (_hOff : ∀ k', k ≠ k' →
      Tendsto (fun N => mpvOverlap (d := d) (X k') (X k) N) atTop (nhds 0)) :
    ∃ N₀, ∀ N ≥ N₀,
      (1 : ℝ) / 2 ≤ ‖mpvOverlap (d := d) X_total (X k) N‖ := by
  sorry

/-- Self-overlap lower bound for a total tensor with a unit-norm dominant block.

Source: arXiv:1606.00608, lines 1170–1192. The self-overlap is dominated by
the (0, 0) diagonal term `|x_0(N)|² · ⟨V^N(X_0), V^N(X_0)⟩`, which tends to
the real value `1` when the dominant coefficient is on the unit circle and
the dominant self-overlap tends to `1`.

**Sorry:** to be discharged via `mpvOverlap_eq_sum_of_decomp_left` applied
twice (once for each factor of the self-overlap). Tracked in #1559 Stage C. -/
private lemma mpvOverlap_total_self_eventually_ge_half
    {d g : ℕ} {dim : Fin g → ℕ} {Dtot : ℕ}
    (X : (k : Fin g) → MPSTensor d (dim k))
    (X_total : MPSTensor d Dtot)
    (xCoeff : ℕ → Fin g → ℂ)
    (_hX_decomp : ∀ N (σ : Fin N → Fin d),
      mpv X_total σ = ∑ k : Fin g, (xCoeff N k) * mpv (X k) σ)
    (hr : 0 < g)
    (_xCoeff_top_norm_one : ∀ N, ‖xCoeff N ⟨0, hr⟩‖ = 1)
    (_xCoeff_norm_le_one : ∀ N k, ‖xCoeff N k‖ ≤ 1)
    (_hSelf : ∀ k, Tendsto (fun N => mpvOverlap (d := d) (X k) (X k) N) atTop (nhds (1 : ℂ)))
    (_hOff : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (X i) (X j) N) atTop (nhds 0)) :
    ∃ N₀, ∀ N ≥ N₀,
      (1 : ℝ) / 2 ≤ ‖mpvOverlap (d := d) X_total X_total N‖ := by
  sorry

/-- Upper bound for the norm of a total-tensor MPV state via its
decomposition with bounded coefficients.

`‖V^N(X_total)‖ ≤ √g · max_k ‖V^N(X k)‖` when `‖xCoeff N k‖ ≤ 1`.
A weaker bound `≤ g` suffices for the contradiction step here.

**Sorry:** triangle inequality on `mpvOverlap_eq_sum_of_decomp_left`. -/
private lemma mpvOverlap_total_self_le_card
    {d g : ℕ} {dim : Fin g → ℕ} {Dtot : ℕ}
    (X : (k : Fin g) → MPSTensor d (dim k))
    (X_total : MPSTensor d Dtot)
    (xCoeff : ℕ → Fin g → ℂ)
    (_hX_decomp : ∀ N (σ : Fin N → Fin d),
      mpv X_total σ = ∑ k : Fin g, (xCoeff N k) * mpv (X k) σ)
    (_xCoeff_norm_le_one : ∀ N k, ‖xCoeff N k‖ ≤ 1)
    (_hSelf : ∀ k, Tendsto (fun N => mpvOverlap (d := d) (X k) (X k) N) atTop (nhds (1 : ℂ))) :
    ∃ M : ℝ, ∀ N, ‖mpvOverlap (d := d) X_total X_total N‖ ≤ M := by
  sorry

/-! ## Key paper step: some mixed overlap does not decay -/

/--
**Key step of Theorem 4.4 (paper route).**

Source: arXiv:1606.00608, lines 1170–1192 (proof of Theorem `thm1`).

Assume we have two families `A j` and `B k` whose within-family overlaps are
asymptotically orthonormal, and that the *full* tensors `A_total` and `B_total`
are proportional MPV families with explicit decompositions into the families.

Then for each `k`, it is impossible that `mpvOverlap (A j) (B k)` tends to `0`
for all `j`.

**Unfaithful:** The proof body is currently `sorry`. The earlier proof relied
on the convergence-to-nonzero-limit hypotheses (`aLim`, `bLim`, `cLim`,
`haCoeff`, `hbCoeff`, `hc`, `haLim_ne`, `hbLim_ne`, `hcLim_ne`) — these were
removed because they are uninstantiable on the source's intended canonical-form
class once `‖μ_1‖ = 1` is in force. Documented in
`docs/paper-gaps/cpsv16_cf_normalization_and_proportional_comparison.tex`.

The CPSV16 proof (lines 1170-1192) gives the lower-bound argument cleanly only
for the dominant block `k = 0` (where `b_top_norm_one` keeps
`‖bCoeff N 0‖ = 1` away from zero). For sub-dominant `k ≥ 1`, the source
matches blocks iteratively: after the dominant block is matched, peel it off
and re-apply the argument to the residual. The "∀ k, ∃ j" form of the
conclusion as stated bundles this iteration; the actual proof will need to
implement the residual-and-recurse step, since a literal one-shot lower
bound on `‖bCoeff N k‖` is not available for sub-dominant blocks under the
source normalization.

Elimination: rewrite using the source-faithful lower-bound + iterative
peeling with `b_top_norm_one`, `b_norm_le_one`, and `hc_ne` from the now
threaded-through `ProportionalDecompositionData` data; tracked in #1559
Stage C. -/
theorem exists_nonzero_overlap_of_proportional_decomp
    {d : ℕ}
    {gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    {DtotA DtotB : ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin gA → ℂ) (bCoeff : ℕ → Fin gB → ℂ)
    (c : ℕ → ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin gA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin gB, (bCoeff N k) * mpv (B k) σ)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ)
    (hc_ne : ∀ N, c N ≠ 0)
    (a_top_norm_one : ∀ N (h : 0 < gA), ‖aCoeff N ⟨0, h⟩‖ = 1)
    (b_top_norm_one : ∀ N (h : 0 < gB), ‖bCoeff N ⟨0, h⟩‖ = 1)
    (a_norm_le_one : ∀ N j, ‖aCoeff N j‖ ≤ 1)
    (b_norm_le_one : ∀ N k, ‖bCoeff N k‖ ≤ 1)
    (hA_self : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hA_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds 0))
    (hB_self : ∀ k,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds (1 : ℂ)))
    (hB_off : ∀ k₁ k₂, k₁ ≠ k₂ →
      Tendsto (fun N => mpvOverlap (d := d) (B k₁) (B k₂) N) atTop (nhds 0)) :
    ∀ k : Fin gB,
      ∃ j : Fin gA,
        ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0) := by
  -- Paper-faithful proof pending. The CPSV16 lines 1170-1192 argument follows
  -- Cor `Lem1` (asymptotically orthonormal NMPVs are eventually LI):
  -- assuming all `mpvOverlap (A j) (B k) → 0`, the joint family
  -- `{V^N(A_j)}_j ∪ {V^N(B_k)}` is asymptotically orthonormal hence eventually
  -- LI; proportionality `V^N(A_total) = c_N V^N(B_total)` then forces
  -- linearly-dependent coefficient relations contradicting LI.
  -- The argument requires BOTH dominant-block normalizations (`a_top_norm_one`
  -- and `b_top_norm_one`) to derive the contradiction; iterative peeling
  -- handles sub-dominant blocks.
  -- See `docs/paper-gaps/cpsv16_cf_normalization_and_proportional_comparison.tex`.
  sorry


/-! ## Symmetric key step (A-indexed)

For the block-count equality we also need the converse direction: for each `A j`, some overlap
with a `B k` does not decay.
-/

/--
**Key step of Theorem 4.4 (paper route), opposite direction.**

Source: arXiv:1606.00608, lines 1170–1192 (proof of Theorem `thm1`,
symmetric to `exists_nonzero_overlap_of_proportional_decomp`).

Under the same proportionality + decomposition hypotheses as
`exists_nonzero_overlap_of_proportional_decomp`, if the `A`-family overlaps
are asymptotically orthonormal, then for each `j` it is impossible that
`mpvOverlap (A j) (B k) → 0` for all `k`.

**Unfaithful:** Same situation as the companion theorem — proof body is
`sorry`, the deleted limit hypotheses are documented in
`docs/paper-gaps/cpsv16_cf_normalization_and_proportional_comparison.tex`,
elimination tracked in #1559 Stage C. -/
theorem exists_nonzero_overlap_of_proportional_decomp_left
    {d : ℕ}
    {gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    {DtotA DtotB : ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin gA → ℂ) (bCoeff : ℕ → Fin gB → ℂ)
    (c : ℕ → ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin gA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin gB, (bCoeff N k) * mpv (B k) σ)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ)
    (hc_ne : ∀ N, c N ≠ 0)
    (a_top_norm_one : ∀ N (h : 0 < gA), ‖aCoeff N ⟨0, h⟩‖ = 1)
    (b_top_norm_one : ∀ N (h : 0 < gB), ‖bCoeff N ⟨0, h⟩‖ = 1)
    (a_norm_le_one : ∀ N j, ‖aCoeff N j‖ ≤ 1)
    (b_norm_le_one : ∀ N k, ‖bCoeff N k‖ ≤ 1)
    (hA_self : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hA_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds 0))
    (hB_self : ∀ k,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds (1 : ℂ)))
    (hB_off : ∀ k₁ k₂, k₁ ≠ k₂ →
      Tendsto (fun N => mpvOverlap (d := d) (B k₁) (B k₂) N) atTop (nhds 0)) :
    ∀ j : Fin gA,
      ∃ k : Fin gB,
        ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0) := by
  -- Paper-faithful proof pending; symmetric to the right-indexed version.
  sorry

end MPSTensor
