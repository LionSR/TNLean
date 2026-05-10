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
full symmetric hypothesis set: dominant-block normalization on each side,
uniform sub-dominant coefficient bounds, per-side asymptotic block-orthonormality
(diagonal overlaps tend to `1`, off-diagonal overlaps tend to `0`), per-length
nonzero proportionality, and the BNT decomposition identities. This matches
CPSV16's hypothesis "$A$ and $B$ in canonical form" (arXiv:1606.00608, statement
of Theorem thm1) — the paper's CF concept implicitly carries the
dominant-block normalization and the per-block primitivity that gives
asymptotic orthonormality. Thus the displayed hypotheses are the explicit
A-side and B-side components of the source's canonical-form assumption; no
hypothesis is added beyond what the paper provides.
-/

open scoped BigOperators Matrix
open Filter Finset

namespace MPSTensor

/-! ## Key paper step: some mixed overlap does not decay

The argument follows arXiv:1606.00608 lines 1170-1192. The proof uses inner-product
manipulation of the BNT decompositions, asymptotic block-orthonormality, and the
dominant-block normalization. Lemma Lem1 supplies eventual linear independence
from asymptotic orthonormality; the contradiction step applies this after showing
that the relevant joint family is asymptotically orthonormal. -/

/-- Translate a fixed-length pointwise MPV decomposition into an equality of
state vectors.

Source: arXiv:1606.00608, lines 1170--1192. This is the Hilbert-space form of
the displayed BNT expansion used when the proof takes inner products with a
single block vector. -/
lemma mpvState_eq_sum_of_decomp
    {d g Dtot : ℕ} {dim : Fin g → ℕ}
    (A : (j : Fin g) → MPSTensor d (dim j))
    (A_total : MPSTensor d Dtot)
    (coeff : Fin g → ℂ)
    {N : ℕ}
    (hdecomp : ∀ σ : Fin N → Fin d,
      mpv A_total σ = ∑ j : Fin g, coeff j * mpv (A j) σ) :
    mpvState (d := d) A_total N =
      ∑ j : Fin g, coeff j • mpvState (d := d) (A j) N := by
  apply PiLp.ext
  intro σ
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mpvState_apply]
  exact hdecomp σ

/-- Expand the inner product against the right side of a fixed-length BNT
decomposition.

Source: arXiv:1606.00608, lines 1170--1192. This is the algebraic step used
when projecting the full proportionality relation onto one block MPV. -/
lemma mpvInner_eq_sum_of_decomp_right
    {d g D Dtot : ℕ} {dim : Fin g → ℕ}
    (X : MPSTensor d D)
    (A : (j : Fin g) → MPSTensor d (dim j))
    (A_total : MPSTensor d Dtot)
    (coeff : Fin g → ℂ)
    {N : ℕ}
    (hdecomp : ∀ σ : Fin N → Fin d,
      mpv A_total σ = ∑ j : Fin g, coeff j * mpv (A j) σ) :
    mpvInner (d := d) X A_total N =
      ∑ j : Fin g, coeff j * mpvInner (d := d) X (A j) N := by
  have hstate :=
    mpvState_eq_sum_of_decomp (d := d) A A_total coeff (N := N) hdecomp
  have h := congr_arg (fun v => @inner ℂ _ _ (mpvState (d := d) X N) v) hstate
  simpa [mpvInner] using h

/-- Expand the inner product against the left side of a fixed-length BNT
decomposition.

Source: arXiv:1606.00608, lines 1170--1192. This is the conjugate-linear
companion of `mpvInner_eq_sum_of_decomp_right`, used for the symmetric
projection in the block-matching argument. -/
lemma mpvInner_eq_sum_of_decomp_left
    {d g D Dtot : ℕ} {dim : Fin g → ℕ}
    (A : (j : Fin g) → MPSTensor d (dim j))
    (A_total : MPSTensor d Dtot)
    (X : MPSTensor d D)
    (coeff : Fin g → ℂ)
    {N : ℕ}
    (hdecomp : ∀ σ : Fin N → Fin d,
      mpv A_total σ = ∑ j : Fin g, coeff j * mpv (A j) σ) :
    mpvInner (d := d) A_total X N =
      ∑ j : Fin g, mpvInner (d := d) (A j) X N * star (coeff j) := by
  have hstate :=
    mpvState_eq_sum_of_decomp (d := d) A A_total coeff (N := N) hdecomp
  have h := congr_arg (fun v => @inner ℂ _ _ v (mpvState (d := d) X N)) hstate
  simpa [mpvInner] using h

/-- If the right tensor in an overlap has a fixed-length BNT decomposition,
then the overlap expands with conjugated coefficients.

Source: arXiv:1606.00608, lines 1170--1192. This is the right-hand companion
to `mpvOverlap_eq_sum_of_decomp_left` used when projecting onto a block from
the decomposed family. -/
lemma mpvOverlap_eq_sum_of_decomp_right
    {d g D Dtot : ℕ} {dim : Fin g → ℕ}
    (X : MPSTensor d D)
    (A : (j : Fin g) → MPSTensor d (dim j))
    (A_total : MPSTensor d Dtot)
    (coeff : Fin g → ℂ)
    {N : ℕ}
    (hdecomp : ∀ σ : Fin N → Fin d,
      mpv A_total σ = ∑ j : Fin g, coeff j * mpv (A j) σ) :
    mpvOverlap (d := d) X A_total N =
      ∑ j : Fin g, mpvOverlap (d := d) X (A j) N * star (coeff j) := by
  calc
    mpvOverlap (d := d) X A_total N = star (mpvInner (d := d) X A_total N) := by
      exact mpvOverlap_eq_star_mpvInner X A_total N
    _ = star (∑ j : Fin g, coeff j * mpvInner (d := d) X (A j) N) := by
      rw [mpvInner_eq_sum_of_decomp_right (d := d) X A A_total coeff hdecomp]
    _ = ∑ j : Fin g, mpvOverlap (d := d) X (A j) N * star (coeff j) := by
      simp [mpvOverlap_eq_star_mpvInner, star_mul, mul_comm]

/-- A finite sum of uniformly bounded coefficients times terms converging to
zero also converges to zero.

Source: arXiv:1606.00608, lines 1170--1192. This is the finite-sum estimate
used after expanding the overlap of a total MPV with a block MPV. -/
lemma tendsto_finset_sum_mul_zero_of_norm_le_one
    {ι : Type*} [Fintype ι]
    (coeff : ℕ → ι → ℂ)
    (f : ι → ℕ → ℂ)
    (hcoeff : ∀ N i, ‖coeff N i‖ ≤ 1)
    (hf : ∀ i, Tendsto (f i) atTop (nhds 0)) :
    Tendsto (fun N => ∑ i : ι, coeff N i * f i N) atTop (nhds 0) := by
  have hterm : ∀ i : ι,
      Tendsto (fun N => coeff N i * f i N) atTop (nhds 0) := by
    intro i
    have hnorm : Tendsto (fun N => ‖f i N‖) atTop (nhds (0 : ℝ)) := by
      simpa only [norm_zero] using (hf i).norm
    apply squeeze_zero_norm (fun N => ?_) hnorm
    calc
      ‖coeff N i * f i N‖ = ‖coeff N i‖ * ‖f i N‖ := norm_mul _ _
      _ ≤ 1 * ‖f i N‖ :=
        mul_le_mul_of_nonneg_right (hcoeff N i) (norm_nonneg _)
      _ = ‖f i N‖ := one_mul _
  simpa using
    tendsto_finset_sum (Finset.univ : Finset ι)
      (fun i _ => hterm i)

/--
**Key step of Theorem 4.4 (paper route).**

Source: arXiv:1606.00608, lines 1170–1192 (proof of Theorem thm1).

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
for the dominant block `k = 0` (where `hB_top_norm_one` keeps
`‖bCoeff N 0‖ = 1` away from zero). For sub-dominant `k ≥ 1`, the source
matches blocks iteratively: after the dominant block is matched, peel it off
and re-apply the argument to the residual. The "∀ k, ∃ j" form of the
conclusion as stated bundles this iteration; the actual proof will need to
implement the residual-and-recurse step, since a literal one-shot lower
bound on `‖bCoeff N k‖` is not available for sub-dominant blocks under the
source normalization.

Elimination: rewrite using the source-faithful lower-bound + iterative
peeling with `hB_top_norm_one`, `hB_norm_le_one`, and `hc_ne` from the now
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
    (hA_top_norm_one : ∀ N (h : 0 < gA), ‖aCoeff N ⟨0, h⟩‖ = 1)
    (hB_top_norm_one : ∀ N (h : 0 < gB), ‖bCoeff N ⟨0, h⟩‖ = 1)
    (hA_norm_le_one : ∀ N j, ‖aCoeff N j‖ ≤ 1)
    (hB_norm_le_one : ∀ N k, ‖bCoeff N k‖ ≤ 1)
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
  -- Cor Lem1 (asymptotically orthonormal NMPVs are eventually LI):
  -- assuming all `mpvOverlap (A j) (B k) → 0`, the joint family
  -- `{V^N(A_j)}_j ∪ {V^N(B_k)}` is asymptotically orthonormal hence eventually
  -- LI; proportionality `V^N(A_total) = c_N V^N(B_total)` then forces
  -- linearly-dependent coefficient relations contradicting LI.
  -- The argument requires BOTH dominant-block normalizations (`hA_top_norm_one`
  -- and `hB_top_norm_one`) to derive the contradiction; iterative peeling
  -- handles sub-dominant blocks.
  -- See `docs/paper-gaps/cpsv16_cf_normalization_and_proportional_comparison.tex`.
  sorry


/-! ## Symmetric key step (A-indexed)

For the block-count equality we also need the converse direction: for each `A j`, some overlap
with a `B k` does not decay.
-/

/--
**Key step of Theorem 4.4 (paper route), opposite direction.**

Source: arXiv:1606.00608, lines 1170–1192 (proof of Theorem thm1,
symmetric to `exists_nonzero_overlap_of_proportional_decomp`).

Under the same proportionality + decomposition hypotheses as
`exists_nonzero_overlap_of_proportional_decomp`, if the `A`-family overlaps
are asymptotically orthonormal, then for each `j` it is impossible that
`mpvOverlap (A j) (B k) → 0` for all `k`.

**Unfaithful:** Same situation as the companion theorem — proof body is
`sorry`, the deleted limit hypotheses are documented in
`docs/paper-gaps/cpsv16_cf_normalization_and_proportional_comparison.tex`,
elimination tracked in #1559 Stage C.

The two nonzero-overlap conclusions are related by interchanging the two
decompositions and replacing the proportionality scalar `c N` by `(c N)⁻¹`.
This direction remains a separate Stage C statement until that interchange is
formalized as a single symmetric argument; the planned elimination is to prove
the joint right- and left-indexed conclusion at once, or derive one side from
the other after this scalar inversion step is available. -/
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
    (hA_top_norm_one : ∀ N (h : 0 < gA), ‖aCoeff N ⟨0, h⟩‖ = 1)
    (hB_top_norm_one : ∀ N (h : 0 < gB), ‖bCoeff N ⟨0, h⟩‖ = 1)
    (hA_norm_le_one : ∀ N j, ‖aCoeff N j‖ ≤ 1)
    (hB_norm_le_one : ∀ N k, ‖bCoeff N k‖ ≤ 1)
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
  -- Paper-faithful proof pending. Mathematically this is the A/B-swapped
  -- direction, with the proportionality scalar inverted at each length.
  sorry

end MPSTensor
