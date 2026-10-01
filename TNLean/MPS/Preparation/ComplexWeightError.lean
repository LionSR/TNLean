/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OverlappingBlockError
import TNLean.MPS.SharedInfra.Scaling

/-!
# The approximation error for complex weights

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S7)) write
a tensor that is not normal as `Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` with complex weights
`|μ_{j,k}| ≤ 1`, at least one of modulus one, and approximate its state on `N = qM` sites by
`V^{⊗M} ∑ⱼ βⱼ |Ω_j⟩` with `βⱼ = ∑ₖ μ_{j,k}^N` (eq. (S4)), where `B = V P` is the polar
decomposition of the `q`-site blocked tensor. The positive part `P` is positive semidefinite, so
the phases of the weights cannot sit in it, as the block form `⊕ⱼ diag(μ_{j,k}^q) ⊗ P_j` of
eq. (S5) asserts; they sit in `V`, and `V^{⊗M}` already supplies the phase `(μⱼ/|μⱼ|)^N` to the
`j`-th block. With `βⱼ = μⱼ^N` this phase is counted twice, and the error does not tend to zero
(`MPSTensor.nonNormalApproxOverlap_phaseBlockTensor`).

This file proves the corrected statement for blocks of multiplicity one: with `βⱼ = |μⱼ|^N`
the error obeys the bound of `exists_approximationError_le_overlappingBlockSum_weight`
for every complex weight with `|μⱼ| ≤ 1` and `max_j |μⱼ| = 1`
(`exists_approximationError_le_overlappingBlockSum_complexWeight`, and in `O`-form
`exists_approximationError_le_mul_overlappingBlockSum_complexWeight`). The proof absorbs the
phase `uⱼ = μⱼ/|μⱼ|` into the block: `⊕ⱼ μⱼ A_j = ⊕ⱼ |μⱼ| (uⱼ A_j)`
(`blockSum_eq_blockSum_phase`), and `uⱼ A_j` is again normal and left-canonical, with the same
transfer map and fixed point, while the mixed transfer maps are multiplied by the phases
`uⱼ conj(u_{j'})` and keep the moduli of their eigenvalues.

**Local fix (rate of the overlapping blocks):** the rate `e^{-γ q/ξ_diag}` of the source is
replaced by `e^{-γ q/ξ}` with `ξ ≥ max(ξ_diag, ξ_off-diag)`. Documented in
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

**False source (eq. (S4), complex weights):** for a weight that is not a nonnegative real number
the coefficient `βⱼ = μⱼ^N` of eq. (S4) is replaced by `|μⱼ|^N`; every block occurs once.
Documented in `docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

## Main declarations

* `MPSTensor.blockSum_eq_blockSum_phase` — the phases of the weights move into the blocks.
* `MPSTensor.exists_approximationError_le_overlappingBlockSum_complexWeight`,
  `MPSTensor.exists_approximationError_le_mul_overlappingBlockSum_complexWeight` —
  Lemma 1'(ii) for blocks of multiplicity one and complex weights, with `βⱼ = |μⱼ|^N`.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S12) and Lemma 1'(ii)
  (`eq:fid_err_gen_non_normal`).
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix Complex

namespace MPSTensor

variable {d D b : ℕ} {Dj : Fin b → ℕ} {Aj : (j : Fin b) → MPSTensor d (Dj j)}
  {ι : (j : Fin b) → Fin (Dj j) → Fin D}

/-- **The phases of the weights move into the blocks.** For any phases `uⱼ` with
`μⱼ = |μⱼ| uⱼ`, the direct sum `⊕ⱼ μⱼ A_j` of arXiv:2307.01696, eq. (S2), for `m_j = 1`, is the
direct sum `⊕ⱼ |μⱼ| (uⱼ A_j)` with the nonnegative weights `|μⱼ|`. -/
theorem blockSum_eq_blockSum_phase (Aj : (j : Fin b) → MPSTensor d (Dj j))
    (ι : (j : Fin b) → Fin (Dj j) → Fin D) (μ u : Fin b → ℂ)
    (hu : ∀ j, μ j = (‖μ j‖ : ℂ) * u j) :
    blockSum Aj ι μ = blockSum (fun j => u j • Aj j) ι fun j => (‖μ j‖ : ℂ) := by
  funext i
  simp only [blockSum, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← hu]

/-- An eigenvalue `μ'` of `c • f` gives the eigenvalue `c⁻¹ μ'` of `f`. -/
private theorem hasEigenvalue_of_hasEigenvalue_smul {V : Type*} [AddCommGroup V] [Module ℂ V]
    {f : Module.End ℂ V} {c μ' : ℂ} (hc : c ≠ 0) (h : (c • f).HasEigenvalue μ') :
    f.HasEigenvalue (c⁻¹ * μ') := by
  obtain ⟨x, hx⟩ := h.exists_hasEigenvector
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := x) ⟨?_, hx.2⟩
  rw [Module.End.mem_genEigenspace_one]
  have h1 := hx.apply_eq_smul
  rw [LinearMap.smul_apply] at h1
  rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- **Approximation error for overlapping blocks with complex weights** (arXiv:2307.01696,
Supplemental Material, Lemma 1'(ii), eq. (S12), at the corrected rate, with the coefficients
`βⱼ = |μⱼ|^N` in place of the `μⱼ^N` of eq. (S4)). Let `Aⁱ = ⊕ⱼ μⱼ A_jⁱ` be the direct sum with
complex weights `|μⱼ| ≤ 1`, at least one of modulus one (the normalization of the source, after
eq. (S2)), of blocks placed on the bond coordinates `ι_j`. Let every block `A_j` be normal in
the gauge `∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j`, `σ_j > 0`, `Tr σ_j = 1` (eq. (5)), let
`λ₂` bound the moduli of the eigenvalues other than `1` of every transfer map `E_{A_j}` and the
moduli of all eigenvalues of the mixed transfer maps `E_{jj'}(X) = ∑ᵢ A_jⁱ X (A_{j'}ⁱ)†` of
distinct blocks, so that `ξ = -1/log|λ₂|` bounds `ξ_diag` and `ξ_off-diag`, and let
`0 < γ < 1/2`. There is `C > 0` such that for every block length `q` and every number of blocks
`M ≥ 1`, with `N = qM`, the coefficients `βⱼ = |μⱼ|^N`, the pairs of the `σ_j` embedded along
`ι_j`, and `y = M e^{-γ q/ξ}`, the error `ε = 1 - |⟨φ~_N|φ_N⟩|` of the approximating state of
eq. (S7) satisfies `ε ≤ C y e^{C y}`.

The proof applies `exists_approximationError_le_overlappingBlockSum_weight` to the blocks
`uⱼ A_j`, `uⱼ = e^{i arg μⱼ}`, with the weights `|μⱼ|`. -/
theorem exists_approximationError_le_overlappingBlockSum_complexWeight
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ}
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {μ : Fin b → ℂ} (hμ1 : ∀ j, ‖μ j‖ ≤ 1) (hμmax : ∃ j, ‖μ j‖ = 1)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      1 - ‖nonNormalApproxOverlap (blockSum Aj ι μ) q M
          (ghzAmplitude fun j => (‖μ j‖ : ℂ) ^ (M * q))
          (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  set u : Fin b → ℂ := fun j => exp (arg (μ j) * I)
  have hu1 : ∀ j, ‖u j‖ = 1 := fun j => norm_exp_ofReal_mul_I _
  have hu0 : ∀ j, u j ≠ 0 := fun j => exp_ne_zero _
  have hT : ∀ j, Kraus.transferMap (u j • Aj j) = Kraus.transferMap (Aj j) := fun j =>
    transferMap_smul_eq_of_norm_eq_one (Aj j) (u j) (hu1 j)
  rw [blockSum_eq_blockSum_phase Aj ι μ u fun j => (norm_mul_exp_arg_mul_I (μ j)).symm]
  refine exists_approximationError_le_overlappingBlockSum_weight (Aj := fun j => u j • Aj j)
    (w := fun j => ‖μ j‖) hι hdisj (fun j => (isNormal_smul_iff (hu0 j) (Aj j)).2 (hN j))
    (fun j => leftCanonical_smul_of_norm_one (u j) (hu1 j) (Aj j) (hA j)) hσ htr
    (fun j => by rw [hT]; exact hfix j) (fun j μ' h => by rw [hT] at h; exact hlam j μ' h)
    (fun j j' hjj' μ' h => ?_) (fun j => norm_nonneg _) hμ1 hμmax hγ0 hγ
  have hc : u j * starRingEnd ℂ (u j') ≠ 0 :=
    mul_ne_zero (hu0 j) ((map_ne_zero _).2 (hu0 j'))
  have hcn : ‖u j * starRingEnd ℂ (u j')‖ = 1 := by
    rw [norm_mul, RCLike.norm_conj, hu1, hu1, one_mul]
  have h' : Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j'))
      ((u j * starRingEnd ℂ (u j'))⁻¹ * μ') := by
    refine hasEigenvalue_of_hasEigenvalue_smul hc ?_
    rw [← Kraus.mixedMapLM_smul]
    exact h
  have := hmix j j' hjj' _ h'
  rwa [norm_mul, norm_inv, hcn, inv_one, one_mul] at this

/-- **Approximation error for overlapping blocks with complex weights, `O`-form**
(arXiv:2307.01696, Supplemental Material, Lemma 1'(ii), eq. (S12), at the corrected rate, with
`βⱼ = |μⱼ|^N`): in the setting of
`exists_approximationError_le_overlappingBlockSum_complexWeight`, there is `C` with
`ε ≤ C (N/q) e^{-γ q/ξ}` for every block length `q` and every number of blocks `M ≥ 1`. -/
theorem exists_approximationError_le_mul_overlappingBlockSum_complexWeight
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ}
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {μ : Fin b → ℂ} (hμ1 : ∀ j, ‖μ j‖ ≤ 1) (hμmax : ∃ j, ‖μ j‖ = 1)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      1 - ‖nonNormalApproxOverlap (blockSum Aj ι μ) q M
          (ghzAmplitude fun j => (‖μ j‖ : ℂ) ^ (M * q))
          (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_overlappingBlockSum_complexWeight hι hdisj
    hN hA hσ htr hfix hlam hmix hμ1 hμmax hγ0 hγ
  refine ⟨C * Real.exp C + 1, by positivity, fun q M _ => ?_⟩
  refine le_mul_of_le_mul_exp_of_le hC.le zero_le_one (by positivity) (h q M) ?_
  linarith [norm_nonneg (nonNormalApproxOverlap (blockSum Aj ι μ) q M
    (ghzAmplitude fun j => (‖μ j‖ : ℂ) ^ (M * q))
    (fun j => embedPair (ι j) (fixedPointPair (σ j))))]

end MPSTensor
