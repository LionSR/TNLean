/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OneCopyPairState

/-!
# Lemma 1'(ii) for orthogonal blocks, for multiplicity one, and for complex weights

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, Lemma 1'(ii)) bound the
error of the approximating state of eq. (S7) for a tensor
`Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` that is not normal. The general bound is
`MPSTensor.exists_approximationError_le_repeatedOverlappingBlockSum`: for normal blocks with any
multiplicities, any nonzero complex weights, and `q`-site states that may overlap, the error of the
corrected approximating state is at most `C y e^{C y}` with `y = M e^{-γ q/ξ}`, for every
`0 < γ < 1`, with `C` independent of the weights. This file derives the special cases from it.

* **Orthogonal blocks.** If the `q₀`-site states of distinct blocks are orthogonal for one
  `q₀`, `B_jᴴ B_{j'} = 0`, then the `q₀`-th power of every mixed transfer map
  `E_{jj'}(X) = ∑ᵢ A_jⁱ X (A_{j'}ⁱ)†` vanishes, so all its eigenvalues are `0`
  (`eq_zero_of_hasEigenvalue_mixedMapLM_of_conjTranspose_mul_eq_zero`), and the bound on the
  mixed transfer maps required by the general theorem holds for every `λ₂`. This gives the bound
  for blocks with multiplicities (`exists_approximationError_le_repeatedBlockSum`), for the
  source's construction with the pairs on one copy
  (`exists_approximationError_le_repeatedBlockSum_oneCopy`), and for multiplicity one
  (`exists_approximationError_le_blockSum`).
* **Multiplicity one.** The direct sum `⊕ⱼ μⱼ A_j` with nonzero weights is the direct sum with
  multiplicities `m_j = 1` (`repeatedBlockSum_single`). With the pairs on the one copy, the
  coefficients `β'ⱼ` of `TNLean.MPS.Preparation.OneCopyPairState` are `|μⱼ|^N`, and the overlap of
  the source's state with these coefficients is the overlap of the corrected state
  (`nonNormalApproxOverlap_blockSum_eq_copyApproxOverlap`). A block of weight zero contributes
  nothing and is dropped (`blockSum_comp_of_eq_zero`, `nonNormalApproxOverlap_comp_of_eq_zero`,
  `ghzAmplitude_comp_of_eq_zero`). This gives the bound for all complex weights, not all zero,
  with `C` independent of the weights
  (`exists_approximationError_le_overlappingBlockSum_complexWeight`), for nonnegative real weights
  (`exists_approximationError_le_overlappingBlockSum_weight`), and for unit weights
  (`exists_approximationError_le_overlappingBlockSum`).

The source states Lemma 1'(ii) for `0 < γ < 1/2`, for weights with `|μ_{j,k}| ≤ 1` of which at
least one has modulus one, and with `q = o(N)`. None of these conditions is needed here, and the
range `γ < 1` is a project result.

**Local fix (corrected fixed-point state):** for blocks with multiplicities the approximating state
is the corrected state `V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩`, or equivalently the state of eq. (S7) with the
pairs on one copy and the coefficients `β'ⱼ`; for multiplicity one the coefficients are
`β'ⱼ = |μⱼ|^N` in place of `μⱼ^N`. Documented in
`docs/paper-gaps/mswc24_repeated_block_corrected_state.tex`.

**Local fix (rate of the overlapping blocks):** when the blocks are not orthogonal, the rate
`e^{-γ q/ξ_diag}` of the source is replaced by `e^{-γ q/ξ}` with `ξ ≥ max(ξ_diag, ξ_off-diag)`.
Documented in `docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

**Scope restriction (orthogonal blocks):** `exists_approximationError_le_repeatedBlockSum`,
`exists_approximationError_le_mul_repeatedBlockSum`,
`exists_approximationError_le_repeatedBlockSum_oneCopy`,
`exists_approximationError_le_mul_repeatedBlockSum_oneCopy`, `exists_approximationError_le_blockSum`
and `exists_approximationError_le_mul_blockSum` assume that the `q`-site states of distinct blocks
are orthogonal, `B_jᴴ B_{j'} = 0`, a hypothesis the source does not state. The other bounds of this
file replace it by the bound `λ₂` on the eigenvalues of the mixed transfer maps. Documented in
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

## Main declarations

* `MPSTensor.eq_zero_of_hasEigenvalue_mixedMapLM_of_conjTranspose_mul_eq_zero` — orthogonal
  blocked tensors have nilpotent mixed transfer maps.
* `MPSTensor.exists_approximationError_le_repeatedBlockSum`,
  `MPSTensor.exists_approximationError_le_repeatedBlockSum_oneCopy` — orthogonal blocks with
  multiplicities.
* `MPSTensor.CopyWeights.single`, `MPSTensor.repeatedBlockSum_single`,
  `MPSTensor.nonNormalApproxOverlap_blockSum_eq_copyApproxOverlap` — multiplicity one as a case of
  multiplicities.
* `MPSTensor.exists_approximationError_le_overlappingBlockSum_complexWeight`,
  `MPSTensor.exists_approximationError_le_overlappingBlockSum_weight`,
  `MPSTensor.exists_approximationError_le_overlappingBlockSum`,
  `MPSTensor.exists_approximationError_le_blockSum` — multiplicity one.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S12) and Lemma 1'(ii)
  (`eq:fid_err_gen_non_normal`).
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace MPSTensor

variable {d D b : ℕ} {Dj : Fin b → ℕ} {Aj : (j : Fin b) → MPSTensor d (Dj j)}

/-! ### Orthogonal blocks -/

/-- **Orthogonal blocked tensors have nilpotent mixed transfer maps.** If for some `q` the
`q`-site blocked tensors satisfy `B_Yᴴ B_X = 0`, then `E_{XY}^q` is the mixed transfer map of the
blocked tensors, which vanishes, so every eigenvalue of `E_{XY}` is `0`. -/
theorem eq_zero_of_hasEigenvalue_mixedMapLM_of_conjTranspose_mul_eq_zero {D₁ D₂ : ℕ}
    {X : MPSTensor d D₁} {Y : MPSTensor d D₂} {q : ℕ}
    (h : (physicalMatrix (blockTensor Y q))ᴴ * physicalMatrix (blockTensor X q) = 0) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (Kraus.mixedMapLM X Y) μ) : μ = 0 := by
  have h0 : Kraus.mixedMapLM X Y ^ q = 0 := by
    ext1 Z
    rw [← mixedMapLM_blockTensor_apply,
      mixedMapLM_eq_zero_of_conjTranspose_physicalMatrix_mul_eq_zero h]
  exact (hμ.isNilpotent_of_isNilpotent ⟨q, h0⟩).eq_zero

/-- If the `q₀`-site states of distinct blocks are orthogonal for some `q₀`, every eigenvalue of
every mixed transfer map of distinct blocks is bounded by `|λ₂|`, for every `λ₂`. -/
private theorem norm_le_of_hasEigenvalue_mixedMapLM_of_orthogonal {q₀ : ℕ}
    (horth : ∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q₀))ᴴ *
      physicalMatrix (blockTensor (Aj j') q₀) = 0) (lam₂ : ℂ) :
    ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖ := fun j j' h μ' hμ' => by
  rw [eq_zero_of_hasEigenvalue_mixedMapLM_of_conjTranspose_mul_eq_zero
    (horth j' j (Ne.symm h)) hμ', norm_zero]
  exact norm_nonneg _

/-- For `q = 0` the rate `e^{-γ q/ξ}` is `1`, and every error is at most `C M e^{C M}` with
`C ≥ 1`. -/
private theorem one_sub_le_of_eq_zero {r C γ : ℝ} {lam₂ : ℂ} (hr : 0 ≤ r) (hC : 1 ≤ C)
    {q M : ℕ} [NeZero M] (hq : q = 0) :
    1 - r ≤ C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
      Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  subst hq
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  have h := one_sub_le_mul_mul_exp_div_of_one_le hr hC
    (u := M * Real.exp (-γ * ((0 : ℕ) : ℝ) / correlationLength lam₂)) (by simpa using hM)
    one_pos le_rfl
  rwa [div_one] at h

section Repeated

variable {m : Fin b → ℕ} {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}

/-- **Approximation error for orthogonal blocks with multiplicities** (arXiv:2307.01696,
Supplemental Material, Lemma 1'(ii), eq. (S12), for the corrected approximating state). Let
`Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` (eq. (S2)), the copy `k` of block `j` placed on the
bond coordinates `ι_{j,k}` with a nonzero complex weight, let every block `A_j` be normal in the
gauge `∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j`, `σ_j > 0`, `Tr σ_j = 1` (eq. (5)), let `λ₂` bound
the moduli of the eigenvalues other than `1` of every transfer map `E_{A_j}`, so that
`ξ = -1/log|λ₂|` bounds the correlation lengths `ξ_jj`, and let `0 < γ < 1`. There is `C > 0`
such that for all weights, every block length `q` at which the `q`-site states of distinct blocks
are orthogonal, `B_jᴴ B_{j'} = 0`, and every number of blocks `M ≥ 1` with `N = qM` and
`βⱼ = ∑ₖ μ_{j,k}^N` not all zero (eq. (S4)), the error `ε = 1 - |⟨φ~_N|φ_N⟩|` of the corrected
approximating state `V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` satisfies `ε ≤ C y e^{C y}` with
`y = M e^{-γ q/ξ}`.

If the blocks are orthogonal at some `q₀`, the mixed transfer maps are nilpotent and
`exists_approximationError_le_repeatedOverlappingBlockSum` applies; otherwise the statement is
vacuous. The source states the bound for `0 < γ < 1/2`; the range
`γ < 1` is a project result. -/
theorem exists_approximationError_le_repeatedBlockSum
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : CopyWeights b m) (q M : ℕ) [NeZero M],
      (∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
        physicalMatrix (blockTensor (Aj j') q) = 0) →
      bntWeight μ (M * q) ≠ 0 →
      1 - ‖copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
          (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  by_cases hex : ∃ q₀, ∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q₀))ᴴ *
      physicalMatrix (blockTensor (Aj j') q₀) = 0
  · obtain ⟨q₀, horth₀⟩ := hex
    obtain ⟨C, hC, h⟩ := exists_approximationError_le_repeatedOverlappingBlockSum hι hdisj hN hA
      hσ htr hfix hlam (norm_le_of_hasEigenvalue_mixedMapLM_of_orthogonal horth₀ lam₂) hγ0 hγ
    exact ⟨C, hC, fun μ q M _ _ hβ => h μ q M hβ⟩
  · exact ⟨1, one_pos, fun μ q M _ horth _ => absurd ⟨q, horth⟩ hex⟩

/-- **Approximation error for orthogonal blocks with multiplicities, `O`-form**
(arXiv:2307.01696, Supplemental Material, Lemma 1'(ii), eq. (S12), for the corrected
approximating state): in the setting of `exists_approximationError_le_repeatedBlockSum`, there is
`C` with `ε ≤ C M e^{-γ q/ξ}`, which is `C (N/q) e^{-γ q/ξ}` for `q ≥ 1`, for all weights, every
block length `q` at which the `q`-site states of distinct blocks are orthogonal, and every number
of blocks `M ≥ 1` with the weights `βⱼ` not all zero. -/
theorem exists_approximationError_le_mul_repeatedBlockSum
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : CopyWeights b m) (q M : ℕ) [NeZero M],
      (∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
        physicalMatrix (blockTensor (Aj j') q) = 0) →
      bntWeight μ (M * q) ≠ 0 →
      1 - ‖copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
          (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_repeatedBlockSum hι hdisj hN hA hσ htr hfix
    hlam hγ0 hγ
  refine ⟨C * Real.exp C + 1, by positivity, fun μ q M _ horth hβ => ?_⟩
  refine le_mul_of_le_mul_exp_of_le hC.le zero_le_one (by positivity) (h μ q M horth hβ) ?_
  linarith [norm_nonneg (copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
    (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ)]

/-- **Approximation error with the pairs on one copy, for orthogonal blocks** (arXiv:2307.01696,
Supplemental Material, Lemma 1'(ii), eq. (S12), with the coefficients `β'ⱼ` in place of the
coefficients `βⱼ` of eq. (S7)). In the setting of `exists_approximationError_le_repeatedBlockSum`,
there is `C > 0` such that for all nonzero complex weights, every choice of copies `k_j`, every
block length `q ≥ 1` at which the `q`-site states of distinct blocks are orthogonal and every number
of blocks `M ≥ 1` with `βⱼ = ∑ₖ μ_{j,k}^N` not all zero, the error of the approximating state
`V^{⊗M} ∑ⱼ α'ⱼ |Ω_j⟩` with the pairs of `σ_j` on the copy `k_j`, `α'ⱼ = β'ⱼ / (∑ₗ |β'ₗ|²)^{1/2}` and
`β'ⱼ = βⱼ (cⱼ / μ_{j,k_j}^q)^M` satisfies `ε ≤ C y e^{C y}` with `y = M e^{-γ q/ξ}`. -/
theorem exists_approximationError_le_repeatedBlockSum_oneCopy
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : CopyWeights b m) (k : (j : Fin b) → Fin (m j)) (q M : ℕ) [NeZero M],
      q ≠ 0 →
      (∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
        physicalMatrix (blockTensor (Aj j') q) = 0) →
      bntWeight μ (M * q) ≠ 0 →
      1 - ‖nonNormalApproxOverlap (repeatedBlockSum Aj ι μ) q M
          (ghzAmplitude (oneCopyWeight μ k q M))
          (fun j => embedPair (ι j (k j)) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_repeatedBlockSum hι hdisj hN hA hσ htr hfix
    hlam hγ0 hγ
  refine ⟨C, hC, fun μ k q M _ hq horth hβ => ?_⟩
  rw [nonNormalApproxOverlap_repeatedBlockSum_oneCopy hι hdisj μ hq]
  exact h μ q M horth hβ

/-- **Approximation error with the pairs on one copy, for orthogonal blocks, `O`-form**
(arXiv:2307.01696, Supplemental Material, Lemma 1'(ii), eq. (S12), with the coefficients `β'ⱼ`):
in the setting of `exists_approximationError_le_repeatedBlockSum_oneCopy`, there is `C` with
`ε ≤ C M e^{-γ q/ξ}`, which is `C (N/q) e^{-γ q/ξ}`. -/
theorem exists_approximationError_le_mul_repeatedBlockSum_oneCopy
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : CopyWeights b m) (k : (j : Fin b) → Fin (m j)) (q M : ℕ) [NeZero M],
      q ≠ 0 →
      (∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
        physicalMatrix (blockTensor (Aj j') q) = 0) →
      bntWeight μ (M * q) ≠ 0 →
      1 - ‖nonNormalApproxOverlap (repeatedBlockSum Aj ι μ) q M
          (ghzAmplitude (oneCopyWeight μ k q M))
          (fun j => embedPair (ι j (k j)) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_mul_repeatedBlockSum hι hdisj hN hA hσ htr
    hfix hlam hγ0 hγ
  refine ⟨C, hC, fun μ k q M _ hq horth hβ => ?_⟩
  rw [nonNormalApproxOverlap_repeatedBlockSum_oneCopy hι hdisj μ hq]
  exact h μ q M horth hβ

end Repeated

/-! ### Multiplicity one -/

/-- The nonzero weights `μⱼ` of a direct sum of blocks of multiplicity one, as the weights of
blocks with one copy each (arXiv:2307.01696, Supplemental Material, eq. (S2) for `m_j = 1`). -/
def CopyWeights.single (μ : Fin b → ℂ) (hμ : ∀ j, μ j ≠ 0) : CopyWeights b fun _ => 1 where
  weight j _ := μ j
  mult_pos _ := Nat.one_pos
  weight_ne_zero j _ := hμ j

variable {ι : (j : Fin b) → Fin (Dj j) → Fin D}

/-- The direct sum `⊕ⱼ μⱼ A_j` is the direct sum with multiplicities `m_j = 1`. -/
theorem repeatedBlockSum_single (Aj : (j : Fin b) → MPSTensor d (Dj j))
    (ι : (j : Fin b) → Fin (Dj j) → Fin D) (μ : Fin b → ℂ) (hμ : ∀ j, μ j ≠ 0) :
    repeatedBlockSum Aj (fun j _ => ι j) (CopyWeights.single μ hμ) = blockSum Aj ι μ := by
  funext i
  simp [repeatedBlockSum, blockSum, CopyWeights.single]

/-- Disjoint bond coordinates of the blocks are disjoint bond coordinates of their single
copies. -/
private theorem single_disjoint (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') :
    ∀ p p' : (j : Fin b) × Fin ((fun _ => 1) j), p ≠ p' → ∀ a a',
      (fun j (_ : Fin 1) => ι j) p.1 p.2 a ≠ (fun j (_ : Fin 1) => ι j) p'.1 p'.2 a' := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ hp a a'
  refine hdisj j j' (fun h => hp ?_) a a'
  subst h
  rw [Subsingleton.elim k k']

/-- **Multiplicity one as a case of multiplicities.** For nonzero weights and `q ≥ 1`, the overlap
with the target of the approximating state of arXiv:2307.01696, Supplemental Material, eq. (S7),
for `⊕ⱼ μⱼ A_j`, with the coefficients `|μⱼ|^N` and the pairs of the `σ_j` embedded along `ι_j`, is
the overlap of the corrected state of the direct sum with multiplicities `m_j = 1`
(`nonNormalApproxOverlap_repeatedBlockSum_oneCopy` and `oneCopyWeight_of_subsingleton`). -/
theorem nonNormalApproxOverlap_blockSum_eq_copyApproxOverlap
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    {μ : Fin b → ℂ} (hμ : ∀ j, μ j ≠ 0) {q : ℕ} (hq : q ≠ 0)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) (M : ℕ) :
    nonNormalApproxOverlap (blockSum Aj ι μ) q M (ghzAmplitude fun j => (‖μ j‖ : ℂ) ^ (M * q))
        (fun j => embedPair (ι j) (fixedPointPair (σ j))) =
      copyApproxOverlap (repeatedBlockSum Aj (fun j _ => ι j) (CopyWeights.single μ hμ)) q M
        (ghzAmplitude (bntWeight (CopyWeights.single μ hμ) (M * q)))
        (copyIsometry (fun j _ => ι j) (CopyWeights.single μ hμ) q) σ := by
  have h := nonNormalApproxOverlap_repeatedBlockSum_oneCopy (Aj := Aj) (fun j _ => hι j)
    (single_disjoint hdisj) (CopyWeights.single μ hμ) hq (fun _ => 0) σ M
  have hw : oneCopyWeight (CopyWeights.single μ hμ) (fun _ => 0) q M =
      fun j => (‖μ j‖ : ℂ) ^ (M * q) := by
    funext j
    rw [oneCopyWeight_of_subsingleton _ _ (fun k => Subsingleton.elim _ _)]
    push_cast
    rfl
  calc _ = nonNormalApproxOverlap (repeatedBlockSum Aj (fun j _ => ι j) (CopyWeights.single μ hμ))
        q M (ghzAmplitude (oneCopyWeight (CopyWeights.single μ hμ) (fun _ => 0) q M))
        (fun j => embedPair (ι j) (fixedPointPair (σ j))) := by
        rw [repeatedBlockSum_single, hw]
    _ = _ := h

/-- A block of weight zero does not contribute to the direct sum: if `μ` vanishes off the range of
an injective `e`, then `⊕ⱼ μⱼ A_j = ⊕ᵢ μ_{e i} A_{e i}`. -/
theorem blockSum_comp_of_eq_zero {b' : ℕ} {e : Fin b' → Fin b} (he : Function.Injective e)
    (Aj : (j : Fin b) → MPSTensor d (Dj j)) (ι : (j : Fin b) → Fin (Dj j) → Fin D)
    {μ : Fin b → ℂ} (hμ : ∀ j, j ∉ Set.range e → μ j = 0) :
    blockSum (fun i => Aj (e i)) (fun i => ι (e i)) (fun i => μ (e i)) = blockSum Aj ι μ := by
  funext i
  exact Fintype.sum_of_injective e he _ _ (fun j hj => by rw [hμ j hj, zero_smul])
    (fun _ => rfl)

/-- A pair with coefficient zero does not contribute to the approximating state: if `α` vanishes
off the range of an injective `e`, the overlap of the approximating state of arXiv:2307.01696,
Supplemental Material, eq. (S7), formed from the coefficients `α` and the pairs `ω`, is that formed
from `α ∘ e` and `ω ∘ e`. -/
theorem nonNormalApproxOverlap_comp_of_eq_zero {b' : ℕ} {e : Fin b' → Fin b}
    (he : Function.Injective e) (A : MPSTensor d D) (q M : ℕ) (α : Fin b → ℂ)
    (ω : Fin b → Fin D × Fin D → ℂ) (hα : ∀ j, j ∉ Set.range e → α j = 0) :
    nonNormalApproxOverlap A q M (fun i => α (e i)) (fun i => ω (e i)) =
      nonNormalApproxOverlap A q M α ω := by
  have h : nonNormalFixedPointState (M := M) (fun i => α (e i)) (fun i => ω (e i)) =
      nonNormalFixedPointState α ω := by
    funext c
    exact Fintype.sum_of_injective e he _ _ (fun j hj => by rw [hα j hj, zero_mul])
      (fun _ => rfl)
  simp only [nonNormalApproxOverlap, nonNormalApproxState, nonNormalApproxVector, h]

/-- Dropping weights that vanish does not change the normalized weights of the others: if `β`
vanishes off the range of an injective `e`, then `ghzAmplitude (β ∘ e) = ghzAmplitude β ∘ e`. -/
theorem ghzAmplitude_comp_of_eq_zero {b' : ℕ} {e : Fin b' → Fin b} (he : Function.Injective e)
    (β : Fin b → ℂ) (hβ : ∀ j, j ∉ Set.range e → β j = 0) :
    ghzAmplitude (fun i => β (e i)) = fun i => ghzAmplitude β (e i) := by
  funext i
  have h : ∑ l, ‖β (e l)‖ ^ 2 = ∑ l, ‖β l‖ ^ 2 :=
    Fintype.sum_of_injective e he _ _
      (fun j hj => by rw [hβ j hj, norm_zero, zero_pow two_ne_zero]) (fun _ => rfl)
  simp only [ghzAmplitude, h]

/-- Lemma 1'(ii) for multiplicity one and nonzero complex weights, with `C ≥ 1` independent of the
weights. -/
private theorem exists_approximationError_le_blockSum_of_ne_zero [NeZero b]
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ}
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ μ : Fin b → ℂ, (∀ j, μ j ≠ 0) → ∀ (q M : ℕ) [NeZero M],
      1 - ‖nonNormalApproxOverlap (blockSum Aj ι μ) q M
          (ghzAmplitude fun j => (‖μ j‖ : ℂ) ^ (M * q))
          (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_repeatedOverlappingBlockSum (Aj := Aj)
    (m := fun _ => 1) (ι := fun j _ => ι j) (fun j _ => hι j) (single_disjoint hdisj) hN hA hσ
    htr hfix hlam hmix hγ0 hγ
  refine ⟨C + 1, by linarith, fun μ hμ q M _ => ?_⟩
  rcases eq_or_ne q 0 with hq | hq
  · exact one_sub_le_of_eq_zero (norm_nonneg _) (by linarith) hq
  rw [nonNormalApproxOverlap_blockSum_eq_copyApproxOverlap hι hdisj hμ hq]
  have hβ : bntWeight (CopyWeights.single μ hμ) (M * q) ≠ 0 := by
    refine Function.ne_iff.2 ⟨0, ?_⟩
    rw [bntWeight, Fin.sum_univ_one]
    exact pow_ne_zero _ (hμ 0)
  refine (h _ q M hβ).trans ?_
  gcongr <;> linarith

/-- **Approximation error for overlapping blocks with complex weights** (arXiv:2307.01696,
Supplemental Material, Lemma 1'(ii), eq. (S12), at the corrected rate, with the coefficients
`βⱼ = |μⱼ|^N` in place of the coefficients `μⱼ^N` that eqs. (S6) and (S7) take from eq. (S4)). Let
`Aⁱ = ⊕ⱼ μⱼ A_jⁱ` be the direct sum with complex weights `μⱼ` of blocks placed on the bond
coordinates `ι_j`. Let every block `A_j` be normal in the gauge `∑ᵢ (A_jⁱ)† A_jⁱ = 1`,
`E_{A_j}(σ_j) = σ_j`, `σ_j > 0`, `Tr σ_j = 1` (eq. (5)), let `λ₂` bound the moduli of the
eigenvalues other than `1` of every transfer map `E_{A_j}` and the moduli of all eigenvalues of the
mixed transfer maps `E_{jj'}(X) = ∑ᵢ A_jⁱ X (A_{j'}ⁱ)†` of distinct blocks, so that
`ξ = -1/log|λ₂|` bounds `ξ_diag` and `ξ_off-diag`, and let `0 < γ < 1`. There is `C > 0` such that
for all weights `μ` not all zero, every block length `q` and every number of blocks `M ≥ 1`, with
`N = qM`, the coefficients `βⱼ = |μⱼ|^N`, the pairs of the `σ_j` embedded along `ι_j`, and
`y = M e^{-γ q/ξ}`, the error `ε = 1 - |⟨φ~_N|φ_N⟩|` of the approximating state of eq. (S7)
satisfies `ε ≤ C y e^{C y}`.

The constant does not depend on the weights, and the normalization of the source after eq. (S2),
`|μⱼ| ≤ 1` with one weight of modulus one, is not needed. Blocks of weight zero are dropped, and the
others are blocks of multiplicity one in `exists_approximationError_le_repeatedOverlappingBlockSum`.
The source states the bound for `0 < γ < 1/2`; the range `γ < 1` is a project result. -/
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
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : Fin b → ℂ, μ ≠ 0 → ∀ (q M : ℕ) [NeZero M],
      1 - ‖nonNormalApproxOverlap (blockSum Aj ι μ) q M
          (ghzAmplitude fun j => (‖μ j‖ : ℂ) ^ (M * q))
          (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  classical
  -- For each set `S` of blocks, the bound for the weights that are nonzero exactly on `S`.
  have hS : ∀ S : Finset (Fin b), ∃ C : ℝ, 1 ≤ C ∧ ∀ μ : Fin b → ℂ, (∀ j, μ j ≠ 0 ↔ j ∈ S) →
      μ ≠ 0 → ∀ (q M : ℕ) [NeZero M],
      1 - ‖nonNormalApproxOverlap (blockSum Aj ι μ) q M
          (ghzAmplitude fun j => (‖μ j‖ : ℂ) ^ (M * q))
          (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
    intro S
    rcases S.eq_empty_or_nonempty with hS0 | hSne
    · refine ⟨1, le_rfl, fun μ hμS hμ0 => absurd (funext fun j => ?_) hμ0⟩
      by_contra h
      have := (hμS j).1 h
      rw [hS0] at this
      exact Finset.notMem_empty j this
    set e : Fin S.card → Fin b := fun i => S.orderEmbOfFin rfl i
    have he : Function.Injective e := (S.orderEmbOfFin rfl).injective
    have hrange : ∀ j, j ∈ Set.range e ↔ j ∈ S := fun j => by
      have := Finset.range_orderEmbOfFin S (rfl : S.card = S.card)
      rw [← Finset.mem_coe, ← this]
    have : NeZero S.card := ⟨(Finset.card_pos.2 hSne).ne'⟩
    obtain ⟨C, hC, h⟩ := exists_approximationError_le_blockSum_of_ne_zero
      (Aj := fun i => Aj (e i)) (ι := fun i => ι (e i)) (σ := fun i => σ (e i))
      (fun i => hι (e i)) (fun i i' hii' => hdisj (e i) (e i') (he.ne hii'))
      (fun i => hN (e i)) (fun i => hA (e i)) (fun i => hσ (e i)) (fun i => htr (e i))
      (fun i => hfix (e i)) (fun i => hlam (e i))
      (fun i i' hii' => hmix (e i) (e i') (he.ne hii')) hγ0 hγ
    refine ⟨C, hC, fun μ hμS _ q M _ => ?_⟩
    have hoff : ∀ j, j ∉ Set.range e → μ j = 0 := fun j hj => by
      by_contra h
      exact hj ((hrange j).2 ((hμS j).1 h))
    rcases eq_or_ne q 0 with hq | hq
    · exact one_sub_le_of_eq_zero (norm_nonneg _) hC hq
    have hNq : M * q ≠ 0 := Nat.mul_ne_zero (NeZero.ne M) hq
    have hβ : ∀ j, j ∉ Set.range e → (‖μ j‖ : ℂ) ^ (M * q) = 0 := fun j hj => by
      rw [hoff j hj, norm_zero, Complex.ofReal_zero, zero_pow hNq]
    have hα : ∀ j, j ∉ Set.range e →
        ghzAmplitude (fun j => (‖μ j‖ : ℂ) ^ (M * q)) j = 0 := fun j hj => by
      rw [ghzAmplitude, hβ j hj, zero_div]
    have key := h (fun i => μ (e i)) (fun i => (hμS (e i)).2 ((hrange (e i)).1 ⟨i, rfl⟩)) q M
    rw [blockSum_comp_of_eq_zero he Aj ι hoff,
      ghzAmplitude_comp_of_eq_zero he (fun j => (‖μ j‖ : ℂ) ^ (M * q)) hβ,
      nonNormalApproxOverlap_comp_of_eq_zero he _ q M _
        (fun j => embedPair (ι j) (fixedPointPair (σ j))) hα] at key
    exact key
  choose C hC h using hS
  have hsum : 0 ≤ ∑ S, C S := Finset.sum_nonneg fun S _ => zero_le_one.trans (hC S)
  refine ⟨1 + ∑ S, C S, by linarith, fun μ hμ q M _ => ?_⟩
  refine (h (Finset.univ.filter fun j => μ j ≠ 0) μ (fun j => by simp) hμ q M).trans ?_
  have hle : C (Finset.univ.filter fun j => μ j ≠ 0) ≤ 1 + ∑ S, C S := by
    have := Finset.single_le_sum (f := C) (fun S _ => (zero_le_one.trans (hC S)))
      (Finset.mem_univ (Finset.univ.filter fun j => μ j ≠ 0))
    linarith
  have hu : 0 ≤ (M : ℝ) * Real.exp (-γ * q / correlationLength lam₂) := by positivity
  gcongr

/-- **Approximation error for overlapping blocks with complex weights, `O`-form**
(arXiv:2307.01696, Supplemental Material, Lemma 1'(ii), eq. (S12), at the corrected rate, with
`βⱼ = |μⱼ|^N`): in the setting of
`exists_approximationError_le_overlappingBlockSum_complexWeight`, there is `C` with
`ε ≤ C (N/q) e^{-γ q/ξ}` for all weights not all zero, every block length `q` and every number of
blocks `M ≥ 1`. -/
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
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : Fin b → ℂ, μ ≠ 0 → ∀ (q M : ℕ) [NeZero M],
      1 - ‖nonNormalApproxOverlap (blockSum Aj ι μ) q M
          (ghzAmplitude fun j => (‖μ j‖ : ℂ) ^ (M * q))
          (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_overlappingBlockSum_complexWeight hι hdisj
    hN hA hσ htr hfix hlam hmix hγ0 hγ
  refine ⟨C * Real.exp C + 1, by positivity, fun μ hμ q M _ => ?_⟩
  refine le_mul_of_le_mul_exp_of_le hC.le zero_le_one (by positivity) (h μ hμ q M) ?_
  linarith [norm_nonneg (nonNormalApproxOverlap (blockSum Aj ι μ) q M
    (ghzAmplitude fun j => (‖μ j‖ : ℂ) ^ (M * q))
    (fun j => embedPair (ι j) (fixedPointPair (σ j))))]

/-- **Approximation error for overlapping blocks with weights of different moduli**
(arXiv:2307.01696, Supplemental Material, Lemma 1'(ii), eq. (S12), at the corrected rate). In the
setting of `exists_approximationError_le_overlappingBlockSum_complexWeight`, there is `C > 0` such
that for all real weights `wⱼ ≥ 0`, not all zero, every block length `q` and every number of blocks
`M ≥ 1`, with `N = qM`, the weights `βⱼ = wⱼ^N` of eq. (S4) for `m_j = 1`, the pairs of the `σ_j`
embedded along `ι_j`, and `y = M e^{-γ q/ξ}`, the error `ε = 1 - |⟨φ~_N|φ_N⟩|` of the approximating
state of eq. (S7) for `⊕ⱼ wⱼ A_j` satisfies `ε ≤ C y e^{C y}`. -/
theorem exists_approximationError_le_overlappingBlockSum_weight
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ}
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : Fin b → ℝ, (∀ j, 0 ≤ w j) → w ≠ 0 → ∀ (q M : ℕ) [NeZero M],
      1 - ‖nonNormalApproxOverlap (blockSum Aj ι fun j => (w j : ℂ)) q M
          (ghzAmplitude fun j => (w j : ℂ) ^ (M * q))
          (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_overlappingBlockSum_complexWeight hι hdisj
    hN hA hσ htr hfix hlam hmix hγ0 hγ
  refine ⟨C, hC, fun w hw0 hw q M _ => ?_⟩
  have hμ : (fun j => (w j : ℂ)) ≠ 0 := fun h0 =>
    hw (funext fun j => Complex.ofReal_injective (congrFun h0 j))
  have hn : ∀ j, ‖(w j : ℂ)‖ = w j := fun j => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 j)]
  have key := h _ hμ q M
  simp only [hn] at key
  exact key

/-- **Approximation error for overlapping blocks with weights of different moduli, `O`-form**
(arXiv:2307.01696, Supplemental Material, Lemma 1'(ii), eq. (S12), at the corrected rate): in the
setting of `exists_approximationError_le_overlappingBlockSum_weight`, there is `C` with
`ε ≤ C (N/q) e^{-γ q/ξ}` for all real weights `wⱼ ≥ 0` not all zero, every block length `q` and
every number of blocks `M ≥ 1`. -/
theorem exists_approximationError_le_mul_overlappingBlockSum_weight
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ}
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : Fin b → ℝ, (∀ j, 0 ≤ w j) → w ≠ 0 → ∀ (q M : ℕ) [NeZero M],
      1 - ‖nonNormalApproxOverlap (blockSum Aj ι fun j => (w j : ℂ)) q M
          (ghzAmplitude fun j => (w j : ℂ) ^ (M * q))
          (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_overlappingBlockSum_weight hι hdisj hN hA hσ
    htr hfix hlam hmix hγ0 hγ
  refine ⟨C * Real.exp C + 1, by positivity, fun w hw0 hw q M _ => ?_⟩
  refine le_mul_of_le_mul_exp_of_le hC.le zero_le_one (by positivity) (h w hw0 hw q M) ?_
  linarith [norm_nonneg (nonNormalApproxOverlap (blockSum Aj ι fun j => (w j : ℂ)) q M
    (ghzAmplitude fun j => (w j : ℂ) ^ (M * q))
    (fun j => embedPair (ι j) (fixedPointPair (σ j))))]

/-- **Approximation error for blocks with overlapping states** (arXiv:2307.01696,
Supplemental Material, Lemma 1'(ii), eq. (S12), at the corrected rate), for unit weights. Let
`Aⁱ = ⊕ⱼ A_jⁱ` be the direct sum with unit weights of blocks placed on the bond coordinates `ι_j`,
in the setting of `exists_approximationError_le_overlappingBlockSum_complexWeight`. There is
`C > 0` such that for every block length `q` and every number of blocks `M ≥ 1`, with `N = qM`,
`βⱼ = 1` (eq. (S4) for `m_j = 1` and `μ_{j,1} = 1`), the pairs of the `σ_j` embedded along `ι_j`,
and `y = M e^{-γ q/ξ}` (`= (N/q) e^{-γ q/ξ}` for `q ≥ 1`), the error `ε = 1 - |⟨φ~_N|φ_N⟩|` of the
approximating state of eq. (S7) satisfies `ε ≤ C y e^{C y}`.

The `q`-site states of distinct blocks need not be orthogonal, and no condition `q = o(N)` is
needed. The source's rate `e^{-γ q/ξ_diag}` fails for overlapping blocks
(`isBNTCanonicalForm_and_not_approximationError_le_overlappingBlock`); here `ξ` also bounds the
correlation lengths `ξ_{jj'}` of the mixed transfer maps. -/
theorem exists_approximationError_le_overlappingBlockSum [NeZero b]
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ}
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      1 - ‖nonNormalApproxOverlap (blockSum Aj ι fun _ => 1) q M (ghzAmplitude fun _ => 1)
          (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_overlappingBlockSum_complexWeight hι hdisj
    hN hA hσ htr hfix hlam hmix hγ0 hγ
  refine ⟨C, hC, fun q M _ => ?_⟩
  simpa using h (fun _ => 1) (fun h0 => one_ne_zero (congrFun h0 0)) q M

/-- **Approximation error for blocks with overlapping states, `O`-form** (arXiv:2307.01696,
Supplemental Material, Lemma 1'(ii), eq. (S12), at the corrected rate): in the setting of
`exists_approximationError_le_overlappingBlockSum`, there is `C` with
`ε ≤ C (N/q) e^{-γ q/ξ}` for every block length `q` and every number of blocks `M ≥ 1`. -/
theorem exists_approximationError_le_mul_overlappingBlockSum [NeZero b]
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ}
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      1 - ‖nonNormalApproxOverlap (blockSum Aj ι fun _ => 1) q M (ghzAmplitude fun _ => 1)
          (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_overlappingBlockSum hι hdisj hN hA hσ htr
    hfix hlam hmix hγ0 hγ
  refine ⟨C * Real.exp C + 1, by positivity, fun q M _ => ?_⟩
  refine le_mul_of_le_mul_exp_of_le hC.le zero_le_one (by positivity) (h q M) ?_
  linarith [norm_nonneg (nonNormalApproxOverlap (blockSum Aj ι fun _ => 1) q M
    (ghzAmplitude fun _ => 1) (fun j => embedPair (ι j) (fixedPointPair (σ j))))]

/-- **Approximation error for orthogonal blocks of multiplicity one** (arXiv:2307.01696,
Supplemental Material, Lemma 1'(ii), eq. (S12)). Let `Aⁱ = ⊕ⱼ μⱼ A_jⁱ` with `μⱼ > 0`, the block
`j` placed on the bond coordinates `ι_j`, let every block `A_j` be normal in the gauge
`∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j`, `σ_j > 0`, `Tr σ_j = 1` (eq. (5)), let `λ₂` bound the
moduli of the eigenvalues other than `1` of every transfer map `E_{A_j}`, so that
`ξ = -1/log|λ₂|` bounds the correlation lengths `ξ_jj`, and let `0 < γ < 1`. There is `C > 0`
such that for all weights `μⱼ > 0`, every block length `q` at which the `q`-site states of distinct
blocks are orthogonal, `B_jᴴ B_{j'} = 0`, and every number of blocks `M ≥ 1`, with `N = qM`,
`βⱼ = μⱼ^N` (eq. (S4) for `m_j = 1`), the pairs of the `σ_j` embedded along `ι_j`, and
`y = M e^{-γ q/ξ}` (`= (N/q) e^{-γ q/ξ}` for `q ≥ 1`), the error `ε = 1 - |⟨φ~_N|φ_N⟩|` of the
approximating state of eq. (S7) satisfies `ε ≤ C y e^{C y}`.

No condition `q = o(N)` is needed: under the orthogonality the mixed transfer maps are nilpotent,
so the source's off-diagonal term vanishes and
`exists_approximationError_le_overlappingBlockSum_weight` applies for every `λ₂`. The source
states the bound for `0 < γ < 1/2`; the range `γ < 1` is a project result. -/
theorem exists_approximationError_le_blockSum [NeZero b] (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : Fin b → ℝ, (∀ j, 0 < μ j) → ∀ (q M : ℕ) [NeZero M],
      (∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
        physicalMatrix (blockTensor (Aj j') q) = 0) →
      1 - ‖nonNormalApproxOverlap (blockSum Aj ι fun j => (μ j : ℂ)) q M
          (ghzAmplitude fun j => (μ j : ℂ) ^ (M * q))
          (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  by_cases hex : ∃ q₀, ∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q₀))ᴴ *
      physicalMatrix (blockTensor (Aj j') q₀) = 0
  · obtain ⟨q₀, horth₀⟩ := hex
    obtain ⟨C, hC, h⟩ := exists_approximationError_le_overlappingBlockSum_weight hι hdisj hN hA
      hσ htr hfix hlam (norm_le_of_hasEigenvalue_mixedMapLM_of_orthogonal horth₀ lam₂) hγ0 hγ
    exact ⟨C, hC, fun μ hμ q M _ _ => h μ (fun j => (hμ j).le)
      (fun h0 => (hμ 0).ne' (congrFun h0 0)) q M⟩
  · exact ⟨1, one_pos, fun μ _ q M _ horth => absurd ⟨q, horth⟩ hex⟩

/-- **Approximation error for orthogonal blocks of multiplicity one, `O`-form**
(arXiv:2307.01696, Supplemental Material, Lemma 1'(ii), eq. (S12)): in the setting of
`exists_approximationError_le_blockSum`, there is `C` with `ε ≤ C (N/q) e^{-γ q/ξ}` for all
weights `μⱼ > 0`, every block length `q` at which the `q`-site states of distinct blocks are
orthogonal and every number of blocks `M ≥ 1`. -/
theorem exists_approximationError_le_mul_blockSum [NeZero b]
    (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : Fin b → ℝ, (∀ j, 0 < μ j) → ∀ (q M : ℕ) [NeZero M],
      (∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
        physicalMatrix (blockTensor (Aj j') q) = 0) →
      1 - ‖nonNormalApproxOverlap (blockSum Aj ι fun j => (μ j : ℂ)) q M
          (ghzAmplitude fun j => (μ j : ℂ) ^ (M * q))
          (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_blockSum hι hdisj hN hA hσ htr hfix hlam
    hγ0 hγ
  refine ⟨C * Real.exp C + 1, by positivity, fun μ hμ q M _ horth => ?_⟩
  refine le_mul_of_le_mul_exp_of_le hC.le zero_le_one (by positivity) (h μ hμ q M horth) ?_
  linarith [norm_nonneg (nonNormalApproxOverlap (blockSum Aj ι fun j => (μ j : ℂ)) q M
    (ghzAmplitude fun j => (μ j : ℂ) ^ (M * q))
    (fun j => embedPair (ι j) (fixedPointPair (σ j))))]

end MPSTensor
