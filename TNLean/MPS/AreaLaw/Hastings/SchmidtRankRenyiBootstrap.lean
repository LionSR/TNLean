/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FlatDensityRenyiEntropy
import TNLean.MPS.AreaLaw.Hastings.SchmidtRankBootstrap
import TNLean.MPS.AreaLaw.Hastings.TailRenyiEntropy

/-!
# Rényi entropy from overlaps with mixtures of bounded Schmidt rank

The Rényi version of the stage form of Hastings' bootstrap lemma for one cut of a bipartite
space. Under the hypotheses of `vonNeumannEntropy_le_of_schmidtRank_mixtures`, the Rényi entropy
of order `0 < α < 1` of the reduced density matrix of `Ψ` is at most
`ln k + ξ' ln(c) ln D + 4 ln D - ln(1 - (D²)^{1-α} exp(-2α/ξ')) / (1 - α)`, provided
`(D²)^{1-α} exp(-2α/ξ') < 1`. The bound differs from the von Neumann one only in the term
replacing `F(ξ', D)`.

The Schmidt-tail constraints are those of the von Neumann stage lemma,
`exists_eigenvalues₀_tail_le_of_schmidtRank_mixtures`, and the Rényi bound under these
constraints is `renyiEntropy_le_of_scale_tails`.

## Main results

* `TNLean.MPS.AreaLaw.Hastings.renyiEntropy_eq_log_sum_eigenvalues₀_rpow`: the Rényi entropy
  through the eigenvalues in descending order.
* `TNLean.MPS.AreaLaw.Hastings.renyiEntropy_le_of_schmidtRank_mixtures`: the stage lemma.

## References

Hastings, arXiv:0705.2024v4, proof of Lemma 2 (`ble`), lines 333–356 and 392–410 of
`References/0705.2024/law16.tex`. As in the von Neumann stage lemma, the mixtures are a
hypothesis; for the ground state of a gapped chain they come from Lemma 1, with
`c = 2 C₁(ξ)² / P`.
-/

open scoped BigOperators
namespace TNLean.MPS.AreaLaw.Hastings

open Finset Matrix
open scoped ComplexOrder

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-- For an order `α ≠ 0, 1`, the Rényi entropy of a Hermitian matrix is
`(1 - α)⁻¹ ln ∑ λ^α` over its eigenvalues in descending order. -/
theorem renyiEntropy_eq_log_sum_eigenvalues₀_rpow {ρ : Matrix m m ℂ} (hρ : ρ.IsHermitian)
    {α : ℝ} (hα0 : α ≠ 0) (hα1 : α ≠ 1) :
    renyiEntropy ρ hρ α =
      (1 - α)⁻¹ * Real.log (∑ a : Fin (Fintype.card m), hρ.eigenvalues₀ a ^ α) := by
  simp only [renyiEntropy, hα0, hα1, ↓reduceIte]
  congr 2
  change RCLike.re ((hρ.cfc (fun x => x ^ α)).trace) = _
  rw [hρ.trace_cfc_eq_sum_re]
  unfold Matrix.IsHermitian.eigenvalues
  exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun a ↦ hρ.eigenvalues₀ a ^ α)

/-- **Rényi stage form of Hastings' bootstrap lemma for one cut.** Let `Ψ` be a unit vector of a
bipartite space with reduced density matrix `C Cᴴ` on the first factor. Suppose that at every
scale `s` with `c exp(-2s/ξ') < 1` some mixture of pure states of Schmidt rank at most
`k D^{2s}` has normalized overlap with `Ψ` at least `1 - c exp(-2s/ξ')`. For `0 < α < 1` with
`(D²)^{1-α} exp(-2α/ξ') < 1`, the Rényi entropy of order `α` of `C Cᴴ` is at most
`ln k + ξ' ln(c) ln D + 4 ln D - ln(1 - (D²)^{1-α} exp(-2α/ξ')) / (1 - α)`.

Hastings, arXiv:0705.2024v4, proof of Lemma 2, lines 333–356 for the Schmidt-tail constraint
and lines 392–410 for its Rényi version, with the convergence condition of line 406. -/
theorem renyiEntropy_le_of_schmidtRank_mixtures (Ψ : m × n → ℂ)
    (hΨ : star Ψ ⬝ᵥ Ψ = 1)
    {k D : ℕ} (hk : 1 ≤ k) (hD : 2 ≤ D) {ξ' c α : ℝ} (hξ : 0 < ξ') (hc : 1 ≤ c)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hconv : ((D : ℝ) ^ 2) ^ (1 - α) * Real.exp (-(2 * α / ξ')) < 1)
    (hmix : ∀ s : ℕ, c * Real.exp (-(2 * s / ξ')) < 1 →
      ∃ (r : ℕ) (w : Fin r → ℝ) (ψ : Fin r → m × n → ℂ), (∀ i, 0 ≤ w i) ∧
        (∀ i, HasSchmidtRankLE (k * D ^ (2 * s)) (ψ i)) ∧
        0 < ∑ i, w i * (star (ψ i) ⬝ᵥ ψ i).re ∧
        (1 - c * Real.exp (-(2 * s / ξ'))) * ∑ i, w i * (star (ψ i) ⬝ᵥ ψ i).re ≤
          ∑ i, w i * ‖star Ψ ⬝ᵥ ψ i‖ ^ 2) :
    renyiEntropy (schmidtCoeffMatrix Ψ * (schmidtCoeffMatrix Ψ)ᴴ)
        (posSemidef_self_mul_conjTranspose (schmidtCoeffMatrix Ψ)).isHermitian α ≤
      Real.log k + ξ' * Real.log c * Real.log D + 4 * Real.log D -
        Real.log (1 - ((D : ℝ) ^ 2) ^ (1 - α) * Real.exp (-(2 * α / ξ'))) / (1 - α) := by
  obtain ⟨hp0, hpsum⟩ := eigenvalues₀_nonneg_and_sum_eq_one Ψ hΨ
  obtain ⟨m', hm'hi, htail⟩ :=
    exists_eigenvalues₀_tail_le_of_schmidtRank_mixtures Ψ hΨ hξ hc hmix
  have hmain := renyiEntropy_le_of_scale_tails _ hp0 hpsum hk hD hα0 hα1 hconv htail
  rw [renyiEntropy_eq_log_sum_eigenvalues₀_rpow _ hα0.ne' hα1.ne]
  have hDr : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
  have : (2 * (m' : ℝ) + 2) * Real.log D ≤ (ξ' * Real.log c + 4) * Real.log D := by
    refine mul_le_mul_of_nonneg_right ?_ hlogD
    linarith [hm'hi, show ξ' / 2 * Real.log c = ξ' * Real.log c / 2 by ring]
  nlinarith

end TNLean.MPS.AreaLaw.Hastings
