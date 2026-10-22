/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.SchmidtTail
import TNLean.MPS.AreaLaw.SequentialTruncation

/-!
# Matrix product state approximation from the decay of the Schmidt tail

Suppose that at every internal cut of a chain of `L` sites the mass beyond the `n` largest
eigenvalues of the left marginal satisfies Hastings' geometric bound
`c e^{-2m/ξ}` once `n ≥ k₀ d^{2m}`. Truncating every cut onto the `k'` leading eigenvectors
then gives an open-boundary matrix product state of bond dimension `k'` within distance
`(L - 1) √(c e^{2/ξ} (k'/k₀)^{-1/(ξ log d)})` of the state.

Source: Hastings, *An area law for one-dimensional quantum systems*, arXiv:0705.2024v4,
section "Matrix Product States", lines 553–557.

**Local fix (error measure):** the source says that the error of the approximation scales
as `N (k'/k₀)^{-1/(ξ' ln D)}` without naming the error measure. The bound proved here is
on the norm distance, through the sequential truncation estimate `∑_k √ε_k`, so the tail
enters through a square root. The constant of the tail is that of
`TNLean.MPS.AreaLaw.Hastings.schmidtTail_le_rpow_of_geometric`. Documented in
`docs/paper-gaps/hastings07_schmidt_tail_constant.tex`.
-/

open Real

namespace TNLean.MPS.AreaLaw.Hastings

variable {L q : ℕ}

/-- **Matrix product state from the decay of the Schmidt tail.** If at every internal cut
`k` the mass beyond the `n` largest eigenvalues of the left marginal `ρ_k` of the unit
vector `ψ` is at most `c e^{-2m/ξ}` whenever `k₀ d^{2m} ≤ n`, then for every bond
dimension `k' ≥ k₀` the truncation onto the `k'` leading eigenvectors at every cut is an
open-boundary matrix product state of bond dimension `k'` within distance
`(L - 1) √(c e^{2/ξ} (k'/k₀)^{-1/(ξ log d)})` of `ψ`.
Hastings, arXiv:0705.2024v4, lines 540–557. The constant and the error measure differ from
the source as described in the module docstring. -/
theorem isOpenMPS_norm_sub_le_of_schmidtTail_geometric
    (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (hψ : ‖ψ‖ = 1)
    {d ξ c k₀ : ℝ} (hd : 1 < d) (hξ : 0 < ξ) (hc : 0 ≤ c) (hk₀ : 0 < k₀)
    (hτ : ∀ k ∈ Finset.Ico 1 L, ∀ m n : ℕ, k₀ * d ^ (2 * m) ≤ n →
      1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (leftBlock L k)
        ψ).kyFanNorm n ≤ c * exp (-(2 * m) / ξ))
    {k' : ℕ} (hk' : k₀ ≤ k') :
    let P : ∀ k : ℕ, LeftBlockMatrix L q k := fun k ↦
      (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (leftBlock L k)
        ψ).leadingEigenprojection k'
    let Φ := sequentialTruncation P (L - 1) ψ
    IsOpenMPS L q k' (fun x ↦ Φ x) ∧
      ‖Φ - ψ‖ ≤ ((L - 1 : ℕ) : ℝ) *
        √(c * exp (2 / ξ) * ((k' : ℝ) / k₀) ^ (-1 / (ξ * log d))) := by
  intro P Φ
  obtain ⟨hmps, herr⟩ := isOpenMPS_sequentialTruncation_leadingEigenprojection ψ hψ k'
  refine ⟨hmps, herr.trans ?_⟩
  calc ∑ k ∈ Finset.Ico 1 L, √(1 -
        (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (leftBlock L k)
          ψ).kyFanNorm k')
      ≤ ∑ _k ∈ Finset.Ico 1 L,
          √(c * exp (2 / ξ) * ((k' : ℝ) / k₀) ^ (-1 / (ξ * log d))) :=
        Finset.sum_le_sum fun k hk ↦ sqrt_le_sqrt <|
          schmidtTail_le_rpow_of_geometric hd hξ hc hk₀ _ (hτ k hk) hk'
    _ = ((L - 1 : ℕ) : ℝ) * √(c * exp (2 / ξ) * ((k' : ℝ) / k₀) ^ (-1 / (ξ * log d))) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

end TNLean.MPS.AreaLaw.Hastings
