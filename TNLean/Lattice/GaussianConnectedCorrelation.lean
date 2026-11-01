/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GaussianGroundFrequencySeparation
import TNLean.Lattice.GaussianNegativeFrequencyLocality

/-!
# Ordinary ground correlations from actual Gaussian frequency separation

The actual regularized commutator converges to a scalar approximating the
ordinary ground correlation with the derived Gaussian gap error. Its norm
is uniformly bounded by the actual short-time propagation increment and
Gaussian tail. Passing this uniform bound to the actual scalar limit gives
the ordinary correlation estimate, rather than an estimate only for a
symmetric low-pass filter.

Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3. The actual local
Hamiltonian supplies the propagation input in the finite-ring caller.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix GaussianFilter Filter
open scoped Matrix.Norms.L2Operator InnerProductSpace NNReal Topology

namespace TNLean.Lattice

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "L" => Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)

/-- The actual ordinary correlation of a centered observable is bounded by
the derived Gaussian gap error and actual uniform frequency-locality
bound. The Cauchy regularizer is eliminated by the proved scalar limit.
No filtered-to-ordinary comparison or clustering estimate is assumed.
Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3. -/
theorem norm_centered_ground_correlation_le_gaussian
    {q Δ T C v : ℝ} (hq : 0 < q) (hΔ : 0 < Δ) (hT : 0 < T)
    (hC : 0 ≤ C) (hv : 0 ≤ v)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hgap : ∀ i, hH.eigenvalues i = E₀ ∨ E₀ + Δ ≤ hH.eigenvalues i)
    {ψ : EuclideanSpace ℂ n} (hψ : ψ ∈ groundEigenspace H E₀)
    (hline : groundEigenspace H E₀ = Submodule.span ℂ {ψ})
    (A B : Matrix n n ℂ) (hcenter : ⟪ψ, L A ψ⟫_ℂ = 0)
    (hLR : ∀ t : ℝ,
      ‖hermitianUnitaryPath H t * A * hermitianUnitaryPath H (-t) * B -
          B * (hermitianUnitaryPath H t * A * hermitianUnitaryPath H (-t))‖ ≤
        C * (Real.exp (v * |t|) - 1)) :
    let h := (q / Δ ^ 2).toNNReal
    ‖⟪ψ, L (A * B) ψ⟫_ℂ‖ ≤
      (2 * Real.exp (-q / 2) * ‖A‖ * ‖B‖ +
        kernel h⁻¹ 0 * (C * v * Real.exp (v * T) +
          (2 * ‖A‖ * ‖B‖ / T) * Real.exp (-T ^ 2 / (2 * (h : ℝ))))) * ‖ψ‖ ^ 2 := by
  let h := (q / Δ ^ 2).toNNReal
  let K := kernel h⁻¹ 0 * (C * v * Real.exp (v * T) +
    (2 * ‖A‖ * ‖B‖ / T) * Real.exp (-T ^ 2 / (2 * (h : ℝ))))
  obtain ⟨z, hlim, herror⟩ := exists_gaussianNegativeFrequency_ground_commutator_limit
    hq hΔ hH hgap hψ hline A B hcenter
  have hpoint (ε : ℝ) (hε : 0 < ε) :
      let F := gaussianNegativeFrequencyOperator h ε H A
      ‖⟪ψ, L (F * B - B * F) ψ⟫_ℂ‖ ≤ K * ‖ψ‖ ^ 2 := by
    let F := gaussianNegativeFrequencyOperator h ε H A
    have hcomm : ‖F * B - B * F‖ ≤ K :=
      norm_commutator_gaussianNegativeFrequencyOperator_le h hH A B hε hT hC hv hLR
    have hnorm (M : Matrix n n ℂ) : ‖L M ψ‖ ≤ ‖M‖ * ‖ψ‖ :=
      Matrix.l2_opNorm_mulVec M ψ
    calc
      _ ≤ ‖ψ‖ * ‖L (F * B - B * F) ψ‖ := norm_inner_le_norm _ _
      _ ≤ ‖ψ‖ * (‖F * B - B * F‖ * ‖ψ‖) :=
        mul_le_mul_of_nonneg_left (hnorm _) (norm_nonneg ψ)
      _ ≤ ‖ψ‖ * (K * ‖ψ‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcomm (norm_nonneg ψ)) (norm_nonneg ψ)
      _ = K * ‖ψ‖ ^ 2 := by ring
  have hz : ‖z‖ ≤ K * ‖ψ‖ ^ 2 := by
    apply le_of_tendsto hlim.norm
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hpoint ε hε
  calc
    _ = ‖(⟪ψ, L (A * B) ψ⟫_ℂ - z) + z‖ := by rw [sub_add_cancel]
    _ ≤ ‖⟪ψ, L (A * B) ψ⟫_ℂ - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ 2 * Real.exp (-q / 2) * ‖A‖ * ‖B‖ * ‖ψ‖ ^ 2 + K * ‖ψ‖ ^ 2 :=
      add_le_add herror hz
    _ = _ := by dsimp only [K]; ring

end TNLean.Lattice
