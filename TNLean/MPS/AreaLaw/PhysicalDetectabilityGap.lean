/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.KernelSpectralGap
import TNLean.MPS.AreaLaw.PhysicalDetectability

/-!
# Detectability above the full zero-energy kernel

The physical even/odd product preserves the orthogonal complement of the
whole kernel. A gap in the actual real spectrum gives a quadratic-form
lower bound there, and hence the same contraction in arbitrary ground
multiplicity. This supports ALVV, arXiv:1602.08828v2, `lem:dl` and
`thm:FF-tH`, lines 1508–1519 and 1562–1568.

The local terms are orthogonal projections. The reduction from general positive contractions is proved in
`PhysicalRangeDetectability.lean`. The regional truncated Hamiltonian
remains a separate construction.
-/

open Matrix
open scoped BigOperators InnerProductSpace

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- A lower bound for the nonzero spectrum contracts the orthogonal complement
of the entire zero-energy kernel. No ground-space dimension or upper-gap bound is assumed.
ALVV, arXiv:1602.08828v2, `lem:dl` and `thm:FF-tH`, lines 1508–1519 and 1562–1568. -/
theorem norm_sq_physicalDetectability_le_of_spectral_gap
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hp : ∀ i, IsStarProjection (h i))
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ e ∈ spectrum ℝ (∑ i, h i), e = 0 ∨ gamma ≤ e)
    {x : EuclideanSpace ℂ (Fin L → Fin q)}
    (horth : ∀ z : EuclideanSpace ℂ (Fin L → Fin q),
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (∑ i, h i) z = 0 →
        ⟪z, x⟫_ℂ = 0) :
    ‖physicalDetectability h x‖ ^ 2 ≤ (4 / (4 + gamma)) * ‖x‖ ^ 2 := by
  have hH : (∑ i, h i).IsHermitian :=
    (isSelfAdjoint_sum _ fun i _ ↦ (hp i).isSelfAdjoint).isHermitian
  set y := physicalDetectability h x
  have hyorth (z : EuclideanSpace ℂ (Fin L → Fin q))
      (hz : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (∑ i, h i) z = 0) :
      ⟪z, y⟫_ℂ = 0 :=
    (inner_physicalDetectability_eq h hp hs hz x).trans (horth z hz)
  have hlo := hH.mul_norm_sq_le_re_inner_of_spectral_gap hgap y hyorth
  have henergy : (⟪y, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (∑ i, h i) y⟫_ℂ).re ≤ 4 * (‖x‖ ^ 2 - ‖y‖ ^ 2) :=
    re_inner_physicalDetectability_le h hp hs x
  rw [div_mul_eq_mul_div, le_div_iff₀ (show 0 < 4 + gamma by linarith only [hgamma])]
  nlinarith only [hlo, henergy]

end TNLean.MPS.AreaLaw
