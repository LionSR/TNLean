/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Convex.Jensen
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef

/-!
# Diagonal Jensen inequality for positive semidefinite matrices

This file proves the **diagonal Jensen inequality** for a convex function
applied to a positive semidefinite matrix via the Hermitian continuous
functional calculus.

## Main result

* `Matrix.diagonal_jensen_of_convexOn`: for a convex `f : ℝ → ℝ` on
  `[0, ∞)`, a positive semidefinite matrix `A`, and a unit vector
  `v` (`star v ⬝ᵥ v = 1`):

    `f ((star v ⬝ᵥ (A *ᵥ v)).re) ≤ (star v ⬝ᵥ (f(A) *ᵥ v)).re`,

  where `f(A)` is computed via `Matrix.IsHermitian.cfc`.

## Proof sketch

Write `A = U * diagonal (λ) * Uᴴ` by the spectral theorem, and set
`w = Uᴴ *ᵥ v`. Since `U` is unitary, `∑ i, |w i|² = ‖v‖² = 1`, so the
family `p i := |w i|²` is a probability distribution over `Fin D`. The
eigenvalues `λ i` of the PSD matrix `A` lie in `[0, ∞)`. A direct
computation gives

  `(star v ⬝ᵥ (A *ᵥ v)).re = ∑ i, p i * λ i`,
  `(star v ⬝ᵥ (f(A) *ᵥ v)).re = ∑ i, p i * f (λ i)`,

so the scalar Jensen inequality `ConvexOn.map_sum_le` applied to the
weights `p` and points `λ` yields the conclusion.

This helper is a prerequisite for the trace convexity axioms
`trace_rpow_concave_axiom` and `trace_rpow_convex_axiom` in
`TNLean.Axioms.OperatorConvexity`.

## References

* Bhatia, *Matrix Analysis*, Ch. V (matrix Jensen inequality).
-/

open scoped Matrix ComplexOrder
open Finset Matrix

noncomputable section

namespace Matrix

variable {D : ℕ}

/-- **Diagonal Jensen inequality** for a convex function on a positive
semidefinite matrix.

For `f : ℝ → ℝ` convex on `[0, ∞)`, `A` positive semidefinite, and `v` a
unit vector (`star v ⬝ᵥ v = 1`):

  `f ((star v ⬝ᵥ (A *ᵥ v)).re) ≤ (star v ⬝ᵥ (f(A) *ᵥ v)).re`,

where `f(A)` is computed via `Matrix.IsHermitian.cfc`.

The proof reduces to the scalar Jensen inequality
`ConvexOn.map_sum_le` applied to the eigenvalues of `A` with weights
`|Uᴴ *ᵥ v i|²`. -/
theorem diagonal_jensen_of_convexOn
    [DecidableEq (Fin D)]
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici (0 : ℝ)) f)
    {A : Matrix (Fin D) (Fin D) ℂ} (hA : A.PosSemidef)
    {v : Fin D → ℂ} (hv : star v ⬝ᵥ v = (1 : ℂ)) :
    f ((star v ⬝ᵥ (A *ᵥ v)).re) ≤ (star v ⬝ᵥ (hA.1.cfc f *ᵥ v)).re := by
  classical
  -- Spectral data for `A`.
  set hH : A.IsHermitian := hA.1 with hH_def
  set U : Matrix (Fin D) (Fin D) ℂ := (↑hH.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)
    with hU_def
  set μ : Fin D → ℝ := hH.eigenvalues with hμ_def
  set w : Fin D → ℂ := Uᴴ *ᵥ v with hw_def
  set p : Fin D → ℝ := fun i => Complex.normSq (w i) with hp_def
  -- Unitarity of `U`: `U * Uᴴ = 1` and `Uᴴ * U = 1`.
  have hUUH : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.prop
  have hUHU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.UnitaryGroup.star_mul_self hH.eigenvectorUnitary
  -- Key computational lemma: for any `g : Fin D → ℂ`,
  --   `star v ⬝ᵥ ((U * diagonal g * Uᴴ) *ᵥ v) = ∑ i, g i * (star (w i) * w i)`.
  have hQ : ∀ g : Fin D → ℂ,
      star v ⬝ᵥ ((U * Matrix.diagonal g * Uᴴ) *ᵥ v)
        = ∑ i, g i * (star (w i) * w i) := by
    intro g
    have hvU : star v ᵥ* U = star w := by
      change star v ᵥ* U = star (Uᴴ *ᵥ v)
      rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
    have hmul :
        (U * Matrix.diagonal g * Uᴴ) *ᵥ v
          = U *ᵥ (Matrix.diagonal g *ᵥ (Uᴴ *ᵥ v)) := by
      rw [mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hmul]
    rw [show (U *ᵥ (Matrix.diagonal g *ᵥ (Uᴴ *ᵥ v)))
          = U *ᵥ (Matrix.diagonal g *ᵥ w) from rfl]
    rw [Matrix.dotProduct_mulVec, hvU]
    -- `star w ⬝ᵥ (diagonal g *ᵥ w) = ∑ i, star (w i) * (g i * w i)`.
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  -- `star (w i) * w i = ↑(p i)` (Complex norm-square identity).
  have h_normSq : ∀ i, star (w i) * w i = ((p i : ℝ) : ℂ) := by
    intro i
    have := Complex.normSq_eq_conj_mul_self (z := w i)
    -- `(normSq (w i) : ℂ) = conj (w i) * w i = star (w i) * w i`.
    simpa [hp_def, Complex.star_def] using this.symm
  -- Spectral form of `A`.
  have hA_spec : A = U * Matrix.diagonal (fun i => ((μ i : ℂ))) * Uᴴ := by
    have h := hH.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      hU_def, hμ_def] using h
  -- Spectral form of `hH.cfc f`.
  have hfA_spec : hH.cfc f
      = U * Matrix.diagonal (fun i => ((f (μ i) : ℂ))) * Uᴴ := by
    unfold IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply, ← Matrix.star_eq_conjTranspose]
    rfl
  -- `⟨v, A v⟩` as a complex sum of `μ i * p i`.
  have h_vAv : star v ⬝ᵥ (A *ᵥ v)
      = ∑ i, ((μ i : ℂ) * ((p i : ℝ) : ℂ)) := by
    rw [hA_spec, hQ]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_normSq i]
  -- `⟨v, f(A) v⟩` as a complex sum of `f(μ i) * p i`.
  have h_vfAv : star v ⬝ᵥ (hH.cfc f *ᵥ v)
      = ∑ i, (((f (μ i) : ℝ) : ℂ) * ((p i : ℝ) : ℂ)) := by
    rw [hfA_spec, hQ]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_normSq i]
  -- Real parts: `(star v ⬝ᵥ (A *ᵥ v)).re = ∑ i, μ i * p i`.
  have h_vAv_re : (star v ⬝ᵥ (A *ᵥ v)).re = ∑ i, μ i * p i := by
    rw [h_vAv]
    rw [show (∑ i, ((μ i : ℂ) * ((p i : ℝ) : ℂ)))
          = (((∑ i, μ i * p i) : ℝ) : ℂ) by push_cast; rfl]
    simp
  have h_vfAv_re : (star v ⬝ᵥ (hH.cfc f *ᵥ v)).re = ∑ i, f (μ i) * p i := by
    rw [h_vfAv]
    rw [show (∑ i, (((f (μ i) : ℝ) : ℂ) * ((p i : ℝ) : ℂ)))
          = (((∑ i, f (μ i) * p i) : ℝ) : ℂ) by push_cast; rfl]
    simp
  -- `∑ i, p i = 1` (unit vector + unitarity).
  have hp_sum : ∑ i, p i = 1 := by
    -- `∑ i, (p i : ℂ) = star w ⬝ᵥ w = star v ⬝ᵥ v = 1`.
    have hstar_w : star w = star v ᵥ* U := by
      change star (Uᴴ *ᵥ v) = star v ᵥ* U
      rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
    have hww : star w ⬝ᵥ w = (1 : ℂ) := by
      rw [hstar_w]
      calc (star v ᵥ* U) ⬝ᵥ w
          = star v ⬝ᵥ (U *ᵥ w) := by rw [← Matrix.dotProduct_mulVec]
        _ = star v ⬝ᵥ (U *ᵥ (Uᴴ *ᵥ v)) := rfl
        _ = star v ⬝ᵥ ((U * Uᴴ) *ᵥ v) := by rw [Matrix.mulVec_mulVec]
        _ = star v ⬝ᵥ ((1 : Matrix (Fin D) (Fin D) ℂ) *ᵥ v) := by rw [hUUH]
        _ = star v ⬝ᵥ v := by rw [Matrix.one_mulVec]
        _ = 1 := hv
    have hsum_c : (∑ i, ((p i : ℝ) : ℂ)) = (1 : ℂ) := by
      rw [← hww]
      simp only [dotProduct, Pi.star_apply]
      refine Finset.sum_congr rfl (fun i _ => (h_normSq i).symm)
    exact_mod_cast hsum_c
  -- Eigenvalues are nonneg: `μ i ∈ [0, ∞)`.
  have hμ_nonneg : ∀ i, μ i ∈ Set.Ici (0 : ℝ) := fun i => hA.eigenvalues_nonneg i
  -- Apply scalar Jensen.
  have hp_nn : ∀ i ∈ (Finset.univ : Finset (Fin D)), 0 ≤ p i :=
    fun i _ => Complex.normSq_nonneg _
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin D)),
      μ i ∈ Set.Ici (0 : ℝ) := fun i _ => hμ_nonneg i
  have hjensen := hf.map_sum_le (t := Finset.univ) hp_nn hp_sum hmem
  simp only [smul_eq_mul] at hjensen
  rw [h_vAv_re, h_vfAv_re]
  -- Match `∑ p i * μ i` with `∑ μ i * p i` (and similarly for `f`).
  have eq1 : ∑ i, p i * μ i = ∑ i, μ i * p i :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have eq2 : ∑ i, p i * f (μ i) = ∑ i, f (μ i) * p i :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [← eq1, ← eq2]
  exact hjensen

end Matrix

end
