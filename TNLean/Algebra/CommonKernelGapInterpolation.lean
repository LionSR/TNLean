/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Gap comparison along an ordered interpolation

For positive semidefinite finite matrices with the same kernel, adding a
positive operator cannot reduce a lower quadratic-form bound on the
orthogonal complement of that kernel. The result applies to interpolation
between a bond-product interaction and a larger parent interaction.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace Matrix

/-- Interpolation with a larger positive semidefinite matrix preserves the
kernel and a lower quadratic-form bound on its orthogonal complement. -/
theorem gap_interpolation_of_le {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hAB : A ≤ B)
    (hker : ∀ x : n → ℂ, A *ᵥ x = 0 → B *ᵥ x = 0)
    (δ t : ℝ) (ht : 0 ≤ t)
    (hgap : ∀ x : EuclideanSpace ℂ n,
      x ∈ (LinearMap.ker (Matrix.toEuclideanLin A))ᗮ →
      δ * (∑ i, Complex.normSq (x i)) ≤
        (star x.ofLp ⬝ᵥ (A *ᵥ x.ofLp)).re) :
    let C := A + t • (B - A)
    C.PosSemidef ∧
    (LinearMap.ker (Matrix.toEuclideanLin C) =
      LinearMap.ker (Matrix.toEuclideanLin A)) ∧
    ∀ x : EuclideanSpace ℂ n,
      x ∈ (LinearMap.ker (Matrix.toEuclideanLin C))ᗮ →
      δ * (∑ i, Complex.normSq (x i)) ≤
        (star x.ofLp ⬝ᵥ (C *ᵥ x.ofLp)).re := by
  dsimp only
  have hAC : A ≤ A + t • (B - A) := by
    rw [le_iff]
    simpa using (le_iff.mp hAB).smul ht
  have hC : (A + t • (B - A)).PosSemidef :=
    (Matrix.nonneg_iff_posSemidef.mp (le_trans (Matrix.nonneg_iff_posSemidef.mpr hA) hAC))
  have hD : (t • (B - A)).PosSemidef := (le_iff.mp hAB).smul ht
  have hkerEq :
      LinearMap.ker (Matrix.toEuclideanLin (A + t • (B - A))) =
        LinearMap.ker (Matrix.toEuclideanLin A) := by
    apply Submodule.ext
    intro x
    simp only [LinearMap.mem_ker]
    constructor
    · intro hx
      simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply,
        WithLp.toLp_eq_zero] at hx ⊢
      have hsum :
          star x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) +
            star x.ofLp ⬝ᵥ ((t • (B - A)) *ᵥ x.ofLp) = 0 := by
        simpa only [Matrix.add_mulVec, dotProduct_add, dotProduct_zero] using
          congrArg (fun v => star x.ofLp ⬝ᵥ v) hx
      have hA0 : star x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) = 0 := by
        apply le_antisymm _ (hA.dotProduct_mulVec_nonneg _)
        rw [← hsum]
        exact le_add_of_nonneg_right (hD.dotProduct_mulVec_nonneg _)
      exact hA.dotProduct_mulVec_zero_iff.mp hA0
    · intro hx
      simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply,
        WithLp.toLp_eq_zero] at hx ⊢
      have hBx := hker x.ofLp hx
      simp [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec,
        hx, hBx]
  refine ⟨hC, hkerEq, ?_⟩
  intro x hx
  have hxA : x ∈ (LinearMap.ker (Matrix.toEuclideanLin A))ᗮ := by
    simpa only [hkerEq] using hx
  have hbase := hgap x hxA
  have hd : 0 ≤ (star x.ofLp ⬝ᵥ ((t • (B - A)) *ᵥ x.ofLp)).re :=
    (RCLike.nonneg_iff.mp (hD.dotProduct_mulVec_nonneg x.ofLp)).1
  calc
    δ * (∑ i, Complex.normSq (x i)) ≤
        (star x.ofLp ⬝ᵥ (A *ᵥ x.ofLp)).re := hbase
    _ ≤ (star x.ofLp ⬝ᵥ ((A + t • (B - A)) *ᵥ x.ofLp)).re := by
      rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
      exact le_add_of_nonneg_right hd

end Matrix
