/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.Algebra
import TNLean.Channel.FixedPoint.CanonicalGauge
import TNLean.MPS.Core.TPGauge

/-!
# Corollaries on weighted fixed-point algebras

This file proves Wolf Corollary 6.7 for the Schrödinger-picture fixed-point
space of a trace-preserving Kraus map.

Given a positive-definite fixed point $\rho$ of the map
$T(X) = \sum_i K_i X K_i^\dagger$, the similarity-transformed Kraus family
$\rho^{-1/2} K_i \rho^{1/2}$ is unital. Applying Wolf Theorem 6.12 to that
unital family shows that the conjugated fixed-point space
$\rho^{-1/2} \Fix(T) \rho^{-1/2}$ is a `StarSubalgebra` of `M_D(\mathbb{C})`.

## Main declarations

* `Kraus.rightCanonicalGauge`: the Kraus family `ρ^{-1/2} K_i ρ^{1/2}`.
* `Kraus.weightedFixedPointsStarSubalgebra`: Wolf Corollary 6.7.
* `Kraus.mem_weightedFixedPointsStarSubalgebra_iff`: membership is equivalent
  to saying that `ρ^{1/2} X ρ^{1/2}` is fixed by the original map.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Corollary 6.7, Section 6.4]
-/

open scoped Matrix ComplexOrder MatrixOrder TNMatrixCFC BigOperators
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The right-canonical gauge `ρ^{-1/2} K_i ρ^{1/2}` attached to a positive
fixed point `ρ`. -/
noncomputable def rightCanonicalGauge (K : Fin d → Mat) (ρ : Mat) : Fin d → Mat :=
  fun i => (CFC.sqrt ρ)⁻¹ * K i * CFC.sqrt ρ

/-- The Kraus map of the right-canonical gauge is the similarity transform of
`map K` by `ρ^{1/2}`. -/
theorem map_rightCanonicalGauge
    (K : Fin d → Mat) (ρ : Mat) (X : Mat) :
    map (rightCanonicalGauge K ρ) X =
      (CFC.sqrt ρ)⁻¹ * map K (CFC.sqrt ρ * X * CFC.sqrt ρ) * (CFC.sqrt ρ)⁻¹ := by
  set S : Mat := CFC.sqrt ρ
  have hS_herm : Sᴴ = S := by
    simpa [S] using MPSTensor.conjTranspose_cfc_sqrt (D := D) ρ
  calc
    map (rightCanonicalGauge K ρ) X
        = ∑ i : Fin d, (S⁻¹ * K i * S) * X * (S⁻¹ * K i * S)ᴴ := by
            simp [map, rightCanonicalGauge, S]
    _ = ∑ i : Fin d, S⁻¹ * (K i * (S * X * S) * (K i)ᴴ) * S⁻¹ := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_nonsing_inv]
          simp [Matrix.mul_assoc, hS_herm]
    _ = (∑ i : Fin d, S⁻¹ * (K i * (S * X * S) * (K i)ᴴ)) * S⁻¹ := by
          rw [← Finset.sum_mul]
    _ = S⁻¹ * (∑ i : Fin d, K i * (S * X * S) * (K i)ᴴ) * S⁻¹ := by
          rw [← Finset.mul_sum]
    _ = S⁻¹ * map K (S * X * S) * S⁻¹ := by
          simp [map, Matrix.mul_assoc, S]

/-- A matrix is fixed by the right-canonical gauge exactly when its conjugate by
`ρ^{1/2}` is fixed by the original map. -/
theorem map_rightCanonicalGauge_eq_iff
    (K : Fin d → Mat) {ρ : Mat} (hρ : ρ.PosDef) (X : Mat) :
    map (rightCanonicalGauge K ρ) X = X ↔
      map K (CFC.sqrt ρ * X * CFC.sqrt ρ) = CFC.sqrt ρ * X * CFC.sqrt ρ := by
  set S : Mat := CFC.sqrt ρ
  have hS_det : IsUnit S.det := by
    simpa [S] using MPSTensor.isUnit_det_cfc_sqrt_of_posDef (D := D) ρ hρ
  have hSinv_mul : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hS_det
  have hSmul_inv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hS_det
  have hmap : map (rightCanonicalGauge K ρ) X = S⁻¹ * map K (S * X * S) * S⁻¹ := by
    simpa [S] using map_rightCanonicalGauge (K := K) ρ X
  constructor
  · intro h
    have h2 : S⁻¹ * map K (S * X * S) = X * S := by
      calc
        S⁻¹ * map K (S * X * S)
            = (S⁻¹ * map K (S * X * S)) * (S⁻¹ * S) := by rw [hSinv_mul, Matrix.mul_one]
        _ = ((S⁻¹ * map K (S * X * S)) * S⁻¹) * S := by simp [Matrix.mul_assoc]
        _ = X * S := by rw [← hmap, h]
    have h3 : map K (S * X * S) = S * (X * S) := by
      calc
        map K (S * X * S) = (S * S⁻¹) * map K (S * X * S) := by rw [hSmul_inv, Matrix.one_mul]
        _ = S * (S⁻¹ * map K (S * X * S)) := by simp [Matrix.mul_assoc]
        _ = S * (X * S) := by rw [h2]
    simpa [Matrix.mul_assoc] using h3
  · intro h
    calc
      map (rightCanonicalGauge K ρ) X = S⁻¹ * map K (S * X * S) * S⁻¹ := hmap
      _ = S⁻¹ * (S * X * S) * S⁻¹ := by rw [h]
      _ = (S⁻¹ * S) * X * (S * S⁻¹) := by simp [Matrix.mul_assoc]
      _ = X := by simp [hSinv_mul, hSmul_inv]
/-- The right-canonical gauge is unital when `ρ` is a fixed point of the
original Schrödinger map. -/
theorem isUnital_rightCanonicalGauge
    (K : Fin d → Mat) {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ) :
    IsUnital (rightCanonicalGauge K ρ) := by
  set S : Mat := CFC.sqrt ρ
  have hS_det : S.det ≠ 0 := by
    exact (MPSTensor.isUnit_det_cfc_sqrt_of_posDef (D := D) ρ hρ).ne_zero
  have hS_herm : Sᴴ = S := by
    simpa [S] using MPSTensor.conjTranspose_cfc_sqrt (D := D) ρ
  have hSS : S * Sᴴ = ρ := by
    calc
      S * Sᴴ = S * S := by rw [hS_herm]
      _ = ρ := by
            simpa [S] using MPSTensor.cfc_sqrt_mul_self_of_posDef (D := D) ρ hρ
  have hρ_fix_transfer : MPSTensor.transferMap (d := d) (D := D) K ρ = ρ := by
    simpa [map, MPSTensor.transferMap_apply] using hρ_fix
  simpa [IsUnital, rightCanonicalGauge, S, hS_herm, Matrix.mul_assoc] using
    (gauged_unital (A := K) (S := S) (ρ := ρ) hS_det hSS hρ_fix_transfer)

/-- The original positive-definite fixed point `ρ` is fixed by the adjoint map
of the right-canonical gauge whenever `K` is trace-preserving. -/
theorem adjointMap_rightCanonicalGauge_fixedPoint
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat} (hρ : ρ.PosDef) :
    adjointMap (rightCanonicalGauge K ρ) ρ = ρ := by
  set S : Mat := CFC.sqrt ρ
  have hGauge : rightCanonicalGauge K ρ = fun i => S⁻¹ * K i * S := by
    ext i
    simp [rightCanonicalGauge, S]
  have hS_det : IsUnit S.det := by
    simpa [S] using MPSTensor.isUnit_det_cfc_sqrt_of_posDef (D := D) ρ hρ
  have hS_herm : Sᴴ = S := by
    simpa [S] using MPSTensor.conjTranspose_cfc_sqrt (D := D) ρ
  have hSS : S * S = ρ := by
    simpa [S] using MPSTensor.cfc_sqrt_mul_self_of_posDef (D := D) ρ hρ
  have hSinv_mul : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hS_det
  have hSmul_inv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hS_det
  rw [hGauge]
  have h_term :
      ∀ i : Fin d,
        (S⁻¹ * K i * S)ᴴ * (S * S) * (S⁻¹ * K i * S) = S * (K i)ᴴ * K i * S := by
    intro i
    calc
      (S⁻¹ * K i * S)ᴴ * (S * S) * (S⁻¹ * K i * S)
          = Sᴴ * (K i)ᴴ * (Sᴴ)⁻¹ * (S * S) * S⁻¹ * K i * S := by
              rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
                Matrix.conjTranspose_nonsing_inv]
              simp [Matrix.mul_assoc]
      _ = S * (K i)ᴴ * K i * S := by
            rw [hS_herm]
            simp [Matrix.mul_assoc, hSinv_mul, hSmul_inv]
  have hcalc : adjointMap (fun i => S⁻¹ * K i * S) (S * S) = S * S := by
    calc
      adjointMap (fun i => S⁻¹ * K i * S) (S * S)
          = ∑ i : Fin d, (S⁻¹ * K i * S)ᴴ * (S * S) * (S⁻¹ * K i * S) := by
              simp [adjointMap]
      _ = ∑ i : Fin d, S * (K i)ᴴ * K i * S := by
            exact Finset.sum_congr rfl (fun i _ => h_term i)
      _ = (∑ i : Fin d, S * ((K i)ᴴ * K i)) * S := by
            simp [Matrix.mul_assoc, Finset.sum_mul]
      _ = S * (∑ i : Fin d, (K i)ᴴ * K i) * S := by
            simp [Finset.mul_sum]
      _ = S * S := by rw [h_tp, Matrix.mul_one]
  simpa [hSS] using hcalc

/-- **Wolf Corollary 6.7**.

If `T(X) = ∑ i, K_i X K_i†` is trace-preserving and `ρ > 0` is a fixed point of
`T`, then `ρ^{-1/2} Fix(T) ρ^{-1/2}` is a `*`-subalgebra of `M_D(ℂ)`. -/
noncomputable def weightedFixedPointsStarSubalgebra
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat}
    (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ) :
    StarSubalgebra ℂ Mat :=
  fixedPointsStarSubalgebra
    (K := rightCanonicalGauge K ρ)
    (h_unital := isUnital_rightCanonicalGauge (K := K) hρ hρ_fix)
    (ρ := ρ) hρ
    (adjointMap_rightCanonicalGauge_fixedPoint (K := K) h_tp hρ)

@[simp] theorem mem_weightedFixedPointsStarSubalgebra_iff
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat}
    (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ) (X : Mat) :
    X ∈ weightedFixedPointsStarSubalgebra (K := K) h_tp hρ hρ_fix ↔
      map K (CFC.sqrt ρ * X * CFC.sqrt ρ) = CFC.sqrt ρ * X * CFC.sqrt ρ := by
  change map (rightCanonicalGauge K ρ) X = X ↔
    map K (CFC.sqrt ρ * X * CFC.sqrt ρ) = CFC.sqrt ρ * X * CFC.sqrt ρ
  exact map_rightCanonicalGauge_eq_iff (K := K) (ρ := ρ) hρ X

end Kraus
