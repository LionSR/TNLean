/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.PhysicalStringAsymptotics

/-!
# Geometric finite-length bounds for physical strings

The contracting branch of arXiv:0802.0447, lines 241–243, has a geometric bound
at every prescribed rate strictly above the twisted spectral radius. In the
symmetry branch, the phase-adjusted string differs from the product of its
physical endpoint coefficients by a geometrically decaying error. These bounds
retain Jordan blocks and the length-dependent peripheral phase.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder TNOperatorSpace NNReal ENNReal

namespace MPSTensor

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- At every rate above the twisted spectral radius the physical string is
geometrically bounded, including zero middle length. Taking the rate below one
proves the exponential decay in arXiv:0802.0447, lines 241–243. -/
theorem physicalStringOrderParam_le_geometric
    (A : MPSTensor d D) (Λ : Mat) (x y u : Matrix (Fin d) (Fin d) ℂ)
    (rate : ℝ≥0) (hRate : spectralRadius ℂ
      (Module.End.toContinuousLinearMap Mat (twistedTransferMap A u)) <
        (rate : ℝ≥0∞)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖physicalStringOrderParam A Λ x y u N‖ ≤ C * (rate : ℝ) ^ N := by
  obtain ⟨C, hC, hpow⟩ := geometric_apply_bound_of_spectralRadius_lt
    (Module.End.toContinuousLinearMap Mat (twistedTransferMap A u)) rate hRate
  let ℓ : Mat →L[ℂ] ℂ := ((Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
    ((LinearMap.mulLeft ℂ Λ).comp (twistedTransferMap A x))).toContinuousLinearMap
  let Y := twistedTransferMap A y 1
  obtain ⟨M, hM, hℓ⟩ := ℓ.bound
  refine ⟨M * C * ‖Y‖ + 1, by positivity, fun N => ?_⟩
  have hp : ‖twistedTransferIter A u N Y‖ ≤ C * (rate : ℝ) ^ N * ‖Y‖ := by
    have h := hpow N Y
    rw [← map_pow] at h
    exact h
  exact (hℓ (twistedTransferIter A u N Y)).trans
    ((mul_le_mul_of_nonneg_left hp hM.le).trans (by
      nlinarith [pow_nonneg rate.coe_nonneg N]))

/-- In the canonical pure regime the physical endpoint coefficient formula
has a geometric error after removing the peripheral phase. The rate is
independent of the fixed endpoints. Source: arXiv:0802.0447, lines 249–255,
with the phase qualification recorded in
`docs/paper-gaps/pgwsvc08_string_order_virtual_boundary.tex`. -/
theorem physicalStringOrderParam_phase_adjusted_le_geometric
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (hPrim : IsPrimitive (Kraus.transferMap A))
    (Λ : Mat) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (u : Matrix (Fin d) (Fin d) ℂ) (V : Mat) (μ : ℂ)
    (hV : V * Vᴴ = 1) (hμ : ‖μ‖ = 1)
    (hInter : ∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ)) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x y : Matrix (Fin d) (Fin d) ℂ,
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
        ‖(μ ^ N)⁻¹ * physicalStringOrderParam A Λ x y u N -
          Matrix.trace (Λ * Vᴴ * twistedTransferMap A y 1) *
            Matrix.trace (Λ * twistedTransferMap A x V)‖ ≤ C * r ^ N := by
  obtain ⟨C, r, hC, hr, hr1, hpow⟩ :=
    canonical_transfer_pow_sub_stationary_le_geometric
      A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm
  refine ⟨r, hr, hr1, fun x y => ?_⟩
  let ℓ : Mat →ₗ[ℂ] ℂ := (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
    ((LinearMap.mulLeft ℂ Λ).comp
      ((twistedTransferMap A x).comp (LinearMap.mulLeft ℂ V)))
  have hℓ_apply (Z : Mat) : ℓ Z = Matrix.trace (Λ * twistedTransferMap A x (V * Z)) := rfl
  let Y := Vᴴ * twistedTransferMap A y 1
  obtain ⟨M, hM, hℓ⟩ := ℓ.toContinuousLinearMap.bound
  refine ⟨M * C * ‖Y‖ + 1, by positivity, fun N hN => ?_⟩
  have hphase : (μ ^ N)⁻¹ * physicalStringOrderParam A Λ x y u N =
      ℓ ((Kraus.transferMap A ^ N) Y) := by
    simp only [physicalStringOrderParam,
      twistedTransferIter_eq_phase_mul_transfer_pow A u V μ hV hInter,
      map_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero N
      (Complex.ne_zero_of_norm_eq_one hμ)), one_mul]
    rfl
  have hlimit : ℓ (fnwLimitMap Λ (by simp [hΛtr]) Y) =
      Matrix.trace (Λ * Vᴴ * twistedTransferMap A y 1) *
        Matrix.trace (Λ * twistedTransferMap A x V) := by
    rw [fnwLimitMap_apply_of_trace_eq_one Λ Y hΛtr, map_smul, hℓ_apply, smul_eq_mul]
    simp only [Y, Matrix.mul_one, Matrix.mul_assoc]
  rw [hphase, ← hlimit, ← map_sub]
  have hp := (Module.End.toContinuousLinearMap Mat
    (Kraus.transferMap A ^ N - fnwLimitMap Λ (by simp [hΛtr]))).le_of_opNorm_le
      (hpow N hN) Y
  change ‖(Kraus.transferMap A ^ N) Y - fnwLimitMap Λ _ Y‖ ≤ C * r ^ N * ‖Y‖ at hp
  exact (hℓ _).trans ((mul_le_mul_of_nonneg_left hp hM.le).trans (by
    nlinarith [pow_nonneg hr.le N]))

end MPSTensor
