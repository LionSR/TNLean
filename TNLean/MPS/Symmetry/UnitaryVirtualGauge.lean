/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.EntanglementSpectrum
import QICLean.Channel.PerronFrobenius.Existence
import TNLean.MPS.Core.PhysicalRotation
import TNLean.Tactic.MatrixReciprocalSmul

/-!
# Unitary virtual gauges from unital normalization

For a one-site injective tensor normalized by `E(1) = 1`, a positive definite
adjoint fixed point follows from Perron--Frobenius theory: the adjoint Perron
eigenvalue is one by trace duality. Thus a virtual gauge implementing a unitary
physical symmetry can be replaced by a unitary gauge without assuming a
boundary fixed point as additional data.

Source: arXiv:1010.3732, Section II.C, “Isometric form and symmetries”;
arXiv:2011.12127, Section III.A, lines 1084 and 1171.

## References

- [arXiv:1010.3732](https://arxiv.org/abs/1010.3732) -- Schuch,
  Pérez-García, Cirac, *Classifying quantum phases using matrix product
  states and projected entangled pair states*, Section II.C
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Perez-Garcia,
  Schuch, Verstraete, *Matrix Product States and Projected Entangled Pair
  States: Concepts, Symmetries, and Theorems*, Section III.A
- [arXiv:quant-ph/0608197](https://arxiv.org/abs/quant-ph/0608197) -- Pérez-García,
  Verstraete, Wolf, Cirac, *Matrix Product State Representations*
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPSTensor

/-- Unital normalization and injectivity supply the positive definite adjoint
fixed point of the canonical tensor. Source: arXiv:quant-ph/0608197,
Theorem `Th:TIcanonical`, proof lines 827--832. -/
theorem exists_posDef_adjoint_fixedPoint_of_isInjective_unital
    {d D : ℕ} [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsInjective A) (hNorm : Kraus.transferMap A 1 = 1) :
    ∃ Λ : Matrix (Fin D) (Fin D) ℂ,
      Λ.PosDef ∧ Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ := by
  obtain ⟨Λ, r, hΛ, _, hEig⟩ := Kraus.exists_posDef_adjoint_eigenvector A
    (Kraus.injective_implies_irreducibleCP A hA)
    (exists_apply_ne_zero_of_isNormal hA.isNormal)
  have hTrace := Kraus.trace_mul_mapLM_adjoint A rfl Λ 1
  have htr : Λ.trace ≠ 0 := hΛ.trace_pos.ne'
  have hr : (r : ℂ) = 1 := mul_right_cancel₀ htr (by
    simpa [hNorm, hEig, Matrix.trace_smul, smul_eq_mul] using hTrace.symm)
  exact ⟨Λ, hΛ, by simpa [hr] using hEig⟩

/-- A unitary physical rotation of a unital injective tensor, when it is a
virtual gauge change, is implemented by a unitary bond matrix. Source:
arXiv:1010.3732, Section II.C, “Isometric form and symmetries”. -/
theorem exists_unitary_covariance_of_isInjective_unital
    {d D : ℕ} [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsInjective A) (hNorm : Kraus.transferMap A 1 = 1)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hCov : GaugeEquiv A (rotatePhysical U A)) :
    ∃ W : Matrix.unitaryGroup (Fin D) ℂ,
      rotatePhysical U A = fun i => (W : Matrix (Fin D) (Fin D) ℂ) * A i *
        (W : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  obtain ⟨Λ, hΛ, hFix⟩ := exists_posDef_adjoint_fixedPoint_of_isInjective_unital hA hNorm
  obtain ⟨X, hX⟩ := hCov
  obtain ⟨W, hWW, hW'W, _, c, hc, hXW⟩ := exists_unitary_gauge_of_symmetry
    hA hNorm hΛ hFix ((Matrix.mem_unitaryGroup_iff).mp hU)
    (ζ := 1) one_ne_zero (fun i => by simpa only [one_smul, rotatePhysical_apply] using hX i)
  have hInv : ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) = c⁻¹ • Wᴴ := by
    have hMul : W * ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) = c⁻¹ • 1 := by
      have h := congrArg (c⁻¹ • ·) (show
        (X : Matrix (Fin D) (Fin D) ℂ) *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) = 1 by simp)
      rw [hXW] at h
      simpa (disch := exact hc) only [matrix_reciprocal_smul] using h
    calc
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
          Wᴴ * (W * ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
            rw [← Matrix.mul_assoc, hW'W, Matrix.one_mul]
      _ = c⁻¹ • Wᴴ := by rw [hMul, Matrix.mul_smul, Matrix.mul_one]
  refine ⟨⟨W, Matrix.mem_unitaryGroup_iff.mpr hWW⟩, ?_⟩
  funext i
  rw [hX i, hXW, hInv]
  simp (disch := exact hc) only [matrix_reciprocal_smul]

end MPSTensor
