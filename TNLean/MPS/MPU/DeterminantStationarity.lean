/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import QICLean.Analysis.HermitianMatrixCone

/-!
# Stationarity of determinant maxima

The determinant normalization in
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5, uses the
first-order condition at a positive definite determinant maximizer.
This module proves the directional derivative and its local-maximum
consequence. Existence of the maximizer and the quantum-circuit construction
are separate statements.
-/

open scoped Matrix ComplexOrder Topology

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma eval_det_one_add_X_smul (M : Matrix n n ℂ) (z : ℂ) :
    (det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C)).eval z =
      (1 + z • M).det := by
  change (Polynomial.evalRingHom z) (det _) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [RingHom.mapMatrix, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  simp [apply_ite, mul_comm]

/-- The directional determinant derivative at the identity.

This is the first derivative identity used in
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem hasDerivAt_det_one_add_smul (M : Matrix n n ℂ) :
    HasDerivAt (fun z : ℂ => (1 + z • M).det) M.trace 0 := by
  convert (Polynomial.hasDerivAt
    (det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C)) 0) using 1
  · exact funext fun z => (eval_det_one_add_X_smul M z).symm
  · exact (derivative_det_one_add_X_smul M).symm

private lemma det_add_smul_eq (P H : Matrix n n ℂ) (hP : IsUnit P.det) (z : ℂ) :
    (P + z • H).det = P.det * (1 + z • (P⁻¹ * H)).det := by
  rw [← det_mul]
  simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
    mul_nonsing_inv_cancel_left P H hP]

/-- Jacobi's directional determinant formula at a nonsingular complex matrix.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem hasDerivAt_det_add_smul (P H : Matrix n n ℂ) (hP : IsUnit P.det) :
    HasDerivAt (fun z : ℂ => (P + z • H).det)
      (P.det * (P⁻¹ * H).trace) 0 := by
  convert (hasDerivAt_det_one_add_smul (P⁻¹ * H)).const_mul P.det using 1
  exact funext (det_add_smul_eq P H hP)

omit [DecidableEq n] in
/-- The trace pairing of two Hermitian matrices is real.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem IsHermitian.star_trace_mul_eq {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    star (A * B).trace = (A * B).trace := by
  rw [← trace_conjTranspose, conjTranspose_mul, hA.eq, hB.eq, trace_mul_comm]

/-- A local determinant maximum in a Hermitian direction has zero inverse-trace pairing.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem trace_nonsing_inv_mul_eq_zero_of_isLocalMax_det
    (P H : Matrix n n ℂ) (hP : P.IsHermitian) (hdet : IsUnit P.det)
    (hH : H.IsHermitian)
    (hmax : IsLocalMax (fun t : ℝ => (P + (t : ℂ) • H).det.re) 0) :
    (P⁻¹ * H).trace = 0 := by
  have hder : HasDerivAt (fun t : ℝ => (P + (t : ℂ) • H).det.re)
      (P.det * (P⁻¹ * H).trace).re 0 := by
    simpa using (hasDerivAt_det_add_smul P H hdet).real_of_complex (z := 0)
  have hzero : (P.det * (P⁻¹ * H).trace).re = 0 := hmax.hasDerivAt_eq_zero hder
  have hstar : star (P.det * (P⁻¹ * H).trace) = P.det * (P⁻¹ * H).trace := by
    rw [star_mul, ← det_conjTranspose, hP.eq, hP.inv.star_trace_mul_eq hH, mul_comm]
  have hprod : P.det * (P⁻¹ * H).trace = 0 := by
    simpa only [hzero, Complex.ofReal_zero] using (Complex.conj_eq_iff_re.mp hstar).symm
  exact (mul_eq_zero.mp hprod).resolve_left (isUnit_iff_ne_zero.mp hdet)

open SemidefiniteProgram.HermitianMatrix

omit [Fintype n] [DecidableEq n] in variable [Finite n] in
/-- Positive definiteness persists under sufficiently small real Hermitian perturbations.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem PosDef.eventually_posDef_add_real_smul {P H : Matrix n n ℂ}
    (hP : P.PosDef) (hH : H.IsHermitian) :
    ∀ᶠ t : ℝ in 𝓝 0, (P + (t : ℂ) • H).PosDef := by
  let := Fintype.ofFinite n
  have hcont : Continuous (fun t : ℝ =>
      ofMatrix n P hP.isHermitian + t • ofMatrix n H hH) := by
    fun_prop
  have hmem : ofMatrix n P hP.isHermitian ∈
      interior (psdCone n : Set (SemidefiniteProgram.HermitianMatrix n)) :=
    (mem_interior_psdCone_iff_posDef n _).mpr
      (by simpa only [toMatrix_ofMatrix] using hP)
  have htendsto : Filter.Tendsto (fun t : ℝ =>
      ofMatrix n P hP.isHermitian + t • ofMatrix n H hH)
      (𝓝 0) (𝓝 (ofMatrix n P hP.isHermitian)) := by
    simpa only [zero_smul, add_zero] using hcont.tendsto 0
  filter_upwards [htendsto.eventually (isOpen_interior.eventually_mem hmem)] with t ht
  simpa only [toMatrix_add, toMatrix_smul, toMatrix_ofMatrix] using
    (mem_interior_psdCone_iff_posDef n _).mp ht

/-- A positive-definite determinant maximizer on the positive-semidefinite part of a real
Hermitian affine slice annihilates every affine tangent direction under the inverse-trace pairing.

Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem PosDef.trace_nonsing_inv_mul_sub_eq_zero_of_isMaxOn_det
    {P : Matrix n n ℂ} (hP : P.PosDef)
    (C : AffineSubspace ℝ (Matrix n n ℂ)) (hPC : P ∈ C)
    (hC : ∀ X ∈ C, X.IsHermitian)
    (hmax : IsMaxOn (fun X : Matrix n n ℂ => X.det.re)
      {X | X ∈ C ∧ X.PosSemidef} P) :
    ∀ X ∈ C, (P⁻¹ * (X - P)).trace = 0 := by
  intro X hX
  have hH : (X - P).IsHermitian := (hC X hX).sub hP.isHermitian
  apply trace_nonsing_inv_mul_eq_zero_of_isLocalMax_det P (X - P) hP.isHermitian
    ((isUnit_iff_isUnit_det P).mp hP.isUnit) hH
  filter_upwards [hP.eventually_posDef_add_real_smul hH] with t ht
  have hline : P + (t : ℂ) • (X - P) ∈ C := by
    simpa only [vsub_eq_sub, vadd_eq_add, add_comm,
      RCLike.real_smul_eq_coe_smul (K := ℂ)] using!
      C.smul_vsub_vadd_mem t hX hPC hPC
  simpa only [Complex.ofReal_zero, zero_smul, add_zero] using
    (isMaxOn_iff.mp hmax _ ⟨hline, ht.posSemidef⟩)

end Matrix
