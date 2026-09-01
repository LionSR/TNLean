/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Lagrange

/-!
# Congruence factorization of symmetric unitary matrices

A complex symmetric unitary matrix has a symmetric unitary square root. The square root is the
finite spectral-projector square root from CPSV17, Lemma `lemma:conjclass-normalform-continuous`
(arXiv:1703.09188, lines 1054--1064).
-/

open scoped Polynomial

noncomputable section

namespace Matrix

variable {R n : Type*} [CommSemiring R] [Fintype n] [DecidableEq n]

/-- Transpose commutes with evaluating a polynomial at a square matrix over a commutative
semiring. -/
theorem transpose_aeval (p : R[X]) (A : Matrix n n R) :
    ((Polynomial.aeval A) p).transpose = (Polynomial.aeval A.transpose) p := by
  simp only [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, Matrix.transpose_sum,
    Matrix.transpose_mul, Matrix.transpose_pow]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show ((algebraMap R (Matrix n n R)) (p.coeff i)).transpose =
      (algebraMap R (Matrix n n R)) (p.coeff i) by
    ext j k
    simp only [Matrix.transpose_apply, Matrix.algebraMap_matrix_apply]
    by_cases h : j = k
    · subst k
      rfl
    · have hk : k ≠ j := Ne.symm h
      simp [h, hk]]
  exact (Algebra.commutes (p.coeff i) (A.transpose ^ i)).symm

variable {n : ℕ}

/-- A complex symmetric unitary matrix has a symmetric unitary square root.

This is the symmetric branch of CPSV17, Lemma `lemma:conjclass-normalform-continuous`
(arXiv:1703.09188, lines 1054--1064). -/
theorem exists_symmetric_unitary_squareRoot
    (x : Matrix (Fin n) (Fin n) ℂ)
    (hx : x ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hsym : x.transpose = x) :
    ∃ S : Matrix (Fin n) (Fin n) ℂ,
      S.transpose = S ∧
      S ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      x = S.transpose * S := by
  let _ : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  let _ : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
  let e := CStarMatrix.ofMatrixStarAlgEquiv (n := Fin n) (A := ℂ)
  let a := e x
  have ha_unitary : a ∈ unitary (CStarMatrix (Fin n) (Fin n) ℂ) := by
    change star a * a = 1 ∧ a * star a = 1
    constructor
    · change star (e x) * e x = 1
      rw [← StarHomClass.map_star e, ← map_mul e, ← map_one e]
      exact congrArg e (Matrix.mem_unitaryGroup_iff'.mp hx)
    · change e x * star (e x) = 1
      rw [← StarHomClass.map_star e, ← map_mul e, ← map_one e]
      exact congrArg e (Matrix.mem_unitaryGroup_iff.mp hx)
  have ha_normal : IsStarNormal a := isStarNormal_of_mem_unitary ha_unitary
  have hspec : (spectrum ℂ a).Finite := Matrix.finite_spectrum a
  have hsqrt_cont : ContinuousOn Complex.sqrt (spectrum ℂ a) := hspec.continuousOn _
  have hsqrt_sq (z : ℂ) : Complex.sqrt z * Complex.sqrt z = z := by
    change (z ^ (2 : ℂ)⁻¹) * (z ^ (2 : ℂ)⁻¹) = z
    simpa [pow_two] using Complex.cpow_nat_inv_pow z (n := 2) (by norm_num)
  have hroot_sq :
      cfc (p := IsStarNormal) Complex.sqrt a * cfc (p := IsStarNormal) Complex.sqrt a = a := by
    rw [← cfc_mul (p := IsStarNormal) Complex.sqrt Complex.sqrt a hsqrt_cont hsqrt_cont]
    rw [cfc_congr (p := IsStarNormal) (g := fun z ↦ z) (fun z _ ↦ hsqrt_sq z),
      cfc_id' ℂ a ha_normal]
  have hroot_unitary :
      cfc (p := IsStarNormal) Complex.sqrt a ∈ unitary (CStarMatrix (Fin n) (Fin n) ℂ) := by
    rw [cfc_unitary_iff (p := IsStarNormal) Complex.sqrt a ha_normal hsqrt_cont]
    intro z hz
    have hz_unitary : z ∈ unitary ℂ := spectrum_subset_unitary_of_mem_unitary ha_unitary hz
    have hz_norm_sq : ‖z‖ * ‖z‖ = 1 := by
      have h := congrArg norm (Unitary.mem_iff_star_mul_self.mp hz_unitary)
      simpa [norm_mul] using h
    have hz_norm : ‖z‖ = 1 := by nlinarith [norm_nonneg z]
    have hsqrt_norm_sq : ‖Complex.sqrt z‖ * ‖Complex.sqrt z‖ = 1 := by
      have h := congrArg norm (hsqrt_sq z)
      simpa [norm_mul, hz_norm] using h
    have hsqrt_norm : ‖Complex.sqrt z‖ = 1 := by
      nlinarith [norm_nonneg (Complex.sqrt z)]
    rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, hsqrt_norm]
    norm_num
  let q : ℂ[X] := (Lagrange.interpolate hspec.toFinset id) Complex.sqrt
  have hq_eval : Set.EqOn Complex.sqrt (fun z ↦ Polynomial.eval z q) (spectrum ℂ a) := by
    intro z hz
    symm
    exact Lagrange.eval_interpolate_at_node Complex.sqrt (Set.injOn_id _)
      (hspec.mem_toFinset.mpr hz)
  have hroot_poly :
      cfc (p := IsStarNormal) Complex.sqrt a = (Polynomial.aeval a) q := by
    rw [cfc_congr (p := IsStarNormal) hq_eval, cfc_polynomial q a ha_normal]
  let S : Matrix (Fin n) (Fin n) ℂ := (Polynomial.aeval x) q
  have hmapS : e S = cfc (p := IsStarNormal) Complex.sqrt a := by
    rw [hroot_poly]
    change e ((Polynomial.aeval x) q) = (Polynomial.aeval (e x)) q
    simp only [Polynomial.aeval_def]
    change e.toRingHom (Polynomial.eval₂ (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ)) x q) = _
    rw [Polynomial.hom_eval₂]
    congr 1
  have hS_sq : S * S = x := by
    apply e.injective
    change e (S * S) = e x
    rw [map_mul e, hmapS]
    simpa [a] using hroot_sq
  have hS_unitary : S ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    apply e.injective
    change e (star S * S) = e 1
    rw [map_mul e, StarHomClass.map_star e, map_one e, hmapS]
    exact hroot_unitary.1
  have hS_symm : S.transpose = S := by
    change ((Polynomial.aeval x) q).transpose = (Polynomial.aeval x) q
    rw [transpose_aeval, hsym]
  exact ⟨S, hS_symm, hS_unitary, by simpa [hS_symm] using hS_sq.symm⟩

end Matrix
