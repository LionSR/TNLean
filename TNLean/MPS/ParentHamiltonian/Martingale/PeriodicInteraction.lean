/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.PeriodicRangeComparison

/-!
# Periodic sums of a fixed local interaction

A local operator is extended by the identity on the remaining sites and
translated around the periodic chain. This construction preserves positivity
and order, and agrees with the canonical parent Hamiltonian when the local
operator is the complementary ground-space projection. Interactions longer
than the chain give zero, matching the existing parent-Hamiltonian convention.

These are the local-to-global comparisons for positive parent interactions
in CPGSV21, arXiv:2011.12127, Section IV.C, lines 1995--2007 and 2183--2187.
-/

open scoped BigOperators ComplexOrder

namespace MPSTensor

variable {d R N : ℕ}

/-- Translate a fixed range-\(R\) interaction to the cyclic window starting at
\(i\), extending it by the identity on the complementary physical sites. -/
noncomputable def periodicLocalInteractionES
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (i : Fin N) : EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  if hRN : R ≤ N then
    (cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i).symm.toLinearEquiv.conj
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - R))
        (LinearMap.toContinuousLinearMap h)).toLinearMap
  else 0

/-- Sum the cyclic translates of one fixed local interaction. -/
noncomputable def periodicInteractionHamiltonianES
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (N : ℕ) : EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  ∑ i : Fin N, periodicLocalInteractionES h i

/-- Cyclic extension preserves local operator inequalities. -/
theorem periodicLocalInteractionES_mono
    {h k : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hle : h ≤ k) (i : Fin N) :
    periodicLocalInteractionES h i ≤ periodicLocalInteractionES k i := by
  unfold periodicLocalInteractionES
  split_ifs with hRN
  · exact ((cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i).symm.conj_le_conj_iff
      _ _).mpr (ContinuousLinearMap.rightFiberwiseMap_mono hle)
  · exact le_rfl

/-- Extending the canonical local projection gives the existing translated
parent-Hamiltonian term. -/
theorem periodicLocalInteractionES_parentInteractionES
    {D : ℕ} (A : MPSTensor d D) (hR : 0 < R) (i : Fin N) :
    periodicLocalInteractionES (parentInteractionES A R) i = localTermES A R i := by
  by_cases hRN : R ≤ N
  · let U := cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i
    have hConj : U.toLinearEquiv.conj (localTermES A R i) =
        (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - R))
          (LinearMap.toContinuousLinearMap (parentInteractionES A R))).toLinearMap := by
      simpa only [U, Fin.val_mk, cyclicForwardSite_zero,
        localTermES_self_zero_eq_parentInteractionES A hR,
        LinearEquiv.conj_apply, LinearMap.comp_assoc] using!
        (localTermES_conj_cyclicActiveBlockConfigLinearIsometryEquiv A
          (R := R) hRN i ⟨0, hR⟩ (by simp))
    unfold periodicLocalInteractionES
    rw [dite_eq_left hRN]
    change U.toLinearEquiv.symm.conj _ = _
    apply U.toLinearEquiv.conj.injective
    rw [LinearEquiv.conj_conj_symm]
    exact hConj.symm
  · simp [periodicLocalInteractionES, localTermES, localTerm, hRN]

/-- Cyclic extension commutes with scalar multiplication. -/
theorem periodicLocalInteractionES_smul (c : ℂ)
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (i : Fin N) :
    periodicLocalInteractionES (c • h) i = c • periodicLocalInteractionES h i := by
  unfold periodicLocalInteractionES
  split_ifs with hRN
  · simp only [map_smul, ContinuousLinearMap.rightFiberwiseMap_smul,
      ContinuousLinearMap.toLinearMap_smul]
  · simp

/-- A zero local interaction gives a zero periodic Hamiltonian. -/
@[simp] theorem periodicInteractionHamiltonianES_zero (N : ℕ) :
    periodicInteractionHamiltonianES
      (0 : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)) N = 0 := by
  simp [periodicInteractionHamiltonianES, periodicLocalInteractionES]

/-- Summing cyclic translates preserves operator inequalities. -/
theorem periodicInteractionHamiltonianES_mono
    {h k : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hle : h ≤ k) (N : ℕ) :
    periodicInteractionHamiltonianES h N ≤ periodicInteractionHamiltonianES k N :=
  Finset.sum_le_sum fun i _ ↦ periodicLocalInteractionES_mono hle i

/-- The periodic sum depends linearly on a scalar multiple of the local interaction. -/
theorem periodicInteractionHamiltonianES_smul (c : ℂ)
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)) (N : ℕ) :
    periodicInteractionHamiltonianES (c • h) N = c • periodicInteractionHamiltonianES h N := by
  simp only [periodicInteractionHamiltonianES, periodicLocalInteractionES_smul, Finset.smul_sum]

/-- A fixed positive local interaction gives a positive periodic Hamiltonian. -/
theorem periodicInteractionHamiltonianES_isPositive
    {h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hh : h.IsPositive) (N : ℕ) :
    (periodicInteractionHamiltonianES h N).IsPositive := by
  apply (LinearMap.nonneg_iff_isPositive _).mp
  simpa only [periodicInteractionHamiltonianES_zero] using
    periodicInteractionHamiltonianES_mono ((LinearMap.nonneg_iff_isPositive h).mpr hh) N

/-- The periodic sum of the canonical parent projection is the canonical
parent Hamiltonian at every volume. -/
theorem periodicInteractionHamiltonianES_parentInteractionES
    {D : ℕ} (A : MPSTensor d D) (hR : 0 < R) (N : ℕ) :
    periodicInteractionHamiltonianES (parentInteractionES A R) N =
      parentHamiltonianES A R N := by
  simp only [periodicInteractionHamiltonianES,
    periodicLocalInteractionES_parentInteractionES A hR, parentHamiltonianES_eq_sum_localTermES]

end MPSTensor
