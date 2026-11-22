/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.PeriodicRangeComparison
import QICLean.Analysis.PositiveComparisonGap

/-!
# Periodic sums of a fixed local interaction

A local operator is extended by the identity on the remaining sites and
translated around the periodic chain. This construction preserves positivity
and order, and agrees with the canonical parent Hamiltonian when the local
operator is the complementary ground-space projection. Interactions longer
than the chain give zero, matching the existing parent-Hamiltonian convention.

These are the local-to-global comparisons for positive parent interactions
in CPGSV21, arXiv:2011.12127, Section IV.C, lines 1995--2007 and 2183--2187.

**Transitional (#10948).** The declarations about `periodicLocalInteractionES` and
`periodicInteractionHamiltonianES` are kept until their last users, the mixed-endpoint files of
`TNLean/MPS/Symmetry/MPOSymmetry`, are converted. The last section states the facts for the terms
of `ManyBody.Interaction.translationInvariant`.
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

/-- Cyclic active-block coordinates expose the actual translated interaction
as its right-spectator extension. Source: PGVWC07, arXiv:quant-ph/0608197,
Theorem 11 proof, lines 1418–1422. -/
theorem cyclicActiveBlock_periodicLocalInteractionES_apply
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hRN : R ≤ N) (i : Fin N) (ψ : EuclideanSpace ℂ (Cfg d N)) :
    cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i
        (periodicLocalInteractionES h i ψ) =
      ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - R))
        (LinearMap.toContinuousLinearMap h)
        (cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i ψ) := by
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i
  let G := ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - R))
    (LinearMap.toContinuousLinearMap h)
  rw [periodicLocalInteractionES, dite_eq_left hRN]
  change U (U.symm (G (U ψ))) = G (U ψ)
  exact U.apply_symm_apply _

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
    {D : ℕ} (A : MPSTensor d D) (_hR : 0 < R) (i : Fin N) :
    periodicLocalInteractionES (parentInteractionES A R) i = localTermES A R i := by
  by_cases hRN : R ≤ N
  · have : NeZero N := NeZero.of_pos i.pos
    let U := cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i
    apply LinearMap.ext
    intro ψ
    apply U.injective
    have hterm : localTermES A R i ψ =
        Matrix.toEuclideanLin ((parentRingInteraction A R N).term i) ψ := by
      ext σ
      rw [localTermES_apply A R i hRN, toEuclideanLin_parentRingInteraction_term_apply A hRN,
        toEuclideanLin_toMatrix'_parentInteraction]
      rfl
    rw [cyclicActiveBlock_periodicLocalInteractionES_apply _ hRN, hterm,
      cyclicActiveBlock_toEuclideanLin_translationInvariant_term_apply hRN,
      toEuclideanLin_toMatrix'_parentInteraction]
    rfl
  · simp [periodicLocalInteractionES, localTermES, localTerm_of_not_le A hRN, hRN]

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

/-- Extending the zero local interaction gives zero. -/
@[simp] theorem periodicLocalInteractionES_zero (i : Fin N) :
    periodicLocalInteractionES
      (0 : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)) i = 0 := by
  simp [periodicLocalInteractionES]

/-- Extension to a cyclic window preserves positivity. -/
theorem periodicLocalInteractionES_isPositive
    {h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hh : h.IsPositive) (i : Fin N) :
    (periodicLocalInteractionES h i).IsPositive := by
  apply LinearMap.nonneg_iff_isPositive.mp
  simpa only [periodicLocalInteractionES_zero] using
    periodicLocalInteractionES_mono (LinearMap.nonneg_iff_isPositive.mpr hh) i

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
  apply LinearMap.nonneg_iff_isPositive.mp
  simpa only [periodicInteractionHamiltonianES_zero] using
    periodicInteractionHamiltonianES_mono (LinearMap.nonneg_iff_isPositive.mpr hh) N

/-- The periodic sum of the canonical parent projection is the canonical
parent Hamiltonian at every volume. -/
theorem periodicInteractionHamiltonianES_parentInteractionES
    {D : ℕ} (A : MPSTensor d D) (hR : 0 < R) (N : ℕ) :
    periodicInteractionHamiltonianES (parentInteractionES A R) N =
      parentHamiltonianES A R N := by
  simp only [periodicInteractionHamiltonianES,
    periodicLocalInteractionES_parentInteractionES A hR, parentHamiltonianES_eq_sum_localTermES]

end MPSTensor

/-! ### Translates of a local matrix on the ring

Order, scalar multiples and positivity of the Hamiltonian of the translates of a local matrix on
the ring (`ManyBody.Interaction.translationInvariant`), and the transfer of a gap above the
kernel along a two-sided comparison of positive semidefinite matrices. -/

namespace ManyBody

open scoped MatrixOrder

/-- **Gap transfer along a comparison.** If positive semidefinite matrices satisfy
`κ A ≤ B ≤ C A` with `κ, C > 0` and every eigenvalue of `A` other than zero is at least `γ > 0`,
then every eigenvalue of `B` other than zero is at least `κ γ`. -/
theorem forall_hasEigenvalue_of_smul_le_of_le_smul {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) {κ C γ : ℝ}
    (hκ : 0 < κ) (hC : 0 < C) (hγ : 0 < γ) (hLower : (κ : ℂ) • A ≤ B)
    (hUpper : B ≤ (C : ℂ) • A)
    (hGap : ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin A) μ →
      μ = 0 ∨ (γ : ℂ) ≤ μ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin B) μ →
      μ = 0 ∨ ((κ * γ : ℝ) : ℂ) ≤ μ := by
  have h1 := Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr hLower
  have h2 := Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr hUpper
  rw [map_smul] at h1 h2
  refine (forall_hasEigenvalue_iff_norm hB).mpr ?_
  simpa only [div_one] using
    LinearMap.IsPositive.norm_gap_of_smul_le_of_le_smul
      (Matrix.isPositive_toEuclideanLin_iff.mpr hA)
      (Matrix.isPositive_toEuclideanLin_iff.mpr hB) (b := 1) hκ zero_lt_one hC hγ
      (by simpa only [Complex.ofReal_one, one_smul] using h1)
      (by simpa only [Complex.ofReal_one, one_smul] using h2)
      ((forall_hasEigenvalue_iff_norm hA).mp hGap)

namespace Interaction

variable {α : Type*} [Fintype α] [DecidableEq α] {R N : ℕ} [NeZero N]

/-- The Hamiltonian of the translates on the ring is monotone in the local matrix. -/
theorem hamiltonian_translationInvariant_mono {h h' : Matrix (Fin R → α) (Fin R → α) ℂ}
    (hle : h ≤ h') :
    (translationInvariant N h).hamiltonian ≤ (translationInvariant N h').hamiltonian := by
  by_cases hRN : R ≤ N
  · rw [hamiltonian_translationInvariant_of_le _ hRN, hamiltonian_translationInvariant_of_le _ hRN]
    exact Finset.sum_le_sum fun i _ ↦ ManyBody.placeAlong_le_placeAlong _ hle
  · rw [hamiltonian_translationInvariant_of_not_le _ hRN,
      hamiltonian_translationInvariant_of_not_le _ hRN]

/-- The Hamiltonian of the translates on the ring of a scalar multiple. -/
theorem hamiltonian_translationInvariant_smul (c : ℂ) (h : Matrix (Fin R → α) (Fin R → α) ℂ) :
    (translationInvariant N (c • h)).hamiltonian = c • (translationInvariant N h).hamiltonian := by
  by_cases hRN : R ≤ N
  · simp only [hamiltonian_translationInvariant_of_le _ hRN, ManyBody.placeAlong_smul,
      Finset.smul_sum]
  · rw [hamiltonian_translationInvariant_of_not_le _ hRN,
      hamiltonian_translationInvariant_of_not_le _ hRN, smul_zero]

/-- A positive semidefinite local matrix has a positive semidefinite Hamiltonian on the ring. -/
theorem posSemidef_hamiltonian_translationInvariant {h : Matrix (Fin R → α) (Fin R → α) ℂ}
    (hh : h.PosSemidef) : (translationInvariant N h).hamiltonian.PosSemidef :=
  posSemidef_hamiltonian fun i ↦
    Matrix.nonneg_iff_posSemidef.mp (translationInvariant_term_nonneg hh.nonneg i)

end Interaction

end ManyBody
