/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.OpenRangeComparison

/-!
# Gaps of interval Hamiltonians after adjoining free sites

An interval Hamiltonian, acting on a larger chain, is an orthogonal direct
sum of copies of its finite-interval operator. Its norm gap on the kernel
complement is therefore preserved. The proof transports the kernel
projection and its positive comparison under the physical coordinate
isometry. This supplies the fixed-ambient interpretation of the local gaps
in Nachtergaele, arXiv:cond-mat/9410110, condition C2, lines 1045--1056.
-/

open scoped InnerProductSpace ComplexOrder

private theorem norm_gap_of_kernel_complement_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (H : E →ₗ[ℂ] E) {κ : ℝ} (hκ : 0 < κ)
    (hLower : (κ : ℂ) • (LinearMap.ker H)ᗮ.starProjection.toLinearMap ≤ H) :
    ∀ v ∈ (LinearMap.ker H)ᗮ, κ * ‖v‖ ≤ ‖H v‖ := by
  have hker : LinearMap.ker ((κ : ℂ) • (LinearMap.ker H)ᗮ.starProjection.toLinearMap) =
      LinearMap.ker H := by
    simp only [LinearMap.ker_smul _ _ (Complex.ofReal_ne_zero.mpr hκ.ne'),
      Submodule.ker_starProjection, Submodule.orthogonal_orthogonal]
  refine LinearMap.IsPositive.norm_gap_of_le_of_ker_eq
    ((Submodule.isSymmetricProjection_starProjection _).isPositive.smul_of_nonneg
      (by exact_mod_cast hκ.le)) hκ.le hLower hker ?_
  intro v hv
  rw [hker] at hv
  simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    (LinearMap.ker H)ᗮ.starProjection_eq_self_iff.mpr hv, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ, le_refl]

private theorem kernel_complement_bound_of_fiberwise_conj
    {E I S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [Fintype I] [Fintype S]
    (U : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (I × S)) (G : E →ₗ[ℂ] E)
    (H : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) {κ : ℝ}
    (hConj : U.toLinearEquiv.conj G =
      (ContinuousLinearMap.rightFiberwiseMap (S := S) H.toContinuousLinearMap).toLinearMap)
    (hLocal : (κ : ℂ) • (LinearMap.ker H)ᗮ.starProjection.toLinearMap ≤ H) :
    (κ : ℂ) • (LinearMap.ker G)ᗮ.starProjection.toLinearMap ≤ G := by
  have hProj := MPSTensor.ker_starProjection_conj_linearIsometryEquiv U G _
    (by simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc] using! hConj)
  rw [ContinuousLinearMap.ker_starProjection_rightFiberwiseMap] at hProj
  have hProjConj : U.toLinearEquiv.conj (LinearMap.ker G).starProjection.toLinearMap =
      (ContinuousLinearMap.rightFiberwiseMap (S := S)
        (LinearMap.ker H).starProjection).toLinearMap := by
    simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc] using! hProj
  have hId : ContinuousLinearMap.rightFiberwiseMap (S := S)
      (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ I)) =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (I × S)) := rfl
  have hOrth : U.toLinearEquiv.conj (LinearMap.ker G)ᗮ.starProjection.toLinearMap =
      (ContinuousLinearMap.rightFiberwiseMap (S := S)
        (LinearMap.ker H)ᗮ.starProjection).toLinearMap := by
    simp only [Submodule.starProjection_orthogonal, ContinuousLinearMap.toLinearMap_sub,
      ContinuousLinearMap.coe_id, map_sub, LinearEquiv.conj_id, hProjConj,
      ContinuousLinearMap.rightFiberwiseMap_sub, hId]
  refine (U.conj_le_conj_iff _ _).mp ?_
  simpa only [map_smul, hOrth, hConj,
    ContinuousLinearMap.rightFiberwiseMap_smul, ContinuousLinearMap.toLinearMap_smul] using
    (ContinuousLinearMap.rightFiberwiseMap_mono (S := S)
      (G := (κ : ℂ) • (LinearMap.ker H)ᗮ.starProjection)
      (H := H.toContinuousLinearMap) hLocal)

private theorem norm_gap_of_fiberwise_conj
    {E I S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [Fintype I] [Fintype S]
    (U : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (I × S)) (G : E →ₗ[ℂ] E)
    (H : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) {κ : ℝ}
    (hκ : 0 < κ) (hPos : H.IsPositive)
    (hConj : U.toLinearEquiv.conj G =
      (ContinuousLinearMap.rightFiberwiseMap (S := S) H.toContinuousLinearMap).toLinearMap)
    (hGap : ∀ v ∈ (LinearMap.ker H)ᗮ, κ * ‖v‖ ≤ ‖H v‖) :
    ∀ v ∈ (LinearMap.ker G)ᗮ, κ * ‖v‖ ≤ ‖G v‖ := by
  exact norm_gap_of_kernel_complement_bound G hκ
    (kernel_complement_bound_of_fiberwise_conj U G H hConj
      (hPos.smul_orthogonal_ker_projection_le_of_norm_gap hκ.le hGap))

namespace MPSTensor

variable {d D : ℕ}

/-- Adjoining free sites to a prefix preserves its finite-interval norm gap.
This is the fixed-ambient interpretation of the local gap in Nachtergaele,
arXiv:cond-mat/9410110, condition C2, lines 1045--1056. -/
theorem openPrefixParentHamiltonianES_norm_gap_of_local_gap
    (A : MPSTensor d D) {R n q : ℕ} (hR : 0 < R) {κ : ℝ} (hκ : 0 < κ)
    (hGap : ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A R n))ᗮ,
      κ * ‖v‖ ≤ ‖openParentHamiltonianES A R n v‖) :
    ∀ v ∈ (LinearMap.ker (openPrefixParentHamiltonianES A R (n + q) n))ᗮ,
      κ * ‖v‖ ≤ ‖openPrefixParentHamiltonianES A R (n + q) n v‖ := by
  have hConj := openPrefixParentHamiltonianES_conj_rightSpectatorConfigLinearIsometryEquiv
    A (n := n) (r := q) (p := n) hR le_rfl
  exact norm_gap_of_fiberwise_conj (rightSpectatorConfigLinearIsometryEquiv d n q)
    (openPrefixParentHamiltonianES A R (n + q) n) (openParentHamiltonianES A R n)
    hκ (openParentHamiltonianES_isPositive A R n)
    (by simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc,
      openPrefixParentHamiltonianES_self_eq_openParentHamiltonianES] using! hConj) hGap

/-- Inserting a finite terminal-interval Hamiltonian into a larger chain
preserves its norm gap. The physical coordinate isometry places its active
sites first and the free sites second. This is the fixed-ambient form of
Nachtergaele's condition C2, arXiv:cond-mat/9410110, lines 1045--1056. -/
theorem openSuffixParentHamiltonianES_norm_gap_of_local_gap
    (A : MPSTensor d D) {R W N n : ℕ} (hR : 0 < R) (hRW : R ≤ W)
    (hWn : W ≤ n) (hnN : n ≤ N) {κ : ℝ} (hκ : 0 < κ)
    (hGap : ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A R W))ᗮ,
      κ * ‖v‖ ≤ ‖openParentHamiltonianES A R W v‖) :
    ∀ v ∈ (LinearMap.ker (openSuffixParentHamiltonianES A R W N n))ᗮ,
      κ * ‖v‖ ≤ ‖openSuffixParentHamiltonianES A R W N n v‖ := by
  have hConj := openSuffixParentHamiltonianES_conj_cyclicActiveBlock A hR hRW hWn hnN
  exact norm_gap_of_fiberwise_conj
    (cyclicActiveBlockConfigLinearIsometryEquiv d W (hWn.trans hnN) ⟨n - W, by omega⟩)
    (openSuffixParentHamiltonianES A R W N n) (openParentHamiltonianES A R W)
    hκ (openParentHamiltonianES_isPositive A R W)
    (by simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc] using! hConj) hGap

end MPSTensor
