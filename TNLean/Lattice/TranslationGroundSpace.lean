/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.TranslationMomentum
import TNLean.Lattice.LowEnergyBasisConstruction
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Translation on the actual ground eigenspace

A site translation preserving the Hamiltonian restricts to a unitary on its actual
finite-dimensional ground eigenspace. Conjugation by this unitary preserves the operator
norm on ground-space operators. The ambient orthogonal ground projection commutes with
the site translation, so the restrictions agree with compression of the physical operators.
These are the operator identifications in Hastings, arXiv:cond-mat/0508554v3,
lines 1603–1618 and 1644–1654.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace TNLean.Lattice

variable {V G : Type*} [Fintype V] [DecidableEq V] [CommGroup G] [MulAction G V]
  {d : ℕ}

/-- A site translation acts unitarily on the actual ground eigenspace.
Hastings, arXiv:cond-mat/0508554v3, lines 1603–1618. -/
noncomputable def groundTranslation {H : Matrix (V → Fin d) (V → Fin d) ℂ}
    (hInv : IsSiteInvariant G d H) (E₀ : ℝ) (g : G) :
    groundEigenspace H E₀ ≃ₗᵢ[ℂ] groundEigenspace H E₀ := by
  let f : groundEigenspace H E₀ →ₗᵢ[ℂ] groundEigenspace H E₀ := {
    toFun := fun x ↦ ⟨toEuclideanLin (sitePermMatrix d g) x,
      mapsTo_groundEigenspace_sitePermMatrix hInv E₀ g x.property⟩
    map_add' := fun x y ↦ Subtype.ext
      (map_add (toEuclideanLin (sitePermMatrix d g))
        (x : EuclideanSpace ℂ (V → Fin d)) (y : EuclideanSpace ℂ (V → Fin d)))
    map_smul' := fun c x ↦ Subtype.ext
      (map_smul (toEuclideanLin (sitePermMatrix d g)) c (x : EuclideanSpace ℂ (V → Fin d)))
    norm_map' := by
      intro x
      change ‖toEuclideanCLM (n := V → Fin d) (𝕜 := ℂ) (sitePermMatrix d g)
        (x : EuclideanSpace ℂ (V → Fin d))‖ = ‖(x : EuclideanSpace ℂ (V → Fin d))‖
      exact ContinuousLinearMap.norm_map_of_mem_unitary
        (Unitary.map_mem (toEuclideanCLM (n := V → Fin d) (𝕜 := ℂ))
          (sitePermMatrix_mem_unitaryGroup d g)) x }
  exact LinearIsometryEquiv.ofSurjective f (LinearMap.surjective_of_injective f.injective)

/-- Conjugation on the ground-space operator algebra preserves the operator norm.
Hastings, arXiv:cond-mat/0508554v3, lines 1644–1654. -/
noncomputable def groundTranslationConjugation {H : Matrix (V → Fin d) (V → Fin d) ℂ}
    (hInv : IsSiteInvariant G d H) (E₀ : ℝ) (g : G) :
    (groundEigenspace H E₀ →L[ℂ] groundEigenspace H E₀) ≃ₗᵢ[ℂ]
      (groundEigenspace H E₀ →L[ℂ] groundEigenspace H E₀) := by
  let u := groundTranslation hInv E₀ g
  refine { (u.toContinuousLinearEquiv.arrowCongr u.toContinuousLinearEquiv).toLinearEquiv with
    norm_map' := ?_ }
  intro B
  change ‖(u : groundEigenspace H E₀ →L[ℂ] groundEigenspace H E₀).comp
    (B.comp (u.symm : groundEigenspace H E₀ →L[ℂ] groundEigenspace H E₀))‖ = ‖B‖
  rw [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

/-- The site translation commutes with the canonical orthogonal ground projection.
Hastings, arXiv:cond-mat/0508554v3, lines 1603–1618. -/
theorem sitePerm_starProjection_commute {H : Matrix (V → Fin d) (V → Fin d) ℂ}
    (hInv : IsSiteInvariant G d H) (E₀ : ℝ) (g : G)
    (x : EuclideanSpace ℂ (V → Fin d)) :
    toEuclideanLin (sitePermMatrix d g) ((groundEigenspace H E₀).starProjection x) =
      (groundEigenspace H E₀).starProjection (toEuclideanLin (sitePermMatrix d g) x) := by
  let u : EuclideanSpace ℂ (V → Fin d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (V → Fin d) :=
    Unitary.linearIsometryEquiv
      ⟨toEuclideanCLM (n := V → Fin d) (𝕜 := ℂ) (sitePermMatrix d g),
        Unitary.map_mem _ (sitePermMatrix_mem_unitaryGroup d g)⟩
  have hle : (groundEigenspace H E₀).map u.toLinearEquiv.toLinearMap ≤
      groundEigenspace H E₀ := by
    rintro y ⟨z, hz, rfl⟩
    exact mapsTo_groundEigenspace_sitePermMatrix hInv E₀ g hz
  have heq : (groundEigenspace H E₀).map u.toLinearEquiv.toLinearMap =
      groundEigenspace H E₀ := Submodule.eq_of_le_of_finrank_eq hle
        (u.toLinearEquiv.finrank_map_eq (groundEigenspace H E₀))
  have h := u.toLinearIsometry.map_starProjection (groundEigenspace H E₀) x
  change u ((groundEigenspace H E₀).starProjection x) =
    ((groundEigenspace H E₀).map u.toLinearEquiv.toLinearMap).starProjection (u x) at h
  have hu (y : EuclideanSpace ℂ (V → Fin d)) :
      u y = toEuclideanLin (sitePermMatrix d g) y := rfl
  simpa only [heq, hu] using h

/-- The ground-space unitary is the restriction of the physical site translation.
Hastings, arXiv:cond-mat/0508554v3, lines 1603–1618. -/
@[simp] theorem groundTranslation_apply_coe {H : Matrix (V → Fin d) (V → Fin d) ℂ}
    (hInv : IsSiteInvariant G d H) (E₀ : ℝ) (g : G) (x : groundEigenspace H E₀) :
    (groundTranslation hInv E₀ g x : EuclideanSpace ℂ (V → Fin d)) =
      toEuclideanLin (sitePermMatrix d g) x := rfl

/-- Inverse ground translation agrees with the inverse physical site translation.
Hastings, arXiv:cond-mat/0508554v3, lines 1603–1618. -/
theorem groundTranslation_symm_apply {H : Matrix (V → Fin d) (V → Fin d) ℂ}
    (hInv : IsSiteInvariant G d H) (E₀ : ℝ) (g : G) (x : groundEigenspace H E₀) :
    (groundTranslation hInv E₀ g).symm x = groundTranslation hInv E₀ g⁻¹ x := by
  apply (groundTranslation hInv E₀ g).injective
  apply Subtype.ext
  simp only [LinearIsometryEquiv.apply_symm_apply, groundTranslation_apply_coe]
  rw [← toEuclideanLin_sitePermMatrix_mul, mul_inv_cancel,
    toEuclideanLin_sitePermMatrix_one]

/-- Ground-space conjugation is compression of physical conjugation.
Hastings, arXiv:cond-mat/0508554v3, lines 1603–1618 and 1644–1654. -/
theorem groundTranslationConjugation_groundSpaceCompression
    {H : Matrix (V → Fin d) (V → Fin d) ℂ}
    (hInv : IsSiteInvariant G d H) (E₀ : ℝ) (g : G)
    (W : Matrix (V → Fin d) (V → Fin d) ℂ) :
    groundTranslationConjugation hInv E₀ g (groundSpaceCompression H E₀ W) =
      groundSpaceCompression H E₀ (sitePermMatrix d g * W * (sitePermMatrix d g)ᴴ) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change (groundTranslation hInv E₀ g
    (groundSpaceCompression H E₀ W ((groundTranslation hInv E₀ g).symm x)) :
      EuclideanSpace ℂ (V → Fin d)) = _
  rw [groundTranslation_symm_apply, groundTranslation_apply_coe,
    coe_groundSpaceCompression_apply, coe_groundSpaceCompression_apply]
  simp only [groundCompression, mul_apply_eq_comp]
  rw [sitePerm_starProjection_commute hInv E₀ g,
    ← sitePermMatrix_inv d g, map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp]
  simp only [Submodule.starProjection_mem_subspace_eq_self, groundTranslation_apply_coe]
  rw [(groundEigenspace H E₀).starProjection_eq_self_iff.mpr
    (mapsTo_groundEigenspace_sitePermMatrix hInv E₀ g⁻¹ x.property)]
  rfl

/-- Iterating ground-space conjugation follows the orbit of any covariant local family.
Hastings, arXiv:cond-mat/0508554v3, lines 1644–1654. -/
theorem groundTranslationConjugation_pow_compression_of_covariant
    {H : Matrix (V → Fin d) (V → Fin d) ℂ}
    (hInv : IsSiteInvariant G d H) (E₀ : ℝ) {κ : Type*} [MulAction G κ]
    (M : κ → Matrix (V → Fin d) (V → Fin d) ℂ)
    (hcov : ∀ (g : G) i, M (g • i) = sitePermMatrix d g * M i * (sitePermMatrix d g)ᴴ)
    (g : G) (k : ℕ) (i : κ) :
    ((groundTranslationConjugation hInv E₀ g).toLinearMap ^ k)
        (groundSpaceCompression H E₀ (M i)) =
      groundSpaceCompression H E₀ (M (g ^ k • i)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    change groundTranslationConjugation hInv E₀ g
      (groundSpaceCompression H E₀ (M (g ^ k • i))) = _
    rw [groundTranslationConjugation_groundSpaceCompression, ← hcov, pow_succ', mul_smul]


/-- Iterated conjugation of an arbitrary observable agrees before and after compression.
No covariance assumption on a local decomposition is needed. Hastings,
arXiv:cond-mat/0508554v3, lines 1644–1654. -/
theorem groundTranslationConjugation_pow_compression
    {V Γ : Type*} [Fintype V] [DecidableEq V] [CommGroup Γ] [MulAction Γ V]
    {d : ℕ} {H : Matrix (V → Fin d) (V → Fin d) ℂ}
    (hInv : IsSiteInvariant Γ d H) (E₀ : ℝ) (g : Γ) (k : ℕ)
    (W : Matrix (V → Fin d) (V → Fin d) ℂ) :
    ((groundTranslationConjugation hInv E₀ g).toLinearMap ^ k)
        (groundSpaceCompression H E₀ W) =
      groundSpaceCompression H E₀
        (sitePermMatrix d (g ^ k) * W * (sitePermMatrix d (g ^ k))ᴴ) := by
  let M : Γ → Matrix (V → Fin d) (V → Fin d) ℂ :=
    fun h ↦ sitePermMatrix d h * W * (sitePermMatrix d h)ᴴ
  have hcov (a b : Γ) : M (a • b) = sitePermMatrix d a * M b * (sitePermMatrix d a)ᴴ := by
    dsimp [M]
    rw [sitePermMatrix_mul, Matrix.conjTranspose_mul]
    noncomm_ring
  have h := groundTranslationConjugation_pow_compression_of_covariant hInv E₀ M hcov g k 1
  simpa only [M, sitePermMatrix_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    smul_eq_mul, mul_one] using h


end TNLean.Lattice
