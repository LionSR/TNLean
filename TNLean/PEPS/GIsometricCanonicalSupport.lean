/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GIsometricSupportCoordinates

/-!
# Canonical averaging tensors and the full physical support

A G-isometric physical tensor is, after its positive scalar normalization,
isometrically equivalent to the canonical averaging tensor on their actual
physical supports. Unused ambient physical directions need not be absent.
Source: SCP10, arXiv:1001.3807, Observation 6.4 and the identification of the
coarse tensor in Observation 6.6, lines 1765–1820 and 1896–1906.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {G ι κ : Type*} [Group G] [Fintype G] [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
attribute [local instance] Representation.invertibleFintypeCardComplex

/-- The normalized adjoint is an isometric equivalence between the original
physical support and the canonical averaging tensor's support. Its action is
explicit and no ambient physical surjectivity is assumed.
Source: SCP10, Observations 6.4 and 6.6, lines 1765–1820 and 1896–1906. -/
theorem IsGIsometric.exists_canonicalSupportEquiv
    {ρ : Representation ℂ G (ι → ℂ)} {T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)}
    (hT : IsGIsometric ρ T)
    (hU : ∀ g x y, star (ρ g x) ⬝ᵥ ρ g y = star x ⬝ᵥ y) :
    ∃ c : ℝ, 0 < c ∧
      ∃ I : (Matrix.toEuclideanLin (LinearMap.toMatrix' T)).range ≃ₗᵢ[ℂ]
          (Matrix.toEuclideanLin (LinearMap.toMatrix' ρ.averageMap)).range,
        (∀ x, (I x).val.ofLp =
          ((Real.sqrt c : ℂ)⁻¹ • coordinateAdjoint T) x.val.ofLp) ∧
        ((Real.sqrt c : ℂ)⁻¹ • coordinateAdjoint T) ∘ₗ T =
          (Real.sqrt c : ℂ) • ρ.averageMap := by
  obtain ⟨c, hc, hJT, hJ⟩ := hT.exists_accessibleCoordinates hU
  let J := (Real.sqrt c : ℂ)⁻¹ • coordinateAdjoint T
  let TE := Matrix.toEuclideanLin (LinearMap.toMatrix' T)
  let AE := Matrix.toEuclideanLin (LinearMap.toMatrix' ρ.averageMap)
  let I := coordinateSupportIsometry T J hJ
  have hTE (u : EuclideanSpace ℂ ι) : (TE u).ofLp = T u.ofLp :=
    LinearMap.toMatrix'_mulVec T _
  have hAE (u : EuclideanSpace ℂ ι) : (AE u).ofLp = ρ.averageMap u.ofLp :=
    LinearMap.toMatrix'_mulVec ρ.averageMap _
  have hI (z : TE.range) : (I z).ofLp = J z.val.ofLp :=
    coordinateSupportIsometry_apply T J hJ z
  have hs : (Real.sqrt c : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hc)
  have hrange : I.range = AE.range := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨u, hu⟩ := z.2
      refine ⟨(Real.sqrt c : ℂ) • u, ?_⟩
      apply WithLp.ofLp_injective 2
      change (AE ((Real.sqrt c : ℂ) • u)).ofLp = (I z).ofLp
      rw [hAE, hI, ← hu, hTE]
      have h := LinearMap.congr_fun hJT u.ofLp
      simpa only [J, LinearMap.comp_apply, LinearMap.smul_apply, map_smul,
        WithLp.ofLp_smul] using h.symm
    · rintro ⟨u, rfl⟩
      let z : TE.range := ⟨TE ((Real.sqrt c : ℂ)⁻¹ • u), ⟨_, rfl⟩⟩
      refine ⟨z, ?_⟩
      apply WithLp.ofLp_injective 2
      change (I z).ofLp = (AE u).ofLp
      rw [hI, hAE]
      change J (TE ((Real.sqrt c : ℂ)⁻¹ • u)).ofLp = _
      rw [hTE]
      have h := LinearMap.congr_fun hJT ((Real.sqrt c : ℂ)⁻¹ • u.ofLp)
      simpa only [J, LinearMap.comp_apply, LinearMap.smul_apply, map_smul,
        WithLp.ofLp_smul, smul_smul, mul_inv_cancel₀ hs, inv_mul_cancel₀ hs, one_smul] using h
  refine ⟨c, hc, I.equivRange.trans (LinearIsometryEquiv.ofEq _ _ hrange), ?_, hJT⟩
  intro x
  exact hI x

end TNLean.PEPS
