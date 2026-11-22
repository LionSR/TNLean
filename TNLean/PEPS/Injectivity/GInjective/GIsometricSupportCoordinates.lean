/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Injectivity.GInjective.GIsometricConcatenation
import QICLean.Analysis.Real.ComplexSqrt
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Normalized adjoints on the physical support of G-isometric tensors

The normalized adjoint is isometric on the actual physical range and recovers
the invariant averaging projector with its exact positive square-root factor.
This is the coordinate form of the physical support restriction in SCP10,
arXiv:1001.3807, Observation 6.4, source lines 1765–1820. Surjectivity onto an
ambient physical space is not required.

## Canonical averaging tensors and the full physical support

A G-isometric physical tensor is, after its positive scalar normalization,
isometrically equivalent to the canonical averaging tensor on their actual
physical supports. Unused ambient physical directions need not be absent.
Source: SCP10, arXiv:1001.3807, Observation 6.4 and the identification of the
coarse tensor in Observation 6.6, lines 1765–1820 and 1896–1906.
-/

section

open scoped Matrix
namespace TNLean.PEPS

variable {G ι κ : Type*} [Group G] [Fintype G] [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
attribute [local instance] Representation.invertibleFintypeCardComplex

/-- The explicitly normalized adjoint restricts to a physical-support
isometry and exposes the invariant virtual coordinates. Source: SCP10,
Observation 6.4, lines 1765–1820. -/
theorem IsGIsometric.exists_accessibleCoordinates
    {ρ : Representation ℂ G (ι → ℂ)} {T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)}
    (hT : IsGIsometric ρ T)
    (hU : ∀ g x y, star (ρ g x) ⬝ᵥ ρ g y = star x ⬝ᵥ y) :
    ∃ c : ℝ, 0 < c ∧
      let J := (Real.sqrt c : ℂ)⁻¹ • coordinateAdjoint T
      J ∘ₗ T = (Real.sqrt c : ℂ) • ρ.averageMap ∧
        ∀ x ∈ T.range, ∀ y ∈ T.range, star (J x) ⬝ᵥ J y = star x ⬝ᵥ y := by
  have hAvg := averageMap_dotProduct_of_unitary ρ hU
  obtain ⟨c, hc, h⟩ := hT.exists_coordinateAdjoint_comp hAvg
  have hs : (Real.sqrt c : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hc)
  have hscalar : (Real.sqrt c : ℂ)⁻¹ * (c : ℂ) = (Real.sqrt c : ℂ) := by
    rw [← Complex.ofReal_sqrt_sq c hc.le, pow_two, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  let J := (Real.sqrt c : ℂ)⁻¹ • coordinateAdjoint T
  have hJT : J ∘ₗ T = (Real.sqrt c : ℂ) • ρ.averageMap := by
    rw [LinearMap.smul_comp, h, smul_smul, hscalar]
  refine ⟨c, hc, hJT, ?_⟩
  intro x hx y hy
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  have hJu := LinearMap.congr_fun hJT u
  have hJv := LinearMap.congr_fun hJT v
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hJu hJv
  rw [hJu, hJv]
  simp only [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    Complex.star_def, Complex.conj_ofReal]
  rw [← mul_assoc, ← pow_two, Complex.ofReal_sqrt_sq c hc.le,
    hAvg, ρ.averageMap_id _ (ρ.averageMap_invariant v)]
  have hv := LinearMap.congr_fun h v
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hv
  rw [← coordinateAdjoint_dotProduct T u (T v), hv, dotProduct_smul, smul_eq_mul]

variable {ν : Type*} [Fintype ν]

/-- A coordinate map preserving inner products on an actual physical range
is a Hilbert-space isometry after restriction to that range.
Source: SCP10, Observation 6.4, lines 1765–1820. -/
noncomputable def coordinateSupportIsometry (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ))
    (J : (κ → ℂ) →ₗ[ℂ] (ν → ℂ))
    (hJ : ∀ x ∈ T.range, ∀ y ∈ T.range, star (J x) ⬝ᵥ J y = star x ⬝ᵥ y) :
    (Matrix.toEuclideanLin (LinearMap.toMatrix' T)).range →ₗᵢ[ℂ] EuclideanSpace ℂ ν := by
  let TE := Matrix.toEuclideanLin (LinearMap.toMatrix' T)
  let JE := Matrix.toEuclideanLin (LinearMap.toMatrix' J)
  refine (JE ∘ₗ TE.range.subtype).isometryOfInner ?_
  intro x y
  have hmem (z : TE.range) : z.val.ofLp ∈ T.range := by
    obtain ⟨u, hu⟩ := z.2
    refine ⟨u.ofLp, ?_⟩
    have h := congrArg WithLp.ofLp hu
    simpa only [TE, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      WithLp.ofLp_toLp, LinearMap.toMatrix'_mulVec] using h
  change inner ℂ (JE x.val) (JE y.val) = inner ℂ x.val y.val
  simp only [JE, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin,
    Matrix.toLpLin_apply, LinearMap.toMatrix'_mulVec]
  simpa only [dotProduct_comm] using hJ _ (hmem x) _ (hmem y)

/-- The support isometry acts by the original coordinate map, with no choice
of a different physical operation. Source: SCP10, Observation 6.4. -/
theorem coordinateSupportIsometry_apply (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ))
    (J : (κ → ℂ) →ₗ[ℂ] (ν → ℂ))
    (hJ : ∀ x ∈ T.range, ∀ y ∈ T.range, star (J x) ⬝ᵥ J y = star x ⬝ᵥ y)
    (x : (Matrix.toEuclideanLin (LinearMap.toMatrix' T)).range) :
    (coordinateSupportIsometry T J hJ x).ofLp = J x.val.ofLp := by
  change LinearMap.toMatrix' J *ᵥ x.val.ofLp = J x.val.ofLp
  exact LinearMap.toMatrix'_mulVec J _

end TNLean.PEPS

end

section

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
end

end
