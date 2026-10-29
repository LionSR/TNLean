/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactGroundPathEndpointClass
import TNLean.MPS.Symmetry.CommonPhysicalExactPhase
import TNLean.MPS.Core.PhysicalIndexMixing
import TNLean.MPS.Symmetry.EntanglementSpectrum
import TNLean.Wielandt.SpanGrowth.CumulativeSpan

/-!
# Cohomology obstruction to an independent exact MPS gapped phase

Blocking retains the virtual factor system, and an isometric inclusion of
the entire physical space retains its virtual covariance and injectivity.
The independently defined physical phase path therefore identifies the
prescribed endpoint classes. The path may vary the minimal bond dimension;
no virtual interpolation or spectral estimate is assumed.

Source: arXiv:1010.3732, Sections II.C.1–2 and II.F.2, and Appendix C.

**Scope restriction (one-site injective endpoints with exact covariance):**
The concluding phase theorem uses the same endpoint domain as the existing
forward construction. The several-block and original scalar-character
extensions are recorded in
`docs/paper-gaps/spc11_uniform_gap_injective_scope.tex` and
`docs/paper-gaps/rmp_spt_fixed_point_trivial_character.tex`.
-/

open scoped Matrix BigOperators TNLean.Algebra.ScalarCohomology
open TNLean.Algebra

namespace MPSTensor

private theorem included_blockTensor_character_covariance
    {G : Type} [Group G] {d D m k : ℕ} (A : MPSTensor d D)
    (U₀ : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (U : G →* Matrix.unitaryGroup (Fin m) ℂ)
    (χ : G →* ℂ) (hχ : ∀ g, ‖χ g‖ = 1)
    (E : Matrix (Fin m) (Fin (blockPhysDim d k)) ℂ)
    (hE : ∀ g, (U g : Matrix (Fin m) (Fin m) ℂ) * E =
      E * (χ g • blockKron k (U₀ g)))
    {ω : ScalarCocycle G} (ρ : ProjectiveRepresentation (D := D) ω)
    (hρ : ∀ g i, twistedTensor A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U₀) g i =
      (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρ.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :
    ∀ g i, twistedTensor (rotatePhysical E (blockTensor A k))
      ((Matrix.unitaryGroup (Fin m) ℂ).subtype.comp
        (physicalCharacterUntwist χ hχ U)) g i =
      (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) *
        rotatePhysical E (blockTensor A k) i *
        (((ρ.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
  intro g i
  have hχne : χ g ≠ 0 := norm_ne_zero_iff.mp (by rw [hχ]; exact one_ne_zero)
  have hMatrix : ((χ g)⁻¹ • (U g : Matrix (Fin m) (Fin m) ℂ)) * E =
      E * blockKron k (U₀ g) := by
    rw [Matrix.smul_mul, hE g, Matrix.mul_smul, smul_smul,
      inv_mul_cancel₀ hχne, one_smul]
  have hBlocked := twistedTensor_blockTensor_eq_gauge
    (U := (Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U₀)
    (g := g) (R := ρ.X (g⁻¹)) (hρ g) k
  change rotatePhysical ((χ g)⁻¹ • (U g : Matrix (Fin m) (Fin m) ℂ))
    (rotatePhysical E (blockTensor A k)) i = _
  rw [rotatePhysical_rotatePhysical, hMatrix, ← rotatePhysical_rotatePhysical]
  change (∑ j, E i j •
    twistedTensor (blockTensor A k)
      (blockKronAction k ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U₀)) g j) = _
  simp only [hBlocked, rotatePhysical, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]

/-- The independent physical exact-MPS phase condition forces equality of
the prescribed virtual cohomology classes. The common blocking, physical
character changes, orthogonal physical inclusions, and changing minimal bond
dimension are those already permitted by the phase definition; no virtual
path, clustering, or transfer-gap premise is added. Source: arXiv:1010.3732,
Sections II.C.1–2 and II.F.2 and Appendix C. -/
theorem IsSameExactMPSGappedPhase.cohomologousTo
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₀] [NeZero D₁]
    {A₀ : MPSTensor d₀ D₀} {A₁ : MPSTensor d₁ D₁}
    {U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ}
    {U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ}
    (hPhase : IsSameExactMPSGappedPhase A₀ A₁ U₀ U₁)
    (hA₀ : Kraus.IsInjective A₀) (hA₁ : Kraus.IsInjective A₁)
    {ω₀ ω₁ : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω₁)
    (hρ₀ : ∀ g i, twistedTensor A₀ ((Matrix.unitaryGroup (Fin d₀) ℂ).subtype.comp U₀) g i =
      (ρ₀.X (g⁻¹) : Matrix (Fin D₀) (Fin D₀) ℂ) * A₀ i *
        (((ρ₀.X (g⁻¹))⁻¹ : GL (Fin D₀) ℂ) : Matrix (Fin D₀) (Fin D₀) ℂ))
    (hρ₁ : ∀ g i, twistedTensor A₁ ((Matrix.unitaryGroup (Fin d₁) ℂ).subtype.comp U₁) g i =
      (ρ₁.X (g⁻¹) : Matrix (Fin D₁) (Fin D₁) ℂ) * A₁ i *
        (((ρ₁.X (g⁻¹))⁻¹ : GL (Fin D₁) ℂ) : Matrix (Fin D₁) (Fin D₁) ℂ)) :
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
      (ScalarCocycle.isMulCocycle₂_of_projRep ρ₁ (NeZero.pos D₁))) =
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
      (ScalarCocycle.isMulCocycle₂_of_projRep ρ₀ (NeZero.pos D₀))) := by
  obtain ⟨k, hk, m, U, χ₀, χ₁, hχ₀, hχ₁, E₀, E₁,
    hE₀, hE₁, _, hCov₀, hCov₁, P, Q, hQ₀, hQ₁⟩ := hPhase
  have hBlock₀ : Kraus.IsInjective (blockTensor A₀ k) :=
    (isNBlkInjective_iff_blockTensor_isInjective A₀ k).mp
      (isNBlkInjective_of_le zero_lt_one (Kraus.isNBlkInjective_one_of_isInjective hA₀) hk)
  have hBlock₁ : Kraus.IsInjective (blockTensor A₁ k) :=
    (isNBlkInjective_iff_blockTensor_isInjective A₁ k).mp
      (isNBlkInjective_of_le zero_lt_one (Kraus.isNBlkInjective_one_of_isInjective hA₁) hk)
  exact Q.cohomologousTo_endpoints
    (isInjective_kraus_isometry _ E₀ hE₀ hBlock₀)
    (isInjective_kraus_isometry _ E₁ hE₁ hBlock₁) hQ₀ hQ₁ χ₀ χ₁ hχ₀ hχ₁ ρ₀ ρ₁
    (included_blockTensor_character_covariance A₀ U₀ U χ₀ hχ₀ E₀ hCov₀ ρ₀ hρ₀)
    (included_blockTensor_character_covariance A₁ U₁ U χ₁ hχ₁ E₁ hCov₁ ρ₁ hρ₁)

/-- On the one-site injective endpoint domain with prescribed exact virtual
covariance, the independent exact physical phase relation is equivalent to
equality of the virtual cohomology classes. Source: arXiv:1010.3732,
Sections II.C.1–2 and II.F.2; the scope is specified in the module docstring. -/
theorem isSameExactMPSGappedPhase_iff_cohomologous
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₀] [NeZero D₁]
    {A₀ : MPSTensor d₀ D₀} {A₁ : MPSTensor d₁ D₁}
    {U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ}
    {U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ}
    (hA₀ : Kraus.IsInjective A₀) (hA₁ : Kraus.IsInjective A₁)
    {ω₀ ω₁ : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω₁)
    (hρ₀ : ∀ g i, twistedTensor A₀ ((Matrix.unitaryGroup (Fin d₀) ℂ).subtype.comp U₀) g i =
      (ρ₀.X (g⁻¹) : Matrix (Fin D₀) (Fin D₀) ℂ) * A₀ i *
        (((ρ₀.X (g⁻¹))⁻¹ : GL (Fin D₀) ℂ) : Matrix (Fin D₀) (Fin D₀) ℂ))
    (hρ₁ : ∀ g i, twistedTensor A₁ ((Matrix.unitaryGroup (Fin d₁) ℂ).subtype.comp U₁) g i =
      (ρ₁.X (g⁻¹) : Matrix (Fin D₁) (Fin D₁) ℂ) * A₁ i *
        (((ρ₁.X (g⁻¹))⁻¹ : GL (Fin D₁) ℂ) : Matrix (Fin D₁) (Fin D₁) ℂ)) :
    IsSameExactMPSGappedPhase A₀ A₁ U₀ U₁ ↔
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
      (ScalarCocycle.isMulCocycle₂_of_projRep ρ₁ (NeZero.pos D₁))) =
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
      (ScalarCocycle.isMulCocycle₂_of_projRep ρ₀ (NeZero.pos D₀))) := by
  constructor
  · intro hPhase
    exact hPhase.cohomologousTo hA₀ hA₁ ρ₀ ρ₁ hρ₀ hρ₁
  · intro hClass
    exact isSameExactMPSGappedPhase_of_isInjective_cohomologous
      ρ₀ ρ₁ U₀ U₁ A₀ hA₀ A₁ hA₁ hρ₀ hρ₁ hClass

end MPSTensor
