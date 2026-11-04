/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactGroundPathEndpointClass
import TNLean.MPS.Symmetry.CommonPhysicalExactPhase
import TNLean.MPS.Core.PhysicalIndexMixing
import TNLean.MPS.Symmetry.EntanglementSpectrum
import TNLean.MPS.Symmetry.SpinHalfObstruction
import TNLean.Wielandt.SpanGrowth.CumulativeSpan

/-!
# Cohomology obstruction to an independent exact MPS gapped phase

Blocking retains the virtual factor system, and an isometric inclusion of
the entire physical space retains its virtual covariance and injectivity.
The independently defined physical phase path therefore identifies the
prescribed endpoint classes. The path may vary the minimal bond dimension;
no virtual interpolation or spectral estimate is assumed.

Source: arXiv:1010.3732, Sections II.C.1–2 and II.F.2, and Appendix C.

Endpoint symmetries carrying a unit-modulus character, as in Appendix B,
lines 2596–2599, are handled by the endpoint phase gauge of Section II.C.2,
lines 440–453: the phase relation is unchanged when an endpoint physical
action is multiplied by a character, so the character can be removed before
applying the exact-covariance theorem.

**Scope restriction (one-site injective endpoints):** The concluding phase
theorems use the same endpoint domain as the existing forward construction,
one-site injective original endpoints. This restriction and the remaining
source-classification comparison are recorded in
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`, in the section on
the source-written physical converse and endpoint domain.
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
      E * (χ g • blockKron k (U₀ g : Matrix (Fin d) (Fin d) ℂ)))
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
      E * blockKron k (U₀ g : Matrix (Fin d) (Fin d) ℂ) := by
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

/-- Multiplying the first endpoint physical action by a unit-modulus character
preserves the independent exact phase relation: the character is absorbed
into the relation's own endpoint character. Source: arXiv:1010.3732, Section II.C.2,
lines 440–453, and Appendix B, lines 2618–2632. -/
theorem IsSameExactMPSGappedPhase.of_smul_left
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ}
    {A₀ : MPSTensor d₀ D₀} {A₁ : MPSTensor d₁ D₁}
    {U₀ U₀' : G →* Matrix.unitaryGroup (Fin d₀) ℂ}
    {U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ}
    (χ : G →* ℂ) (hχ : ∀ g, ‖χ g‖ = 1)
    (hU : ∀ g, (U₀' g : Matrix (Fin d₀) (Fin d₀) ℂ) = χ g • (U₀ g : Matrix (Fin d₀) (Fin d₀) ℂ))
    (h : IsSameExactMPSGappedPhase A₀ A₁ U₀ U₁) :
    IsSameExactMPSGappedPhase A₀ A₁ U₀' U₁ := by
  rcases h with ⟨k, hk, m, U, χ₀, χ₁, hχ₀, hχ₁, E₀, E₁,
    hE₀, hE₁, hEorth, hCov₀, hCov₁, P, Q, hQ₀, hQ₁⟩
  refine ⟨k, hk, m, U, χ₀ * (invMonoidHom.comp χ) ^ k, χ₁, fun g => ?_, hχ₁, E₀, E₁,
    hE₀, hE₁, hEorth, fun g => ?_, hCov₁, P, Q, hQ₀, hQ₁⟩
  · simp [hχ₀, hχ]
  · have hχne : χ g ≠ 0 := Complex.ne_zero_of_norm_eq_one (hχ g)
    rw [hCov₀ g, hU g, blockKron_smul, smul_smul]
    congr 2
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.comp_apply,
      invMonoidHom_apply, inv_pow]
    rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hχne), mul_one]

/-- Classification for one-site injective endpoints whose prescribed virtual
actions implement the on-site symmetry up to unit-modulus characters, as in
arXiv:1010.3732, Appendix B, lines 2596–2599. The characters are removed by
the endpoint phase gauge of Section II.C.2, lines 440–453, as in Appendix B,
lines 2618–2632; the scope is specified in the module docstring. -/
theorem isSameExactMPSGappedPhase_iff_cohomologous_of_character
    {G : Type} [Group G] {d₀ d₁ D₀ D₁ : ℕ} [NeZero D₀] [NeZero D₁]
    {A₀ : MPSTensor d₀ D₀} {A₁ : MPSTensor d₁ D₁}
    {U₀ : G →* Matrix.unitaryGroup (Fin d₀) ℂ}
    {U₁ : G →* Matrix.unitaryGroup (Fin d₁) ℂ}
    (hA₀ : Kraus.IsInjective A₀) (hA₁ : Kraus.IsInjective A₁)
    {ω₀ ω₁ : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω₁)
    (χ₀ χ₁ : G →* ℂ) (hχ₀ : ∀ g, ‖χ₀ g‖ = 1) (hχ₁ : ∀ g, ‖χ₁ g‖ = 1)
    (hρ₀ : ∀ g i, twistedTensor A₀ ((Matrix.unitaryGroup (Fin d₀) ℂ).subtype.comp U₀) g i =
      χ₀ g • ((ρ₀.X (g⁻¹) : Matrix (Fin D₀) (Fin D₀) ℂ) * A₀ i *
        (((ρ₀.X (g⁻¹))⁻¹ : GL (Fin D₀) ℂ) : Matrix (Fin D₀) (Fin D₀) ℂ)))
    (hρ₁ : ∀ g i, twistedTensor A₁ ((Matrix.unitaryGroup (Fin d₁) ℂ).subtype.comp U₁) g i =
      χ₁ g • ((ρ₁.X (g⁻¹) : Matrix (Fin D₁) (Fin D₁) ℂ) * A₁ i *
        (((ρ₁.X (g⁻¹))⁻¹ : GL (Fin D₁) ℂ) : Matrix (Fin D₁) (Fin D₁) ℂ))) :
    IsSameExactMPSGappedPhase A₀ A₁ U₀ U₁ ↔
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
      (ScalarCocycle.isMulCocycle₂_of_projRep ρ₁ (NeZero.pos D₁))) =
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
      (ScalarCocycle.isMulCocycle₂_of_projRep ρ₀ (NeZero.pos D₀))) := by
  have hInvNorm : ∀ (χ : G →* ℂ), (∀ g, ‖χ g‖ = 1) → ∀ g, ‖(invMonoidHom.comp χ) g‖ = 1 :=
    fun χ hχ g => by simp [hχ]
  rw [← isSameExactMPSGappedPhase_iff_cohomologous hA₀ hA₁ ρ₀ ρ₁
    (U₀ := physicalCharacterUntwist χ₀ hχ₀ U₀) (U₁ := physicalCharacterUntwist χ₁ hχ₁ U₁)
    (fun g i => by rw [twistedTensor_physicalCharacterUntwist, Pi.smul_apply, hρ₀,
      inv_smul_smul₀ (Complex.ne_zero_of_norm_eq_one (hχ₀ g))])
    (fun g i => by rw [twistedTensor_physicalCharacterUntwist, Pi.smul_apply, hρ₁,
      inv_smul_smul₀ (Complex.ne_zero_of_norm_eq_one (hχ₁ g))])]
  constructor
  · intro h
    exact ((h.of_smul_left _ (hInvNorm χ₀ hχ₀) fun g => rfl).symm.of_smul_left _
      (hInvNorm χ₁ hχ₁) fun g => rfl).symm
  · intro h
    refine ((h.of_smul_left χ₀ hχ₀ fun g => ?_).symm.of_smul_left χ₁ hχ₁ fun g => ?_).symm
    · simp [smul_smul, mul_inv_cancel₀ (Complex.ne_zero_of_norm_eq_one (hχ₀ g))]
    · simp [smul_smul, mul_inv_cancel₀ (Complex.ne_zero_of_norm_eq_one (hχ₁ g))]

end MPSTensor
