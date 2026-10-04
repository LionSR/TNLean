/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.CompactMinimalClassStability
import TNLean.MPS.Symmetry.VaryingBondPhysicalCharacter
import TNLean.MPS.Symmetry.PolarVirtualCohomology
import TNLean.MPS.Symmetry.ExactMPSPhaseGaugeInvariance
import Mathlib.Topology.LocallyConstant.Basic
import TNLean.Algebra.UnitaryGeneralLinearInverse

/-!
# Virtual classes of exact ground-state paths under a transfer bound

The finite-chain ground lines determine a common physical character.
After removing this character, injective representatives of the periodic
rays have unitary virtual projective actions. Compactness and a supplied
uniform transfer bound imply local constancy of their classes; connectedness
of the interval then gives one class along the whole path.

Source context: arXiv:1010.3732, Appendix B, lines 2614–2632, and Appendix C,
lines 2653–2717. The uniform transfer bound is an explicit auxiliary
hypothesis. Its derivation from the Hamiltonian gap is separate; see
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix Matrix.Norms.Frobenius Topology
open Filter TNLean.Algebra

namespace MPSTensor

private theorem isOnSiteSymmetric_of_samePositiveMpvRay
    {G : Type} [Group G] {d D E : ℕ} {A : MPSTensor d D} {B : MPSTensor d E}
    (hRay : SamePositiveMpvRay A B)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (hA : IsOnSiteSymmetric A U) :
    IsOnSiteSymmetric B U := by
  intro g N s
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [mpv, coeff]
  · simpa only [one_mul] using (hRay.symmetry_eigenvalue U g 1 hN
      (fun s => by simpa only [one_mul] using (hA g N s).symm) s).symm

private theorem cohomologousTo_of_locally_constant_classes
    {T G : Type} [TopologicalSpace T] [PreconnectedSpace T] [Group G]
    (ω : T → ScalarCocycle G)
    (hω : ∀ s, ∀ᶠ t in 𝓝 s, (ω t).CohomologousTo (ω s)) :
    ∀ s t, (ω t).CohomologousTo (ω s) := by
  let f : T → Quotient (scalarCocycleSetoid (G := G)) := fun t => Quotient.mk' (ω t)
  have hf : IsLocallyConstant f := IsLocallyConstant.iff_eventually_eq f |>.mpr
    (fun s => (hω s).mono fun t ht => Quotient.sound ht)
  intro s t
  exact Quotient.exact (congrFun (hf.eq_const s) t)

private theorem exists_unitary_projective_covariance_of_unital_symmetry
    {G : Type} [Group G] {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hAU : Kraus.IsUnital A)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (hSym : IsOnSiteSymmetric A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U)) :
    ∃ ω : ScalarCocycle G, ∃ ρ : ProjectiveRepresentation (D := D) ω,
      (∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ) ∧
      ∀ g, rotatePhysical (U g) A = fun i =>
        (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
          (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  obtain ⟨ω, ρ, hρ, hCov⟩ := exists_unitary_virtualRep_polarDeformation
    A hA (Kraus.map_one_of_isUnital A hAU) U hSym
  refine ⟨ω, ρ, hρ, ?_⟩
  intro g
  funext i
  have h := hCov 1 g i
  simp only [polarDeformation_one] at h
  rw [Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup _ (hρ _)] at h
  exact h

/-- A continuous exact ground-state path has one virtual cohomology class
under a supplied uniform bound below one on the nonunit transfer spectra
of its unital injective representatives. The common physical character,
representatives, and unitary virtual actions are derived. Source context:
arXiv:1010.3732, Appendix B, lines 2614–2632, and Appendix C, lines 2653–2717.
This is a transfer-bound conditional result, not a Hamiltonian-gap theorem. -/
theorem ExactMPSGroundPath.exists_constant_virtual_class_of_uniform_transfer_bound
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁} (Q : ExactMPSGroundPath P)
    (q : ℝ) (hq : 0 ≤ q) (hqOne : q < 1)
    (hTransfer : ∀ t : unitInterval, ∀ D : ℕ, 0 < D → ∀ A : MPSTensor d D,
      Kraus.IsInjective A → Kraus.IsUnital A → SamePositiveMpvRay (Q.tensor t) A →
      ∀ z ∈ spectrum ℂ (Kraus.transferMap A), z ≠ 1 → ‖z‖ ≤ q) :
    ∃ χ : G →* ℂ, ∃ hχ : ∀ g, ‖χ g‖ = 1,
    ∃ D : unitInterval → ℕ, ∃ A : ∀ t, MPSTensor d (D t),
    ∃ ω : unitInterval → ScalarCocycle G,
    ∃ ρ : ∀ t, ProjectiveRepresentation (D := D t) (ω t),
      (∀ t, 0 < D t ∧ D t ≤ Q.bondDimension) ∧
      (∀ t, Kraus.IsInjective (A t) ∧ Kraus.IsUnital (A t)) ∧
      (∀ t : unitInterval, SamePositiveMpvRay (Q.tensor t) (A t)) ∧
      (∀ t g, ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ) ∈
        Matrix.unitaryGroup _ ℂ) ∧
      (∀ t g, rotatePhysical (physicalCharacterUntwist χ hχ U g) (A t) = fun i =>
        ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
          ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ)ᴴ) ∧
      ∀ s t, (ω t).CohomologousTo (ω s) := by
  classical
  obtain ⟨χ, hχ, hSym⟩ := Q.exists_exact_symmetry
  let V := physicalCharacterUntwist χ hχ U
  have hData : ∀ t : unitInterval, ∃ D : ℕ, 0 < D ∧ D ≤ Q.bondDimension ∧
      ∃ A : MPSTensor d D, Kraus.IsInjective A ∧ Kraus.IsUnital A ∧
        SamePositiveMpvRay (Q.tensor t) A := by
    intro t
    obtain ⟨D, hD, hBound, A, hA, hRay⟩ := Q.injective_representative t t.property
    let : NeZero D := ⟨hD.ne'⟩
    obtain ⟨B, c, hc, hGauge, hB, hBU, _⟩ :=
      exists_unital_parent_representative_of_isInjective A hA
    refine ⟨D, hD, hBound, B, hB, ?_,
      hRay.trans (samePositiveMpvRay_of_smul_gaugeEquiv c hc hGauge)⟩
    change ∑ i, B i * (B i)ᴴ = 1
    simpa only [Kraus.transferMap_apply, Matrix.mul_one] using hBU
  choose D hD hBound A hA hAU hRay using hData
  have hVirtual : ∀ t, ∃ ω : ScalarCocycle G,
      ∃ ρ : ProjectiveRepresentation (D := D t) ω,
        (∀ g, (ρ.X g : Matrix (Fin (D t)) (Fin (D t)) ℂ) ∈
          Matrix.unitaryGroup _ ℂ) ∧
        ∀ g, rotatePhysical (V g) (A t) = fun i =>
          (ρ.X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
            (ρ.X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ)ᴴ := by
    intro t
    let : NeZero (D t) := ⟨(hD t).ne'⟩
    exact exists_unitary_projective_covariance_of_unital_symmetry (A t) (hA t) (hAU t)
      V (isOnSiteSymmetric_of_samePositiveMpvRay (hRay t) _ (hSym t))
  choose ω ρ hρ hCov using hVirtual
  refine ⟨χ, hχ, D, A, ω, ρ, fun t => ⟨hD t, hBound t⟩,
    fun t => ⟨hA t, hAU t⟩, hRay, hρ, hCov, ?_⟩
  apply cohomologousTo_of_locally_constant_classes ω
  intro t₀
  have hQ : Continuous (fun t : unitInterval => Q.tensor t) := Q.continuous.domRestrict
  exact eventually_cohomologousTo_of_continuousAt_bounded_unital_periodic_rays
    D hD hBound A
    (fun t => Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM (A t)
      (Kraus.injective_implies_irreducibleCP (A t) (hA t))) hAU t₀ (hA t₀)
    (fun t => Q.tensor t) hQ.continuousAt hRay q hq hqOne
    (fun t => hTransfer t (D t) (hD t) (A t) (hA t) (hAU t) (hRay t))
    V ω ρ hρ hCov

end MPSTensor
