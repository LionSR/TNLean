/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.TriangularBoundaryDecomposition
import TNLean.MPS.MPDO.TriangularPaddingGauge
import TNLean.MPS.MPDO.BoundaryZipperBlocked

/-!
# A common positive blocking for triangular fusion and action families

The operator and state blocks remain labelled by their disjoint union.
Relabelling only the simultaneous-inverse argument by a finite ordinal
supplies a common positive blocking. Returning its inverse rows to the
disjoint-union labels leaves all fusion and action matrices unchanged.

Individual injectivity, positive virtual dimensions, and scalar-gauge
separation within each original kind suffice. Separation across the two
kinds follows from their disjoint padded physical supports. No simultaneous
inverse or coherence equation is assumed in the source construction.

Source: Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `rawrels`,
`eq:F_symbol2`, `coupledpent`, and Appendix A; arXiv:1511.08090,
simultaneous block inverse at lines 269--277 and blocking at lines 427--431.
-/

open scoped Matrix BigOperators

namespace MPSTensor.IsBiorthogonalDecomposition

/-- Positive physical blocking preserves an exact pairwise decomposition
over any finite label type, with its rectangular matrices unchanged. -/
theorem blockMPO_fintype {Λ : Type*} [Fintype Λ] {p : ℕ} {D : Λ → ℕ}
    {T : ∀ c, MPOTensor p (D c)} {N : Λ → ℕ} {a b : Λ}
    {V : ∀ c, Fin (N c) → Matrix (Fin (D c)) (Fin (D a * D b)) ℂ}
    {W : ∀ c, Fin (N c) → Matrix (Fin (D a * D b)) (Fin (D c)) ℂ}
    (h : IsBiorthogonalDecomposition (MPOTensor.mulTensor (T a) (T b)).toMPSTensor
      (fun q : (c : Λ) × Fin (N c) ↦ (T q.1).toMPSTensor)
      (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2))
    {L : ℕ} (hL : 0 < L) :
    IsBiorthogonalDecomposition
      (MPOTensor.mulTensor (MPOTensor.blockTensor (T a) L)
        (MPOTensor.blockTensor (T b) L)).toMPSTensor
      (fun q : (c : Λ) × Fin (N c) ↦ (MPOTensor.blockTensor (T q.1) L).toMPSTensor)
      (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2) :=
  h.ofWords (MPOTensor.blockedPairWord p L) (MPOTensor.blockedPairWord_ne_nil hL)
    (fun I ↦ by
      rw [← MPOTensor.blockTensor_mulTensor]
      exact MPOTensor.toMPSTensor_blockTensor_apply _ L I)
    (fun q I ↦ MPOTensor.toMPSTensor_blockTensor_apply (T q.1) L I)

end MPSTensor.IsBiorthogonalDecomposition

namespace MPOTensor

/-- The derived common-block inverse is independent of the finite label
coordinates. Only its row label is transported by the given equivalence. -/
theorem exists_blockTensor_leftInverse_of_labelEquiv
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {p g : ℕ} {D : Λ → ℕ}
    (e : Λ ≃ Fin g) (T : ∀ c, MPOTensor p (D c))
    (hT : ∀ c, Kraus.IsNormal (T c).toMPSTensor) (hD : ∀ c, 0 < D c)
    (hne : ∀ a b : Λ, a ≠ b → ∀ h : D a = D b,
      ¬ MPSTensor.GaugePhaseEquiv
        (cast (congrArg (MPSTensor (p * p)) h) (T a).toMPSTensor) (T b).toMPSTensor) :
    ∃ L : ℕ, 0 < L ∧ (∀ c, Kraus.IsInjective (blockTensor (T c) L).toMPSTensor) ∧
      ∃ K : Matrix ((c : Λ) × (Fin (D c) × Fin (D c)))
          (Fin (MPSTensor.blockPhysDim p L) × Fin (MPSTensor.blockPhysDim p L)) ℂ,
        ∀ (a b : Λ) (x y : Fin (D a)) (x' y' : Fin (D b)),
          (∑ i, ∑ j, K ⟨a, x, y⟩ (i, j) * blockTensor (T b) L i j x' y') =
            if he : a = b then
              if _ : he ▸ x = x' then if _ : he ▸ y = y' then 1 else 0 else 0
            else 0 := by
  classical
  obtain ⟨L, hL, hInj, K, hK⟩ := exists_blockTensor_isMPOBlockLeftInverse
    (fun c ↦ T (e.symm c)) (fun c ↦ hT (e.symm c)) (fun c ↦ hD (e.symm c))
    (fun a b hab hdim ↦ hne (e.symm a) (e.symm b) (e.symm.injective.ne hab) hdim)
  let Krow : ∀ c : Λ, Matrix (Fin (D c) × Fin (D c))
      (Fin (MPSTensor.blockPhysDim p L) × Fin (MPSTensor.blockPhysDim p L)) ℂ :=
    Equiv.piCongrLeft (fun c ↦ Matrix (Fin (D c) × Fin (D c))
      (Fin (MPSTensor.blockPhysDim p L) × Fin (MPSTensor.blockPhysDim p L)) ℂ)
      e.symm (fun c xy ij ↦ K ⟨c, xy⟩ ij)
  refine ⟨L, hL, ?_, (fun q ↦ Krow q.1 q.2), ?_⟩
  · intro c
    obtain ⟨j, rfl⟩ := e.symm.surjective c
    exact hInj j
  · intro a b
    obtain ⟨j, rfl⟩ := e.symm.surjective a
    obtain ⟨k, rfl⟩ := e.symm.surjective b
    intro x y x' y'
    have hspec := hK j k x y x' y'
    by_cases hjk : j = k
    · subst k
      simpa [Krow] using hspec
    · have hne' : e.symm j ≠ e.symm k := e.symm.injective.ne hjk
      simpa [Krow, hjk, hne'] using hspec

private theorem gaugePhaseEquiv_of_operatorPhysicalPadding_cast
    {d D₁ D₂ : ℕ} (hD : D₁ = D₂) {O : MPOTensor d D₁} {P : MPOTensor d D₂}
    (h : MPSTensor.GaugePhaseEquiv
      (cast (congrArg (MPSTensor ((d + 1) * (d + 1))) hD)
        (operatorPhysicalPadding O).toMPSTensor)
      (operatorPhysicalPadding P).toMPSTensor) :
    MPSTensor.GaugePhaseEquiv
      (cast (congrArg (MPSTensor (d * d)) hD) O.toMPSTensor) P.toMPSTensor := by
  subst D₂
  exact gaugePhaseEquiv_of_operatorPhysicalPadding h

private theorem gaugePhaseEquiv_of_statePhysicalPadding_cast
    {d D₁ D₂ : ℕ} (hD : D₁ = D₂) {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (h : MPSTensor.GaugePhaseEquiv
      (cast (congrArg (MPSTensor ((d + 1) * (d + 1))) hD)
        (statePhysicalPadding A).toMPSTensor)
      (statePhysicalPadding B).toMPSTensor) :
    MPSTensor.GaugePhaseEquiv (cast (congrArg (MPSTensor d) hD) A) B := by
  subst D₂
  exact gaugePhaseEquiv_of_statePhysicalPadding h

private theorem not_gaugePhaseEquiv_operatorPhysicalPadding_statePhysicalPadding_cast
    {d D₁ D₂ : ℕ} (hDim : D₁ = D₂) (O : MPOTensor d D₁) {A : MPSTensor d D₂}
    (hD : 0 < D₂) (hA : Kraus.IsInjective A) :
    ¬ MPSTensor.GaugePhaseEquiv
      (cast (congrArg (MPSTensor ((d + 1) * (d + 1))) hDim)
        (operatorPhysicalPadding O).toMPSTensor)
      (statePhysicalPadding A).toMPSTensor := by
  subst D₂
  exact not_gaugePhaseEquiv_operatorPhysicalPadding_statePhysicalPadding O hD hA

private theorem not_gaugePhaseEquiv_statePhysicalPadding_operatorPhysicalPadding_cast
    {d D₁ D₂ : ℕ} (hDim : D₁ = D₂) (A : MPSTensor d D₁) {O : MPOTensor d D₂}
    (hD : 0 < D₂) (hO : Kraus.IsInjective O.toMPSTensor) :
    ¬ MPSTensor.GaugePhaseEquiv
      (cast (congrArg (MPSTensor ((d + 1) * (d + 1))) hDim)
        (statePhysicalPadding A).toMPSTensor)
      (operatorPhysicalPadding O).toMPSTensor := by
  subst D₂
  exact not_gaugePhaseEquiv_statePhysicalPadding_operatorPhysicalPadding A hD hO

variable {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  (O : ∀ a, MPOTensor d (χ a)) (A : ∀ x, MPSTensor d (D x))
  (hInjO : ∀ a, Kraus.IsInjective (O a).toMPSTensor)
  (hInjA : ∀ x, Kraus.IsInjective (A x))
  (hχ : ∀ a, 0 < χ a) (hD : ∀ x, 0 < D x)
  (hneO : MPSTensor.BlocksNotGaugePhaseEquiv (fun a ↦ (O a).toMPSTensor))
  (hneA : MPSTensor.BlocksNotGaugePhaseEquiv A)

include hInjO hInjA hχ hD hneO hneA in
private theorem triangularTensor_separated
    (a b : Fin r ⊕ Fin s) (hab : a ≠ b)
    (hDim : triangularBondDim χ D a = triangularBondDim χ D b) :
    ¬ MPSTensor.GaugePhaseEquiv
      (cast (congrArg (MPSTensor ((d + 1) * (d + 1))) hDim)
        (triangularTensor O A a).toMPSTensor) (triangularTensor O A b).toMPSTensor := by
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      intro h
      exact hneO a b (fun he ↦ hab (congrArg Sum.inl he)) hDim
        (gaugePhaseEquiv_of_operatorPhysicalPadding_cast hDim h)
    | inr y =>
      exact not_gaugePhaseEquiv_operatorPhysicalPadding_statePhysicalPadding_cast
        hDim (O a) (hD y) (hInjA y)
  | inr x =>
    cases b with
    | inl b =>
      exact not_gaugePhaseEquiv_statePhysicalPadding_operatorPhysicalPadding_cast
        hDim (A x) (hχ b) (hInjO b)
    | inr y =>
      intro h
      exact hneA x y (fun he ↦ hab (congrArg Sum.inr he)) hDim
        (gaugePhaseEquiv_of_statePhysicalPadding_cast hDim h)

include hInjO hInjA hχ hD hneO hneA in
/-- Original individual injectivity and within-kind scalar-gauge separation
derive one common positive blocking and a simultaneous inverse for the
disjoint-union family. Cross-kind separation follows from physical support. -/
theorem exists_triangular_blockTensor_leftInverse :
    ∃ L : ℕ, 0 < L ∧
      (∀ c, Kraus.IsInjective (blockTensor (triangularTensor O A c) L).toMPSTensor) ∧
      ∃ K : Matrix ((c : Fin r ⊕ Fin s) ×
          (Fin (triangularBondDim χ D c) × Fin (triangularBondDim χ D c)))
          (Fin (MPSTensor.blockPhysDim (d + 1) L) ×
            Fin (MPSTensor.blockPhysDim (d + 1) L)) ℂ,
        ∀ (a b : Fin r ⊕ Fin s) (x y : Fin (triangularBondDim χ D a))
          (x' y' : Fin (triangularBondDim χ D b)),
          (∑ i, ∑ j, K ⟨a, x, y⟩ (i, j) *
            blockTensor (triangularTensor O A b) L i j x' y') =
            if he : a = b then
              if _ : he ▸ x = x' then if _ : he ▸ y = y' then 1 else 0 else 0
            else 0 := by
  apply exists_blockTensor_leftInverse_of_labelEquiv finSumFinEquiv (triangularTensor O A)
  · intro c
    cases c with
    | inl a => exact (isInjective_operatorPhysicalPadding (hInjO a)).isNormal
    | inr x => exact (isInjective_statePhysicalPadding (hInjA x)).isNormal
  · intro c
    cases c with
    | inl a => exact hχ a
    | inr x => exact hD x
  · exact triangularTensor_separated O A hInjO hInjA hχ hD hneO hneA

/-- The common positive blocking length derived for the padded operator and
state blocks, with no simultaneous inverse among the inputs. -/
noncomputable def triangularBlockLength : ℕ :=
  (exists_triangular_blockTensor_leftInverse O A hInjO hInjA hχ hD hneO hneA).choose

/-- The selected common physical blocking is positive. -/
theorem triangularBlockLength_pos :
    0 < triangularBlockLength O A hInjO hInjA hχ hD hneO hneA :=
  (exists_triangular_blockTensor_leftInverse O A hInjO hInjA hχ hD hneO hneA).choose_spec.1

variable {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
  (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
  (hF : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
      (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
  (hAct : ∀ a x,
    MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
      (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
      (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2))

namespace CompleteZipperFusionFamily

/-- The exact original fusion and action matrices form a complete zipper
family after a derived common positive physical blocking. Its labels remain
the disjoint union, and its matrices are the original rectangular maps. -/
@[reducible] noncomputable def ofTriangularBiorthogonalBlocked :
    CompleteZipperFusionFamily (Fin r ⊕ Fin s)
      (MPSTensor.blockPhysDim (d + 1)
        (triangularBlockLength O A hInjO hInjA hχ hD hneO hneA)) :=
  let hspec :=
    (exists_triangular_blockTensor_leftInverse O A hInjO hInjA hχ hD hneO hneA).choose_spec
  ofBiorthogonal (T := fun c ↦ blockTensor (triangularTensor O A c)
      (triangularBlockLength O A hInjO hInjA hχ hD hneO hneA))
    (fun c ↦ by
      cases c with
      | inl a => exact hχ a
      | inr x => exact hD x) hspec.2.1
    (triangularFusionAnalysis VF VA) (triangularFusionSynthesis WF WA)
    (fun a b ↦ (isBiorthogonalDecomposition_triangularTensor VF WF VA WA O A hF hAct
      a b).blockMPO_fintype hspec.1)
    hspec.2.2.choose hspec.2.2.choose_spec

/-- The complete family uses the commonly blocked original padded tensor. -/
theorem ofTriangularBiorthogonalBlocked_tensor (c : Fin r ⊕ Fin s) :
    (ofTriangularBiorthogonalBlocked O A hInjO hInjA hχ hD hneO hneA
      VF WF VA WA hF hAct).tensor c =
        blockTensor (triangularTensor O A c)
          (triangularBlockLength O A hInjO hInjA hχ hD hneO hneA) := rfl

/-- Common blocking leaves the collected synthesis matrix unchanged. -/
theorem ofTriangularBiorthogonalBlocked_fusionSynthesis (a b : Fin r ⊕ Fin s) :
    (ofTriangularBiorthogonalBlocked O A hInjO hInjA hχ hD hneO hneA
      VF WF VA WA hF hAct).fusionSynthesis a b =
        biorthogonalSynthesis (triangularFusionSynthesis WF WA a b) := rfl

/-- Common blocking leaves the collected analysis matrix unchanged. -/
theorem ofTriangularBiorthogonalBlocked_fusionAnalysis (a b : Fin r ⊕ Fin s) :
    (ofTriangularBiorthogonalBlocked O A hInjO hInjA hχ hD hneO hneA
      VF WF VA WA hF hAct).fusionAnalysis a b =
        biorthogonalAnalysis (triangularFusionAnalysis VF VA a b) := rfl

end CompleteZipperFusionFamily

end MPOTensor
