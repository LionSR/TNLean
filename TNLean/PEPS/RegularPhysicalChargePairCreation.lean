/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularRegionChargePairCreation
import TNLean.PEPS.RegularChargeCompleteMeasurement
import TNLean.PEPS.RegularPhysicalUnitaryTransport

/-!
# Literal correlated charge-pair columns on original spins

The two-bond character weight is retained inside the actual open contraction.
Local regular invariance identifies this contraction with the image of its
canonical column. Local G-isometry then supplies physical unitary transport.
Source: SCP10, arXiv:1001.3807, charge-pair creation, lines 2505–2558.
These finite-region formulas do not assume a Gram or boundary-column identity.
-/
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {κ : V → Type*}

/-- The actual original-spin open contraction with the two-bond correlated weight
of the printed charge-pair operator. Source: SCP10, lines 2505–2558. -/
def regularChargePairOpenRegionMatrix
    (a : (v : V) → (IncidentEdge Γ v → G) → κ v → ℂ) (R : Finset V)
    (e₀ e₁ : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}) (χ : G → ℂ) (p : G) :
    Matrix ((v : {v // v ∈ R}) → κ v.1)
      ({e : Edge Γ // IsRegionBoundaryEdge R e} → G) ℂ :=
  fun s θ => ∑ η : {e : Edge Γ // IsRegionIncidentEdge R e} → G,
    if (fun f : {e : Edge Γ // IsRegionBoundaryEdge R e} =>
        η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = θ then
      χ (p * (η ⟨e₁.1, Or.inl e₁.2.1⟩)⁻¹ * η ⟨e₀.1, Or.inl e₀.2.1⟩) *
      ∏ w : {w : V // w ∈ R},
        a w.1 (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩) (s w)
    else 0

/-- The product of the original site maps sends the actual canonical correlated
column to the actual physical correlated contraction. Source: SCP10, the
accessible-to-physical comparison in charge-pair creation, lines 2534–2558. -/
theorem regularChargePairOpenRegionMatrix_eq_image
    (a : (v : V) → (IncidentEdge Γ v → G) → κ v → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (e₀ e₁ : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}) (χ : G → ℂ) (p : G)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s) *ᵥ
        (fun α => regularProjectorChargePairOpenRegionMatrix R e₀ e₁ χ p α θ) =
      fun s => regularChargePairOpenRegionMatrix a R e₀ e₁ χ p s θ := by
  classical
  let T := regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s)
  let P := regionPhysicalProductMatrix R
    (fun v => regularLegProjector (G := G) (IncidentEdge Γ v))
  let z : RegionHalfEdgeConfig (Γ := Γ) G R → ℂ :=
    ∑ η : {e : Edge Γ // IsRegionIncidentEdge R e} → G,
      if (fun f : {e : Edge Γ // IsRegionBoundaryEdge R e} =>
          η ⟨f.1, isRegionBoundaryEdge_touches R f.2⟩) = θ then
        χ (p * (η ⟨e₁.1, Or.inl e₁.2.1⟩)⁻¹ * η ⟨e₀.1, Or.inl e₀.2.1⟩) •
          Pi.single (fun w f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩) 1
      else 0
  have hP : P *ᵥ z = fun α =>
      regularProjectorChargePairOpenRegionMatrix R e₀ e₁ χ p α θ := by
    rw [show z = _ from rfl, Matrix.mulVec_sum]
    funext α
    simp only [Finset.sum_apply, regularProjectorChargePairOpenRegionMatrix]
    apply Finset.sum_congr rfl
    intro η _
    split_ifs
    · simp only [Matrix.mulVec_smul, Matrix.mulVec_single_one, Pi.smul_apply,
        smul_eq_mul, P]
      rfl
    · simp only [Matrix.mulVec_zero, Pi.zero_apply]
  have hT : T *ᵥ z = fun s => regularChargePairOpenRegionMatrix a R e₀ e₁ χ p s θ := by
    rw [show z = _ from rfl, Matrix.mulVec_sum]
    funext s
    simp only [Finset.sum_apply, regularChargePairOpenRegionMatrix]
    apply Finset.sum_congr rfl
    intro η _
    split_ifs
    · simp only [Matrix.mulVec_smul, Matrix.mulVec_single_one, Pi.smul_apply,
        smul_eq_mul, T]
      rfl
    · simp only [Matrix.mulVec_zero, Pi.zero_apply]
  have hTP : T * P = T :=
    regionPhysicalProductMatrix_mul_regularLocalProjector a ha R
  rw [← hP, Matrix.mulVec_mulVec, hTP]
  exact hT


/-- Removing the correlated weight recovers the actual numbered open-region
contraction. Source: SCP10, the unmodified six-spin input in lines 2505–2558. -/
theorem regularChargePairOpenRegionMatrix_one_eq_openRegionWeight {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (e₀ e₁ : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R})
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    (fun s => regularChargePairOpenRegionMatrix a R e₀ e₁ (fun _ => 1) 1 s θ) =
      openRegionWeight (groupBondTensor a) R (fun f => Fintype.equivFin G (θ f)) := by
  rw [← regularChargePairOpenRegionMatrix_eq_image a ha R e₀ e₁ _ 1 θ]
  have hplain : (fun α => regularProjectorChargePairOpenRegionMatrix
        (G := G) R e₀ e₁ (fun _ => 1) 1 α θ) =
      fun α => regularProjectorOpenRegionMatrix R α θ := by
    funext α
    simp only [regularProjectorChargePairOpenRegionMatrix, regularProjectorOpenRegionMatrix,
      one_mul]
  rw [hplain]
  exact regionPhysicalMap_regularProjectorOpenRegionMatrix a ha R θ

/-- The actual correlated two-bond charge insertion can be prepared by one unitary
on the original spins, uniformly in every remaining boundary label. The local
Gram matrix and the reference symmetry are derived rather than assumed.
Source: SCP10, charge-pair creation, lines 2505–2558. This is an auxiliary
finite-region statement with a specified tree and two distinct internal bonds. -/
theorem exists_unitary_regularPhysicalChargePairCreation
    [∀ v, Fintype (κ v)] [∀ v, DecidableEq (κ v)]
    (a : (v : V) → (IncidentEdge Γ v → G) → κ v → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R})
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (e₀ e₁ : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}) (hne : e₀ ≠ e₁)
    (χ : G → ℂ) (hχ : χ ∈ regularChargeLabels (G := G)) (p : G) :
    ∃ W : Matrix ((v : {v // v ∈ R}) → κ v.1) ((v : {v // v ∈ R}) → κ v.1) ℂ,
      W ∈ Matrix.unitaryGroup _ ℂ ∧
      ∀ θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G,
        W *ᵥ (fun s => regularChargePairOpenRegionMatrix a R e₀ e₁ (fun _ => 1) 1 s θ) =
          fun s => regularChargePairOpenRegionMatrix a R e₀ e₁ χ p s θ := by
  classical
  obtain ⟨S, hS, rfl, hunit⟩ := exists_unitary_irreducible_regularChargeLabel χ hχ
  let := hS
  obtain ⟨Q, hQ, hact, hcomm⟩ :=
    exists_unitary_regularChargeReferencePreparation S.toRepresentation hunit p
  have hn : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hraw : Q *ᵥ (fun _ : G × G => (1 : ℂ)) =
      regularChargePairCoefficient S.toRepresentation.character p := by
    simp only [normalizedRegularChargePairCoefficient, Nat.card_eq_fintype_card] at hact
    rw [Matrix.mulVec_smul] at hact
    funext q
    exact mul_left_cancel₀ (inv_ne_zero hn) (congrFun hact q)
  let U := regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne Q
  have hU : U ∈ Matrix.unitaryGroup _ ℂ :=
    regularRegionChargeReferenceMatrix_mem_unitaryGroup R T hT htree o e₀ e₁ hne Q hQ
  have hUP := regularRegionChargeReferenceMatrix_commute_localProjector
    R T hT htree o e₀ e₁ hne Q hcomm
  obtain ⟨W, hW, hWT⟩ :=
    exists_unitary_regionPhysicalProductMatrix_mul_of_projector_commute a ha R U hU hUP.eq
  refine ⟨W, hW, fun θ => ?_⟩
  have hplain : (fun α => regularProjectorChargePairOpenRegionMatrix
        (G := G) R e₀ e₁ (fun _ => 1) 1 α θ) =
      fun α => regularProjectorOpenRegionMatrix R α θ := by
    funext α
    simp only [regularProjectorChargePairOpenRegionMatrix, regularProjectorOpenRegionMatrix,
      one_mul]
  rw [← regularChargePairOpenRegionMatrix_eq_image a
      (fun v => (ha v).toIsGInjective) R e₀ e₁ _ 1 θ,
    hplain, Matrix.mulVec_mulVec, hWT, ← Matrix.mulVec_mulVec]
  rw [regularRegionChargeReferenceMatrix_mulVec R T hT htree o e₀ e₁ hne Q
    S.toRepresentation.character p hraw θ]
  exact regularChargePairOpenRegionMatrix_eq_image a
    (fun v => (ha v).toIsGInjective) R e₀ e₁ S.toRepresentation.character p θ

end TNLean.PEPS
