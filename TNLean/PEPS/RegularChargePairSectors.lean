/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SemiRegularGroupAlgebra
import TNLean.PEPS.RegularPhysicalChargePairCreation
import TNLean.PEPS.RegularTwoSitePhysicalChargeMeasurement

/-!
# The two character slices of the actual correlated charge pair

Fixing the middle bond gives a translated original character on the top bond.
Fixing the top bond gives a translated contragredient character on the middle
bond. The correlated weight is retained throughout. Source: SCP10,
arXiv:1001.3807, charge-pair creation, lines 2505–2558.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Every actual regular charge label has an actual regular contragredient label.
No character table is assumed. Source: SCP10, conjugate charge, lines 2514–2518. -/
theorem regularChargeLabels_inv_mem (χ : G → ℂ)
    (hχ : χ ∈ regularChargeLabels (G := G)) :
    (fun g => χ g⁻¹) ∈ regularChargeLabels (G := G) := by
  obtain ⟨S, hS, rfl, _⟩ := exists_unitary_irreducible_regularChargeLabel χ hχ
  let := hS
  let := Representation.isIrreducible_dual S.toRepresentation
  have hc : S.toRepresentation.dual.character =
      fun g => S.toRepresentation.character g⁻¹ :=
    funext (Representation.char_dual S.toRepresentation)
  rw [← hc]
  exact character_mem_regularChargeLabels S.toRepresentation.dual

omit [Fintype G] [DecidableEq G] in
/-- The top-bond slice is a translated character of the original charge.
Source: SCP10, correlated pair equation, lines 2505–2513. -/
theorem regularChargePairCoefficient_top (χ : G → ℂ) (p middle top : G) :
    regularChargePairCoefficient χ p (top,middle) = χ ((p * middle⁻¹) * top) := rfl

omit [Fintype G] [DecidableEq G] in
/-- Cyclicity identifies the middle-bond slice with a translated dual character.
Source: SCP10, the conjugate charge of the created pair, lines 2514–2518. -/
theorem regularChargePairCoefficient_middle
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (σ : Representation ℂ G E) (p top middle : G) :
    regularChargePairCoefficient σ.character p (top,middle) =
      σ.dual.character ((top * p)⁻¹ * middle) := by
  rw [Representation.char_dual]
  simp only [regularChargePairCoefficient, mul_inv_rev, inv_inv, mul_assoc]
  simpa only [mul_assoc] using Representation.char_mul_comm σ (middle⁻¹ * top) p

/-- The actual contragredient label of a charge of the regular representation.
Source: SCP10, conjugate charge, lines 2514–2518. -/
def regularDualChargeLabel (χ : regularChargeLabels (G := G)) :
    regularChargeLabels (G := G) :=
  ⟨fun g => χ.val g⁻¹, regularChargeLabels_inv_mem χ.val χ.property⟩

private theorem middle_label_slice (χ : regularChargeLabels (G := G))
    (p top middle : G) :
    χ.val (p * middle⁻¹ * top) =
      (regularDualChargeLabel χ).val ((top * p)⁻¹ * middle) := by
  obtain ⟨S, _, hχ, _⟩ := exists_unitary_irreducible_regularChargeLabel χ.val χ.property
  change χ.val (p * middle⁻¹ * top) = χ.val (((top * p)⁻¹ * middle)⁻¹)
  rw [hχ]
  simpa only [regularChargePairCoefficient, Representation.char_dual] using
    regularChargePairCoefficient_middle S.toRepresentation p top middle

open scoped Classical in
/-- The same complete original-spin two-site detector distinguishes both actual
character slices of the correlated pair. The top slice has charge χ; the middle
slice has its actual contragredient label. The measurement precedes all charge
and internal parameters and every remaining boundary configuration.
Source: SCP10, charge-pair creation, lines 2505–2558. This is a shared-bond
slice assertion before its embedding into the six-spin regional contraction. -/
theorem exists_regularPhysicalChargePairSliceMeasurement
    {ι κ A B : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [Fintype A] [Fintype B] (i : ι) (j : κ)
    (a : (ι → G) → A → ℂ) (b : (κ → G) → B → ℂ)
    (ha : IsGIsometric (regularLegRepresentation ι) (regularSiteMap a))
    (hb : IsGIsometric (regularLegRepresentation κ) (regularSiteMap b)) :
    ∃ Q : Option (regularChargeLabels (G := G)) → Matrix (A × B) (A × B) ℂ,
      (∀ r, (Q r).IsHermitian ∧ (Q r).PosSemidef) ∧
      (∀ r s, Q r * Q s = if r = s then Q r else 0) ∧ (∑ r, Q r = 1) ∧
      (∀ (χ : regularChargeLabels (G := G)) r p middle θ,
        Q r *ᵥ regularTwoSitePhysicalChargeColumn i j a b
            (fun k => χ.val (p * middle⁻¹ * k)) 1 θ =
          if r = some χ then regularTwoSitePhysicalChargeColumn i j a b
            (fun k => χ.val (p * middle⁻¹ * k)) 1 θ else 0) ∧
      (∀ (χ : regularChargeLabels (G := G)) r p top θ,
        Q r *ᵥ regularTwoSitePhysicalChargeColumn i j a b
            (fun k => χ.val (p * k⁻¹ * top)) 1 θ =
          if r = some (regularDualChargeLabel χ) then regularTwoSitePhysicalChargeColumn i j a b
            (fun k => χ.val (p * k⁻¹ * top)) 1 θ else 0) := by
  obtain ⟨Q, hQh, hQQ, hsum, hact⟩ :=
    exists_regularTwoSitePhysicalAllChargeMeasurement i j a b ha hb
  refine ⟨Q, hQh, hQQ, hsum, ?_, ?_⟩
  · intro χ r p middle θ
    have hc : regularTwoSitePhysicalChargeColumn i j a b
        (fun k => χ.val (p * middle⁻¹ * k)) 1 θ =
        regularTwoSitePhysicalChargeColumn i j a b χ.val (p * middle⁻¹) θ := by
      funext s
      unfold regularTwoSitePhysicalChargeColumn
      simp only [one_mul]
    rw [hc]
    exact hact χ r (p * middle⁻¹) θ
  · intro χ r p top θ
    have hc : regularTwoSitePhysicalChargeColumn i j a b
        (fun k => χ.val (p * k⁻¹ * top)) 1 θ =
        regularTwoSitePhysicalChargeColumn i j a b (regularDualChargeLabel χ).val
          (top * p)⁻¹ θ := by
      funext s
      simp only [regularTwoSitePhysicalChargeColumn, one_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [middle_label_slice]
    rw [hc]
    exact hact (regularDualChargeLabel χ) r (top * p)⁻¹ θ
end TNLean.PEPS
