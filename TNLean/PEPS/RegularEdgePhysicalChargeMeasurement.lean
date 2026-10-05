/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularEdgeChargeContraction
import TNLean.PEPS.RegularPhysicalCutColumnAction

/-!
# Charge measurement on the actual two-endpoint region

The complete physical measurement is transported along the actual endpoint
coordinate equivalence. It detects a diagonal irreducible-character insertion
on the shared bond uniformly in every native boundary label.
Source: SCP10, arXiv:1001.3807, charge detection, lines 2464–2486.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

/-- A complete original-spin measurement for the literal character-weighted
shared bond, fixed before every charge, parameter and boundary configuration.
Source: SCP10, charge detection, lines 2464–2486. -/
theorem exists_regularEdgePhysicalAllChargeMeasurement
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (e : Edge Γ)
    (ha : IsGIsometric (regularLegRepresentation (IncidentEdge Γ e.1.1))
      (regularSiteMap (a e.1.1)))
    (hb : IsGIsometric (regularLegRepresentation (IncidentEdge Γ e.1.2))
      (regularSiteMap (a e.1.2))) :
    ∃ Q : Option (regularChargeLabels (G := G)) →
        Matrix (RegionPhysicalConfig (d := d) {e.1.1,e.1.2})
          (RegionPhysicalConfig (d := d) {e.1.1,e.1.2}) ℂ,
      (∀ r, (Q r).IsHermitian ∧ (Q r).PosSemidef) ∧
      (∀ r s, Q r * Q s = if r = s then Q r else 0) ∧
      (∑ r, Q r = 1) ∧
      ∀ (b : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
        (_ : ∀ v ∈ ({e.1.1,e.1.2} : Finset V), b v = a v)
        (χ : regularChargeLabels (G := G)) r p
        (θ : {f : Edge Γ // IsRegionBoundaryEdge {e.1.1,e.1.2} f} → G),
        Q r *ᵥ openRegionWeight (groupBondTensor (regularEdgeCharacterSite b e χ.val p))
            {e.1.1,e.1.2} (fun f => Fintype.equivFin G (θ f)) =
          if r = some χ then
            openRegionWeight (groupBondTensor (regularEdgeCharacterSite b e χ.val p))
              {e.1.1,e.1.2} (fun f => Fintype.equivFin G (θ f)) else 0 := by
  classical
  obtain ⟨P,hPh,hPP,hPs,hPa⟩ := exists_regularTwoSitePhysicalAllChargeMeasurement
    (regularEdgeTailLeg e) (regularEdgeHeadLeg e) (a e.1.1) (a e.1.2) ha hb
  let E := regularEdgePhysicalPairEquiv (d := d) e
  refine ⟨fun r => (P r).submatrix E E, ?_, ?_, ?_, ?_⟩
  · intro r
    exact ⟨(hPh r).1.submatrix E, (hPh r).2.submatrix E⟩
  · intro r s
    rw [Matrix.submatrix_mul_equiv, hPP]
    split_ifs <;> rfl
  · ext σ τ
    have hs := congrFun (congrFun hPs (E σ)) (E τ)
    simpa only [Matrix.sum_apply, Matrix.submatrix_apply, Matrix.one_apply,
      E.injective.eq_iff] using hs
  · intro b hba χ r p θ
    have hcol : openRegionWeight
        (groupBondTensor (regularEdgeCharacterSite b e χ.val p)) {e.1.1,e.1.2}
        (fun f => Fintype.equivFin G (θ f)) =
        regularTwoSitePhysicalChargeColumn (regularEdgeTailLeg e) (regularEdgeHeadLeg e)
          (a e.1.1) (a e.1.2) χ.val p (regularEdgeChargeBoundaryLabels e θ) ∘ E := by
      funext σ
      have ht := hba e.1.1 (by simp)
      have hh := hba e.1.2 (by simp)
      simpa only [ht, hh, E, Function.comp_apply] using
        openRegionWeight_regularEdgeCharacterSite b e χ.val p θ σ
    rw [hcol, Matrix.submatrix_mulVec_equiv]
    funext σ
    simp only [Function.comp_def, Equiv.apply_symm_apply]
    have hs := congrFun (hPa χ r p (regularEdgeChargeBoundaryLabels e θ)) (E σ)
    split_ifs with h
    · simpa only [h, ite_true] using hs
    · simpa only [h, ite_false, Pi.zero_apply] using hs
end TNLean.PEPS
