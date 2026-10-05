/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularCyclePermutation

/-!
# A fixed physical controlled conjugation of two cycle labels

The permutation (g,h) ↦ (g,ghg⁻¹) commutes with simultaneous conjugation.
It therefore gives a unitary on arbitrary original regular G-isometric site
tensors, implementing this change in every actual open contraction column.
The unitary is fixed before all cycle labels and boundary data are chosen.

Source: SCP10, arXiv:1001.3807, `eq:anyons:fluxon-braiding-lazy`,
lines 2360–2395, using the accessible coordinates of lines 1765–1920.

**Scope restriction (controlled cycle conjugation):** These statements implement
the algebraic change of two accessible cycle labels. The prescribed native
string crossing, the unchanged inverse partner, and the surrounding measurement
loop must still be identified to obtain the paper's braiding experiment. This
auxiliary operation is not that experiment; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {J G : Type*} [DecidableEq J] [Group G]

/-- Conjugate one cycle label by a distinct retained cycle label.
Source: SCP10, `eq:anyons:fluxon-braiding-lazy`, lines 2360–2388. -/
def regularTwoCycleConjugation (e₀ e₁ : J) (hne : e₀ ≠ e₁) : Equiv.Perm (J → G) where
  toFun z e := if e = e₁ then MulAut.conj (z e₀) (z e₁) else z e
  invFun z e := if e = e₁ then (MulAut.conj (z e₀)).symm (z e₁) else z e
  left_inv z := by
    funext e
    by_cases he : e = e₁
    · subst e
      simp only [ite_true, ite_eq_right hne, MulAut.conj_apply, MulAut.conj_symm_apply]
      group
    · simp only [ite_eq_right he]
  right_inv z := by
    funext e
    by_cases he : e = e₁
    · subst e
      simp only [ite_true, ite_eq_right hne, MulAut.conj_apply, MulAut.conj_symm_apply]
      group
    · simp only [ite_eq_right he]

/-- The selected cycle has the conjugated label ghg⁻¹.
Source: SCP10, `eq:anyons:fluxon-braiding-lazy`, lines 2360–2388. -/
theorem regularTwoCycleConjugation_apply_selected
    (e₀ e₁ : J) (hne : e₀ ≠ e₁) (z : J → G) :
    regularTwoCycleConjugation e₀ e₁ hne z e₁ = z e₀ * z e₁ * (z e₀)⁻¹ := by
  simp only [regularTwoCycleConjugation, Equiv.coe_fn_mk, ite_true, MulAut.conj_apply]

/-- Every other cycle, including the controlling cycle, is retained.
Source: SCP10, `eq:anyons:fluxon-braiding-lazy`, lines 2360–2388. -/
theorem regularTwoCycleConjugation_apply_other
    (e₀ e₁ : J) (hne : e₀ ≠ e₁) (z : J → G) (e : J) (he : e ≠ e₁) :
    regularTwoCycleConjugation e₀ e₁ hne z e = z e := by
  simp only [regularTwoCycleConjugation, Equiv.coe_fn_mk, ite_eq_right he]

/-- Controlled conjugation is equivariant under simultaneous conjugation of all
cycle labels. Source: SCP10, accessible coordinates, lines 1765–1920. -/
theorem regularTwoCycleConjugation_conjugation
    (e₀ e₁ : J) (hne : e₀ ≠ e₁) (z : J → G) (x : G) :
    regularTwoCycleConjugation e₀ e₁ hne (fun e => x * z e * x⁻¹) =
      fun e => x * regularTwoCycleConjugation e₀ e₁ hne z e * x⁻¹ := by
  funext e
  by_cases he : e = e₁
  · subst e
    rw [regularTwoCycleConjugation_apply_selected, regularTwoCycleConjugation_apply_selected]
    group
  · rw [regularTwoCycleConjugation_apply_other _ _ _ _ _ he,
      regularTwoCycleConjugation_apply_other _ _ _ _ _ he]

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] [Fintype G]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RC (R : Finset V) (T : SimpleGraph (RV R)) :=
  {e : RI (Γ := Γ) R // ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩}
variable (R : Finset V) (T : SimpleGraph (RV R)) [DecidableRel T.Adj]

/-- A fixed original-spin unitary conjugates one selected cycle by another in
every actual contraction column, retaining all other cycle labels and boundary
data. Source: SCP10, `eq:anyons:fluxon-braiding-lazy`, lines 2360–2388,
and accessible-coordinate construction, lines 1765–1920. -/
theorem exists_unitary_regularTwoCyclePhysicalConjugation {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e₀ e₁ : RC (Γ := Γ) R T) (hne : e₀ ≠ e₁) :
    ∃ W : Matrix (RV R → Fin d) (RV R → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV R → Fin d) ℂ ∧
      ∀ (ω : RC (Γ := Γ) R T → G)
        (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G),
        W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite a
          (regularTreeCycleAssignment R T ω))) R
          (fun f => Fintype.equivFin G (θ f)) =
        openRegionWeight (groupBondTensor (regularTwistedSite a
          (regularTreeCycleAssignment R T (regularTwoCycleConjugation e₀ e₁ hne ω)))) R
          (fun f => Fintype.equivFin G (θ f)) :=
  exists_unitary_regularCyclePhysicalPermutation R T a ha hT htree o
    (regularTwoCycleConjugation e₀ e₁ hne) (regularTwoCycleConjugation_conjugation e₀ e₁ hne)

end TNLean.PEPS
