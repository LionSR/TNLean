/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GIsometricConcatenation
import TNLean.PEPS.RegularBoundaryState

/-!
# The group-basis Gram identity of a regular isometric site

For any finite set of incident legs, simultaneous left translation of the group labels
acts by permuting the group basis. Its averaging projector has the group-translation
Kronecker delta as its matrix kernel. A regular `G`-isometric site therefore has the same
Gram kernel, multiplied by its positive isometry factor.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Definition 6.1 and the proof of
Lemma 6.2 (`Papers/1001.3807/paper_v3.tex`, lines 1692–1716). The positive scalar convention
is that of `IsGIsometric`; see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

open Module LinearMap Representation Matrix
open scoped Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable (ι : Type*) [Fintype ι] [DecidableEq ι]
attribute [local instance] Representation.invertibleFintypeCardComplex

/-- Simultaneous regular translation on an arbitrary finite set of group-labelled legs. -/
noncomputable def regularLegRepresentation : Representation ℂ G ((ι → G) → ℂ) :=
  basisRepresentation (MonoidAlgebra.basis (ι → G) ℂ)
    (Representation.ofMulAction ℂ G (ι → G))

omit [DecidableEq G] in
/-- On finitely many numbered legs this is the existing regular boundary representation. -/
theorem regularLegRepresentation_fin (b : ℕ) :
    regularLegRepresentation (G := G) (Fin b) = regularBoundaryRepresentation b := rfl

omit [DecidableEq G] in
@[simp]
theorem regularLegRepresentation_apply (g : G) (x : (ι → G) → ℂ) (η : ι → G) :
    regularLegRepresentation ι g x η = x (g⁻¹ • η) := by
  classical
  simp [regularLegRepresentation, basisRepresentation, LinearEquiv.conjAlgEquiv_apply,
    Basis.equivFun, MonoidAlgebra.basis]

omit [DecidableEq G] in
/-- The simultaneous regular action is unitary in the group basis. -/
theorem regularLegRepresentation_unitary (g : G) (x y : (ι → G) → ℂ) :
    star (regularLegRepresentation ι g x) ⬝ᵥ regularLegRepresentation ι g y = star x ⬝ᵥ y := by
  classical
  simp only [dotProduct, Pi.star_apply, regularLegRepresentation_apply]
  exact Equiv.sum_comp (MulAction.toPermHom G (ι → G) g⁻¹) (fun η => star (x η) * y η)

/-- The invariant-boundary projector for any finite incident-leg set. -/
noncomputable def regularLegProjector : Matrix (ι → G) (ι → G) ℂ :=
  LinearMap.toMatrix' (regularLegRepresentation (G := G) ι).averageMap

/-- Numbering the incident legs recovers the existing boundary projector. -/
theorem regularLegProjector_fin (b : ℕ) :
    regularLegProjector (G := G) (Fin b) = regularBoundaryProjector b := rfl

/-- The regular averaging projector is the normalized common-translation delta kernel. -/
theorem regularLegProjector_apply (η θ : ι → G) :
    regularLegProjector (G := G) ι η θ = (Fintype.card G : ℂ)⁻¹ *
      ∑ g : G, if η = g • θ then 1 else 0 := by
  classical
  rw [regularLegProjector, LinearMap.toMatrix'_apply, Representation.averageMap_apply_eq_sum]
  simp only [Pi.smul_apply, Finset.sum_apply, regularLegRepresentation_apply,
    Pi.single_apply, invOf_eq_inv, smul_eq_mul]
  simp only [inv_smul_eq_iff]

variable {ι} {κ : Type*} [Fintype κ]

/-- The physical coefficient map of a site whose incident legs are indexed by `ι`. -/
def regularSiteMap (a : (ι → G) → κ → ℂ) : ((ι → G) → ℂ) →ₗ[ℂ] (κ → ℂ) :=
  Matrix.mulVecLin (fun s η => a η s)

omit [Group G] [Fintype κ] in
@[simp]
theorem toMatrix_regularSiteMap (a : (ι → G) → κ → ℂ) :
    LinearMap.toMatrix' (regularSiteMap a) = fun s η => a η s := by
  classical
  ext s η
  rw [LinearMap.toMatrix'_apply]
  exact congrFun (Matrix.mulVec_single_one (Matrix.of fun s η => a η s) η) s

omit [DecidableEq G] [Fintype κ] in
/-- The physical coefficients of a regular G-injective site are invariant under common
translation of their incident group labels. Source: arXiv:1001.3807,
Definition `def:2d-Ug-inj` (i), lines 1278–1296. -/
theorem IsGInjective.regularSiteMap_translation {a : (ι → G) → κ → ℂ}
    (ha : IsGInjective (regularLegRepresentation ι) (regularSiteMap a))
    (g : G) (η : ι → G) (s : κ) : a (g • η) s = a η s := by
  classical
  have hsingle : regularLegRepresentation ι g (Pi.single η 1) = Pi.single (g • η) 1 := by
    ext θ
    simp only [regularLegRepresentation_apply, Pi.single_apply, inv_smul_eq_iff]
  have h := congrFun (LinearMap.congr_fun (ha.invariant g) (Pi.single η 1)) s
  simp only [LinearMap.comp_apply, hsingle] at h
  change ((Matrix.of fun s η => a η s) *ᵥ Pi.single (g • η) 1) s =
    ((Matrix.of fun s η => a η s) *ᵥ Pi.single η 1) s at h
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
  exact h

/-- A regular isometric site has the explicit positive multiple of the translation Gram
kernel. Source: arXiv:1001.3807, Definition 6.1, lines 1692–1700. -/
theorem IsGIsometric.exists_regularSiteGram {a : (ι → G) → κ → ℂ}
    (ha : IsGIsometric (regularLegRepresentation ι) (regularSiteMap a)) :
    ∃ c : ℝ, 0 < c ∧ ∀ η θ : ι → G,
      (∑ s : κ, star (a η s) * a θ s) = ((c : ℂ) / (Fintype.card G : ℂ)) *
        ∑ g : G, if η = g • θ then 1 else 0 := by
  classical
  obtain ⟨c, hc, h⟩ := ha.exists_coordinateAdjoint_comp
    (averageMap_dotProduct_of_unitary _ (regularLegRepresentation_unitary ι))
  refine ⟨c, hc, fun η θ => ?_⟩
  have hmat := congrArg LinearMap.toMatrix' h
  simp only [LinearMap.toMatrix'_comp, coordinateAdjoint,
    LinearMap.toMatrix'_toLin', map_smul] at hmat
  have hij := congrFun (congrFun hmat η) θ
  rw [toMatrix_regularSiteMap] at hij
  change (∑ s : κ, star (a η s) * a θ s) =
    (c : ℂ) * regularLegProjector ι η θ at hij
  rw [regularLegProjector_apply] at hij
  simpa only [div_eq_mul_inv, mul_assoc] using hij

end TNLean.PEPS
