/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphBondContraction
import TNLean.PEPS.TorusThetaBondState

/-!
# Weighted averaging-site contractions on finite graphs

At the head of each native ordered edge, the local averaging tensor uses U(g).
At the tail it uses the transpose of U(g⁻¹). Inserting a weight W on every
virtual leg is a genuine local convolution. Its two endpoint weights combine
on every bond, and when W commutes with U the actual graph contraction becomes
a coherent sum of W² U(q_head q_tail⁻¹) bond vectors. The statements include
the ordinary averaging site and the actual fourth-root operator Θ.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2974–3007.
These identities hold on every finite simple graph, including disconnected
graphs and isolated vertices. No global coefficient or Gram identity is assumed.

**Local fix (group-average normalization):** Each site average is divided by
|G|, so the graph coefficient carries |G|⁻ᴺ for N vertices. The source's
fourth-root normalization is documented in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {X G : Type*} [Fintype X] [DecidableEq X] [Group G] [Fintype G]

/-- The normalized oriented averaging site on all incident virtual legs. Source: SCP10, Section 7,
lines 2977–3019. -/
def graphAveragingSite (U : G →* Matrix X X ℂ) (v : V)
    (η σ : IncidentEdge Γ v → X) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g : G, ∏ f : IncidentEdge Γ v,
    if f.1.1.1 = v then U g⁻¹ (η f) (σ f) else U g (σ f) (η f)

/-- Insert one matrix on every oriented virtual leg of a site. Source: SCP10, Section 7, lines
2977–3019. -/
def graphDress (W : Matrix X X ℂ) (v : V)
    (a : (IncidentEdge Γ v → X) → ℂ) (η : IncidentEdge Γ v → X) : ℂ :=
  ∑ ξ : IncidentEdge Γ v → X,
    (∏ f : IncidentEdge Γ v,
      if f.1.1.1 = v then W (η f) (ξ f) else W (ξ f) (η f)) * a ξ

/-- The averaging site with the same virtual weight on every incident leg. Source: SCP10, Section
7, lines 2977–3019. -/
def graphDressedAveragingSite (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ)
    (v : V) (η σ : IncidentEdge Γ v → X) : ℂ :=
  graphDress W v (fun ξ => graphAveragingSite U v ξ σ) η

/-- Identity virtual weights leave every site coefficient unchanged. Source: SCP10, Section 7,
lines 2977–3019. -/
theorem graphDress_one (v : V) (a : (IncidentEdge Γ v → X) → ℂ)
    (η : IncidentEdge Γ v → X) : graphDress 1 v a η = a η := by
  classical
  simp [graphDress, Matrix.one_apply, eq_comm, Fintype.prod_boole, ← funext_iff]

/-- The local virtual insertion has the literal endpoint matrix products. Source: SCP10, Section
7, lines 2977–3019. -/
theorem graphDress_averagingSite (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ)
    (v : V) (η σ : IncidentEdge Γ v → X) :
    graphDress W v (fun ξ => graphAveragingSite U v ξ σ) η =
      (Fintype.card G : ℂ)⁻¹ * ∑ g : G, ∏ f : IncidentEdge Γ v,
        if f.1.1.1 = v then (W * U g⁻¹) (η f) (σ f)
        else (U g * W) (σ f) (η f) := by
  simp only [graphDress, graphAveragingSite, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp only [mul_left_comm _ (Fintype.card G : ℂ)⁻¹, ← Finset.mul_sum]
  congr 1
  simp only [← Finset.prod_mul_distrib]
  let F : IncidentEdge Γ v → X → ℂ := fun f j =>
    (if f.1.1.1 = v then W (η f) j else W j (η f)) *
      (if f.1.1.1 = v then U g⁻¹ j (σ f) else U g (σ f) j)
  change (∑ ξ : IncidentEdge Γ v → X, ∏ f, F f (ξ f)) = _
  rw [← Fintype.prod_sum]
  dsimp only [F]
  apply Finset.prod_congr rfl
  intro f _
  by_cases h : f.1.1.1 = v
  · simp only [ite_eq_left h, Matrix.mul_apply]
  · simp only [ite_eq_right h, Matrix.mul_apply, mul_comm]

/-- Regrouped dressed averaging-site coefficients are coherent products of
actual weighted relative representation matrices. Source: SCP10, Section 7, lines 2977–3019. -/
theorem graphBondRegrouping_dressedAveragingSite_coherent
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g)) :
    graphBondRegrouping (Γ := Γ) (graphBondNetwork (graphDressedAveragingSite U W)) =
      fun β => ∑ q : V → G,
        (Fintype.card G : ℂ)⁻¹ ^ Fintype.card V *
          ∏ e : Edge Γ, (W ^ 2 * U (q e.1.2 * (q e.1.1)⁻¹)) (β e).1 (β e).2 := by
  funext β
  rw [graphBondRegrouping_apply]
  simp only [graphBondNetwork, graphDressedAveragingSite, graphDress_averagingSite,
    Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]
  simp_rw [Fintype.prod_sum]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [prod_incident_eq_prod_edge]
  have hne (e : Edge Γ) : ¬ e.1.1 = e.1.2 := ne_of_lt e.2.1
  simp only [graphSiteBondEndpointEquiv, Equiv.coe_fn_symm_mk,
    edgeLeftIncident, edgeRightIncident, hne, ↓reduceIte]
  let F : Edge Γ → X → ℂ := fun e j =>
    (W * U (q e.1.1)⁻¹) j (β e).2 * (U (q e.1.2) * W) (β e).1 j
  change (∑ η : Edge Γ → X, ∏ e, F e (η e)) = _
  rw [← Fintype.prod_sum]
  apply Finset.prod_congr rfl
  intro e _
  dsimp only [F]
  rw [← U.mul_weight_mul_weight_mul W hc]
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _
/-- Actual unweighted graph coefficients have one relative representation
matrix on each physical bond. Source: SCP10, Section 7, lines 2977–3019. -/
theorem graphBondRegrouping_averagingSite_coherent (U : G →* Matrix X X ℂ) :
    graphBondRegrouping (Γ := Γ) (graphBondNetwork (graphAveragingSite U)) =
      fun β => ∑ q : V → G,
        (Fintype.card G : ℂ)⁻¹ ^ Fintype.card V *
          ∏ e : Edge Γ, U (q e.1.2 * (q e.1.1)⁻¹) (β e).1 (β e).2 := by
  have hs : graphDressedAveragingSite (Γ := Γ) U 1 = graphAveragingSite U := by
    funext v η σ
    exact graphDress_one v (fun ξ => graphAveragingSite U v ξ σ) η
  have h := graphBondRegrouping_dressedAveragingSite_coherent (Γ := Γ) U 1
    (fun _ => Commute.one_left _)
  rw [hs] at h
  simpa only [one_pow, Matrix.one_mul] using h

/-- The canonical graph averaging tensor weighted by the actual fourth-root operator. Source:
SCP10, Section 7, lines 2977–3019. -/
def graphThetaWeightedAveragingSite (U : G →* Matrix X X ℂ) :
    (v : V) → (IncidentEdge Γ v → X) → (IncidentEdge Γ v → X) → ℂ :=
  graphDressedAveragingSite U (thetaMatrix U)

/-- The actual fourth-root-weighted graph contraction has Θ² on every bond. Source: SCP10, Section
7, lines 2977–3019. -/
theorem graphBondRegrouping_thetaWeightedAveragingSite_coherent
    (U : G →* Matrix X X ℂ) :
    graphBondRegrouping (Γ := Γ) (graphBondNetwork (graphThetaWeightedAveragingSite U)) =
      fun β => ∑ q : V → G,
        (Fintype.card G : ℂ)⁻¹ ^ Fintype.card V *
          ∏ e : Edge Γ, (thetaMatrix U ^ 2 * U (q e.1.2 * (q e.1.1)⁻¹))
            (β e).1 (β e).2 := by
  apply graphBondRegrouping_dressedAveragingSite_coherent
  intro g
  let E : Matrix X X ℂ ≃ₐ[ℂ] Module.End ℂ (X → ℂ) := Matrix.toLinAlgEquiv'
  have hc := (Representation.thetaOperator_commute (E.toMonoidHom.comp U) g).map E.symm
  change Commute (E.symm (Representation.thetaOperator (E.toMonoidHom.comp U)))
    (E.symm (E (U g))) at hc
  rw [E.symm_apply_apply] at hc
  exact hc
end TNLean.PEPS
