/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Injectivity.Multiplicity.GraphInsertedBondState
import TNLean.PEPS.Injectivity.Charge.RegularWeightedOpenContraction
import TNLean.PEPS.Injectivity.Regular.RegularRegionGaugeContraction
import TNLean.PEPS.Tensor.GraphState.RegularClosedGauge
import TNLean.PEPS.Injectivity.Regular.RegularSweptPatchDeformation

/-!
# Actual regular contractions with arbitrary diagonal bond weights

The diagonal weight acts on the tail register before the oriented group
insertion. Independent head and tail summation therefore gives an actual
weighted contraction; no span of diagonal matrices by group matrices is used.
Source: SCP10, arXiv:1001.3807, charge insertions, lines 2449–2486, and
charge–flux transport, lines 2569–2581. This is an auxiliary finite-graph
coefficient calculation, without a physical or Hamiltonian conclusion.

## Literal diagonal weights under vertex gauge changes

The tail reference on an ordered edge changes by the inverse tail gauge.
Consequently an arbitrary diagonal weight is pulled back by multiplication
with that gauge. These identities are proved from the actual finite incidence
contractions, retaining all internal and crossing operators.

Source: SCP10, arXiv:1001.3807, charge–flux string deformation, lines 2560–2581.
These are auxiliary gauge-presentation identities. A physical crossing or
braiding route is not inferred from equality of gauge presentations.
-/

section

open ManyBody (Edge)
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Arbitrary diagonal tail weights are retained in the literal regular
bond contraction. Source: SCP10, lines 2449–2486 and 2569–2581. -/
theorem graphInsertedBondNetwork_leftRegular_mul_diagonal {P : V → Type*}
    (a : (v : V) → (IncidentEdge Γ v → G) → P v → ℂ)
    (u : Edge Γ → G) (f : Edge Γ → G → ℂ) (σ : (v : V) → P v) :
    graphInsertedBondNetwork
      (fun e => leftRegularMatrix G (u e) * Matrix.diagonal (f e)) a σ =
      ∑ η : Edge Γ → G, (∏ e, f e (η e)) *
        ∏ v, a v (regularTwistedLabels u v (fun e => η e.1)) (σ v) := by
  classical
  let E := Equiv.arrowProdEquivProdArrow (Edge Γ) (fun _ => G) (fun _ => G)
  unfold graphInsertedBondNetwork
  rw [← E.symm.sum_comp, Fintype.sum_prod_type]
  simp only [E, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk,
    Matrix.mul_diagonal, leftRegularMatrix_apply, Finset.prod_mul_distrib,
    Fintype.prod_boole, ← funext_iff]
  rw [Finset.sum_comm]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro η _
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext e
  rcases e.2 with ht | hh
  · have hn : ¬ v = e.1.1.2 := fun h => ne_of_lt e.1.2.1 (ht.trans h)
    simp [graphSiteBondEndpointEquiv, regularTwistedLabels, ht, hn]
  · have hn : ¬ e.1.1.1 = v := fun h => ne_of_lt e.1.2.1 (h.trans hh.symm)
    simp [graphSiteBondEndpointEquiv, regularTwistedLabels, hh, hn]
end TNLean.PEPS
end

end

section

open ManyBody (Edge)
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Actual diagonal bond insertions transform by the tail gauge, with no span
assumption on their diagonal matrices. Source: SCP10, lines 2569–2581. -/
theorem graphInsertedBondNetwork_diagonal_vertexGauge {P : V → Type*}
    (a : (v : V) → (IncidentEdge Γ v → G) → P v → ℂ)
    (ha : ∀ x v η s, a v (fun e => x * η e) s = a v η s)
    (k : V → G) (u : Edge Γ → G) (f : Edge Γ → G → ℂ)
    (σ : (v : V) → P v) :
    graphInsertedBondNetwork
      (fun e => leftRegularMatrix G (u e) * Matrix.diagonal (f e)) a σ =
    graphInsertedBondNetwork
      (fun e => leftRegularMatrix G (regularVertexGaugeOperators k u e) *
        Matrix.diagonal (fun t => f e (k e.1.1 * t))) a σ := by
  classical
  rw [graphInsertedBondNetwork_leftRegular_mul_diagonal,
    graphInsertedBondNetwork_leftRegular_mul_diagonal]
  let E : (Edge Γ → G) ≃ (Edge Γ → G) :=
    Equiv.piCongrRight fun e => Equiv.mulLeft (k e.1.1)⁻¹
  conv_rhs => rw [← Equiv.sum_comp E]
  apply Finset.sum_congr rfl
  intro η _
  have hf : (∏ e, f e (k e.1.1 * E η e)) = ∏ e, f e (η e) := by
    apply Finset.prod_congr rfl
    intro e _
    congr 1
    change k e.1.1 * ((k e.1.1)⁻¹ * η e) = η e
    group
  rw [hf]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  symm
  have hlabels := regularTwistedLabels_gauge u k v (fun e => η e.1)
  change a v (regularTwistedLabels (fun e => (k e.1.2)⁻¹ * u e * k e.1.1) v
    (fun e => (k e.1.1.1)⁻¹ * η e.1)) (σ v) = _
  rw [hlabels]
  exact ha (k v)⁻¹ v _ (σ v)

/-- Independent vertex gauges transport every actual weighted open column and
its boundary labels. The weight may correlate several edges.
Source: SCP10, lines 2505–2535 and 2569–2581. -/
theorem regularWeightedOpenRegionWeight_vertexGauge {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ x v η s, a v (fun e => x * η e) s = a v η s)
    (R : Finset V) (k : V → G) (u : Edge Γ → G)
    (F : ({e : Edge Γ // ManyBody.IsRegionIncidentEdge R e} → G) → ℂ)
    (θ : {e : Edge Γ // ManyBody.IsRegionBoundaryEdge R e} → G)
    (σ : {v : V // v ∈ R} → Fin d) :
    regularWeightedOpenRegionWeight a R u F θ σ =
      regularWeightedOpenRegionWeight a R (regularVertexGaugeOperators k u)
        (fun η => F (fun e => k e.1.1.1 * η e))
        (fun e => (k e.1.1.1)⁻¹ * θ e) σ := by
  classical
  let E : ({e : Edge Γ // ManyBody.IsRegionIncidentEdge R e} → G) ≃
      ({e : Edge Γ // ManyBody.IsRegionIncidentEdge R e} → G) :=
    Equiv.piCongrRight fun e => Equiv.mulLeft (k e.1.1.1)⁻¹
  let B : ({e : Edge Γ // ManyBody.IsRegionBoundaryEdge R e} → G) ≃
      ({e : Edge Γ // ManyBody.IsRegionBoundaryEdge R e} → G) :=
    Equiv.piCongrRight fun e => Equiv.mulLeft (k e.1.1.1)⁻¹
  have hθ : (fun e : {e : Edge Γ // ManyBody.IsRegionBoundaryEdge R e} =>
      (k e.1.1.1)⁻¹ * θ e) = B θ := rfl
  rw [hθ]
  unfold regularWeightedOpenRegionWeight
  conv_rhs => rw [← Equiv.sum_comp E]
  apply Finset.sum_congr rfl
  intro η _
  have hb : (fun f : {e : Edge Γ // ManyBody.IsRegionBoundaryEdge R e} =>
      E η ⟨f.1, ManyBody.isRegionBoundaryEdge_touches R f.2⟩) =
      B (fun f => η ⟨f.1, ManyBody.isRegionBoundaryEdge_touches R f.2⟩) := rfl
  have hF : F (fun e => k e.1.1.1 * E η e) = F η := by
    congr 1
    funext e
    change k e.1.1.1 * ((k e.1.1.1)⁻¹ * η e) = η e
    group
  simp only [hF, hb, B.injective.eq_iff]
  split_ifs
  · congr 1
    apply Finset.prod_congr rfl
    intro v _
    symm
    have hlabels := regularTwistedLabels_gauge u k v.1
      (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩)
    change a v.1 (regularTwistedLabels (fun e => (k e.1.2)⁻¹ * u e * k e.1.1)
      v.1 (fun f => (k f.1.1.1)⁻¹ * η
        ⟨f.1, isRegionIncidentEdge_of_regionVertex R v f⟩)) (σ v) = _
    rw [hlabels]
    exact ha (k v.1)⁻¹ v.1 _ (σ v)
  · rfl

/-- Sweeping one of the two literal diagonal registers retains their correlation.
The inserted inverse flux lies between the two labels, rather than being
commuted past the partner label. Source: SCP10, lines 2505–2535 and 2569–2581. -/
theorem regularWeightedOpenRegionWeight_chargePair_swept {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ x v η s, a v (fun e => x * η e) s = a v η s)
    (R S : Finset V) (u : Edge Γ → G) (g : G)
    (e₀ e₁ : {e : Edge Γ // ManyBody.IsRegionIncidentEdge R e})
    (h₀ : e₀.1.1.1 ∈ S) (h₁ : e₁.1.1.1 ∉ S)
    (χ : G → ℂ) (p : G)
    (θ : {e : Edge Γ // ManyBody.IsRegionBoundaryEdge R e} → G)
    (σ : {v : V // v ∈ R} → Fin d) :
    regularWeightedOpenRegionWeight a R u
        (fun η => χ (p * (η e₁)⁻¹ * η e₀)) θ σ =
      regularWeightedOpenRegionWeight a R (regularSweptPatchOperators S g u)
        (fun η => χ (p * (η e₁)⁻¹ * g⁻¹ * η e₀))
        (fun e => (regularSweptPatchGauge S g e.1.1.1)⁻¹ * θ e) σ := by
  rw [regularSweptPatchOperators_eq_vertexGauge]
  have h := regularWeightedOpenRegionWeight_vertexGauge a ha R
    (regularSweptPatchGauge S g) u (fun η => χ (p * (η e₁)⁻¹ * η e₀)) θ σ
  simpa only [regularSweptPatchGauge, ite_eq_left h₀, ite_eq_right h₁, one_mul, mul_inv_rev,
    inv_one, mul_assoc] using h

end TNLean.PEPS
end

end
