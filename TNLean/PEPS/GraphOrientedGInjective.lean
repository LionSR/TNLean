/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphAveragingGInjective
import TNLean.PEPS.GraphOrientedAveragingBondState

/-!
# G-injectivity for arbitrary edge orientations

The actual canonical site is the average of the incident representation with
U(g) at native heads and transpose U(g⁻¹) at native tails. All coordinate
identities retain the supplied edge-flip flag.
Source: SCP10, Definition 5.1 and Section 7.
-/

noncomputable section
open scoped Matrix BigOperators
namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {X G : Type*} [Fintype X] [DecidableEq X] [Group G]

/-- The simultaneous oriented action on the actual incident legs. Rows are
output configurations and columns are input configurations. Source: SCP10,
Section 7, lines 2977–3019. -/
def graphOrientedIncidentMatrix (U : G →* Matrix X X ℂ)
    (o : Edge Γ → Bool) (v : V) (g : G) :
    Matrix (IncidentEdge Γ v → X) (IncidentEdge Γ v → X) ℂ :=
  fun σ η => ∏ f : IncidentEdge Γ v,
    if graphNativeTail o v f then U g⁻¹ (η f) (σ f) else U g (σ f) (η f)

/-- The identity acts trivially on every incident configuration. -/
@[simp]
theorem graphOrientedIncidentMatrix_one (U : G →* Matrix X X ℂ)
    (o : Edge Γ → Bool) (v : V) :
    graphOrientedIncidentMatrix (Γ := Γ) U o v 1 = 1 := by
  classical
  ext σ η
  simp [graphOrientedIncidentMatrix, Matrix.one_apply, eq_comm, Fintype.prod_boole, ← funext_iff]

/-- Transposing the inverse on outgoing legs reverses the inverse product,
so the full oriented action is multiplicative. -/
theorem graphOrientedIncidentMatrix_mul (U : G →* Matrix X X ℂ)
    (o : Edge Γ → Bool) (v : V) (g h : G) :
    graphOrientedIncidentMatrix (Γ := Γ) U o v (g * h) =
      graphOrientedIncidentMatrix U o v g * graphOrientedIncidentMatrix U o v h := by
  classical
  ext σ η
  simp only [graphOrientedIncidentMatrix, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  let F : IncidentEdge Γ v → X → ℂ := fun f j =>
    (if graphNativeTail o v f then U g⁻¹ j (σ f) else U g (σ f) j) *
      (if graphNativeTail o v f then U h⁻¹ (η f) j else U h j (η f))
  change _ = ∑ j : IncidentEdge Γ v → X, ∏ f, F f (j f)
  rw [← Fintype.prod_sum]
  dsimp only [F]
  apply Finset.prod_congr rfl
  intro f _
  by_cases hf : graphNativeTail o v f
  · simp only [hf, ↓reduceIte, mul_inv_rev, map_mul, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  · simp only [hf, ↓reduceIte, map_mul, Matrix.mul_apply]

/-- The incident coefficient-space representation with the graph's actual
head-tail orientation. Source: SCP10, Definition 5.1 and Section 7. -/
def graphOrientedIncidentRepresentation (U : G →* Matrix X X ℂ)
    (o : Edge Γ → Bool) (v : V) :
    Representation ℂ G ((IncidentEdge Γ v → X) → ℂ) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp
    { toFun := graphOrientedIncidentMatrix U o v
      map_one' := graphOrientedIncidentMatrix_one U o v
      map_mul' := graphOrientedIncidentMatrix_mul U o v }

/-- The incident representation acts by its explicit oriented matrix. -/
@[simp]
theorem graphOrientedIncidentRepresentation_apply (U : G →* Matrix X X ℂ)
    (o : Edge Γ → Bool) (v : V)
    (g : G) (x : (IncidentEdge Γ v → X) → ℂ) :
    graphOrientedIncidentRepresentation U o v g x = graphOrientedIncidentMatrix U o v g *ᵥ x := rfl

variable [Fintype G]
attribute [local instance] Representation.invertibleFintypeCardComplex

/-- The local map of the actual graph averaging site is exactly the average
of the oriented incident representation. Source: SCP10, Definition 5.1(ii)
and Section 7, lines 2977–3019. -/
theorem regularSiteMap_graphOrientedAveragingSite (U : G →* Matrix X X ℂ)
    (o : Edge Γ → Bool) (v : V) :
    regularSiteMap (graphOrientedAveragingSite (Γ := Γ) U 1 o v) =
      (graphOrientedIncidentRepresentation U o v).averageMap := by
  classical
  apply LinearMap.toMatrix'.injective
  ext σ η
  rw [toMatrix_regularSiteMap, LinearMap.toMatrix'_apply,
    Representation.averageMap_apply_eq_sum]
  simp only [graphOrientedAveragingSite, Pi.smul_apply, Finset.sum_apply,
    graphOrientedIncidentRepresentation_apply, Matrix.mulVec_single_one, Matrix.col_apply,
    invOf_eq_inv, smul_eq_mul, graphOrientedIncidentMatrix, Matrix.one_mul, Matrix.mul_one]

/-- The actual graph averaging site is G-injective, without any unitarity,
irreducibility, or semi-regularity hypothesis. Source: SCP10, Definition 5.1,
lines 1278–1296, applied to the Section 7 averaging tensor. -/
theorem isGInjective_graphOrientedAveragingSite (U : G →* Matrix X X ℂ)
    (o : Edge Γ → Bool) (v : V) :
    IsGInjective (graphOrientedIncidentRepresentation (Γ := Γ) U o v)
      (regularSiteMap (graphOrientedAveragingSite U 1 o v)) := by
  rw [regularSiteMap_graphOrientedAveragingSite]
  refine ⟨?_, ?_⟩
  · intro g
    change (graphOrientedIncidentRepresentation U o v).averageMap *
      graphOrientedIncidentRepresentation U o v g =
        (graphOrientedIncidentRepresentation U o v).averageMap
    rw [Representation.averageMap, ← Representation.asAlgebraHom_single_one,
      ← map_mul, GroupAlgebra.mul_average_right]
  · intro x hx hzero
    rwa [(graphOrientedIncidentRepresentation U o v).averageMap_id x hx] at hzero


section NumberedCoordinates

variable {p : ℕ}

/-- The same oriented incident representation in the virtual bond numbering
used by the actual graph tensor. Source: SCP10, Definition 5.1 and Section 7. -/
def graphOrientedNumberedIncidentRepresentation (U : G →* Matrix X X ℂ)
    (o : Edge Γ → Bool) (v : V) :
    Representation ℂ G ((IncidentEdge Γ v → Fin (Fintype.card X)) → ℂ) :=
  ((graphNumberedVirtualCoeffEquiv X v).symm.conjAlgEquiv ℂ).toMonoidHom.comp
    (graphOrientedIncidentRepresentation U o v)

omit [Fintype G] in
/-- The numbered action is exactly the conjugated native oriented action. -/
@[simp]
theorem graphOrientedNumberedIncidentRepresentation_apply
    (U : G →* Matrix X X ℂ)
    (o : Edge Γ → Bool) (v : V) (g : G)
    (x : (IncidentEdge Γ v → Fin (Fintype.card X)) → ℂ) :
    graphOrientedNumberedIncidentRepresentation U o v g x =
      (graphNumberedVirtualCoeffEquiv X v).symm
        (graphOrientedIncidentRepresentation U o v g (graphNumberedVirtualCoeffEquiv X v x)) := rfl

/-- The coefficient map of the actual numbered graph tensor is the incident
averaging projector, with precisely its virtual and physical coordinate changes.
Source: SCP10, Definition 5.1(ii) and Section 7, lines 2977–3019. -/
theorem localTensorMap_numberedGraphOrientedAveragingTensor_one
    (U : G →* Matrix X X ℂ) (o : Edge Γ → Bool)
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p) (v : V) :
    localTensorMap (numberedGraphOrientedAveragingTensor U 1 o e) v =
      (graphNumberedPhysicalCoeffEquiv e v).toLinearMap ∘ₗ
        (graphOrientedIncidentRepresentation U o v).averageMap ∘ₗ
          (graphNumberedVirtualCoeffEquiv X v).toLinearMap := by
  classical
  rw [← regularSiteMap_graphOrientedAveragingSite]
  apply LinearMap.ext
  intro x
  funext s
  simp only [localTensorMap, Fintype.linearCombination_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  change (∑ η : IncidentEdge Γ v → Fin (Fintype.card X),
      x η * graphOrientedAveragingSite U 1 o v
        (fun f => (Fintype.equivFin X).symm (η f)) ((e v).symm s)) =
    ∑ ξ : IncidentEdge Γ v → X,
      graphOrientedAveragingSite U 1 o v ξ ((e v).symm s) *
        x (fun f => Fintype.equivFin X (ξ f))
  have h := Equiv.sum_comp (graphNumberedVirtualConfigEquiv (Γ := Γ) X v).symm
    (fun η : IncidentEdge Γ v → Fin (Fintype.card X) =>
      x η * graphOrientedAveragingSite U 1 o v
        (fun f => (Fintype.equivFin X).symm (η f)) ((e v).symm s))
  have hequiv (ξ : IncidentEdge Γ v → X) :
      (graphNumberedVirtualConfigEquiv (Γ := Γ) X v).symm ξ =
        fun f => Fintype.equivFin X (ξ f) := rfl
  simpa only [hequiv, Equiv.symm_apply_apply, mul_comm] using h.symm

/-- G-injectivity of the canonical actual graph tensor, stated directly for
its `LocalVirtualConfig` coefficient map. The representation is the oriented
incident action in the actual bond numbering, and no kernel equality is assumed.
Source: SCP10, Definition 5.1, lines 1278–1296, and Section 7, lines 2977–3019. -/
theorem isGInjective_numberedGraphOrientedAveragingTensor_one
    (U : G →* Matrix X X ℂ) (o : Edge Γ → Bool)
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p) (v : V) :
    IsGInjective (graphOrientedNumberedIncidentRepresentation U o v)
      (localTensorMap (numberedGraphOrientedAveragingTensor U 1 o e) v) := by
  rw [localTensorMap_numberedGraphOrientedAveragingTensor_one]
  let E := graphNumberedVirtualCoeffEquiv (Γ := Γ) X v
  have hT := isGInjective_graphOrientedAveragingSite (Γ := Γ) U o v
  rw [regularSiteMap_graphOrientedAveragingSite] at hT
  have h : IsGInjective (graphOrientedNumberedIncidentRepresentation U o v)
      ((graphOrientedIncidentRepresentation U o v).averageMap ∘ₗ E.toLinearMap) := by
    refine ⟨?_, ?_⟩
    · intro g
      apply LinearMap.ext
      intro x
      change (graphOrientedIncidentRepresentation U o v).averageMap
          (E (E.symm (graphOrientedIncidentRepresentation U o v g (E x)))) =
        (graphOrientedIncidentRepresentation U o v).averageMap (E x)
      rw [E.apply_symm_apply]
      exact LinearMap.congr_fun (hT.invariant g) (E x)
    · intro x hx hzero
      have hmem : E x ∈ (graphOrientedIncidentRepresentation U o v).invariants := by
        intro g
        have heq := congrArg E (hx g)
        change E (E.symm (graphOrientedIncidentRepresentation U o v g (E x))) = E x at heq
        simpa only [E.apply_symm_apply] using heq
      apply E.injective
      rw [map_zero]
      exact hT.injOn_invariants (E x) hmem hzero
  exact h.comp_equiv (graphNumberedPhysicalCoeffEquiv e v)

end NumberedCoordinates
end TNLean.PEPS
