/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.GraphCanonicalBondCoordinates
import TNLean.PEPS.GInjectivePhysicalMap

/-!
# G-injectivity of the oriented graph averaging tensor

The actual graph averaging tensor is the average of the incident representation:
heads carry U(g), and tails carry the transpose of U(g⁻¹). This is a representation
for any matrix representation U, with no unitarity hypothesis. Its average is
G-injective. Numbering virtual bonds and physical configurations preserves this
statement for the genuine graph tensor and its local coefficient map.

Source: SCP10, arXiv:1001.3807, Definition 5.1, lines 1278–1296, and Section 7,
lines 2977–3019. The normalized group average follows the convention documented
in `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {X G : Type*} [Fintype X] [DecidableEq X] [Group G]

/-- The simultaneous oriented action on the actual incident legs. Rows are
output configurations and columns are input configurations. Source: SCP10,
Section 7, lines 2977–3019. -/
def graphIncidentMatrix (U : G →* Matrix X X ℂ) (v : V) (g : G) :
    Matrix (IncidentEdge Γ v → X) (IncidentEdge Γ v → X) ℂ :=
  fun σ η => ∏ f : IncidentEdge Γ v,
    if f.1.1.1 = v then U g⁻¹ (η f) (σ f) else U g (σ f) (η f)

/-- The identity acts trivially on every incident configuration. -/
@[simp]
theorem graphIncidentMatrix_one (U : G →* Matrix X X ℂ) (v : V) :
    graphIncidentMatrix (Γ := Γ) U v 1 = 1 := by
  classical
  ext σ η
  simp [graphIncidentMatrix, Matrix.one_apply, eq_comm, Fintype.prod_boole, ← funext_iff]

/-- Transposing the inverse on outgoing legs reverses the inverse product,
so the full oriented action is multiplicative. -/
theorem graphIncidentMatrix_mul (U : G →* Matrix X X ℂ) (v : V) (g h : G) :
    graphIncidentMatrix (Γ := Γ) U v (g * h) =
      graphIncidentMatrix U v g * graphIncidentMatrix U v h := by
  classical
  ext σ η
  simp only [graphIncidentMatrix, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  let F : IncidentEdge Γ v → X → ℂ := fun f j =>
    (if f.1.1.1 = v then U g⁻¹ j (σ f) else U g (σ f) j) *
      (if f.1.1.1 = v then U h⁻¹ (η f) j else U h j (η f))
  change _ = ∑ j : IncidentEdge Γ v → X, ∏ f, F f (j f)
  rw [← Fintype.prod_sum]
  dsimp only [F]
  apply Finset.prod_congr rfl
  intro f _
  by_cases hf : f.1.1.1 = v
  · simp only [hf, ↓reduceIte, mul_inv_rev, map_mul, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  · simp only [hf, ↓reduceIte, map_mul, Matrix.mul_apply]

/-- The incident coefficient-space representation with the graph's actual
head-tail orientation. Source: SCP10, Definition 5.1 and Section 7. -/
def graphIncidentRepresentation (U : G →* Matrix X X ℂ) (v : V) :
    Representation ℂ G ((IncidentEdge Γ v → X) → ℂ) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp
    { toFun := graphIncidentMatrix U v
      map_one' := graphIncidentMatrix_one U v
      map_mul' := graphIncidentMatrix_mul U v }

/-- The incident representation acts by its explicit oriented matrix. -/
@[simp]
theorem graphIncidentRepresentation_apply (U : G →* Matrix X X ℂ) (v : V)
    (g : G) (x : (IncidentEdge Γ v → X) → ℂ) :
    graphIncidentRepresentation U v g x = graphIncidentMatrix U v g *ᵥ x := rfl

variable [Fintype G]
attribute [local instance] Representation.invertibleFintypeCardComplex

/-- The local map of the actual graph averaging site is exactly the average
of the oriented incident representation. Source: SCP10, Definition 5.1(ii)
and Section 7, lines 2977–3019. -/
theorem regularSiteMap_graphAveragingSite (U : G →* Matrix X X ℂ) (v : V) :
    regularSiteMap (graphAveragingSite (Γ := Γ) U v) =
      (graphIncidentRepresentation U v).averageMap := by
  classical
  apply LinearMap.toMatrix'.injective
  ext σ η
  rw [toMatrix_regularSiteMap, LinearMap.toMatrix'_apply,
    Representation.averageMap_apply_eq_sum]
  simp only [graphAveragingSite, Pi.smul_apply, Finset.sum_apply,
    graphIncidentRepresentation_apply, Matrix.mulVec_single_one, Matrix.col_apply,
    invOf_eq_inv, smul_eq_mul, graphIncidentMatrix]

/-- The actual graph averaging site is G-injective, without any unitarity,
irreducibility, or semi-regularity hypothesis. Source: SCP10, Definition 5.1,
lines 1278–1296, applied to the Section 7 averaging tensor. -/
theorem isGInjective_graphAveragingSite (U : G →* Matrix X X ℂ) (v : V) :
    IsGInjective (graphIncidentRepresentation (Γ := Γ) U v)
      (regularSiteMap (graphAveragingSite U v)) := by
  rw [regularSiteMap_graphAveragingSite]
  refine ⟨?_, ?_⟩
  · intro g
    change (graphIncidentRepresentation U v).averageMap *
      graphIncidentRepresentation U v g = (graphIncidentRepresentation U v).averageMap
    rw [Representation.averageMap, ← Representation.asAlgebraHom_single_one,
      ← map_mul, GroupAlgebra.mul_average_right]
  · intro x hx hzero
    rwa [(graphIncidentRepresentation U v).averageMap_id x hx] at hzero


section NumberedCoordinates

variable {p : ℕ}

/-- The actual finite bond numbering, applied independently to every
incident virtual label. -/
def graphNumberedVirtualConfigEquiv (X : Type*) [Fintype X] (v : V) :
    (IncidentEdge Γ v → Fin (Fintype.card X)) ≃ (IncidentEdge Γ v → X) :=
  Equiv.piCongrRight fun _ => (Fintype.equivFin X).symm

/-- Transport virtual coefficient functions from numbered bonds to the
original representation coordinates. -/
def graphNumberedVirtualCoeffEquiv (X : Type*) [Fintype X] (v : V) :
    ((IncidentEdge Γ v → Fin (Fintype.card X)) → ℂ) ≃ₗ[ℂ]
      ((IncidentEdge Γ v → X) → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (graphNumberedVirtualConfigEquiv (Γ := Γ) X v).symm

/-- The same oriented incident representation in the virtual bond numbering
used by the actual graph tensor. Source: SCP10, Definition 5.1 and Section 7. -/
def graphNumberedIncidentRepresentation (U : G →* Matrix X X ℂ) (v : V) :
    Representation ℂ G ((IncidentEdge Γ v → Fin (Fintype.card X)) → ℂ) :=
  ((graphNumberedVirtualCoeffEquiv X v).symm.conjAlgEquiv ℂ).toMonoidHom.comp
    (graphIncidentRepresentation U v)

omit [Fintype G] in
/-- The numbered action is exactly the conjugated native oriented action. -/
@[simp]
theorem graphNumberedIncidentRepresentation_apply
    (U : G →* Matrix X X ℂ) (v : V) (g : G)
    (x : (IncidentEdge Γ v → Fin (Fintype.card X)) → ℂ) :
    graphNumberedIncidentRepresentation U v g x =
      (graphNumberedVirtualCoeffEquiv X v).symm
        (graphIncidentRepresentation U v g (graphNumberedVirtualCoeffEquiv X v x)) := rfl

/-- The numbered physical basis only relabels the incident configurations. -/
def graphNumberedPhysicalCoeffEquiv
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p) (v : V) :
    ((IncidentEdge Γ v → X) → ℂ) ≃ₗ[ℂ] (Fin p → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (e v).symm

/-- The coefficient map of the actual numbered graph tensor is the incident
averaging projector, with precisely its virtual and physical coordinate changes.
Source: SCP10, Definition 5.1(ii) and Section 7, lines 2977–3019. -/
theorem localTensorMap_numberedGraphDressedAveragingTensor_one
    (U : G →* Matrix X X ℂ)
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p) (v : V) :
    localTensorMap (numberedGraphDressedAveragingTensor U 1 e) v =
      (graphNumberedPhysicalCoeffEquiv e v).toLinearMap ∘ₗ
        (graphIncidentRepresentation U v).averageMap ∘ₗ
          (graphNumberedVirtualCoeffEquiv X v).toLinearMap := by
  classical
  rw [← regularSiteMap_graphAveragingSite]
  apply LinearMap.ext
  intro x
  funext s
  simp only [localTensorMap, Fintype.linearCombination_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  change (∑ η : IncidentEdge Γ v → Fin (Fintype.card X),
      x η * graphDressedAveragingSite U 1 v
        (fun f => (Fintype.equivFin X).symm (η f)) ((e v).symm s)) =
    ∑ ξ : IncidentEdge Γ v → X,
      graphAveragingSite U v ξ ((e v).symm s) *
        x (fun f => Fintype.equivFin X (ξ f))
  simp only [graphDressedAveragingSite, graphDress_one]
  have h := Equiv.sum_comp (graphNumberedVirtualConfigEquiv (Γ := Γ) X v).symm
    (fun η : IncidentEdge Γ v → Fin (Fintype.card X) =>
      x η * graphAveragingSite U v
        (fun f => (Fintype.equivFin X).symm (η f)) ((e v).symm s))
  have hequiv (ξ : IncidentEdge Γ v → X) :
      (graphNumberedVirtualConfigEquiv (Γ := Γ) X v).symm ξ =
        fun f => Fintype.equivFin X (ξ f) := rfl
  simpa only [hequiv, Equiv.symm_apply_apply, mul_comm] using h.symm

/-- G-injectivity of the canonical actual graph tensor, stated directly for
its `LocalVirtualConfig` coefficient map. The representation is the oriented
incident action in the actual bond numbering, and no kernel equality is assumed.
Source: SCP10, Definition 5.1, lines 1278–1296, and Section 7, lines 2977–3019. -/
theorem isGInjective_numberedGraphDressedAveragingTensor_one
    (U : G →* Matrix X X ℂ)
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p) (v : V) :
    IsGInjective (graphNumberedIncidentRepresentation U v)
      (localTensorMap (numberedGraphDressedAveragingTensor U 1 e) v) := by
  rw [localTensorMap_numberedGraphDressedAveragingTensor_one]
  let E := graphNumberedVirtualCoeffEquiv (Γ := Γ) X v
  have hT := isGInjective_graphAveragingSite (Γ := Γ) U v
  rw [regularSiteMap_graphAveragingSite] at hT
  have h : IsGInjective (graphNumberedIncidentRepresentation U v)
      ((graphIncidentRepresentation U v).averageMap ∘ₗ E.toLinearMap) := by
    refine ⟨?_, ?_⟩
    · intro g
      apply LinearMap.ext
      intro x
      change (graphIncidentRepresentation U v).averageMap
          (E (E.symm (graphIncidentRepresentation U v g (E x)))) =
        (graphIncidentRepresentation U v).averageMap (E x)
      rw [E.apply_symm_apply]
      exact LinearMap.congr_fun (hT.invariant g) (E x)
    · intro x hx hzero
      have hmem : E x ∈ (graphIncidentRepresentation U v).invariants := by
        intro g
        have heq := congrArg E (hx g)
        change E (E.symm (graphIncidentRepresentation U v g (E x))) = E x at heq
        simpa only [E.apply_symm_apply] using heq
      apply E.injective
      rw [map_zero]
      exact hT.injOn_invariants (E x) hmem hzero
  exact h.comp_equiv (graphNumberedPhysicalCoeffEquiv e v)

end NumberedCoordinates
end TNLean.PEPS
