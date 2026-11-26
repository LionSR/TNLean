/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Injectivity.Multiplicity.GraphAveragingBondState
import TNLean.PEPS.Tensor.GraphState.RegularTwistedRegion
import QICLean.Algebra.MonoidAux
import QICLean.Algebra.Combinatorics.FinSumPermutation
import TNLean.PEPS.Tensor.GraphState.GraphOpenRegionContraction
import TNLean.PEPS.Tensor.Region.RegionGroundSpace

/-!
# Closed contractions with inserted oriented bond matrices

On a finite simple graph, every bond has independent head and tail virtual
labels. Its inserted matrix has row at the head and column at the tail.
The site factors use exactly these labels at their actual incidences.
Identity insertions recover the existing closed graph contraction.

Expanding dressed averaging sites gives U(q_head) W K_e W U(q_tail⁻¹)
without any commutation hypothesis. For group-representation insertions
K_e=U(u_e) and a commuting weight W, this becomes
W²U(q_head u_e q_tail⁻¹). The literal regular specialization is proved to
be the existing contraction of regularTwistedSite: its head label is
u_e times its tail label, with no assumed coefficient identity.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2977–3019, and the
oriented regular insertions in equation `eq:2d:peps-with-ug-uh`, lines
1935–1990. The arbitrary-matrix formula is an auxiliary extension of the
closed contraction calculation. It makes no physical-isometry assertion
for arbitrary inserted matrices and no parent-Hamiltonian assertion.

**Local fix (group-average normalization):** Each site average is divided
by |G|, as documented in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

It also contains the following results.

* `TNLean.PEPS.graphInsertedBondNetwork_slice_mem_regionGroundSpace_of_internal_eq_one`: regional
  support of contractions with exterior bond insertions.
-/

open ManyBody (Edge)

section GraphInsertedBondState

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Actual independent endpoint contraction with an oriented bond matrix.
Auxiliary to SCP10, Section 7, lines 2977–3019. The first virtual pair label
is the head label; the second is the tail label. -/
def graphInsertedBondNetwork {P : V → Type*}
    (K : Edge Γ → Matrix X X ℂ)
    (a : (v : V) → (IncidentEdge Γ v → X) → P v → ℂ)
    (σ : (v : V) → P v) : ℂ :=
  ∑ ζ : Edge Γ → X × X, (∏ e, K e (ζ e).1 (ζ e).2) *
    ∏ v, a v (graphSiteBondEndpointEquiv.symm ζ v) (σ v)

/-- Identity bond matrices recover the actual closed contraction.
Source: SCP10, Section 7, lines 2977–3019, and regular insertions, lines 1935–1990. -/
theorem graphInsertedBondNetwork_one {P : V → Type*}
    (a : (v : V) → (IncidentEdge Γ v → X) → P v → ℂ)
    (σ : (v : V) → P v) :
    graphInsertedBondNetwork (fun _ => 1) a σ = graphBondNetwork a σ := by
  classical
  let E := Equiv.arrowProdEquivProdArrow (Edge Γ) (fun _ => X) (fun _ => X)
  unfold graphInsertedBondNetwork
  rw [← E.symm.sum_comp, Fintype.sum_prod_type]
  simp only [E, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk, Matrix.one_apply,
    Fintype.prod_boole, ← funext_iff]
  simp [graphBondNetwork, graphSiteBondEndpointEquiv, eq_comm]

variable {G : Type*} [Group G] [Fintype G]

/-- Arbitrary inserted matrices give the literal product of the two endpoint factors.
Source: SCP10, Section 7, lines 2977–3019, and regular insertions, lines 1935–1990. -/
theorem graphInsertedBondNetwork_dressedAveragingSite
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ)
    (K : Edge Γ → Matrix X X ℂ) (β : Edge Γ → X × X) :
    graphBondRegrouping (graphInsertedBondNetwork K (graphDressedAveragingSite U W)) β =
      ∑ q : V → G, (Fintype.card G : ℂ)⁻¹ ^ Fintype.card V *
        ∏ e : Edge Γ, (U (q e.1.2) * W * K e * W * U (q e.1.1)⁻¹)
          (β e).1 (β e).2 := by
  classical
  rw [graphBondRegrouping_apply]
  unfold graphInsertedBondNetwork
  simp only [graphDressedAveragingSite, graphDress_averagingSite,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  simp_rw [Fintype.prod_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp only [mul_left_comm _ ((Fintype.card G : ℂ)⁻¹ ^ Fintype.card V),
    ← Finset.mul_sum]
  congr 1
  simp_rw [prod_incident_eq_prod_edge]
  have hne (e : Edge Γ) : ¬ e.1.1 = e.1.2 := ne_of_lt e.2.1
  simp only [graphSiteBondEndpointEquiv, Equiv.coe_fn_symm_mk,
    edgeLeftIncident, edgeRightIncident, hne, ↓reduceIte]
  simp_rw [← Finset.prod_mul_distrib]
  let F : Edge Γ → X × X → ℂ := fun e j =>
    K e j.1 j.2 * ((W * U (q e.1.1)⁻¹) j.2 (β e).2 *
      (U (q e.1.2) * W) (β e).1 j.1)
  change (∑ ζ : Edge Γ → X × X, ∏ e, F e (ζ e)) = _
  rw [← Fintype.prod_sum]
  apply Finset.prod_congr rfl
  intro e _
  dsimp only [F]
  have hm : U (q e.1.2) * W * K e * W * U (q e.1.1)⁻¹ =
      (U (q e.1.2) * W) * (K e * (W * U (q e.1.1)⁻¹)) := by
    simp only [mul_assoc]
  rw [hm]
  simp only [Fintype.sum_prod_type,
    Matrix.mul_apply (M := U (q e.1.2) * W) (N := K e * (W * U (q e.1.1)⁻¹)),
    Matrix.mul_apply (M := K e) (N := W * U (q e.1.1)⁻¹), Finset.mul_sum]
  refine Finset.sum_congr₂ fun j _ k _ ↦ ?_
  ring

/-- Group insertions and commuting weights give weighted relative group matrices.
Source: SCP10, Section 7, lines 2977–3019, and regular insertions, lines 1935–1990. -/
theorem graphInsertedBondNetwork_dressedAveragingSite_group
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (u : Edge Γ → G) (β : Edge Γ → X × X) :
    graphBondRegrouping
      (graphInsertedBondNetwork (fun e => U (u e)) (graphDressedAveragingSite U W)) β =
      ∑ q : V → G, (Fintype.card G : ℂ)⁻¹ ^ Fintype.card V *
        ∏ e : Edge Γ, (W ^ 2 * U (q e.1.2 * u e * (q e.1.1)⁻¹))
          (β e).1 (β e).2 := by
  have hm (a b c : G) : U a * W * U b * W * U c = W ^ 2 * U (a * b * c) := by
    have h : U a * W * U b = U (a * b) * W := by
      rw [mul_assoc, (hc b).eq, ← mul_assoc, ← map_mul]
    rw [h]
    simpa only [mul_assoc] using U.mul_weight_mul_weight_mul W hc (a * b) c
  rw [graphInsertedBondNetwork_dressedAveragingSite]
  simp_rw [hm]

/-- Identity dressing gives the actual ordinary averaging contraction with group insertions.
Source: SCP10, Section 7, lines 2977–3019, and regular insertions, lines 1935–1990. -/
theorem graphInsertedBondNetwork_averagingSite_group
    (U : G →* Matrix X X ℂ) (u : Edge Γ → G) (β : Edge Γ → X × X) :
    graphBondRegrouping
      (graphInsertedBondNetwork (fun e => U (u e)) (graphAveragingSite U)) β =
      ∑ q : V → G, (Fintype.card G : ℂ)⁻¹ ^ Fintype.card V *
        ∏ e : Edge Γ, U (q e.1.2 * u e * (q e.1.1)⁻¹) (β e).1 (β e).2 := by
  have hs : graphDressedAveragingSite (Γ := Γ) U 1 = graphAveragingSite U :=
    funext fun v => funext fun η => funext fun σ =>
      graphDress_one v (fun ξ => graphAveragingSite U v ξ σ) η
  have h := graphInsertedBondNetwork_dressedAveragingSite_group U 1
    (fun _ => Commute.one_left _) u β
  rw [hs] at h
  simpa only [one_pow, Matrix.one_mul] using h

variable [DecidableEq G]
/-- The regular inserted contraction equals the existing head-twisted site contraction.
Source: SCP10, Section 7, lines 2977–3019, and regular insertions, lines 1935–1990. -/
theorem graphInsertedBondNetwork_leftRegular_eq_labels {P : V → Type*}
    (a : (v : V) → (IncidentEdge Γ v → G) → P v → ℂ)
    (u : Edge Γ → G) (σ : (v : V) → P v) :
    graphInsertedBondNetwork (fun e => leftRegularMatrix G (u e)) a σ =
      graphBondNetwork (fun v η s => a v (regularTwistedLabels u v η) s) σ := by
  classical
  let E := Equiv.arrowProdEquivProdArrow (Edge Γ) (fun _ => G) (fun _ => G)
  unfold graphInsertedBondNetwork
  rw [← E.symm.sum_comp, Fintype.sum_prod_type]
  simp only [E, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk,
    leftRegularMatrix_apply, Fintype.prod_boole, ← funext_iff]
  rw [Finset.sum_comm]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold graphBondNetwork
  apply Finset.sum_congr rfl
  intro η _
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext f
  rcases f.2 with ht | hh
  · have hn : ¬ v = f.1.1.2 := fun h => ne_of_lt f.1.2.1 (ht.trans h)
    simp [graphSiteBondEndpointEquiv, regularTwistedLabels, ht, hn]
  · have hn : ¬ f.1.1.1 = v := fun h => ne_of_lt f.1.2.1 (h.trans hh.symm)
    simp [graphSiteBondEndpointEquiv, regularTwistedLabels, hh, hn]

/-- Uniform physical alphabets recover the existing head-twisted site family.
Source: SCP10, Section 7, lines 2977–3019, and regular insertions, lines 1935–1990. -/
theorem graphInsertedBondNetwork_leftRegular_eq_twisted {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (u : Edge Γ → G) (σ : V → Fin d) :
    graphInsertedBondNetwork (fun e => leftRegularMatrix G (u e)) a σ =
      graphBondNetwork (regularTwistedSite a u) σ :=
  graphInsertedBondNetwork_leftRegular_eq_labels a u σ

/-- The numbered regular specialization is the actual tensor-network coefficient.
Source: SCP10, Section 7, lines 2977–3019, and regular insertions, lines 1935–1990. -/
theorem graphInsertedBondNetwork_leftRegular_eq_stateCoeff {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (u : Edge Γ → G) (σ : V → Fin d) :
    graphInsertedBondNetwork (fun e => leftRegularMatrix G (u e)) a σ =
      stateCoeff (groupBondTensor (regularTwistedSite a u)) σ := by
  rw [stateCoeff_groupBondTensor_eq_graphBondNetwork]
  exact graphInsertedBondNetwork_leftRegular_eq_twisted a u σ
end TNLean.PEPS

end

end GraphInsertedBondState

section GraphInsertedRegionSupport

/-!
## Regional support of contractions with exterior bond insertions

An arbitrary matrix on a crossing or exterior bond changes only the boundary
condition presented to a region. When every internal bond matrix is the
identity, every physical slice therefore belongs to the original regional
ground space. The virtual alphabet and the site coefficients are arbitrary.

Source: SCP10, arXiv:1001.3807, local closure deformation in Theorem 5.5,
lines 1440–1545, and regional contraction, lines 1935–1990.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {X : Type*} [Fintype X] [DecidableEq X]

private abbrev Internal (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev Noninternal (R : Finset V) := {e : Edge Γ // ¬ (e.1.1 ∈ R ∧ e.1.2 ∈ R)}
private abbrev Boundary (R : Finset V) := {e : Edge Γ // ManyBody.IsRegionBoundaryEdge R e}

omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem boundary_not_internal (R : Finset V) (e : Boundary (Γ := Γ) R) :
    ¬ (e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R) := by
  rcases e.2 with h | h
  · exact fun hh => h.2 hh.2
  · exact fun hh => h.1 hh.1

private def insertedBoundary (R : Finset V) (ζ : Noninternal (Γ := Γ) R → X × X)
    (e : Boundary (Γ := Γ) R) : X :=
  if e.1.1.1 ∈ R then (ζ ⟨e.1, boundary_not_internal R e⟩).2
  else (ζ ⟨e.1, boundary_not_internal R e⟩).1

omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem outside_not_internal (R : Finset V) (v : {v : V // v ∉ R})
    (e : IncidentEdge Γ v.1) : ¬ (e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R) := by
  rintro ⟨ht, hh⟩
  rcases e.2 with h | h
  · exact v.2 (h ▸ ht)
  · exact v.2 (h ▸ hh)

private def outsideLabels (R : Finset V) (ζ : Noninternal (Γ := Γ) R → X × X)
    (v : {v : V // v ∉ R}) (e : IncidentEdge Γ v.1) : X :=
  if e.1.1.1 = v.1 then (ζ ⟨e.1, outside_not_internal R v e⟩).2
  else (ζ ⟨e.1, outside_not_internal R v e⟩).1

private theorem sum_identity_pairs {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → X × X) → ℂ) :
    (∑ ξ : I → X × X, (∏ i, (1 : Matrix X X ℂ) (ξ i).1 (ξ i).2) * f ξ) =
      ∑ ξ : I → X, f (fun i => (ξ i, ξ i)) := by
  classical
  let E := Equiv.arrowProdEquivProdArrow I (fun _ => X) (fun _ => X)
  rw [← E.symm.sum_comp, Fintype.sum_prod_type]
  simp [E, Equiv.arrowProdEquivProdArrow, Matrix.one_apply,
    Fintype.prod_boole, ← funext_iff]

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype X] [DecidableEq X] in
private theorem assembled_region_labels (R : Finset V)
    (ξ : Internal (Γ := Γ) R → X) (ζ : Noninternal (Γ := Γ) R → X × X)
    (v : {v : V // v ∈ R}) (e : IncidentEdge Γ v.1) :
    graphSiteBondEndpointEquiv.symm
      ((Equiv.piEquivPiSubtypeProd
        (fun e : Edge Γ => e.1.1 ∈ R ∧ e.1.2 ∈ R) (fun _ => X × X)).symm
          ((fun e => (ξ e, ξ e)), ζ)) v.1 e =
    (graphRegionIncidentConfigEquiv R).symm (ξ, insertedBoundary R ζ)
      ⟨e.1, isRegionIncidentEdge_of_regionVertex R v e⟩ := by
  classical
  by_cases hi : e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R
  · have h := graphRegionIncidentConfigEquiv_apply_internal R
      ((graphRegionIncidentConfigEquiv R).symm (ξ, insertedBoundary R ζ)) ⟨e.1, hi⟩
    rw [Equiv.apply_symm_apply] at h
    simp only [graphSiteBondEndpointEquiv, Equiv.coe_fn_symm_mk,
      Equiv.piEquivPiSubtypeProd, hi]
    simpa using h
  · have hb : ManyBody.IsRegionBoundaryEdge R e.1 :=
      ManyBody.IsRegionIncidentEdge.isRegionBoundaryEdge
        (isRegionIncidentEdge_of_regionVertex R v e) hi
    have h := graphRegionIncidentConfigEquiv_apply_boundary R
      ((graphRegionIncidentConfigEquiv R).symm (ξ, insertedBoundary R ζ)) ⟨e.1, hb⟩
    rw [Equiv.apply_symm_apply] at h
    rw [← h]
    simp only [graphSiteBondEndpointEquiv, Equiv.coe_fn_symm_mk,
      Equiv.piEquivPiSubtypeProd, hi, ↓reduceDIte, insertedBoundary]
    by_cases ht : e.1.1.1 = v.1
    · simp [ht, v.2]
    · have hh := e.2.resolve_left ht
      have hn : e.1.1.1 ∉ R := fun hn => hi ⟨hn, hh.symm ▸ v.2⟩
      simp [ht, hn]

/-- Matrices on crossing and exterior bonds preserve every regional physical
slice when all internal matrices are identities. No invertibility or symmetry
of the matrices or sites is required. Source: SCP10, Theorem 5.5 and
lines 1935–1990, the boundary-condition argument for local closures. -/
theorem graphInsertedBondNetwork_slice_mem_regionGroundSpace_of_internal_eq_one {d : ℕ}
    (K : Edge Γ → Matrix X X ℂ)
    (a : (v : V) → (IncidentEdge Γ v → X) → Fin d → ℂ)
    (R : Finset V)
    (hK : ∀ e : Edge Γ, e.1.1 ∈ R → e.1.2 ∈ R → K e = 1)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    (fun σ => graphInsertedBondNetwork K a (assembleRegionσ R σ τ)) ∈
      regionGroundSpace (groupBondTensor a) R := by
  classical
  let E := Equiv.piEquivPiSubtypeProd
    (fun e : Edge Γ => e.1.1 ∈ R ∧ e.1.2 ∈ R) (fun _ => X × X)
  let c : (Noninternal (Γ := Γ) R → X × X) → ℂ := fun ζ =>
    (∏ e : Noninternal (Γ := Γ) R, K e.1 (ζ e).1 (ζ e).2) *
      ∏ v : {v : V // v ∉ R}, a v.1 (outsideLabels R ζ v)
        (τ ⟨v.1, by simp [v.2]⟩)
  have hk (ξ : Internal (Γ := Γ) R → X × X)
      (ζ : Noninternal (Γ := Γ) R → X × X) :
      (∏ e, K e (E.symm (ξ, ζ) e).1 (E.symm (ξ, ζ) e).2) =
        (∏ e : Internal (Γ := Γ) R, (1 : Matrix X X ℂ) (ξ e).1 (ξ e).2) *
        ∏ e : Noninternal (Γ := Γ) R, K e.1 (ζ e).1 (ζ e).2 := by
    rw [← Fintype.prod_subtype_mul_prod_subtype
      (fun e : Edge Γ => e.1.1 ∈ R ∧ e.1.2 ∈ R)]
    congr 1
    · apply Finset.prod_congr rfl
      intro e _
      simp [E, hK e.1 e.2.1 e.2.2, e.2]
    · apply Finset.prod_congr rfl
      intro e _
      simp [E, e.2]
  have hv (ξ : Internal (Γ := Γ) R → X)
      (ζ : Noninternal (Γ := Γ) R → X × X)
      (σ : RegionPhysicalConfig (d := d) R) :
      (∏ e : Noninternal (Γ := Γ) R, K e.1 (ζ e).1 (ζ e).2) *
        (∏ v, a v (graphSiteBondEndpointEquiv.symm
          (E.symm ((fun e => (ξ e, ξ e)), ζ)) v) (assembleRegionσ R σ τ v)) =
      c ζ * ∏ v : {v : V // v ∈ R}, a v.1
        (fun e => (graphRegionIncidentConfigEquiv R).symm (ξ, insertedBoundary R ζ)
          ⟨e.1, isRegionIncidentEdge_of_regionVertex R v e⟩) (σ v) := by
    have hr : (∏ v : {v : V // v ∈ R}, a v.1
          (graphSiteBondEndpointEquiv.symm (E.symm ((fun e => (ξ e, ξ e)), ζ)) v.1)
          (assembleRegionσ R σ τ v.1)) =
        ∏ v : {v : V // v ∈ R}, a v.1
          (fun e => (graphRegionIncidentConfigEquiv R).symm (ξ, insertedBoundary R ζ)
            ⟨e.1, isRegionIncidentEdge_of_regionVertex R v e⟩) (σ v) := by
      apply Finset.prod_congr rfl
      intro v _
      simp only [assembleRegionσ, v.2, ↓reduceDIte]
      congr 1
      funext e
      exact assembled_region_labels R ξ ζ v e
    have ho : (∏ v : {v : V // v ∉ R}, a v.1
          (graphSiteBondEndpointEquiv.symm (E.symm ((fun e => (ξ e, ξ e)), ζ)) v.1)
          (assembleRegionσ R σ τ v.1)) =
        ∏ v : {v : V // v ∉ R}, a v.1 (outsideLabels R ζ v)
          (τ ⟨v.1, by simp [v.2]⟩) := by
      apply Finset.prod_congr rfl
      intro v _
      simp only [assembleRegionσ, v.2, ↓reduceDIte]
      congr 1
      funext e
      simp only [graphSiteBondEndpointEquiv, E, Equiv.piEquivPiSubtypeProd,
        Equiv.coe_fn_symm_mk, outside_not_internal R v e, ↓reduceDIte, outsideLabels]
    have hp := Fintype.prod_subtype_mul_prod_subtype (fun v : V => v ∈ R)
      (fun v => a v (graphSiteBondEndpointEquiv.symm
        (E.symm ((fun e => (ξ e, ξ e)), ζ)) v) (assembleRegionσ R σ τ v))
    have hi : Subtype.fintype (fun v : V => v ∈ R) = Finset.Subtype.fintype R :=
      Subsingleton.elim _ _
    rw [hi] at hp
    have ht := hp.symm.trans (congrArg₂ (· * ·) hr ho)
    exact (congrArg
      (fun z => (∏ e : Noninternal (Γ := Γ) R, K e.1 (ζ e).1 (ζ e).2) * z)
      ht).trans (by dsimp only [c]; ring)
  have heq : (fun σ => graphInsertedBondNetwork K a (assembleRegionσ R σ τ)) =
      ∑ ζ : Noninternal (Γ := Γ) R → X × X,
        c ζ • graphOpenRegionNetwork a R (insertedBoundary R ζ) := by
    funext σ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    unfold graphInsertedBondNetwork
    rw [← E.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ζ _
    simp_rw [hk, mul_assoc]
    rw [sum_identity_pairs]
    simp_rw [hv]
    rw [← Finset.mul_sum, graphOpenRegionNetwork_eq_sum_internal]
  rw [heq]
  apply Submodule.sum_mem
  intro ζ _
  apply Submodule.smul_mem
  have h := openRegionWeight_mem_regionGroundSpace (groupBondTensor a) R
    (fun e => Fintype.equivFin X (insertedBoundary R ζ e))
  have heq : openRegionWeight (groupBondTensor a) R
      (fun e => Fintype.equivFin X (insertedBoundary R ζ e)) =
      graphOpenRegionNetwork a R (insertedBoundary R ζ) := by
    funext σ
    exact openRegionWeight_groupBondTensor_eq_graphOpenRegionNetwork a R _ σ
  rwa [heq] at h

end TNLean.PEPS

end

end GraphInsertedRegionSupport
