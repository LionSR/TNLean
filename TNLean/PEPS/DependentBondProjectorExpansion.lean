/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentBondNetwork
import TNLean.PEPS.GInjective
import TNLean.Algebra.RepresentationTensorProduct

/-!
# Canonical projector contractions with different bond dimensions

Each labelled edge has its own finite coordinate type and its own group
representation. At its head the group acts directly, and at its tail by inverse
transpose. Thus the local virtual action is defined on the actual dependent
incident configuration space. The canonical tensor is its averaging projector.

Expanding the literal contraction gives one group label per vertex and one
matrix product per edge. No common bond dimension, graph simplicity, unitarity,
or semi-regularity is required for this expansion. Self edges have two distinct
endpoint incidences throughout.

Source: Schuch, Cirac, Pérez-García, arXiv:1001.3807, Definition 5.1 and the
projector contraction in Theorem 5.9, lines 1582–1621.
-/

noncomputable section
open scoped BigOperators Matrix

namespace TNLean.PEPS.DependentBondNetwork

variable {Vertex Edge : Type*} [Fintype Edge] [DecidableEq Edge] [DecidableEq Vertex]
variable (tail head : Edge → Vertex) (D : Edge → Type*)
variable [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
variable {G : Type*} [Group G]

/-- The oriented tensor product of the independently chosen edge actions.
Rows are outputs and columns inputs. Source: SCP10, Definition 5.1. -/
def incidentMatrix (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (v : Vertex) (g : G) :
    Matrix (LocalConfig tail head D v) (LocalConfig tail head D v) ℂ :=
  fun σ η => ∏ p : IncidentEndpoint tail head v,
    if p.1.2 then U p.1.1 g (σ p) (η p) else U p.1.1 g⁻¹ (η p) (σ p)

omit [DecidableEq Edge] in
/-- The incident action of the identity is the identity matrix. -/
@[simp]
theorem incidentMatrix_one (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (v : Vertex) : incidentMatrix tail head D U v 1 = 1 := by
  classical
  ext σ η
  simp only [incidentMatrix, inv_one, map_one, Matrix.one_apply]
  have h (p : IncidentEndpoint tail head v) :
      (if p.1.2 then (if σ p = η p then (1 : ℂ) else 0)
        else (if η p = σ p then 1 else 0)) = (if σ p = η p then 1 else 0) := by
    cases p.1.2 <;> simp [eq_comm]
  simp only [h, Fintype.prod_boole, ← funext_iff]

/-- Inverse transpose reverses the reversed product at each tail, so the
incident action is a representation even for nonunitary edge actions. -/
theorem incidentMatrix_mul (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (v : Vertex) (g h : G) :
    incidentMatrix tail head D U v (g * h) =
      incidentMatrix tail head D U v g * incidentMatrix tail head D U v h := by
  classical
  ext σ η
  simp only [incidentMatrix, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  let F : (p : IncidentEndpoint tail head v) → D p.1.1 → ℂ := fun p j =>
    (if p.1.2 then U p.1.1 g (σ p) j else U p.1.1 g⁻¹ j (σ p)) *
      (if p.1.2 then U p.1.1 h j (η p) else U p.1.1 h⁻¹ (η p) j)
  change _ = ∑ j : LocalConfig tail head D v, ∏ p, F p (j p)
  rw [← Fintype.prod_sum]
  dsimp only [F]
  apply Finset.prod_congr rfl
  intro p _
  cases p.1.2
  · simp only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, map_mul, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · simp only [↓reduceIte, map_mul, Matrix.mul_apply]

/-- The actual dependent incident representation. Source: SCP10, Definition 5.1. -/
def incidentRepresentation (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ) (v : Vertex) :
    Representation ℂ G (LocalConfig tail head D v → ℂ) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp
    { toFun := incidentMatrix tail head D U v
      map_one' := incidentMatrix_one tail head D U v
      map_mul' := incidentMatrix_mul tail head D U v }

/-- The incident representation acts by its explicitly defined matrix. -/
@[simp]
theorem incidentRepresentation_apply
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ) (v : Vertex) (g : G)
    (x : LocalConfig tail head D v → ℂ) :
    incidentRepresentation tail head D U v g x =
      incidentMatrix tail head D U v g *ᵥ x := rfl

/-- The coefficient map from the actual local virtual space to an arbitrary
site-dependent physical space. Source: SCP10, lines 501–507. -/
def localSiteMap {Phys : Vertex → Type*}
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ) (v : Vertex) :
    (LocalConfig tail head D v → ℂ) →ₗ[ℂ] (Phys v → ℂ) :=
  Matrix.mulVecLin (fun s η => A v η s)

omit [∀ e, DecidableEq (D e)] in
/-- Evaluation of the actual local coefficient map. -/
theorem localSiteMap_apply {Phys : Vertex → Type*}
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ) (v : Vertex)
    (x : LocalConfig tail head D v → ℂ) (s : Phys v) :
    localSiteMap tail head D A v x s = ∑ η, A v η s * x η := rfl

variable [Fintype G]
attribute [local instance] Representation.invertibleFintypeCardComplex

/-- A canonical averaging tensor for an arbitrary representation on each
actual local configuration space. Source: SCP10, Definition 5.1(ii). -/
def representationAveragingSite
    (ρ : (v : Vertex) → Representation ℂ G (LocalConfig tail head D v → ℂ))
    (v : Vertex) (η s : LocalConfig tail head D v) : ℂ :=
  LinearMap.toMatrix' (ρ v).averageMap s η

/-- The canonical tensor expands over one group element at a site. -/
theorem representationAveragingSite_apply
    (ρ : (v : Vertex) → Representation ℂ G (LocalConfig tail head D v → ℂ))
    (v : Vertex) (η s : LocalConfig tail head D v) :
    representationAveragingSite tail head D ρ v η s =
      (Fintype.card G : ℂ)⁻¹ * ∑ g : G, LinearMap.toMatrix' (ρ v g) s η := by
  rw [representationAveragingSite, LinearMap.toMatrix'_apply,
    Representation.averageMap_apply_eq_sum]
  simp only [Pi.smul_apply, Finset.sum_apply, invOf_eq_inv, smul_eq_mul,
    LinearMap.toMatrix'_apply]

/-- The coefficient map of the canonical tensor is its averaging projector. -/
@[simp]
theorem localSiteMap_representationAveragingSite
    (ρ : (v : Vertex) → Representation ℂ G (LocalConfig tail head D v → ℂ))
    (v : Vertex) :
    localSiteMap tail head D (representationAveragingSite tail head D ρ) v =
      (ρ v).averageMap := by
  change Matrix.toLin' (LinearMap.toMatrix' (ρ v).averageMap) = _
  exact Matrix.toLin'_toMatrix' _

/-- The canonical tensor is invariant and injective on invariant vectors.
Source: SCP10, Definition 5.1, lines 1278–1296. -/
theorem isGInjective_representationAveragingSite
    (ρ : (v : Vertex) → Representation ℂ G (LocalConfig tail head D v → ℂ))
    (v : Vertex) :
    IsGInjective (ρ v)
      (localSiteMap tail head D (representationAveragingSite tail head D ρ) v) := by
  rw [localSiteMap_representationAveragingSite]
  refine ⟨?_, ?_⟩
  · intro g
    change (ρ v).averageMap * ρ v g = (ρ v).averageMap
    rw [Representation.averageMap, ← Representation.asAlgebraHom_single_one,
      ← map_mul, GroupAlgebra.mul_average_right]
  · intro x hx hzero
    rwa [(ρ v).averageMap_id x hx] at hzero

/-- Averaging the true incident representation gives the canonical local tensor.
Source: SCP10, Theorem 5.9, lines 1582–1621. -/
def averagingSite (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (v : Vertex) (η s : LocalConfig tail head D v) : ℂ :=
  representationAveragingSite tail head D (incidentRepresentation tail head D U) v η s

/-- The actual incident averaging tensor has precisely the invariant projector
as its local coefficient map. -/
@[simp]
theorem localSiteMap_averagingSite
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ) (v : Vertex) :
    localSiteMap tail head D (averagingSite tail head D U) v =
      (incidentRepresentation tail head D U v).averageMap :=
  localSiteMap_representationAveragingSite tail head D _ v

/-- The actual dependent-dimensional averaging tensor is G-injective.
Source: SCP10, Definition 5.1, lines 1278–1296. -/
theorem isGInjective_averagingSite
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ) (v : Vertex) :
    IsGInjective (incidentRepresentation tail head D U v)
      (localSiteMap tail head D (averagingSite tail head D U) v) :=
  isGInjective_representationAveragingSite tail head D _ v

/-- Canonical local coefficients are the normalized sum of the incident matrices. -/
theorem averagingSite_apply (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (v : Vertex) (η s : LocalConfig tail head D v) :
    averagingSite tail head D U v η s =
      (Fintype.card G : ℂ)⁻¹ * ∑ g : G, incidentMatrix tail head D U v g s η := by
  rw [averagingSite, representationAveragingSite, LinearMap.toMatrix'_apply,
    Representation.averageMap_apply_eq_sum]
  simp only [Pi.smul_apply, Finset.sum_apply, incidentRepresentation_apply,
    Matrix.mulVec_single_one, Matrix.col_apply, invOf_eq_inv, smul_eq_mul]

variable [Fintype Vertex]

omit [∀ e, DecidableEq (D e)] in
/-- Independent local sums expand over one choice at each vertex. -/
theorem network_sum {I : Type*} [Fintype I] {Phys : Vertex → Type*}
    (A : I → (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ) (σ : (v : Vertex) → Phys v) :
    network tail head D (fun v η s => ∑ i, A i v η s) B σ =
      ∑ q : Vertex → I, network tail head D (fun v => A (q v) v) B σ := by
  simp_rw [network, Fintype.prod_sum, Finset.mul_sum]
  exact Finset.sum_comm

omit [∀ e, DecidableEq (D e)] [DecidableEq Vertex] in
/-- Local scalar factors multiply into the global contraction normalization. -/
theorem network_mul {Phys : Vertex → Type*} (c : Vertex → ℂ)
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ) (σ : (v : Vertex) → Phys v) :
    network tail head D (fun v η s => c v * A v η s) B σ =
      (∏ v, c v) * network tail head D A B σ := by
  simp only [network, Finset.prod_mul_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

omit [Fintype G] in
/-- A fixed choice of vertex group labels transforms each edge by its own
head and tail actions. This is the literal independent-endpoint contraction. -/
theorem network_incidentMatrix
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (q : Vertex → G) (B : (e : Edge) → Matrix (D e) (D e) ℂ)
    (σ : EndpointConfig D) :
    network tail head D (fun v η s => incidentMatrix tail head D U v (q v) s η)
        B (endpointSiteEquiv tail head D σ) =
      ∏ e, (U e (q (head e)) * B e * U e ((q (tail e))⁻¹))
        (σ (e, true)) (σ (e, false)) := by
  classical
  have hprod (β : EndpointConfig D) :
      (∏ v, incidentMatrix tail head D U v (q v)
        (endpointSiteEquiv tail head D σ v) (endpointSiteEquiv tail head D β v)) =
      ∏ e, U e (q (head e)) (σ (e, true)) (β (e, true)) *
        U e ((q (tail e))⁻¹) (β (e, false)) (σ (e, false)) := by
    let f : Endpoint Edge → ℂ := fun p =>
      if p.2 then U p.1 (q (endpointVertex tail head p)) (σ p) (β p)
      else U p.1 ((q (endpointVertex tail head p))⁻¹) (β p) (σ p)
    calc
      _ = ∏ v, ∏ p : IncidentEndpoint tail head v, f p.1 := by
        apply Finset.prod_congr rfl
        intro v _
        apply Finset.prod_congr rfl
        intro p _
        simp only [f, endpointSiteEquiv_apply, p.property]
      _ = ∏ e, f (e, false) * f (e, true) :=
        prod_incident_eq_prod_edge tail head f
      _ = _ := by simp only [f, endpointVertex, Bool.false_eq_true, ↓reduceIte, mul_comm]
  simp only [network, hprod, bondWeight, ← Finset.prod_mul_distrib]
  rw [sum_endpoint_prod_eq_prod_sum D (fun e h t => B e h t *
    (U e (q (head e)) (σ (e, true)) h * U e ((q (tail e))⁻¹) t (σ (e, false))))]
  apply Finset.prod_congr rfl
  intro e _
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- Expanding the actual canonical tensor network gives one independent group
label per vertex and the head-row/tail-column matrix product on each edge.
Bond dimensions and representations may vary independently, and self and
parallel edges remain present. Source: SCP10, Theorem 5.9, lines 1582–1621. -/
theorem network_averagingSite
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ)
    (σ : (v : Vertex) → LocalConfig tail head D v) :
    network tail head D (averagingSite tail head D U) B σ =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card Vertex *
        ∑ q : Vertex → G, ∏ e,
          (U e (q (head e)) * B e * U e ((q (tail e))⁻¹))
            ((endpointSiteEquiv tail head D).symm σ (e, true))
            ((endpointSiteEquiv tail head D).symm σ (e, false)) := by
  have h : averagingSite tail head D U = fun v η s =>
      (Fintype.card G : ℂ)⁻¹ * ∑ g : G, incidentMatrix tail head D U v g s η := by
    funext v η s
    exact averagingSite_apply tail head D U v η s
  rw [h, network_mul, network_sum]
  simp only [Finset.prod_const, Finset.card_univ]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  simpa only [Equiv.apply_symm_apply] using
    network_incidentMatrix tail head D U q B ((endpointSiteEquiv tail head D).symm σ)

/-- A vertex-dependent gauge transformation does not change the canonical
network, even for arbitrary inserted bond matrices. Source: SCP10,
Definition 5.1(i) and equation `eq:2d:move-strings`. -/
theorem network_averagingSite_bondGauge
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ) (q : Vertex → G)
    (σ : (v : Vertex) → LocalConfig tail head D v) :
    network tail head D (averagingSite tail head D U)
        (fun e => U e (q (head e)) * B e * U e ((q (tail e))⁻¹)) σ =
      network tail head D (averagingSite tail head D U) B σ := by
  rw [network_averagingSite, network_averagingSite]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight q) _ _ fun r => ?_
  apply Finset.prod_congr rfl
  intro e _
  simp only [Equiv.coe_mulRight, Pi.mul_apply, mul_inv_rev, map_mul, Matrix.mul_assoc]

/-- Gauge-related group labels give exactly the same canonical contraction.
Source: SCP10, the virtual symmetry in Definition 5.1 and the closure
manipulations in Theorem 5.5. -/
theorem network_averagingSite_vertexGauge
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (p : Edge → G) (q : Vertex → G)
    (σ : (v : Vertex) → LocalConfig tail head D v) :
    network tail head D (averagingSite tail head D U)
        (fun e => U e (q (head e) * p e * (q (tail e))⁻¹)) σ =
      network tail head D (averagingSite tail head D U) (fun e => U e (p e)) σ := by
  simpa only [map_mul] using
    network_averagingSite_bondGauge tail head D U (fun e => U e (p e)) q σ

end TNLean.PEPS.DependentBondNetwork
