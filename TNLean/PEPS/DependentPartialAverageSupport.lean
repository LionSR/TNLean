/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentCutBondSupport

/-!
# Partial vertex averaging and uncut bond support

Composing the incident action at each vertex with its own group endomorphism
allows averaging at the core vertices while keeping boundary vertices unchanged.
The identity endomorphism gives the usual canonical tensor; the trivial
endomorphism gives the identity tensor. Expanding the contraction retains the
full coherent sum over vertex labels. Every uncut edge consequently has
representation-matrix support in each physical slice, including for arbitrary
correlated cut boundaries. No assumption about coefficient support is used.

Source: Schuch, Cirac, Pérez-García, arXiv:1001.3807, Definition 5.1 and
Theorem 5.4, `thm:2d:intersection`, lines 1373–1420.
-/

noncomputable section
open scoped BigOperators Matrix

namespace TNLean.PEPS.DependentBondNetwork

variable {Vertex Edge G : Type*} [Group G]
variable [Fintype Edge] [DecidableEq Vertex] [DecidableEq Edge]
variable (tail head : Edge → Vertex) (D : Edge → Type*)
variable [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]

/-- Precompose each vertex's incident action by a chosen group endomorphism.
Identity endomorphisms act on core vertices, and trivial ones on boundary vertices. -/
def partialIncidentRepresentation
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (f : Vertex → G →* G) (v : Vertex) :
    Representation ℂ G (LocalConfig tail head D v → ℂ) :=
  (incidentRepresentation tail head D U v).comp (f v)

/-- The partially selected action is still the literal incident matrix action. -/
@[simp]
theorem partialIncidentRepresentation_apply
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (f : Vertex → G →* G) (v : Vertex) (g : G)
    (x : LocalConfig tail head D v → ℂ) :
    partialIncidentRepresentation tail head D U f v g x =
      incidentMatrix tail head D U v (f v g) *ᵥ x := rfl

/-- An identity vertex endomorphism retains the canonical incident representation. -/
theorem partialIncidentRepresentation_of_eq_id
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (f : Vertex → G →* G) (v : Vertex) (hv : f v = MonoidHom.id G) :
    partialIncidentRepresentation tail head D U f v =
      incidentRepresentation tail head D U v := by
  simp [partialIncidentRepresentation, hv]

/-- A trivial vertex endomorphism gives the trivial incident representation. -/
theorem partialIncidentRepresentation_of_eq_one
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (f : Vertex → G →* G) (v : Vertex) (hv : f v = 1) :
    partialIncidentRepresentation tail head D U f v = 1 := by
  ext g
  simp [partialIncidentRepresentation, hv]

variable [Fintype G]
attribute [local instance] Representation.invertibleFintypeCardComplex

/-- Canonical averaging at vertices selected by their endomorphisms. -/
def partialAveragingSite
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (f : Vertex → G →* G) (v : Vertex) (η s : LocalConfig tail head D v) : ℂ :=
  representationAveragingSite tail head D
    (partialIncidentRepresentation tail head D U f) v η s

/-- The selected averaging tensor is its representation's averaging projector. -/
@[simp]
theorem localSiteMap_partialAveragingSite
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (f : Vertex → G →* G) (v : Vertex) :
    localSiteMap tail head D (partialAveragingSite tail head D U f) v =
      (partialIncidentRepresentation tail head D U f v).averageMap :=
  localSiteMap_representationAveragingSite tail head D _ v

/-- Selected averaging is invariant and injective on invariant vectors. -/
theorem isGInjective_partialAveragingSite
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (f : Vertex → G →* G) (v : Vertex) :
    IsGInjective (partialIncidentRepresentation tail head D U f v)
      (localSiteMap tail head D (partialAveragingSite tail head D U f) v) :=
  isGInjective_representationAveragingSite tail head D _ v

/-- Identity endomorphisms retain exactly the usual canonical site tensor. -/
theorem partialAveragingSite_of_eq_id
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (f : Vertex → G →* G) (v : Vertex) (hv : f v = MonoidHom.id G) :
    partialAveragingSite tail head D U f v = averagingSite tail head D U v := by
  funext η s
  unfold partialAveragingSite averagingSite representationAveragingSite
  rw [partialIncidentRepresentation_of_eq_id tail head D U f v hv]

/-- At a trivially acting boundary vertex the coefficient map is the identity. -/
theorem localSiteMap_partialAveragingSite_of_eq_one
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (f : Vertex → G →* G) (v : Vertex) (hv : f v = 1) :
    localSiteMap tail head D (partialAveragingSite tail head D U f) v = LinearMap.id := by
  rw [localSiteMap_partialAveragingSite]
  apply LinearMap.ext
  intro x
  have hx : x ∈ (partialIncidentRepresentation tail head D U f v).invariants := by
    intro g
    rw [partialIncidentRepresentation_of_eq_one tail head D U f v hv]
    rfl
  exact Representation.averageMap_id _ x hx

/-- A trivial vertex endomorphism gives identity tensor coefficients. -/
theorem partialAveragingSite_of_eq_one
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (f : Vertex → G →* G) (v : Vertex) (hv : f v = 1)
    (η s : LocalConfig tail head D v) :
    partialAveragingSite tail head D U f v η s =
      (1 : Matrix (LocalConfig tail head D v) (LocalConfig tail head D v) ℂ) s η := by
  have h := localSiteMap_partialAveragingSite_of_eq_one tail head D U f v hv
  rw [localSiteMap_partialAveragingSite] at h
  unfold partialAveragingSite representationAveragingSite
  rw [h]
  simp only [LinearMap.toMatrix'_id]

/-- Partial averaging coefficients are the normalized sum of the selected incident actions. -/
theorem partialAveragingSite_apply
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (f : Vertex → G →* G) (v : Vertex) (η s : LocalConfig tail head D v) :
    partialAveragingSite tail head D U f v η s =
      (Fintype.card G : ℂ)⁻¹ * ∑ g : G, incidentMatrix tail head D U v (f v g) s η := by
  rw [partialAveragingSite, representationAveragingSite, LinearMap.toMatrix'_apply,
    Representation.averageMap_apply_eq_sum]
  simp only [Pi.smul_apply, Finset.sum_apply, partialIncidentRepresentation_apply,
    Matrix.mulVec_single_one, Matrix.col_apply, invOf_eq_inv, smul_eq_mul]

variable [Fintype Vertex]

/-- The full contraction retains one coherent group choice per vertex, with
that vertex's endomorphism applied before the incident action. -/
theorem network_partialAveragingSite
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (f : Vertex → G →* G) (B : (e : Edge) → Matrix (D e) (D e) ℂ)
    (σ : (v : Vertex) → LocalConfig tail head D v) :
    network tail head D (partialAveragingSite tail head D U f) B σ =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card Vertex *
        ∑ q : Vertex → G, ∏ e,
          gaugeBondMatrix tail head D U B (fun v => f v (q v)) e
            ((endpointSiteEquiv tail head D).symm σ (e, true))
            ((endpointSiteEquiv tail head D).symm σ (e, false)) := by
  have h : partialAveragingSite tail head D U f = fun v η s =>
      (Fintype.card G : ℂ)⁻¹ * ∑ g : G, incidentMatrix tail head D U v (f v g) s η := by
    funext v η s
    exact partialAveragingSite_apply tail head D U f v η s
  rw [h, network_mul, network_sum]
  simp only [Finset.prod_const, Finset.card_univ]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  simpa only [Equiv.apply_symm_apply, gaugeBondMatrix] using
    network_incidentMatrix tail head D U (fun v => f v (q v)) B
      ((endpointSiteEquiv tail head D).symm σ)

/-- Gauge transformations coming from the selected vertex actions leave the
partially averaged contraction unchanged, including with arbitrary edge insertions. -/
theorem network_partialAveragingSite_bondGauge
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (f : Vertex → G →* G) (B : (e : Edge) → Matrix (D e) (D e) ℂ)
    (q : Vertex → G) (σ : (v : Vertex) → LocalConfig tail head D v) :
    network tail head D (partialAveragingSite tail head D U f)
        (gaugeBondMatrix tail head D U B (fun v => f v (q v))) σ =
      network tail head D (partialAveragingSite tail head D U f) B σ := by
  rw [network_partialAveragingSite, network_partialAveragingSite]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight q) _ _ fun r => ?_
  apply Finset.prod_congr rfl
  intro e _
  simp only [gaugeBondMatrix, Equiv.coe_mulRight, Pi.mul_apply, map_mul,
    mul_inv_rev, Matrix.mul_assoc]

/-- Edge group labels related by the selected vertex actions give the same
partial-average contraction. Boundary vertices may act trivially. -/
theorem network_partialAveragingSite_vertexGauge
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (f : Vertex → G →* G) (p : Edge → G) (q : Vertex → G)
    (σ : (v : Vertex) → LocalConfig tail head D v) :
    network tail head D (partialAveragingSite tail head D U f)
        (fun e => U e (f (head e) (q (head e)) * p e * (f (tail e) (q (tail e)))⁻¹)) σ =
      network tail head D (partialAveragingSite tail head D U f) (fun e => U e (p e)) σ := by
  simp only [map_mul]
  exact network_partialAveragingSite_bondGauge tail head D U f (fun e => U e (p e)) q σ

/-- Regrouping the partial-average contraction gives the product of gauged edge matrices. -/
theorem bondRegrouping_network_partialAveragingSite
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (f : Vertex → G →* G) (B : (e : Edge) → Matrix (D e) (D e) ℂ) :
    bondRegrouping tail head D (network tail head D (partialAveragingSite tail head D U f) B) =
      fun β => (Fintype.card G : ℂ)⁻¹ ^ Fintype.card Vertex *
        ∑ q : Vertex → G, ∏ e,
          gaugeBondMatrix tail head D U B (fun v => f v (q v)) e (β e).1 (β e).2 := by
  funext β
  rw [bondRegrouping_apply, network_partialAveragingSite]
  simp only [siteBondEquiv, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.symm_apply_apply, endpointPairEquiv, Equiv.coe_fn_symm_mk,
    Bool.false_eq_true, ↓reduceIte]

/-- The partial-average network is a coherent sum of physical matrix products. -/
theorem network_partialAveragingSite_eq_sum_matrixBondProduct
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (f : Vertex → G →* G) (B : (e : Edge) → Matrix (D e) (D e) ℂ) :
    network tail head D (partialAveragingSite tail head D U f) B =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card Vertex •
        ∑ q : Vertex → G,
          matrixBondProduct tail head D (gaugeBondMatrix tail head D U B (fun v => f v (q v))) := by
  funext σ
  rw [network_partialAveragingSite]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, matrixBondProduct,
    siteBondEquiv, Equiv.trans_apply, endpointPairEquiv_apply]

/-- An identity edge has representation-matrix support in every physical slice
under partial averaging, for arbitrary insertions on all other edges. -/
theorem physicalBondSlice_network_partialAveragingSite_mem_range
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (f : Vertex → G →* G) (B : (e : Edge) → Matrix (D e) (D e) ℂ)
    (e : Edge) (he : B e = 1) (τ : (w : Edge) → D w × D w) :
    physicalBondSlice tail head D e τ
      (network tail head D (partialAveragingSite tail head D U f) B) ∈
      (Matrix.mulVecLin (bondMatrix D U e)).range := by
  have hrepr (q : Vertex → G) :
      (fun s : D e × D e =>
        gaugeBondMatrix tail head D U B (fun v => f v (q v)) e s.1 s.2) ∈
        (Matrix.mulVecLin (bondMatrix D U e)).range := by
    simpa only [gaugeBondMatrix, he, Matrix.mul_one, ← map_mul] using
      representation_mem_bondMatrix_range D U e
        (f (head e) (q (head e)) * (f (tail e) (q (tail e)))⁻¹)
  have heq : physicalBondSlice tail head D e τ
      (network tail head D (partialAveragingSite tail head D U f) B) =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card Vertex •
        ∑ q : Vertex → G, (fun s => ∏ w,
          gaugeBondMatrix tail head D U B (fun v => f v (q v)) w
            (Function.update τ e s w).1 (Function.update τ e s w).2) := by
    funext s
    simpa only [physicalBondSlice, LinearMap.pi_apply, LinearMap.proj_apply,
      bondRegrouping_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using
      congrFun (bondRegrouping_network_partialAveragingSite tail head D U f B)
        (Function.update τ e s)
  rw [heq]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro q _
  rw [dependentProduct_coordinateSlice_eq_smul
    (fun w (s : D w × D w) =>
      gaugeBondMatrix tail head D U B (fun v => f v (q v)) w s.1 s.2) e τ]
  exact Submodule.smul_mem _ _ (hrepr q)

/-- Arbitrary correlated cut boundaries retain representation-matrix support
on every uncut edge of a partially averaged network. -/
theorem physicalBondSlice_mem_range_of_mem_partialCutSpace
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (f : Vertex → G →* G) (C : Finset Edge) (e : Edge) (he : e ∉ C)
    (τ : (w : Edge) → D w × D w)
    {ψ : ((v : Vertex) → LocalConfig tail head D v) → ℂ}
    (hψ : ψ ∈ cutSpace tail head D (partialAveragingSite tail head D U f) C) :
    physicalBondSlice tail head D e τ ψ ∈ (Matrix.mulVecLin (bondMatrix D U e)).range := by
  classical
  let S := (Matrix.mulVecLin (bondMatrix D U e)).range.comap (physicalBondSlice tail head D e τ)
  have hle : cutSpace tail head D (partialAveragingSite tail head D U f) C ≤ S := by
    rw [cutSpace_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨η, rfl⟩
    change physicalBondSlice tail head D e τ
      (cutMap tail head D (partialAveragingSite tail head D U f) C (Pi.single η 1)) ∈
        (Matrix.mulVecLin (bondMatrix D U e)).range
    have hnet := funext
      (cutMap_single_eq_network tail head D (partialAveragingSite tail head D U f) C η)
    rw [hnet]
    apply physicalBondSlice_network_partialAveragingSite_mem_range
    simp [cutBondUnits, he]
  exact hle hψ

end TNLean.PEPS.DependentBondNetwork
