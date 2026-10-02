/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularCycleControlledBoundary
import TNLean.PEPS.RegionPhysicalMap
import TNLean.PEPS.RegularTorusGramExpansion
import TNLean.PEPS.RegularPhysicalUnitaryTransport

/-!
# Local invariant support of actual free-word controlled permutations

Independent vertex translations have an explicit action on the actual
spanning-tree physical coordinates. Evaluation of each constructed walk word
commutes with simultaneous conjugation, so the controlled boundary permutation
commutes with these translations. Averaging independent translations is the
product of the local regular projectors. The controlled permutation therefore
preserves the genuine locally invariant physical support; no surjectivity of
that projector on the ambient half-edge space is asserted.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, accessible virtual
coordinates and complementary disentangling, lines 1765–1920 and 1935–1990.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}
variable {G : Type*} [Group G] [Fintype G]

/-- Independent vertex translation in actual spanning-tree coordinates.
The reference labels transform by the root translation, and the cycles by
its conjugation. Source: SCP10, accessible coordinates, lines 1765–1920. -/
def regularRegionCoordinateTranslation (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) (o : {v : V // v ∈ R})
    (ℓ : {v : V // v ∈ R} → G)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) :
    RegularRegionCoordinates (Γ := Γ) (G := G) R T o :=
  (fun f => ℓ o * c.1 f, fun e => ℓ o * c.2.1 e,
    ⟨fun v => ℓ v * c.2.2.1.1 v * (ℓ o)⁻¹, by simp [c.2.2.1.2]⟩,
    fun e => ℓ o * c.2.2.2 e * (ℓ o)⁻¹)

/-- Reconstructing translated coordinates gives the independent left
translations of the original physical half-edge labels. Source: SCP10,
actual regular coordinates, lines 1765–1920. -/
theorem regularRegionCoordinatesEquiv_symm_coordinateTranslation (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (ℓ : {v : V // v ∈ R} → G)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) :
    (regularRegionCoordinatesEquiv R T hT htree o).symm
        (regularRegionCoordinateTranslation R T o ℓ c) =
      regularRegionGaugePhysicalLabels R (fun v => (ℓ v)⁻¹)
        ((regularRegionCoordinatesEquiv R T hT htree o).symm c) := by
  funext v e
  rcases e with ⟨f, hf⟩
  by_cases hi : f.1.1 ∈ R ∧ f.1.2 ∈ R
  · rcases hf with ht | hh
    · have hv : v = ⟨f.1.1, hi.1⟩ := Subtype.ext ht.symm
      subst v
      rw [regularRegionCoordinatesEquiv_symm_internal_tail R T hT htree o _ ⟨f, hi⟩,
        regularRegionGaugePhysicalLabels_apply,
        regularRegionCoordinatesEquiv_symm_internal_tail R T hT htree o _ ⟨f, hi⟩]
      dsimp only [regularRegionCoordinateTranslation]
      group
    · have hv : v = ⟨f.1.2, hi.2⟩ := Subtype.ext hh.symm
      subst v
      rw [regularRegionCoordinatesEquiv_symm_internal_head R T hT htree o _ ⟨f, hi⟩,
        regularRegionGaugePhysicalLabels_apply,
        regularRegionCoordinatesEquiv_symm_internal_head R T hT htree o _ ⟨f, hi⟩]
      dsimp only [regularRegionCoordinateTranslation]
      split_ifs <;> group
  · rcases hf with ht | hh
    · have htail : f.1.1 ∈ R := by simpa only [ht] using v.2
      have hhead : f.1.2 ∉ R := fun h => hi ⟨htail, h⟩
      have hv : v = ⟨f.1.1, htail⟩ := Subtype.ext ht.symm
      subst v
      rw [regularRegionCoordinatesEquiv_symm_boundary_tail R T hT htree o _ f htail hhead,
        regularRegionGaugePhysicalLabels_apply,
        regularRegionCoordinatesEquiv_symm_boundary_tail R T hT htree o _ f htail hhead]
      dsimp only [regularRegionCoordinateTranslation]
      group
    · have hhead : f.1.2 ∈ R := by simpa only [hh] using v.2
      have htail : f.1.1 ∉ R := fun h => hi ⟨h, hhead⟩
      have hv : v = ⟨f.1.2, hhead⟩ := Subtype.ext hh.symm
      subst v
      rw [regularRegionCoordinatesEquiv_symm_boundary_head R T hT htree o _ f htail hhead,
        regularRegionGaugePhysicalLabels_apply,
        regularRegionCoordinatesEquiv_symm_boundary_head R T hT htree o _ f htail hhead]
      dsimp only [regularRegionCoordinateTranslation]
      group

omit [Fintype G] in
/-- Actual free-word boundary control commutes with independent vertex
translations in spanning-tree coordinates. Source: SCP10, controlled
complement coordinates, lines 1935–1990. -/
theorem regularCycleControlledBoundary_coordinateTranslation (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (o : {v : V // v ∈ R})
    (v w : {e : Edge Γ // IsRegionBoundaryEdge R e} → {v : V // v ∈ R})
    (p : (f : {e : Edge Γ // IsRegionBoundaryEdge R e}) →
      (Γ.induce (R : Set V)).Walk (v f) (w f))
    (ℓ : {v : V // v ∈ R} → G)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) :
    regularCycleControlledBoundary R T o
        (fun z f => FreeGroup.lift z (regularRegionCycleWord R T (p f)))
        (regularRegionCoordinateTranslation R T o ℓ c) =
      regularRegionCoordinateTranslation R T o ℓ
        (regularCycleControlledBoundary R T o
          (fun z f => FreeGroup.lift z (regularRegionCycleWord R T (p f))) c) := by
  apply Prod.ext
  · funext f
    change (FreeGroup.lift (fun e => ℓ o * c.2.2.2 e * (ℓ o)⁻¹)
        (regularRegionCycleWord R T (p f)))⁻¹ * (ℓ o * c.1 f) =
      ℓ o * ((FreeGroup.lift c.2.2.2 (regularRegionCycleWord R T (p f)))⁻¹ * c.1 f)
    rw [regularRegionCycleWord_eval_conj]
    group
  · rfl

variable [Fintype V] [DecidableRel Γ.Adj] [DecidableEq G]

/-- The native physical permutation matrix of independent vertex left
translations. It acts on the original half-edge labels. -/
noncomputable def regularRegionVertexTranslationMatrix (R : Finset V)
    (ℓ : {v : V // v ∈ R} → G) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G R) (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ :=
  Matrix.permMatrixHom (R := ℂ) (regularRegionGaugePhysicalLabels R (fun v => (ℓ v)⁻¹))

/-- The actual free-word controlled physical matrix commutes with every
independent vertex translation, without an equivariance hypothesis on the
control function. Source: SCP10, lines 1935–1990. -/
theorem regularCycleControlledBoundaryMatrix_commute_vertexTranslation (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (v w : {e : Edge Γ // IsRegionBoundaryEdge R e} → {v : V // v ∈ R})
    (p : (f : {e : Edge Γ // IsRegionBoundaryEdge R e}) →
      (Γ.induce (R : Set V)).Walk (v f) (w f)) (ℓ : {v : V // v ∈ R} → G) :
    Commute (regularCycleControlledBoundaryMatrix R T hT htree o
        (fun z f => FreeGroup.lift z (regularRegionCycleWord R T (p f))))
      (regularRegionVertexTranslationMatrix R ℓ) := by
  let E := regularRegionCoordinatesEquiv (G := G) R T hT htree o
  let W := fun (z : RegionCycleEdge (Γ := Γ) R T → G) f =>
    FreeGroup.lift z (regularRegionCycleWord R T (p f))
  let σ := E.trans ((regularCycleControlledBoundary R T o W).trans E.symm)
  let τ := regularRegionGaugePhysicalLabels (Γ := Γ) R (fun v => (ℓ v)⁻¹)
  have hE (α : RegionHalfEdgeConfig (Γ := Γ) G R) :
      E (τ α) = regularRegionCoordinateTranslation R T o ℓ (E α) := by
    apply E.symm.injective
    rw [E.symm_apply_apply, regularRegionCoordinatesEquiv_symm_coordinateTranslation,
      E.symm_apply_apply]
  have hperm : Commute σ τ := by
    apply Equiv.ext
    intro α
    change E.symm (regularCycleControlledBoundary R T o W (E (τ α))) =
      τ (E.symm (regularCycleControlledBoundary R T o W (E α)))
    rw [hE, regularCycleControlledBoundary_coordinateTranslation,
      regularRegionCoordinatesEquiv_symm_coordinateTranslation]
  exact hperm.map (Matrix.permMatrixHom (R := ℂ))

/-- The native translation matrix has the delta kernel of independent vertex
left translations on the actual half-edge labels. -/
theorem regularRegionVertexTranslationMatrix_apply (R : Finset V)
    (ℓ : {v : V // v ∈ R} → G) (α β : RegionHalfEdgeConfig (Γ := Γ) G R) :
    regularRegionVertexTranslationMatrix R ℓ α β =
      if α = (fun v e => ℓ v * β v e) then 1 else 0 := by
  rw [regularRegionVertexTranslationMatrix, permMatrixHom_apply_eq_ite]
  have h : regularRegionGaugePhysicalLabels R (fun v => (ℓ v)⁻¹) β =
      (fun v e => ℓ v * β v e) := by
    funext v e
    simp only [regularRegionGaugePhysicalLabels_apply, inv_inv]
  rw [h]

/-- Averaging the actual independent vertex translations is precisely the
existing product of the local regular projectors. Source: SCP10,
accessible invariant physical systems, lines 1765–1820. -/
theorem regionPhysicalProductMatrix_regularLegProjector_eq_sum_vertexTranslation
    (R : Finset V) :
    regionPhysicalProductMatrix R (fun v => regularLegProjector (G := G) (IncidentEdge Γ v)) =
      ((Fintype.card G : ℂ)⁻¹ ^ R.card) •
        ∑ ℓ : {v : V // v ∈ R} → G, regularRegionVertexTranslationMatrix (Γ := Γ) R ℓ := by
  classical
  ext α β
  simp only [regionPhysicalProductMatrix, regularLegProjector_apply, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_coe, Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum_boole]
  congr 1
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [regularRegionVertexTranslationMatrix_apply]
  simp only [funext_iff, Pi.smul_apply, smul_eq_mul]

/-- Commutation with every independent vertex translation implies commutation
with the actual product of local regular averaging projectors.
Source: SCP10, accessible invariant physical systems, lines 1765–1820. -/
theorem commute_regionLocalProjector_of_vertexTranslation (R : Finset V)
    (U : Matrix (RegionHalfEdgeConfig (Γ := Γ) G R)
      (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ)
    (hcomm : ∀ ℓ : {v : V // v ∈ R} → G,
      Commute U (regularRegionVertexTranslationMatrix (Γ := Γ) R ℓ)) :
    Commute U (regionPhysicalProductMatrix R
      (fun v => regularLegProjector (G := G) (IncidentEdge Γ v))) := by
  rw [regionPhysicalProductMatrix_regularLegProjector_eq_sum_vertexTranslation]
  apply Commute.smul_right
  exact Commute.sum_right Finset.univ _ _ (fun ℓ _ => hcomm ℓ)

/-- The actual free-word controlled matrix commutes with the genuine product
of local invariant projectors. Source: SCP10, lines 1765–1820 and 1935–1990.
No group-valued equivariance or physical surjectivity hypothesis is required. -/
theorem regularCycleControlledBoundaryMatrix_commute_localProjector (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (v w : {e : Edge Γ // IsRegionBoundaryEdge R e} → {v : V // v ∈ R})
    (p : (f : {e : Edge Γ // IsRegionBoundaryEdge R e}) →
      (Γ.induce (R : Set V)).Walk (v f) (w f)) :
    Commute (regularCycleControlledBoundaryMatrix R T hT htree o
        (fun z f => FreeGroup.lift z (regularRegionCycleWord R T (p f))))
      (regionPhysicalProductMatrix R
        (fun v => regularLegProjector (G := G) (IncidentEdge Γ v))) := by
  exact commute_regionLocalProjector_of_vertexTranslation R _ (fun ℓ =>
    regularCycleControlledBoundaryMatrix_commute_vertexTranslation R T hT htree o v w p ℓ)

/-- The actual free-word controlled operation preserves the range of the
product local averaging projector, the genuine locally invariant physical
support. Source: SCP10, lines 1765–1820 and 1935–1990. -/
theorem regularCycleControlledBoundaryMatrix_maps_localProjector_range (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (v w : {e : Edge Γ // IsRegionBoundaryEdge R e} → {v : V // v ∈ R})
    (p : (f : {e : Edge Γ // IsRegionBoundaryEdge R e}) →
      (Γ.induce (R : Set V)).Walk (v f) (w f))
    (ψ : RegionHalfEdgeConfig (Γ := Γ) G R → ℂ)
    (hψ : ψ ∈ LinearMap.range (Matrix.mulVecLin (regionPhysicalProductMatrix R
      (fun v => regularLegProjector (G := G) (IncidentEdge Γ v))))) :
    (regularCycleControlledBoundaryMatrix R T hT htree o
      (fun z f => FreeGroup.lift z (regularRegionCycleWord R T (p f)))) *ᵥ ψ ∈
      LinearMap.range (Matrix.mulVecLin (regionPhysicalProductMatrix R
        (fun v => regularLegProjector (G := G) (IncidentEdge Γ v)))) := by
  obtain ⟨φ, rfl⟩ := hψ
  refine ⟨(regularCycleControlledBoundaryMatrix R T hT htree o
    (fun z f => FreeGroup.lift z (regularRegionCycleWord R T (p f)))) *ᵥ φ, ?_⟩
  change _ *ᵥ (_ *ᵥ φ) = _ *ᵥ (_ *ᵥ φ)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    (regularCycleControlledBoundaryMatrix_commute_localProjector R T hT htree o v w p).eq]

variable {κ : V → Type*} [∀ v, Fintype (κ v)] [∀ v, DecidableEq (κ v)]

/-- A fixed actual walk-word controlled operation has a unitary implementation
on the original local G-isometric physical region. The canonical projector need
not be surjective. The operation and its implementation are chosen without any
closure labels. Source: SCP10, Lemma 6.3 and accessible complement disentangling,
lines 1729–1820 and 1935–1990. -/
theorem exists_unitary_regionPhysicalProductMatrix_mul_cycleWords
    (a : (v : V) → (IncidentEdge Γ v → G) → κ v → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (v w : {e : Edge Γ // IsRegionBoundaryEdge R e} → {v : V // v ∈ R})
    (p : (f : {e : Edge Γ // IsRegionBoundaryEdge R e}) →
      (Γ.induce (R : Set V)).Walk (v f) (w f)) :
    ∃ W : Matrix ((v : {v // v ∈ R}) → κ v.1) ((v : {v // v ∈ R}) → κ v.1) ℂ,
      W ∈ Matrix.unitaryGroup ((v : {v // v ∈ R}) → κ v.1) ℂ ∧
      W * regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s) =
        regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s) *
          regularCycleControlledBoundaryMatrix R T hT htree o
            (fun z f => FreeGroup.lift z (regularRegionCycleWord R T (p f))) :=
  exists_unitary_regionPhysicalProductMatrix_mul_of_projector_commute a ha R _
    (regularCycleControlledBoundaryMatrix_mem_unitaryGroup R T hT htree o _)
    (regularCycleControlledBoundaryMatrix_commute_localProjector R T hT htree o v w p).eq

end TNLean.PEPS
