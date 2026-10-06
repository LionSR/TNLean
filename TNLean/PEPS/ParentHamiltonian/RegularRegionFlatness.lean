/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionParentHamiltonian
import TNLean.PEPS.RegularTwistedRegionProjectorCoordinates
import TNLean.PEPS.RegularRegionCycleHolonomy

/-!
# Local parent constraints exclude nontrivial regular holonomy

The local inverse of a regular G-injective tensor exposes its original
half-edge coordinates. The untwisted regional ground space has only identity
cycle coordinates. Inserting bond operators replaces this condition by
simultaneous conjugates of their spanning-tree residuals. These supports are
disjoint when a residual is nontrivial. Consequently the original and inserted
regional ground spaces have zero intersection, and a nonzero vector satisfying
both regional conditions forces every internal closed-walk holonomy to be the
identity. No G-isometry is required.

This is a necessary local flatness step in the converse torus ground-space
argument, not a representation of every parent-kernel vector by inserted bonds.
Source: SCP10, arXiv:1001.3807, proof of Theorem 5.5, lines 1440–1514,
and accessible regular coordinates, lines 1765–1920.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

variable {d : ℕ}

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
private theorem twistedSite_one
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) :
    regularTwistedSite a (fun _ => 1) = a := by
  funext v η s
  change a v (regularTwistedLabels (fun _ => 1) v η) s = a v η s
  congr 1
  funext f
  simp only [regularTwistedLabels, one_mul, ite_self]

set_option maxHeartbeats 800000 in
-- The dependent boundary equivalences require additional reduction steps.
omit [DecidableEq G] in
/-- A gauge removing every internal inserted bond preserves the original
regional ground space; crossing insertions are absorbed by a bijective
boundary-label transport. Source: SCP10, string deformation and accessible
regular coordinates, lines 1622–1647 and 1765–1920. -/
theorem regionGroundSpace_regularTwisted_eq_of_internalGaugeFlat
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ g v η s, a v (fun e => g * η e) s = a v η s)
    (R : Finset V) (k : {v : V // v ∈ R} → G) (u : Edge Γ → G)
    (hflat : ∀ e, regularRegionGaugeResidual R k u e = 1) :
    regionGroundSpace (groupBondTensor (regularTwistedSite a u)) R =
      regionGroundSpace (groupBondTensor a) R := by
  classical
  let E : ({f : Edge Γ // IsRegionBoundaryEdge R f} → G) ≃
      RegionBoundaryConfig (groupBondTensor a) R :=
    Equiv.piCongrRight (fun _ => Fintype.equivFin G)
  let B : RegionBoundaryConfig (groupBondTensor a) R ≃
      RegionBoundaryConfig (groupBondTensor a) R :=
    E.symm.trans ((regularRegionBoundaryTransport R k u).trans E)
  have hf : openRegionWeight (groupBondTensor (regularTwistedSite a u)) R =
      openRegionWeight (groupBondTensor a) R ∘ B := by
    funext μ σ
    let θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G :=
      fun f => (Fintype.equivFin G).symm (μ f)
    have hμ : (fun f => Fintype.equivFin G (θ f)) = μ := by
      funext f
      exact Equiv.apply_symm_apply (Fintype.equivFin G) (μ f)
    have hB : B μ = (fun f => Fintype.equivFin G
        (regularRegionBoundaryTransport R k u θ f)) := by
      funext f
      rfl
    simpa only [hμ, ← hB, Function.comp_apply] using
      openRegionWeight_eq_untwisted_of_regularRegionGaugeResidual_eq_one
        a ha R k u hflat θ σ
  rw [regionGroundSpace_eq_span, regionGroundSpace_eq_span, hf]
  congr 1
  ext φ
  constructor
  · rintro ⟨μ, hμ⟩
    exact ⟨B μ, hμ⟩
  · rintro ⟨μ, hμ⟩
    refine ⟨B.symm μ, ?_⟩
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hμ

/-- A local G-injective inverse maps every inserted regional ground vector
into the actual canonical projector range. Source: SCP10, accessible inverse
coordinates, lines 1765–1820. -/
theorem regionPhysicalMap_mem_regularProjectorTwistedRange
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γ v) α η)
    (R : Finset V) (u : Edge Γ → G)
    {ψ : RegionPhysicalConfig (d := d) R → ℂ}
    (hψ : ψ ∈ regionGroundSpace (groupBondTensor (regularTwistedSite a u)) R) :
    regionPhysicalMap R F ψ ∈
      (Matrix.mulVecLin (regularProjectorTwistedRegionMatrix R u)).range := by
  classical
  have hle : regionGroundSpace (groupBondTensor (regularTwistedSite a u)) R ≤
      ((Matrix.mulVecLin (regularProjectorTwistedRegionMatrix R u)).range).comap
        (regionPhysicalMap R F) := by
    apply (regionGroundSpace_le_iff
      (groupBondTensor (regularTwistedSite a u)) R _).mpr
    intro μ
    let θ := fun f => (Fintype.equivFin G).symm (μ f)
    refine ⟨Pi.single θ 1, ?_⟩
    change regularProjectorTwistedRegionMatrix R u *ᵥ Pi.single θ 1 = _
    rw [Matrix.mulVec_single_one]
    funext α
    symm
    simpa only [θ, Equiv.apply_symm_apply, Matrix.col_apply] using
      regionPhysicalMap_eq_regularProjectorTwistedRegionMatrix a F hF R u α θ
  exact hle hψ

/-- Restoring the original local coefficients reverses the exposed half-edge
map on every regional ground vector, for every insertion. Source: SCP10,
accessible inverse coordinates, lines 1765–1820. -/
theorem regionPhysicalMap_leftInverse_on_regularGroundSpace
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γ v) α η)
    (R : Finset V) (u : Edge Γ → G)
    {ψ : RegionPhysicalConfig (d := d) R → ℂ}
    (hψ : ψ ∈ regionGroundSpace (groupBondTensor (regularTwistedSite a u)) R) :
    regionPhysicalMap R (fun v => Matrix.of (fun s α => a v α s))
      (regionPhysicalMap R F ψ) = ψ := by
  classical
  let L := regionPhysicalMap R (fun v => Matrix.of (fun s α => a v α s)) ∘ₗ
    regionPhysicalMap R F - LinearMap.id
  have hle : regionGroundSpace (groupBondTensor (regularTwistedSite a u)) R ≤ L.ker := by
    apply (regionGroundSpace_le_iff
      (groupBondTensor (regularTwistedSite a u)) R _).mpr
    intro μ
    let θ := fun f => (Fintype.equivFin G).symm (μ f)
    have hforward : regionPhysicalMap R F
        (openRegionWeight (groupBondTensor (regularTwistedSite a u)) R μ) =
          fun α => regularProjectorTwistedRegionMatrix R u α θ := by
      funext α
      simpa only [θ, Equiv.apply_symm_apply] using
        regionPhysicalMap_eq_regularProjectorTwistedRegionMatrix a F hF R u α θ
    apply LinearMap.mem_ker.mpr
    change regionPhysicalMap R (fun v => Matrix.of (fun s α => a v α s))
      (regionPhysicalMap R F (openRegionWeight
        (groupBondTensor (regularTwistedSite a u)) R μ)) -
      openRegionWeight (groupBondTensor (regularTwistedSite a u)) R μ = 0
    rw [hforward, regionPhysicalMap_regularProjectorTwistedRegionMatrix a ha R u θ]
    simp only [θ, Equiv.apply_symm_apply, sub_self]
  exact sub_eq_zero.mp (hle hψ)

/-- Every original canonical regional ground vector vanishes at nonidentity
cycle coordinates. Source: SCP10, regular accessible coordinates,
lines 1765–1920; auxiliary local flatness in Theorem 5.5. -/
theorem regularProjectorOpenRegionRange_apply_eq_zero_of_cycle_ne_one
    (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    {φ : RegionHalfEdgeConfig (Γ := Γ) G R → ℂ}
    (hφ : φ ∈ (Matrix.mulVecLin (regularProjectorOpenRegionMatrix (G := G) R)).range)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) (hc : c.2.2.2 ≠ 1) :
    φ ((regularRegionCoordinatesEquiv R T hT htree o).symm c) = 0 := by
  obtain ⟨x, hx⟩ := hφ
  have hzero : regularProjectorOpenRegionMatrix (G := G) R
      ((regularRegionCoordinatesEquiv R T hT htree o).symm c) = 0 := by
    funext θ
    rw [regularProjectorOpenRegionMatrix_coordinates]
    simp only [hc, ↓reduceIte, mul_zero, Pi.zero_apply]
  have h := congrFun hx ((regularRegionCoordinatesEquiv R T hT htree o).symm c)
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hzero,
    Pi.zero_apply, zero_mul, Finset.sum_const_zero] using h.symm

/-- Exposing any original regional ground vector by a local G-injective
inverse gives a vector with identity cycle coordinates. This is a pointwise
constraint on arbitrary regional parent-kernel vectors, rather than an
assumption about inserted-bond representations. Source: SCP10, inverse
closure argument in Theorem 5.5, lines 1440–1514, and lines 1765–1920. -/
theorem regionPhysicalMap_apply_eq_zero_of_mem_regularGroundSpace_of_cycle_ne_one
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γ v) α η)
    (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    {ψ : RegionPhysicalConfig (d := d) R → ℂ}
    (hψ : ψ ∈ regionGroundSpace (groupBondTensor a) R)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) (hc : c.2.2.2 ≠ 1) :
    regionPhysicalMap R F ψ ((regularRegionCoordinatesEquiv R T hT htree o).symm c) = 0 := by
  classical
  have hψone : ψ ∈ regionGroundSpace
      (groupBondTensor (regularTwistedSite a (fun _ => 1))) R := by
    simpa only [twistedSite_one] using hψ
  have hφ := regionPhysicalMap_mem_regularProjectorTwistedRange a F hF R
    (fun _ => 1) hψone
  rw [regularProjectorTwistedRegionMatrix_one] at hφ
  exact regularProjectorOpenRegionRange_apply_eq_zero_of_cycle_ne_one R T hT htree o hφ c hc

/-- Every complementary slice of an arbitrary vector satisfying the
original regional parent condition has exposed identity cycle coordinates.
Source: SCP10, converse local closure argument in Theorem 5.5,
lines 1440–1514; no inserted-bond description of the vector is assumed. -/
theorem regionPhysicalMap_slice_apply_eq_zero_of_parent_annihilates
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γ v) α η)
    (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (Q : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ)
    (hQ : IsRegionParentInteraction (groupBondTensor a) R Q)
    (Ψ : (V → Fin d) → ℂ) (hground : regionLocalTerm R Q *ᵥ Ψ = 0)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R))
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) (hc : c.2.2.2 ≠ 1) :
    regionPhysicalMap R F (regionSliceMap R τ Ψ)
      ((regularRegionCoordinatesEquiv R T hT htree o).symm c) = 0 := by
  exact regionPhysicalMap_apply_eq_zero_of_mem_regularGroundSpace_of_cycle_ne_one
    a F hF R T hT htree o
    ((regionLocalTerm_mulVec_eq_zero_iff (groupBondTensor a) R hQ Ψ).mp hground τ) c hc

/-- A nontrivial residual of the inserted internal bonds separates the two
canonical regional coefficient ranges. Auxiliary to SCP10, Theorem 5.5,
lines 1440–1514, in the actual regular half-edge coordinates. -/
theorem disjoint_regularProjectorRegion_ranges_of_cycleResidual_ne_one
    (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (u : Edge Γ → G)
    (hu : regularRegionTreeCycleResidual R T hT htree o u ≠ 1) :
    Disjoint (Matrix.mulVecLin (regularProjectorOpenRegionMatrix (G := G) R)).range
      (Matrix.mulVecLin (regularProjectorTwistedRegionMatrix R u)).range := by
  apply Submodule.disjoint_def.mpr
  intro φ hφ hφu
  obtain ⟨x, hx⟩ := hφ
  obtain ⟨y, hy⟩ := hφu
  funext α
  let E := regularRegionCoordinatesEquiv (G := G) R T hT htree o
  let c := E α
  have hα : E.symm c = α := E.symm_apply_apply α
  by_cases hc : c.2.2.2 = 1
  · have hzero : regularProjectorTwistedRegionMatrix R u α = 0 := by
      funext θ
      rw [← hα, regularProjectorTwistedRegionMatrix_coordinates]
      have hnot (z : G) :
          c.2.2.2 ≠ (fun e => z * regularRegionTreeCycleResidual R T hT htree o u e * z⁻¹) := by
        intro h
        apply hu
        funext e
        have he := congrFun (hc.symm.trans h) e
        change 1 = z * regularRegionTreeCycleResidual R T hT htree o u e * z⁻¹ at he
        have := congrArg (fun k => z⁻¹ * k * z) he
        simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right,
          mul_one, inv_mul_cancel, Pi.one_apply] using this.symm
      simp only [hnot, and_false, ↓reduceIte, Finset.sum_const_zero, mul_zero, Pi.zero_apply]
    have h := congrFun hy α
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hzero,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero] using h.symm
  · have hzero : regularProjectorOpenRegionMatrix (G := G) R α = 0 := by
      funext θ
      rw [← hα, regularProjectorOpenRegionMatrix_coordinates]
      simp only [hc, ↓reduceIte, mul_zero, Pi.zero_apply]
    have h := congrFun hx α
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hzero,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero] using h.symm

omit [DecidableEq G] in
/-- A nontrivial internal residual excludes every common regional ground
vector of the original and inserted regular G-injective tensors. Source:
SCP10, converse local closure argument in Theorem 5.5, lines 1440–1514.
The statement is an auxiliary regular-group consequence, without G-isometry. -/
theorem disjoint_regionGroundSpace_regularTwisted_of_cycleResidual_ne_one
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (u : Edge Γ → G)
    (hu : regularRegionTreeCycleResidual R T hT htree o u ≠ 1) :
    Disjoint (regionGroundSpace (groupBondTensor a) R)
      (regionGroundSpace (groupBondTensor (regularTwistedSite a u)) R) := by
  classical
  choose F hF using fun v => (ha v).exists_regularProjectorCoefficients
  apply Submodule.disjoint_def.mpr
  intro ψ hψ hψu
  have hψone : ψ ∈ regionGroundSpace
      (groupBondTensor (regularTwistedSite a (fun _ => 1))) R := by
    simpa only [twistedSite_one] using hψ
  have hφ := regionPhysicalMap_mem_regularProjectorTwistedRange a F hF R
    (fun _ => 1) hψone
  rw [regularProjectorTwistedRegionMatrix_one] at hφ
  have hφu := regionPhysicalMap_mem_regularProjectorTwistedRange a F hF R u hψu
  have hzero := Submodule.disjoint_def.mp
    (disjoint_regularProjectorRegion_ranges_of_cycleResidual_ne_one R T hT htree o u hu)
    _ hφ hφu
  have hrecover := regionPhysicalMap_leftInverse_on_regularGroundSpace a ha F hF R u hψu
  rw [hzero, map_zero] at hrecover
  exact hrecover.symm

omit [DecidableEq G] in
/-- A common nonzero regional vector forces all internal closed-walk
holonomies of inserted regular bonds to be trivial. Source: SCP10,
Theorem 5.5, lines 1440–1514, auxiliary regular local flatness implication. -/
theorem regularWalkHolonomy_eq_one_of_mem_regionGroundSpace_of_mem_twisted
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (R : Finset V) (hR : (Γ.induce (R : Set V)).Connected)
    (u : Edge Γ → G) (o : {v : V // v ∈ R})
    (p : (Γ.induce (R : Set V)).Walk o o)
    {ψ : RegionPhysicalConfig (d := d) R → ℂ} (hne : ψ ≠ 0)
    (hψ : ψ ∈ regionGroundSpace (groupBondTensor a) R)
    (hψu : ψ ∈ regionGroundSpace (groupBondTensor (regularTwistedSite a u)) R) :
    regularWalkHolonomy (regularRegionInternalOperators R u) p = 1 := by
  classical
  obtain ⟨T, hT, htree⟩ := hR.exists_isTree_le
  have hres : regularRegionTreeCycleResidual R T hT htree o u = 1 := by
    by_contra hn
    exact hne (Submodule.disjoint_def.mp
      (disjoint_regionGroundSpace_regularTwisted_of_cycleResidual_ne_one
        a ha R T hT htree o u hn) _ hψ hψu)
  rw [← regularRegionCycleWord_eval_rootLoop R T hT htree o u p, hres]
  have hlift : FreeGroup.lift (1 : RegionCycleEdge (Γ := Γ) R T → G) = 1 := by
    apply FreeGroup.ext_hom
    intro e
    simp
  rw [hlift]
  rfl

omit [DecidableEq G] in
/-- A nonzero inserted PEPS killed by an original regional parent term has
trivial holonomy on every internal closed walk of that region. Source:
SCP10, converse local closure argument in Theorem 5.5, lines 1440–1514. -/
theorem regularWalkHolonomy_eq_one_of_regionParent_annihilates_twistedState
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (R : Finset V) (hR : (Γ.induce (R : Set V)).Connected)
    (u : Edge Γ → G) (o : {v : V // v ∈ R})
    (p : (Γ.induce (R : Set V)).Walk o o)
    (Q : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ)
    (hQ : IsRegionParentInteraction (groupBondTensor a) R Q)
    (hne : stateCoeff (groupBondTensor (regularTwistedSite a u)) ≠ 0)
    (hground : regionLocalTerm R Q *ᵥ
      stateCoeff (groupBondTensor (regularTwistedSite a u)) = 0) :
    regularWalkHolonomy (regularRegionInternalOperators R u) p = 1 := by
  classical
  obtain ⟨σ, hσ⟩ := Function.ne_iff.mp hne
  let τ : RegionPhysicalConfig (d := d) (Finset.univ \ R) := fun w => σ w.1
  let φ := fun ν => stateCoeff (groupBondTensor (regularTwistedSite a u))
    (assembleRegionσ R ν τ)
  have hrec : assembleRegionσ R (fun w => σ w.1) τ = σ := by
    funext v
    simp [assembleRegionσ, τ]
  have hφne : φ ≠ 0 := by
    intro hz
    apply hσ
    have he := congrFun hz (fun w => σ w.1)
    simpa only [φ, hrec, Pi.zero_apply] using he
  have hφ := (regionLocalTerm_mulVec_eq_zero_iff (groupBondTensor a) R hQ _).mp hground τ
  exact regularWalkHolonomy_eq_one_of_mem_regionGroundSpace_of_mem_twisted
    a ha R hR u o p hφne hφ
    (stateCoeff_slice_mem_regionGroundSpace (groupBondTensor (regularTwistedSite a u)) R τ)

end TNLean.PEPS
