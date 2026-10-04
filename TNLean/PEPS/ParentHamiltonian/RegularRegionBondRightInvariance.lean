/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularRegionFlatness

/-!
# Right multiplication on shared internal regular bonds

Multiplying both exposed half-edge labels of each internal bond on the right
by the same group element preserves the actual canonical regional coefficients.
The proof changes each summed shared bond label by that right multiplication.
Boundary labels remain fixed. Arbitrary inserted left group multiplications may be
present; associativity allows the same change of summation variables.

Consequently, exposing the original regular projector through local inverse
coefficients makes every parent-supported physical slice invariant under these
internal bond actions. Only the stated inverse coefficient identity and the
actual original regional parent condition are used. No flat-connection
reconstruction, global closure-span representation, or G-isometry is assumed.

Source: SCP10, arXiv:1001.3807, accessible regular coordinates and internal bond
synchronization, lines 1765–1920. This is an auxiliary local contraction identity.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
/-- Simultaneous right multiplication on both half-edge labels of each bond.
Source: SCP10, shared regular reference labels, lines 1765–1920. -/
def regularRegionHalfEdgeRightMul (R : Finset V) (r : Edge Γ → G)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R) : RegionHalfEdgeConfig (Γ := Γ) G R :=
  fun w e => α w e * r e.1

private theorem projector_rightMul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α η r : ι → G) :
    regularLegProjector ι (fun i => α i * r i) (fun i => η i * r i) =
      regularLegProjector ι α η := by
  classical
  rw [regularLegProjector_apply, regularLegProjector_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  have h : (fun i => α i * r i) = g • (fun i => η i * r i) ↔ α = g • η := by
    simp only [funext_iff, Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_right_cancel_iff]
  simp only [h]

/-- Actual canonical inserted-region columns are invariant under simultaneous
right multiplication on internal bonds. The multiplier is identity on every
crossing bond, so the original boundary condition is preserved. Source:
SCP10, accessible regular coordinates, lines 1765–1920. -/
theorem regularProjectorTwistedRegionMatrix_halfEdgeRightMul
    (R : Finset V) (u r : Edge Γ → G)
    (hr : ∀ e, IsRegionBoundaryEdge R e → r e = 1)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G) :
    regularProjectorTwistedRegionMatrix R u (regularRegionHalfEdgeRightMul R r α) θ =
      regularProjectorTwistedRegionMatrix R u α θ := by
  classical
  let E : ({f : Edge Γ // IsRegionIncidentEdge R f} → G) ≃
      ({f : Edge Γ // IsRegionIncidentEdge R f} → G) :=
    Equiv.piCongrRight fun e => Equiv.mulRight (r e.1)
  unfold regularProjectorTwistedRegionMatrix
  rw [← Equiv.sum_comp E]
  apply Finset.sum_congr rfl
  intro η _
  have hb : (fun e : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
      E η ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩) =
      (fun e : {f : Edge Γ // IsRegionBoundaryEdge R f} =>
        η ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩) := by
    funext e
    simp only [E, Equiv.piCongrRight_apply, Pi.map_apply, Equiv.coe_mulRight,
      hr e.1 e.2, mul_one]
  rw [hb]
  split_ifs
  · apply Finset.prod_congr rfl
    intro w _
    have ht : regularTwistedLabels u w.1
        (fun e => E η ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩) =
        (fun e => regularTwistedLabels u w.1
          (fun f => η ⟨f.1, isRegionIncidentEdge_of_regionVertex R w f⟩) e * r e.1) := by
      funext e
      simp only [regularTwistedLabels, E, Equiv.piCongrRight_apply, Pi.map_apply,
        Equiv.coe_mulRight]
      split_ifs <;> simp only [mul_assoc]
    rw [ht]
    exact projector_rightMul (α w) _ (fun e => r e.1)
  · rfl

/-- The original actual canonical regional columns have the same internal
right invariance. Source: SCP10, lines 1765–1920. -/
theorem regularProjectorOpenRegionMatrix_halfEdgeRightMul
    (R : Finset V) (r : Edge Γ → G)
    (hr : ∀ e, IsRegionBoundaryEdge R e → r e = 1)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G) :
    regularProjectorOpenRegionMatrix R (regularRegionHalfEdgeRightMul R r α) θ =
      regularProjectorOpenRegionMatrix R α θ := by
  rw [← regularProjectorTwistedRegionMatrix_one R]
  exact regularProjectorTwistedRegionMatrix_halfEdgeRightMul R (fun _ => 1) r hr α θ


/-- Multiplying exactly the two half-edge labels of one internal edge on the
right preserves every original canonical regional column. Source: SCP10,
shared internal regular reference label, lines 1765–1920. -/
theorem regularProjectorOpenRegionMatrix_internalEdgeRightMul
    (R : Finset V) (e : Edge Γ) (he : e.1.1 ∈ R ∧ e.1.2 ∈ R) (g : G)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G) :
    regularProjectorOpenRegionMatrix R
      (regularRegionHalfEdgeRightMul R (fun f => if f = e then g else 1) α) θ =
      regularProjectorOpenRegionMatrix R α θ := by
  apply regularProjectorOpenRegionMatrix_halfEdgeRightMul
  intro f hf
  have hne : f ≠ e := by
    intro h
    subst f
    rcases hf with hf | hf
    · exact hf.2 he.2
    · exact hf.1 he.1
  simp only [hne, ↓reduceIte]

variable {d : ℕ}

/-- Every original regional ground vector, exposed by coefficients recovering
the local regular projector, is invariant under shared internal right
multiplication. Source: SCP10, accessible coordinates, lines 1765–1920. -/
theorem regionPhysicalMap_halfEdgeRightMul_of_mem_regularGroundSpace
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γ v) α η)
    (R : Finset V) (r : Edge Γ → G)
    (hr : ∀ e, IsRegionBoundaryEdge R e → r e = 1)
    {ψ : RegionPhysicalConfig (d := d) R → ℂ}
    (hψ : ψ ∈ regionGroundSpace (groupBondTensor a) R)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R) :
    regionPhysicalMap R F ψ (regularRegionHalfEdgeRightMul R r α) =
      regionPhysicalMap R F ψ α := by
  classical
  let L : (RegionPhysicalConfig (d := d) R → ℂ) →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ => ℂ)
      (regularRegionHalfEdgeRightMul R r α) -
      LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) α) ∘ₗ
    regionPhysicalMap R F
  have hle : regionGroundSpace (groupBondTensor a) R ≤ L.ker := by
    apply (regionGroundSpace_le_iff (groupBondTensor a) R _).mpr
    intro μ
    let θ := fun e => (Fintype.equivFin G).symm (μ e)
    have hf (β : RegionHalfEdgeConfig (Γ := Γ) G R) :
        regionPhysicalMap R F (openRegionWeight (groupBondTensor a) R μ) β =
          regularProjectorOpenRegionMatrix R β θ := by
      simpa only [θ, Equiv.apply_symm_apply] using
        regionPhysicalMap_eq_regularProjectorOpenRegionMatrix a F hF R β θ
    apply LinearMap.mem_ker.mpr
    change regionPhysicalMap R F (openRegionWeight (groupBondTensor a) R μ)
      (regularRegionHalfEdgeRightMul R r α) -
        regionPhysicalMap R F (openRegionWeight (groupBondTensor a) R μ) α = 0
    rw [hf, hf, regularProjectorOpenRegionMatrix_halfEdgeRightMul R r hr α θ, sub_self]
  exact sub_eq_zero.mp (hle hψ)

/-- Every complementary physical slice satisfying the original regional
parent constraint has exposed shared-bond right invariance. Source:
SCP10, local ground-space constraints and accessible coordinates,
lines 1440–1514 and 1765–1920. No global representation is assumed. -/
theorem regionPhysicalMap_slice_halfEdgeRightMul_of_parent_annihilates
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γ v) α η)
    (R : Finset V) (r : Edge Γ → G)
    (hr : ∀ e, IsRegionBoundaryEdge R e → r e = 1)
    (P : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ)
    (hP : IsRegionParentInteraction (groupBondTensor a) R P)
    (Ψ : (V → Fin d) → ℂ) (hΨ : regionLocalTerm R P *ᵥ Ψ = 0)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R))
    (α : RegionHalfEdgeConfig (Γ := Γ) G R) :
    regionPhysicalMap R F (fun σ => Ψ (assembleRegionσ R σ τ))
        (regularRegionHalfEdgeRightMul R r α) =
      regionPhysicalMap R F (fun σ => Ψ (assembleRegionσ R σ τ)) α := by
  exact regionPhysicalMap_halfEdgeRightMul_of_mem_regularGroundSpace a F hF R r hr
    ((regionLocalTerm_mulVec_eq_zero_iff (groupBondTensor a) R hP Ψ).mp hΨ τ) α

end TNLean.PEPS
