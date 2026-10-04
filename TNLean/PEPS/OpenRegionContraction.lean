/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegionBlock.BlockRangeCoincidence
import TNLean.PEPS.SquareLatticeGraph
import Mathlib.Logic.Equiv.Prod

/-!
# Open-boundary contraction of a finite PEPS region

The tensor of a finite region is obtained by summing its internal bond labels and
leaving its crossing bonds open. Labels on edges wholly outside the region are
absent from this contraction. This distinguishes the physical region tensor from
the globally indexed region weight, which counts every exterior assignment.

The construction applies to any finite graph, and hence to rectangular regions
of a square lattice. It provides the actual finite-region map needed before the
virtual boundary state in Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
Theorem 6.9 can be identified with a physical cut. The source's blocking and cut
are described in `Papers/1001.3807/paper_v3.tex`, lines 1935–1980 and 2043–2076.
No assertion about the entropy of a particular PEPS is made here.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- Virtual labels only on edges touching the region. -/
abbrev RegionIncidentConfig (A : Tensor Γ d) (R : Finset V) :=
  (e : {e : Edge Γ // IsRegionIncidentEdge R e}) → Fin (A.bondDim e.1)

/-- Boundary labels read from an incident-edge configuration. -/
def regionIncidentBoundaryLabel (A : Tensor Γ d) (R : Finset V)
    (η : RegionIncidentConfig A R) : RegionBoundaryConfig A R :=
  fun e => η ⟨e.1, isRegionBoundaryEdge_touches R e.2⟩

omit [Fintype V] [DecidableRel Γ.Adj] in
/-- An edge attached to a vertex of the region touches that region. -/
theorem isRegionIncidentEdge_of_regionVertex (R : Finset V) (w : {w : V // w ∈ R})
    (e : IncidentEdge Γ w.1) : IsRegionIncidentEdge R e.1 := by
  rcases e.2 with h | h
  · exact Or.inl (by rw [h]; exact w.2)
  · exact Or.inr (by rw [h]; exact w.2)

/-- The product of the tensors at the region vertices for a fixed incident-edge assignment. -/
noncomputable def regionIncidentWeight (A : Tensor Γ d) (R : Finset V)
    (η : RegionIncidentConfig A R) (σ : RegionPhysicalConfig (d := d) R) : ℂ :=
  ∏ w : {w : V // w ∈ R},
    A.component w.1 (fun e => η ⟨e.1, isRegionIncidentEdge_of_regionVertex R w e⟩) (σ w)

/-- Source: arXiv:1001.3807, blocking of the region `D`, lines 1935–1957.
The open-region tensor coefficient: fix every crossing bond and sum the remaining
incident labels, which are exactly the bonds internal to the region. -/
noncomputable def openRegionWeight (A : Tensor Γ d) (R : Finset V)
    (μ : RegionBoundaryConfig A R) (σ : RegionPhysicalConfig (d := d) R) : ℂ :=
  ∑ η : RegionIncidentConfig A R,
    if regionIncidentBoundaryLabel A R η = μ then regionIncidentWeight A R η σ else 0

/-- Source: arXiv:1001.3807, region maps in `eq:iso:L-shape-scenario`, lines 1935–1957.
The physical map of a region with its crossing bonds left open. -/
noncomputable def openRegionMap (A : Tensor Γ d) (R : Finset V) :
    (RegionBoundaryConfig A R → ℂ) →ₗ[ℂ] (RegionPhysicalConfig (d := d) R → ℂ) :=
  Fintype.linearCombination ℂ (openRegionWeight A R)

/-- Coefficients of the genuine physical open-region map. -/
theorem openRegionMap_apply (A : Tensor Γ d) (R : Finset V)
    (x : RegionBoundaryConfig A R → ℂ) (σ : RegionPhysicalConfig (d := d) R) :
    openRegionMap A R x σ = ∑ μ, x μ * openRegionWeight A R μ σ := by
  simp [openRegionMap, Fintype.linearCombination_apply, Finset.sum_apply, smul_eq_mul]

open scoped Classical in
/-- A virtual boundary basis vector is sent to its open-region physical tensor. -/
theorem openRegionMap_single (A : Tensor Γ d) (R : Finset V)
    (μ : RegionBoundaryConfig A R) :
    openRegionMap A R (Pi.single μ 1) = openRegionWeight A R μ := by
  funext σ
  simp [openRegionMap_apply, Pi.single_apply]

/-- The coefficient matrix of the actual open-region physical map. -/
noncomputable def openRegionCoefficientMatrix (A : Tensor Γ d) (R : Finset V) :
    Matrix (RegionPhysicalConfig (d := d) R) (RegionBoundaryConfig A R) ℂ :=
  fun σ μ => openRegionWeight A R μ σ

/-- The open-region matrix acts by the genuine finite-region contraction. -/
theorem openRegionMap_apply_eq_mulVec (A : Tensor Γ d) (R : Finset V)
    (x : RegionBoundaryConfig A R → ℂ) :
    openRegionMap A R x = openRegionCoefficientMatrix A R *ᵥ x := by
  funext σ
  simp [openRegionMap_apply, openRegionCoefficientMatrix, Matrix.mulVec, dotProduct, mul_comm]

open scoped Classical in
/-- Reading the matrix of the open-region map gives its contraction coefficients. -/
theorem toMatrix_openRegionMap (A : Tensor Γ d) (R : Finset V) :
    LinearMap.toMatrix' (openRegionMap A R) = openRegionCoefficientMatrix A R := by
  ext σ μ
  simp [LinearMap.toMatrix'_apply, openRegionMap_single, openRegionCoefficientMatrix]

/-- The number of assignments to edges wholly outside the region. -/
noncomputable def regionExteriorMultiplicity (A : Tensor Γ d) (R : Finset V) : ℕ :=
  Fintype.card ((e : {e : Edge Γ // ¬ IsRegionIncidentEdge R e}) → Fin (A.bondDim e.1))

/-- The globally indexed region weight counts each genuine open-region coefficient
once for every assignment to the exterior edges. -/
theorem regionBlockedWeight_eq_exterior_mul_openRegionWeight (A : Tensor Γ d) (R : Finset V)
    (μ : RegionBoundaryConfig A R) (σ : RegionPhysicalConfig (d := d) R) :
    regionBlockedWeight A R μ σ =
      (regionExteriorMultiplicity A R : ℂ) * openRegionWeight A R μ σ := by
  let e := Equiv.piEquivPiSubtypeProd (IsRegionIncidentEdge (G := Γ) R)
    (fun f : Edge Γ => Fin (A.bondDim f))
  rw [regionBlockedWeight, Finset.sum_filter, ← Equiv.sum_comp e.symm,
    Fintype.sum_prod_type]
  have hlabel (η : RegionIncidentConfig A R)
      (θ : (f : {f : Edge Γ // ¬ IsRegionIncidentEdge R f}) → Fin (A.bondDim f.1)) :
      regionBoundaryLabel A R (e.symm (η, θ)) = regionIncidentBoundaryLabel A R η := by
    funext f
    simp only [regionBoundaryLabel, regionIncidentBoundaryLabel, e,
      Equiv.piEquivPiSubtypeProd_symm_apply,
      dite_eq_left (isRegionBoundaryEdge_touches R f.2)]
  have hweight (η : RegionIncidentConfig A R)
      (θ : (f : {f : Edge Γ // ¬ IsRegionIncidentEdge R f}) → Fin (A.bondDim f.1)) :
      (∏ w : {w : V // w ∈ R},
        A.component w.1 (fun ie => e.symm (η, θ) ie.1) (σ w)) =
      regionIncidentWeight A R η σ := by
    refine Finset.prod_congr rfl fun w _ => ?_
    congr 1
    funext ie
    simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply,
      dite_eq_left (isRegionIncidentEdge_of_regionVertex R w ie)]
  simp only [hlabel, hweight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  rfl

/-- Exterior assignments are counted by the product of the exterior bond dimensions. -/
theorem regionExteriorMultiplicity_eq_prod (A : Tensor Γ d) (R : Finset V) :
    regionExteriorMultiplicity A R =
      ∏ e : Edge Γ, if IsRegionIncidentEdge R e then 1 else A.bondDim e := by
  rw [regionExteriorMultiplicity, Fintype.card_pi]
  simp only [Fintype.card_fin]
  symm
  simpa using (Fintype.prod_dite (p := IsRegionIncidentEdge R)
    (fun _ _ => (1 : ℕ)) (fun e _ => A.bondDim e))

/-- The spectator multiplicities of a region and its complement give the full
non-crossing bond multiplicity of the globally indexed cut formula. -/
theorem regionInteriorBondProd_eq_exterior_mul_exterior (A : Tensor Γ d) (R : Finset V) :
    regionInteriorBondProd A R =
      regionExteriorMultiplicity A R * regionExteriorMultiplicity A (Finset.univ \ R) := by
  rw [regionInteriorBondProd, Finset.prod_filter, regionExteriorMultiplicity_eq_prod,
    regionExteriorMultiplicity_eq_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  by_cases h₁ : e.1.1 ∈ R <;> by_cases h₂ : e.1.2 ∈ R <;>
    simp [IsRegionIncidentEdge, IsRegionBoundaryEdge, h₁, h₂]

/-- Nonzero bonds have a nonzero number of exterior assignments. -/
theorem regionExteriorMultiplicity_ne_zero (A : Tensor Γ d) (R : Finset V)
    (hA : ∀ e, A.bondDim e ≠ 0) : regionExteriorMultiplicity A R ≠ 0 := by
  rw [regionExteriorMultiplicity_eq_prod]
  refine Finset.prod_ne_zero_iff.mpr fun e _ => ?_
  split_ifs
  · exact one_ne_zero
  · exact hA e

/-- Source: arXiv:1001.3807, finite-region cut in `eq:iso:L-shape-scenario`,
lines 1935–1957. Joining the two genuine open-region tensors along their crossing
bonds recovers the coefficient of the physical PEPS. Nonzero bond dimensions
allow cancellation of the spectator multiplicities in the older globally indexed
region formula; regular bonds satisfy this hypothesis automatically. -/
theorem stateCoeff_eq_openRegionComplement (A : Tensor Γ d) (R : Finset V)
    (hA : ∀ e, A.bondDim e ≠ 0)
    (σ : RegionPhysicalConfig (d := d) R)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    stateCoeff A (assembleRegionσ R σ τ) =
      ∑ μ : RegionBoundaryConfig A R,
        openRegionWeight A R μ σ *
          openRegionWeight A (Finset.univ \ R) (regionComplementBoundaryConfig A R μ) τ := by
  have h := sum_regionBlockedWeight_mul_complement A R σ τ
  simp only [regionBlockedWeight_eq_exterior_mul_openRegionWeight,
    regionInteriorBondProd_eq_exterior_mul_exterior, nsmul_eq_mul, Nat.cast_mul] at h
  have hc : (regionExteriorMultiplicity A R : ℂ) *
      (regionExteriorMultiplicity A (Finset.univ \ R) : ℂ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (regionExteriorMultiplicity_ne_zero A R hA))
      (Nat.cast_ne_zero.mpr (regionExteriorMultiplicity_ne_zero A _ hA))
  apply (mul_left_cancel₀ hc ?_).symm
  simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h

/-- Source: arXiv:1001.3807, auxiliary finite-region cut identity in
`eq:iso:L-shape-scenario`, lines 1935–1957. For regular bonds, the actual
physical PEPS coefficient is the contraction of its two open-region tensors.
This coefficient identity does not identify the resulting cut with the regular
boundary state and does not assert Theorem 6.9. -/
theorem stateCoeff_eq_openRegionComplement_of_regularBonds
    {H : Type*} [Group H] [Fintype H] (A : Tensor Γ d) (R : Finset V)
    (hBond : ∀ e, A.bondDim e = Fintype.card H)
    (σ : RegionPhysicalConfig (d := d) R)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    stateCoeff A (assembleRegionσ R σ τ) =
      ∑ μ : RegionBoundaryConfig A R,
        openRegionWeight A R μ σ *
          openRegionWeight A (Finset.univ \ R) (regionComplementBoundaryConfig A R μ) τ := by
  apply stateCoeff_eq_openRegionComplement A R
  intro e
  rw [hBond e]
  exact Fintype.card_ne_zero

/-- Source: arXiv:1001.3807, rectangular region cut in `eq:iso:L-shape-scenario`,
lines 1935–1957. This is the coefficient factorization for an actual contiguous
rectangle in a finite square lattice with regular bond dimensions. It is an
auxiliary contraction identity, without an entropy conclusion. -/
theorem stateCoeff_rectangle_eq_openRegionComplement_of_regularBonds
    {H : Type*} [Group H] [Fintype H] {width height : ℕ}
    (A : Tensor (squareLatticeGraph width height) d)
    (xStart yStart xLength yLength : ℕ)
    (hBond : ∀ e, A.bondDim e = Fintype.card H) :
    let R := squareLatticeContiguousRectangle xStart yStart xLength yLength
    ∀ (σ : RegionPhysicalConfig (d := d) R)
      (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)),
      stateCoeff A (assembleRegionσ R σ τ) =
        ∑ μ : RegionBoundaryConfig A R,
          openRegionWeight A R μ σ *
            openRegionWeight A (Finset.univ \ R) (regionComplementBoundaryConfig A R μ) τ := by
  intro R σ τ
  exact stateCoeff_eq_openRegionComplement_of_regularBonds A R hBond σ τ

end TNLean.PEPS
