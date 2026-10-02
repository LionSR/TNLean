/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionParentHamiltonian
import QICLean.Channel.MaximalOverlap

/-!
# Reduced densities and local PEPS ground spaces

The reduced density of the closed PEPS vector on a region is the partial
trace of its outer product, without normalization. Its range is contained
in the regional ground space, and every parent interaction annihilates it.
These assertions hold for arbitrary finite graphs and site-dependent tensors,
including zero-dimensional virtual spaces and a zero contracted vector.

Source: Cirac, Pérez-García, Schuch, and Verstraete, arXiv:2011.12127,
Section IV.C.1, local source lines 2003–2011.
-/

open scoped BigOperators Matrix ComplexOrder

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- The exact open-region cut contraction also holds when virtual bond
spaces have dimension zero. Source: arXiv:2011.12127, the regional contraction
at lines 2003–2008. -/
theorem stateCoeff_eq_openRegionComplement_unconditional (A : Tensor Γ d) (R : Finset V)
    (σ : RegionPhysicalConfig (d := d) R)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    stateCoeff A (assembleRegionσ R σ τ) =
      ∑ μ : RegionBoundaryConfig A R,
        openRegionWeight A R μ σ *
          openRegionWeight A (Finset.univ \ R) (regionComplementBoundaryConfig A R μ) τ := by
  classical
  by_cases h : Nonempty (VirtualConfig A)
  · obtain ⟨ζ⟩ := h
    exact stateCoeff_eq_openRegionComplement A R
      (fun e => Nat.ne_zero_of_lt
        (lt_of_le_of_lt (Nat.zero_le (ζ e).val) (ζ e).isLt)) σ τ
  · let : IsEmpty (VirtualConfig A) := not_nonempty_iff.mp h
    by_cases hR : Nonempty (RegionIncidentConfig A R)
    · obtain ⟨η⟩ := hR
      have hS : ¬ Nonempty (RegionIncidentConfig A (Finset.univ \ R)) := by
        rintro ⟨θ⟩
        apply h
        refine ⟨fun e => if he : IsRegionIncidentEdge R e then η ⟨e, he⟩
          else θ ⟨e, ?_⟩⟩
        simp only [IsRegionIncidentEdge, not_or] at he
        exact Or.inl (by simp [he.1])
      let : IsEmpty (RegionIncidentConfig A (Finset.univ \ R)) :=
        not_nonempty_iff.mp hS
      simp [stateCoeff, openRegionWeight]
    · let : IsEmpty (RegionIncidentConfig A R) := not_nonempty_iff.mp hR
      simp [stateCoeff, openRegionWeight]

/-- The unnormalized physical reduced density of the actual closed PEPS.
Source: arXiv:2011.12127, regional contraction and frustration freeness,
lines 2003–2011. -/
noncomputable def regionReducedDensity (A : Tensor Γ d) (R : Finset V) :
    Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ :=
  Matrix.partialTraceRight (Matrix.vecMulVec
    (stateCoeff A ∘ (regionConfigEquiv (d := d) R).symm)
    (star (stateCoeff A ∘ (regionConfigEquiv (d := d) R).symm)))

/-- Equal closed coefficient vectors have equal physical reduced densities.
Source: arXiv:2011.12127, the physical regional reduction, lines 2003–2011. -/
theorem SameState.regionReducedDensity_eq {A B : Tensor Γ d}
    (hAB : SameState A B) (R : Finset V) :
    regionReducedDensity A R = regionReducedDensity B R := by
  have hψ : stateCoeff A = stateCoeff B := funext hAB
  simp only [regionReducedDensity, hψ]

/-- The regional reduced density is the Gram matrix of the actual physical
coefficient matrix across the cut. Source: arXiv:2011.12127,
regional contraction, lines 2003–2008. -/
theorem regionReducedDensity_eq_mul_conjTranspose (A : Tensor Γ d) (R : Finset V) :
    let M : Matrix (RegionPhysicalConfig (d := d) R)
        (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
      fun σ τ => stateCoeff A (assembleRegionσ R σ τ)
    regionReducedDensity A R = M * M.conjTranspose := by
  exact Matrix.partialTraceRight_vecMulVec_eq _

/-- A regional reduced density is positive semidefinite.
Source: arXiv:2011.12127, reduced physical state on a region, lines 2003–2008. -/
theorem regionReducedDensity_posSemidef (A : Tensor Γ d) (R : Finset V) :
    (regionReducedDensity A R).PosSemidef := by
  rw [regionReducedDensity_eq_mul_conjTranspose]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- The physical reduced density and its coefficient matrix have exactly the
same column space. Source: arXiv:2011.12127, the physical cut underlying
regional frustration freeness at lines 2003–2011. -/
theorem range_regionReducedDensity_eq_cutRange (A : Tensor Γ d) (R : Finset V) :
    let M : Matrix (RegionPhysicalConfig (d := d) R)
        (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
      fun σ τ => stateCoeff A (assembleRegionσ R σ τ)
    (Matrix.mulVecLin (regionReducedDensity A R)).range = (Matrix.mulVecLin M).range := by
  classical
  dsimp only
  rw [regionReducedDensity_eq_mul_conjTranspose]
  let M : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
    fun σ τ => stateCoeff A (assembleRegionσ R σ τ)
  change (Matrix.mulVecLin (M * M.conjTranspose)).range = (Matrix.mulVecLin M).range
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · change (M * M.conjTranspose).rank = M.rank
    exact Matrix.rank_self_mul_conjTranspose M

/-- The support of the physical reduced density lies in the regional PEPS
ground space. Source: arXiv:2011.12127, lines 2003–2011. -/
theorem range_regionReducedDensity_le (A : Tensor Γ d) (R : Finset V) :
    (Matrix.mulVecLin (regionReducedDensity A R)).range ≤ regionGroundSpace A R := by
  rintro ψ ⟨x, rfl⟩
  classical
  change regionReducedDensity A R *ᵥ x ∈ _
  rw [regionReducedDensity_eq_mul_conjTranspose]
  let M : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
    fun σ τ => stateCoeff A (assembleRegionσ R σ τ)
  change (M * M.conjTranspose) *ᵥ x ∈ _
  rw [← Matrix.mulVec_mulVec]
  have hsum : M *ᵥ (M.conjTranspose *ᵥ x) =
      ∑ τ, (M.conjTranspose *ᵥ x) τ • (fun σ => M σ τ) := by
    ext σ
    simp [Matrix.mulVec, dotProduct, mul_comm]
  change M *ᵥ (M.conjTranspose *ᵥ x) ∈ _
  rw [hsum]
  apply Submodule.sum_mem
  intro τ _
  exact Submodule.smul_mem _ _ (stateCoeff_slice_mem_regionGroundSpace A R τ)

/-- A regional parent interaction annihilates the physical reduced density.
Source: arXiv:2011.12127, frustration freeness, lines 2008–2011. -/
theorem IsRegionParentInteraction.mul_regionReducedDensity_eq_zero
    {A : Tensor Γ d} {R : Finset V}
    {h : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ}
    (hh : IsRegionParentInteraction A R h) : h * regionReducedDensity A R = 0 := by
  apply Matrix.toLin'.injective
  change Matrix.mulVecLin (h * regionReducedDensity A R) = Matrix.mulVecLin 0
  rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_zero]
  apply LinearMap.ext
  intro x
  have hmem := range_regionReducedDensity_le A R ⟨x, rfl⟩
  rw [← hh.2] at hmem
  exact hmem

/-- The physical reduced density also annihilates a regional parent
interaction on the right. Source: arXiv:2011.12127, frustration freeness,
lines 2008–2011. -/
theorem IsRegionParentInteraction.regionReducedDensity_mul_eq_zero
    {A : Tensor Γ d} {R : Finset V}
    {h : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ}
    (hh : IsRegionParentInteraction A R h) : regionReducedDensity A R * h = 0 := by
  have heq := congrArg Matrix.conjTranspose hh.mul_regionReducedDensity_eq_zero
  simpa only [Matrix.conjTranspose_mul, hh.1.isHermitian.eq,
    (regionReducedDensity_posSemidef A R).isHermitian.eq, Matrix.conjTranspose_zero] using heq

end TNLean.PEPS
