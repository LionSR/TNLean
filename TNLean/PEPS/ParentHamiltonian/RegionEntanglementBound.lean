/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularRegionEntropyBound

/-!
# Entanglement bounds for PEPS on arbitrary finite graphs

The reduced-state rank on any region is bounded by the product of the
crossing-bond dimensions. After normalization of a nonzero closed state,
its von Neumann entropy is bounded by the sum of the logarithms of those
dimensions. No injectivity, regular lattice, or uniform bond dimension
is assumed.

Source: Cirac, Pérez-García, Schuch, and Verstraete, arXiv:2011.12127,
Section II.A.3, the boundary-rank argument and PEPS area law,
local source lines 429–448 and 539. The variable-dimension finite-graph
statement is the same crossing-bond dimension argument.
-/

open scoped BigOperators Matrix ComplexOrder

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- A nonzero closed PEPS has a nonzero virtual space on every edge.
Source: the virtual-index contraction in CPGSV21, Section II.A.3,
lines 429–448. -/
theorem bondDim_pos_of_stateCoeff_ne_zero (A : Tensor Γ d) (hA : stateCoeff A ≠ 0)
    (e : Edge Γ) : 0 < A.bondDim e := by
  classical
  have hconfig : Nonempty (VirtualConfig A) := by
    by_contra h
    let : IsEmpty (VirtualConfig A) := not_nonempty_iff.mp h
    apply hA
    funext σ
    simp [stateCoeff]
  obtain ⟨η⟩ := hconfig
  exact lt_of_le_of_lt (Nat.zero_le (η e).val) (η e).isLt

/-- The rank of the physical reduced operator is bounded by the product
of dimensions crossing the cut. Source: CPGSV21, Section II.A.3,
the PEPS area-law argument, lines 429–448. -/
theorem rank_regionReducedDensity_le_boundary (A : Tensor Γ d) (R : Finset V) :
    (regionReducedDensity A R).rank ≤
      ∏ e : {e : Edge Γ // IsRegionBoundaryEdge R e}, A.bondDim e.1 := by
  change Module.finrank ℂ (Matrix.mulVecLin (regionReducedDensity A R)).range ≤ _
  exact (Submodule.finrank_mono (range_regionReducedDensity_le A R)).trans
    (finrank_regionGroundSpace_le A R)

/-- Schmidt rank is bounded by the physical dimensions on both sides of
the cut. Source: the bipartite Schmidt-rank argument in CPGSV21,
Section II.A.3, lines 429–448. -/
theorem rank_regionReducedDensity_le_physical (A : Tensor Γ d) (R : Finset V) :
    (regionReducedDensity A R).rank ≤ min (d ^ R.card) (d ^ (Finset.univ \ R).card) := by
  classical
  let M : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
    fun σ τ => stateCoeff A (assembleRegionσ R σ τ)
  rw [regionReducedDensity_eq_mul_conjTranspose]
  change (M * M.conjTranspose).rank ≤ _
  rw [Matrix.rank_self_mul_conjTranspose]
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  simpa [RegionPhysicalConfig] using
    (le_min (Matrix.rank_le_card_height M) (Matrix.rank_le_card_width M))

/-- The normalized physical reduced density of a nonzero PEPS has the
same boundary-rank bound. Source: CPGSV21, Section II.A.3,
lines 429–448. -/
theorem rank_normalizedRegionReducedDensity_le_boundary (A : Tensor Γ d) (R : Finset V)
    (hA : stateCoeff A ≠ 0) :
    (normalizedRegionReducedDensity A R).rank ≤
      ∏ e : {e : Edge Γ // IsRegionBoundaryEdge R e}, A.bondDim e.1 := by
  change Module.finrank ℂ (Matrix.mulVecLin (normalizedRegionReducedDensity A R)).range ≤ _
  rw [range_normalizedRegionReducedDensity_eq A R hA]
  exact rank_regionReducedDensity_le_boundary A R

/-- Every finite-graph PEPS obeys the crossing-bond entropy bound.
Source: CPGSV21, Section II.A.3, lines 429–448; the uniform square-lattice
specialization is the bound at line 445. -/
theorem entropy_normalizedRegionReducedDensity_le_boundary (A : Tensor Γ d) (R : Finset V)
    (hA : stateCoeff A ≠ 0) :
    let ρ := normalizedRegionReducedDensity A R
    ∃ hρ : ρ.IsHermitian,
      0 ≤ vonNeumannEntropy ρ hρ ∧
      vonNeumannEntropy ρ hρ ≤
        ∑ e : {e : Edge Γ // IsRegionBoundaryEdge R e}, Real.log (A.bondDim e.1 : ℝ) := by
  classical
  obtain ⟨hpos, htr, _⟩ := normalizedRegionReducedDensity_properties A R hA
  have hrank := rank_normalizedRegionReducedDensity_le_boundary A R hA
  have hrankpos : 0 < ((normalizedRegionReducedDensity A R).rank : ℝ) :=
    Nat.cast_pos.mpr (hpos.rank_pos_of_trace_one htr)
  have hlog : Real.log ((normalizedRegionReducedDensity A R).rank : ℝ) ≤
      Real.log (∏ e : {e : Edge Γ // IsRegionBoundaryEdge R e}, (A.bondDim e.1 : ℝ)) := by
    apply Real.log_le_log hrankpos
    exact_mod_cast hrank
  rw [Real.log_prod (fun e _ => Nat.cast_ne_zero.mpr
    (bondDim_pos_of_stateCoeff_ne_zero A hA e.1).ne')] at hlog
  exact ⟨hpos.isHermitian, vonNeumannEntropy_nonneg_of_posSemidef_trace_one hpos htr,
    (vonNeumannEntropy_le_log_rank hpos htr).trans hlog⟩

/-- With a uniform bond dimension the finite-graph entropy bound is the
number of crossing edges times its logarithm. Source: CPGSV21,
Section II.A.3, PEPS area law at line 445. -/
theorem entropy_normalizedRegionReducedDensity_le_uniform_boundary
    (A : Tensor Γ d) (R : Finset V) (hA : stateCoeff A ≠ 0)
    (D : ℕ) (hD : ∀ e, IsRegionBoundaryEdge R e → A.bondDim e = D) :
    let ρ := normalizedRegionReducedDensity A R
    ∃ hρ : ρ.IsHermitian,
      0 ≤ vonNeumannEntropy ρ hρ ∧
      vonNeumannEntropy ρ hρ ≤
        Fintype.card {e : Edge Γ // IsRegionBoundaryEdge R e} * Real.log (D : ℝ) := by
  obtain ⟨hρ, hnonneg, hbound⟩ := entropy_normalizedRegionReducedDensity_le_boundary A R hA
  refine ⟨hρ, hnonneg, hbound.trans_eq ?_⟩
  simp only [hD _ (Subtype.property _), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- A cut carrying only one-dimensional virtual bonds has zero
entanglement entropy. In particular this covers cuts with no crossing
edges. Source: CPGSV21, Section II.A.3, the boundary-rank argument
at lines 429–448. -/
theorem entropy_normalizedRegionReducedDensity_eq_zero_of_boundary_bondOne
    (A : Tensor Γ d) (R : Finset V) (hA : stateCoeff A ≠ 0)
    (hboundary : ∀ e, IsRegionBoundaryEdge R e → A.bondDim e = 1) :
    let ρ := normalizedRegionReducedDensity A R
    ∃ hρ : ρ.IsHermitian, vonNeumannEntropy ρ hρ = 0 := by
  obtain ⟨hρ, hnonneg, hbound⟩ :=
    entropy_normalizedRegionReducedDensity_le_uniform_boundary A R hA 1 hboundary
  refine ⟨hρ, le_antisymm ?_ hnonneg⟩
  simpa only [Nat.cast_one, Real.log_one, mul_zero] using hbound

end TNLean.PEPS
