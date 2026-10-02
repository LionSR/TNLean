/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularRegionSupport
import TNLean.Algebra.FlatDensityRenyiEntropy

/-!
# An entropy bound for regular G-injective cuts

The physical reduced density is normalized by its trace. For a regular
G-injective PEPS, a cut with connected induced regions and `n + 1` crossing
bonds has positive trace and normalized rank `|G|^n`. Its von Neumann entropy
is therefore at most `n log |G|`, while its zero-order Rényi entropy equals
that quantity. No isometry or flat spectrum is assumed.

**Scope restriction (regular connected cuts):** The virtual representation
is regular, both induced regions are connected, and the boundary is nonempty.
These are auxiliary entropy consequences of the regular boundary construction,
not the general semi-regular entropy assertion; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Corollary 6.10,
local source lines 2074–2090; Wolf, Quantum Channels & Operations, Section 8.2,
for the entropy bound by the logarithm of the support dimension.
-/

open scoped BigOperators Matrix ComplexOrder

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- The trace-one physical reduced density of the actual closed PEPS vector.
For a zero vector this definition gives zero. Source: SCP10, the normalized
reduced density in Corollary 6.10, lines 2074–2090. -/
noncomputable def normalizedRegionReducedDensity (A : Tensor Γ d) (R : Finset V) :
    Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ :=
  (regionReducedDensity A R).trace⁻¹ • regionReducedDensity A R

/-- A nonzero closed coefficient vector has a reduced density of positive
trace on every region. This is the normalization preceding the entropy
calculation in SCP10, Corollary 6.10, lines 2074–2090. -/
theorem trace_regionReducedDensity_pos_of_stateCoeff_ne_zero
    (A : Tensor Γ d) (R : Finset V) (hA : stateCoeff A ≠ 0) :
    0 < (regionReducedDensity A R).trace := by
  classical
  let M : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
    fun σ τ => stateCoeff A (assembleRegionσ R σ τ)
  have hM : M ≠ 0 := by
    intro hzero
    apply hA
    funext σ
    let p := regionConfigEquiv (d := d) R σ
    have h := congrFun (congrFun hzero p.1) p.2
    change stateCoeff A ((regionConfigEquiv (d := d) R).symm p) = 0 at h
    simpa only [p, Equiv.symm_apply_apply, Pi.zero_apply] using h
  rw [regionReducedDensity_eq_mul_conjTranspose]
  change 0 < (M * M.conjTranspose).trace
  have ht : (M * M.conjTranspose).trace ≠ 0 :=
    mt Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp hM
  exact lt_of_le_of_ne (Matrix.posSemidef_self_mul_conjTranspose M).trace_nonneg
    (Ne.symm ht)

/-- Normalizing a nonzero closed PEPS preserves positivity and rank and gives
trace one. Source: SCP10, Corollary 6.10, lines 2074–2090. -/
theorem normalizedRegionReducedDensity_properties
    (A : Tensor Γ d) (R : Finset V) (hA : stateCoeff A ≠ 0) :
    (normalizedRegionReducedDensity A R).PosSemidef ∧
      (normalizedRegionReducedDensity A R).trace = 1 ∧
      (normalizedRegionReducedDensity A R).rank = (regionReducedDensity A R).rank := by
  classical
  have ht := trace_regionReducedDensity_pos_of_stateCoeff_ne_zero A R hA
  have htn : (regionReducedDensity A R).trace ≠ 0 := ne_of_gt ht
  refine ⟨(regionReducedDensity_posSemidef A R).smul (inv_nonneg.mpr ht.le), ?_, ?_⟩
  · rw [normalizedRegionReducedDensity, Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ htn]
  · exact Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero htn))

/-- Normalization of a nonzero closed PEPS leaves its regional physical
support unchanged. Source: SCP10, normalized reduced densities in
Corollary 6.10, lines 2074–2090. -/
theorem range_normalizedRegionReducedDensity_eq
    (A : Tensor Γ d) (R : Finset V) (hA : stateCoeff A ≠ 0) :
    (Matrix.mulVecLin (normalizedRegionReducedDensity A R)).range =
      (Matrix.mulVecLin (regionReducedDensity A R)).range := by
  classical
  have htn := ne_of_gt (trace_regionReducedDensity_pos_of_stateCoeff_ne_zero A R hA)
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    change ((regionReducedDensity A R).trace⁻¹ • regionReducedDensity A R) *ᵥ y ∈ _
    rw [Matrix.smul_mulVec]
    exact Submodule.smul_mem _ _ ⟨y, rfl⟩
  · rintro x ⟨y, rfl⟩
    refine ⟨(regionReducedDensity A R).trace • y, ?_⟩
    change ((regionReducedDensity A R).trace⁻¹ • regionReducedDensity A R) *ᵥ
      ((regionReducedDensity A R).trace • y) = _
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ htn, one_smul]
    rfl

/-- A regional parent interaction also annihilates the normalized physical
reduced density. Source: arXiv:2011.12127, Section IV.C.1, lines 2003–2011. -/
theorem IsRegionParentInteraction.mul_normalizedRegionReducedDensity_eq_zero
    {A : Tensor Γ d} {R : Finset V}
    {h : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ}
    (hh : IsRegionParentInteraction A R h) :
    h * normalizedRegionReducedDensity A R = 0 := by
  rw [normalizedRegionReducedDensity, Matrix.mul_smul,
    hh.mul_regionReducedDensity_eq_zero, smul_zero]

variable {G : Type*} [Group G] [Fintype G]

/-- Normalized physical support is the entire regional ground space for a
connected regular G-injective cut. Source: SCP10, the regular boundary
construction in Lemma 5.2 and Corollary 6.10, lines 1318–1358 and 2074–2090. -/
theorem range_normalizedRegionReducedDensity_of_regular_connected_cut
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected)
    (hS : (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Connected)
    (n : ℕ) (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    (Matrix.mulVecLin (normalizedRegionReducedDensity (groupBondTensor a) R)).range =
      regionGroundSpace (groupBondTensor a) R := by
  rw [range_normalizedRegionReducedDensity_eq _ _
    (stateCoeff_groupBondTensor_ne_zero_of_regular_connected_cut a ha R hR hS n e)]
  exact range_regionReducedDensity_eq_regionGroundSpace_of_regular_connected_cut a ha R hR hS n e

/-- The normalized physical density determines exactly which local linear
operators annihilate the regional ground space. Positivity of the operator
is not required. This is an auxiliary support consequence of the regular
boundary construction in SCP10, Lemma 5.2 and Corollary 6.10. -/
theorem mul_normalizedRegionReducedDensity_eq_zero_iff_of_regular_connected_cut
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected)
    (hS : (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Connected)
    (n : ℕ) (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1))
    (h : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ) :
    h * normalizedRegionReducedDensity (groupBondTensor a) R = 0 ↔
      regionGroundSpace (groupBondTensor a) R ≤ (Matrix.mulVecLin h).ker := by
  classical
  rw [← range_normalizedRegionReducedDensity_of_regular_connected_cut a ha R hR hS n e,
    LinearMap.range_le_ker_iff, ← Matrix.mulVecLin_mul]
  constructor
  · intro hzero
    rw [hzero, Matrix.mulVecLin_zero]
  · intro hzero
    apply Matrix.toLin'.injective
    change Matrix.mulVecLin (h * normalizedRegionReducedDensity (groupBondTensor a) R) =
      Matrix.mulVecLin 0
    simpa only [Matrix.mulVecLin_zero] using hzero

/-- The normalized reduced density of a connected regular G-injective cut
has the full invariant boundary rank. No separate nonvanishing assumption
is needed. Source: SCP10, Corollary 6.10, lines 2074–2090. -/
theorem normalizedRegionReducedDensity_properties_of_regular_connected_cut
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected)
    (hS : (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Connected)
    (n : ℕ) (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    (normalizedRegionReducedDensity (groupBondTensor a) R).PosSemidef ∧
      (normalizedRegionReducedDensity (groupBondTensor a) R).trace = 1 ∧
      (normalizedRegionReducedDensity (groupBondTensor a) R).rank = Fintype.card G ^ n := by
  obtain ⟨hpos, htr, hrank⟩ := normalizedRegionReducedDensity_properties
    (groupBondTensor a) R
    (stateCoeff_groupBondTensor_ne_zero_of_regular_connected_cut a ha R hR hS n e)
  exact ⟨hpos, htr, hrank.trans
    (rank_regionReducedDensity_of_regular_connected_cut a ha R hR hS n e)⟩

/-- The von Neumann entropy of a connected regular G-injective cut is at
most one group logarithm per relative crossing label. Its zero-order Rényi
entropy is exactly that quantity. Source: SCP10, Corollary 6.10, lines
2074–2090, and Wolf Section 8.2 for the entropy-rank bound. -/
theorem entropy_normalizedRegionReducedDensity_of_regular_connected_cut
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected)
    (hS : (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Connected)
    (n : ℕ) (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    let ρ := normalizedRegionReducedDensity (groupBondTensor a) R
    ∃ hρ : ρ.IsHermitian,
      0 ≤ vonNeumannEntropy ρ hρ ∧
      vonNeumannEntropy ρ hρ ≤ n * Real.log (Fintype.card G : ℝ) ∧
      renyiEntropy ρ hρ 0 = n * Real.log (Fintype.card G : ℝ) := by
  classical
  obtain ⟨hpos, htr, hrank⟩ :=
    normalizedRegionReducedDensity_properties_of_regular_connected_cut a ha R hR hS n e
  have hlog : Real.log ((normalizedRegionReducedDensity (groupBondTensor a) R).rank : ℝ) =
      n * Real.log (Fintype.card G : ℝ) := by
    rw [hrank, Nat.cast_pow, Real.log_pow]
  refine ⟨hpos.isHermitian, vonNeumannEntropy_nonneg_of_posSemidef_trace_one hpos htr,
    (vonNeumannEntropy_le_log_rank hpos htr).trans_eq hlog, ?_⟩
  simpa only [renyiEntropy, ↓reduceIte] using hlog

end TNLean.PEPS
