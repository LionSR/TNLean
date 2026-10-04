/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionPhysicalGroundSpaceTransport
import TNLean.PEPS.ParentHamiltonian.RegionParentComparison
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-!
# The full-region PEPS ground space

The full vertex region has no crossing bonds. Its open physical range is
therefore exactly the span of the closed PEPS vector. A collection of parent
interactions containing the full region has this same ground space, including
when the PEPS vector vanishes. The canonical projector has unit excitation gap.

These are consequences of the finite regional parent construction in CPGSV21,
arXiv:2011.12127, Section IV.C.1, lines 2003–2011. The full-region interaction
is a term on the entire graph; no nearest-neighbour uniqueness theorem is asserted.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators ComplexOrder Matrix MatrixOrder

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

omit [DecidableRel Γ.Adj] in
/-- The full region has no boundary edges.
Source: CPGSV21, arXiv:2011.12127, arbitrary boundary conditions, lines 2003–2008. -/
theorem not_isRegionBoundaryEdge_univ (e : Edge Γ) :
    ¬ IsRegionBoundaryEdge (Finset.univ : Finset V) e := by
  simp [IsRegionBoundaryEdge]

/-- Every boundary-labelled tensor of the full region equals the closed PEPS
vector in the regional physical coordinates. Source: CPGSV21,
arXiv:2011.12127, consequence of the boundary-condition construction, lines 2003–2008. -/
theorem openRegionWeight_univ (A : Tensor Γ d)
    (μ : RegionBoundaryConfig A Finset.univ) :
    openRegionWeight A Finset.univ μ = fullRegionPhysicalEquiv d (stateCoeff A) := by
  classical
  let : IsEmpty {e : Edge Γ // IsRegionBoundaryEdge (Finset.univ : Finset V) e} :=
    ⟨fun e => not_isRegionBoundaryEdge_univ e.1 e.2⟩
  have hmult : regionExteriorMultiplicity A Finset.univ = 1 := by
    rw [regionExteriorMultiplicity_eq_prod]
    simp [IsRegionIncidentEdge]
  have h := regionBlockedWeight_eq_exterior_mul_openRegionWeight A Finset.univ μ
  funext σ
  have hs := h σ
  rw [hmult, Nat.cast_one, one_mul] at hs
  rw [← hs]
  simp only [regionBlockedWeight, Subsingleton.elim (regionBoundaryLabel A Finset.univ _) μ,
    Finset.filter_true]
  change (∑ ζ : VirtualConfig A, ∏ w : {w : V // w ∈ Finset.univ},
    A.component w.1 (fun ie => ζ ie.1) (σ w)) =
      ∑ ζ : VirtualConfig A, ∏ v : V,
        A.component v (fun ie => ζ ie.1) (σ ⟨v, Finset.mem_univ v⟩)
  apply Finset.sum_congr rfl
  intro ζ hζ
  exact (Finset.prod_subtype Finset.univ (fun _ => Iff.rfl)
    (fun v => A.component v (fun ie => ζ ie.1) (σ ⟨v, Finset.mem_univ v⟩))).symm

/-- The full-region ground space is exactly the span of the closed PEPS vector.
This includes a vanishing vector, whose span is zero. Source: CPGSV21,
arXiv:2011.12127, consequence of the regional construction, lines 2003–2011. -/
theorem regionGroundSpace_univ (A : Tensor Γ d) :
    regionGroundSpace A Finset.univ =
      Submodule.span ℂ {fullRegionPhysicalEquiv d (stateCoeff A)} := by
  have : Nonempty (RegionBoundaryConfig A Finset.univ) :=
    ⟨fun e => False.elim (not_isRegionBoundaryEdge_univ e.1 e.2)⟩
  have hw : openRegionWeight A Finset.univ =
      fun _ => fullRegionPhysicalEquiv d (stateCoeff A) :=
    funext (openRegionWeight_univ A)
  rw [regionGroundSpace_eq_span, hw, Set.range_const]

/-- Taking a slice across the full region only changes the physical coordinates.
Source: CPGSV21, arXiv:2011.12127, regional physical space, lines 2003–2008. -/
theorem regionSliceMap_univ
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ Finset.univ)) :
    regionSliceMap Finset.univ τ = (fullRegionPhysicalEquiv d).toLinearMap := by
  refine LinearMap.ext fun ψ => funext fun σ => ?_
  change ψ (assembleRegionσ Finset.univ σ τ) = ψ (fun v => σ ⟨v, Finset.mem_univ v⟩)
  congr 1
  funext v
  simp [assembleRegionσ]

/-- A collection containing the full region has exactly the PEPS span as its
common regional ground space. Source: CPGSV21, arXiv:2011.12127, consequence
of the finite regional parent construction, lines 2003–2011. -/
theorem regionParentGroundSpace_eq_span_of_full_region (A : Tensor Γ d)
    {ι : Type*} (R : ι → Finset V) (hfull : ∃ i, R i = Finset.univ) :
    regionParentGroundSpace A R = Submodule.span ℂ {stateCoeff A} := by
  apply le_antisymm
  · intro ψ hψ
    simp only [regionParentGroundSpace, Submodule.mem_iInf, Submodule.mem_comap] at hψ
    obtain ⟨i, hi⟩ := hfull
    have hwhole := hψ i
    rw [hi] at hwhole
    let τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ Finset.univ) :=
      fun w => False.elim (by simpa using w.2)
    have hmem := hwhole τ
    rw [regionSliceMap_univ, regionGroundSpace_univ] at hmem
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hmem
    apply Submodule.mem_span_singleton.mpr
    refine ⟨z, (fullRegionPhysicalEquiv d).injective ?_⟩
    change z • fullRegionPhysicalEquiv d (stateCoeff A) = fullRegionPhysicalEquiv d ψ at hz
    rw [map_smul]
    exact hz
  · exact Submodule.span_le.mpr
      (Set.singleton_subset_iff.mpr (stateCoeff_mem_regionParentGroundSpace A R))

/-- The corresponding positive parent Hamiltonian has exactly the PEPS span
as its kernel. Source: CPGSV21, arXiv:2011.12127, consequence of regional
parent kernels, lines 2003–2011; the collection here contains the full region. -/
theorem ker_regionParentHamiltonian_eq_span_of_full_region (A : Tensor Γ d)
    {ι : Type*} [Fintype ι] (R : ι → Finset V)
    (h : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hh : ∀ i, IsRegionParentInteraction A (R i) (h i))
    (hfull : ∃ i, R i = Finset.univ) :
    (Matrix.mulVecLin (regionParentHamiltonian R h)).ker =
      Submodule.span ℂ {stateCoeff A} := by
  rw [ker_regionParentHamiltonian A R h hh,
    regionParentGroundSpace_eq_span_of_full_region A R hfull]

/-- A nonzero PEPS has a one-dimensional common ground space when a full-region
condition is included. Source: CPGSV21, arXiv:2011.12127, consequence of the
regional parent construction, lines 2003–2011. -/
theorem finrank_regionParentGroundSpace_eq_one_of_full_region (A : Tensor Γ d)
    {ι : Type*} (R : ι → Finset V) (hfull : ∃ i, R i = Finset.univ)
    (hA : stateCoeff A ≠ 0) : Module.finrank ℂ (regionParentGroundSpace A R) = 1 := by
  rw [regionParentGroundSpace_eq_span_of_full_region A R hfull]
  exact finrank_span_singleton hA

/-- The canonical regional interaction is an idempotent operator.
Source: CPGSV21, arXiv:2011.12127, projector parent interactions, line 2170. -/
theorem canonicalRegionParentInteraction_isIdempotentElem (A : Tensor Γ d) (R : Finset V) :
    IsIdempotentElem (canonicalRegionParentInteraction A R) := by
  classical
  change canonicalRegionParentInteraction A R * canonicalRegionParentInteraction A R =
    canonicalRegionParentInteraction A R
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul 2 2 2]
  simp only [canonicalRegionParentInteraction, LinearEquiv.apply_symm_apply]
  have hP := Submodule.isSymmetricProjection_starProjection (regionGroundSpaceES A R)ᗮ
  exact hP.isIdempotentElem.eq

/-- The canonical projector acts as the identity on the orthogonal complement
of its regional ground space. Source: CPGSV21, arXiv:2011.12127,
projector parent interactions and their gap, line 2170. -/
theorem canonicalRegionParentInteraction_apply_eq_self (A : Tensor Γ d) (R : Finset V)
    {ψ : EuclideanSpace ℂ (RegionPhysicalConfig (d := d) R)}
    (hψ : ψ ∈ (regionGroundSpaceES A R)ᗮ) :
    Matrix.toEuclideanLin (canonicalRegionParentInteraction A R) ψ = ψ := by
  classical
  rw [canonicalRegionParentInteraction, LinearEquiv.apply_symm_apply]
  exact Submodule.starProjection_eq_self_iff.mpr hψ

/-- The canonical regional interaction has unit norm gap on the complement
of its kernel. Source: CPGSV21, arXiv:2011.12127, projector comparison, line 2170. -/
theorem canonicalRegionParentInteraction_unit_norm_gap (A : Tensor Γ d) (R : Finset V) :
    ∀ ψ ∈ (Matrix.toEuclideanLin (canonicalRegionParentInteraction A R)).kerᗮ,
      (1 : ℝ) * ‖ψ‖ ≤ ‖Matrix.toEuclideanLin (canonicalRegionParentInteraction A R) ψ‖ := by
  classical
  intro ψ hψ
  rw [(isRegionParentInteraction_canonical A R).ker_toEuclideanLin] at hψ
  rw [canonicalRegionParentInteraction_apply_eq_self A R hψ, one_mul]

/-- The spectrum of the canonical regional projector contains only zero and one.
Source: CPGSV21, arXiv:2011.12127, projector parent interactions, line 2170. -/
theorem canonicalRegionParentInteraction_spectrum_subset (A : Tensor Γ d) (R : Finset V) :
    spectrum ℂ (canonicalRegionParentInteraction A R) ⊆ {0, 1} := by
  classical
  exact (canonicalRegionParentInteraction_isIdempotentElem A R).spectrum_subset ℂ

/-- A single canonical interaction on the full graph has precisely the PEPS
span as its kernel. Source: CPGSV21, arXiv:2011.12127, consequence of regional
parent kernels, lines 2003–2011; this interaction acts on the full region. -/
theorem ker_regionLocalTerm_univ_canonical (A : Tensor Γ d) :
    (Matrix.mulVecLin (regionLocalTerm Finset.univ
      (canonicalRegionParentInteraction A Finset.univ))).ker =
      Submodule.span ℂ {stateCoeff A} := by
  classical
  simpa only [regionParentHamiltonian, Fintype.sum_unique] using
    ker_regionParentHamiltonian_eq_span_of_full_region A (fun _ : Unit => Finset.univ)
      (fun _ => canonicalRegionParentInteraction A Finset.univ)
      (fun _ => isRegionParentInteraction_canonical A Finset.univ) ⟨(), rfl⟩

/-- Extending a canonical parent projector by the identity preserves idempotence.
Source: CPGSV21, arXiv:2011.12127, regional extensions, lines 2003–2011,
and projector interactions, line 2170. -/
theorem regionLocalTerm_canonical_isIdempotentElem (A : Tensor Γ d) (R : Finset V) :
    IsIdempotentElem (regionLocalTerm R (canonicalRegionParentInteraction A R)) := by
  classical
  change regionLocalTerm R (canonicalRegionParentInteraction A R) *
    regionLocalTerm R (canonicalRegionParentInteraction A R) =
      regionLocalTerm R (canonicalRegionParentInteraction A R)
  unfold regionLocalTerm
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul,
    (canonicalRegionParentInteraction_isIdempotentElem A R).eq, mul_one]

/-- In the full physical Hilbert space each canonical local term is an orthogonal
projection. Source: CPGSV21, arXiv:2011.12127, regional extensions, lines 2003–2011,
and projector interactions, line 2170. -/
theorem regionLocalTerm_canonical_isSymmetricProjection (A : Tensor Γ d) (R : Finset V) :
    (Matrix.toEuclideanLin
      (regionLocalTerm R (canonicalRegionParentInteraction A R))).IsSymmetricProjection := by
  classical
  have hp := Matrix.isPositive_toEuclideanLin_iff.mpr
    (regionLocalTerm_posSemidef R (canonicalRegionParentInteraction_posSemidef A R))
  refine ⟨?_, hp.isSymmetric⟩
  have h := congrArg Matrix.toEuclideanLin (regionLocalTerm_canonical_isIdempotentElem A R).eq
  rw [Matrix.toLpLin_mul 2 2 2] at h
  exact h

/-- The lifted canonical projector has unit norm gap on its excitation space.
Source: CPGSV21, arXiv:2011.12127, projector parent interactions, line 2170. -/
theorem regionLocalTerm_canonical_unit_norm_gap (A : Tensor Γ d) (R : Finset V) :
    ∀ ψ ∈ (Matrix.toEuclideanLin
      (regionLocalTerm R (canonicalRegionParentInteraction A R))).kerᗮ,
      (1 : ℝ) * ‖ψ‖ ≤ ‖Matrix.toEuclideanLin
        (regionLocalTerm R (canonicalRegionParentInteraction A R)) ψ‖ := by
  classical
  intro ψ hψ
  have hP := regionLocalTerm_canonical_isSymmetricProjection A R
  rw [← hP.isSymmetric.orthogonal_range, Submodule.orthogonal_orthogonal] at hψ
  rw [(LinearMap.IsIdempotentElem.mem_range_iff hP.isIdempotentElem).mp hψ, one_mul]

end TNLean.PEPS
