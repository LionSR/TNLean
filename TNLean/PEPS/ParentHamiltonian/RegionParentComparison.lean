/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionParentHamiltonian
import TNLean.MPS.ParentHamiltonian.Martingale.FiniteIntervalGapComparison

/-!
# Comparison of regional PEPS parent interactions

On a fixed finite region, every positive parent interaction is bounded above
and below by positive multiples of the canonical orthogonal projector. Extending
the interactions by the identity and adding them preserves these comparisons.
The constants for a finite family depend on the local interactions.

This is the finite-dimensional comparison described in CPGSV21,
arXiv:2011.12127, line 2170, applied to the PEPS parent interactions of
Section IV.C.1, lines 2003–2011. No bound uniform in the number of sites is asserted.
-/

open scoped BigOperators Kronecker ComplexOrder Matrix MatrixOrder

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- Euclidean coordinates preserve the prescribed regional kernel.
Source: CPGSV21, arXiv:2011.12127, regional kernels, lines 2003–2011. -/
theorem IsRegionParentInteraction.ker_toEuclideanLin
    {A : Tensor Γ d} {R : Finset V}
    {h : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ}
    (hh : IsRegionParentInteraction A R h) :
    (Matrix.toEuclideanLin h).ker = regionGroundSpaceES A R := by
  classical
  ext ψ
  rw [regionGroundSpaceES, ← hh.2]
  simp [LinearMap.mem_ker, Matrix.toEuclideanLin, Matrix.toLpLin]

/-- A positive regional parent interaction bounds, and is bounded by, positive
multiples of the canonical parent projector. Source: CPGSV21,
arXiv:2011.12127, comparison with projections, line 2170. -/
theorem IsRegionParentInteraction.exists_pos_comparison
    {A : Tensor Γ d} {R : Finset V}
    {h : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ}
    (hh : IsRegionParentInteraction A R h) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧
      (κ : ℂ) • canonicalRegionParentInteraction A R ≤ h ∧
      h ≤ (C : ℂ) • canonicalRegionParentInteraction A R := by
  classical
  have hp := Matrix.isPositive_toEuclideanLin_iff.mpr hh.1
  obtain ⟨κ, hκ, hLower⟩ := hp.exists_pos_smul_orthogonal_ker_projection_le
  obtain ⟨C, hC, hUpper⟩ := hp.exists_pos_le_smul_orthogonal_ker_projection
  refine ⟨κ, C, hκ, hC, ?_, ?_⟩
  · rw [Matrix.le_iff, ← Matrix.isPositive_toEuclideanLin_iff]
    simpa only [map_sub, map_smul, canonicalRegionParentInteraction,
      LinearEquiv.apply_symm_apply, hh.ker_toEuclideanLin] using
      LinearMap.le_def.mp hLower
  · rw [Matrix.le_iff, ← Matrix.isPositive_toEuclideanLin_iff]
    simpa only [map_sub, map_smul, canonicalRegionParentInteraction,
      LinearEquiv.apply_symm_apply, hh.ker_toEuclideanLin] using
      LinearMap.le_def.mp hUpper

end TNLean.PEPS
