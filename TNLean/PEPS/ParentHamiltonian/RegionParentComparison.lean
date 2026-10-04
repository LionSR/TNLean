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

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
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

/-- Extending a regional operator by the identity commutes with subtraction.
Source: CPGSV21, arXiv:2011.12127, local extensions, lines 2003–2011. -/
theorem regionLocalTerm_sub (R : Finset V)
    (h k : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ) :
    regionLocalTerm R (h - k) = regionLocalTerm R h - regionLocalTerm R k := by
  classical
  ext σ τ
  simp [regionLocalTerm, sub_mul]

/-- Extending a regional operator by the identity commutes with scalar multiplication.
Source: CPGSV21, arXiv:2011.12127, local extensions, lines 2003–2011. -/
theorem regionLocalTerm_smul (R : Finset V) (z : ℂ)
    (h : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ) :
    regionLocalTerm R (z • h) = z • regionLocalTerm R h := by
  classical
  ext σ τ
  simp [regionLocalTerm, mul_assoc]

/-- Extending regional operators by the identity preserves Loewner order.
Source: CPGSV21, arXiv:2011.12127, positive regional extensions, lines 2003–2011. -/
theorem regionLocalTerm_mono (R : Finset V)
    {h k : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ} (hhk : h ≤ k) :
    regionLocalTerm R h ≤ regionLocalTerm R k := by
  rw [Matrix.le_iff, ← regionLocalTerm_sub]
  exact regionLocalTerm_posSemidef R hhk

variable {ι : Type*} [Fintype ι]

/-- Common regional comparison constants also compare the full Hamiltonians.
Source: CPGSV21, arXiv:2011.12127, comparison with projections, line 2170,
and the PEPS parent sum, lines 2003–2011. -/
theorem regionParentHamiltonian_comparison (R : ι → Finset V)
    (h k : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ) (κ C : ℝ)
    (hLower : ∀ i, (κ : ℂ) • k i ≤ h i)
    (hUpper : ∀ i, h i ≤ (C : ℂ) • k i) :
    (κ : ℂ) • regionParentHamiltonian R k ≤ regionParentHamiltonian R h ∧
    regionParentHamiltonian R h ≤ (C : ℂ) • regionParentHamiltonian R k := by
  constructor
  · simp only [regionParentHamiltonian, Finset.smul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [regionLocalTerm_smul] using regionLocalTerm_mono (R i) (hLower i)
  · simp only [regionParentHamiltonian, Finset.smul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [regionLocalTerm_smul] using regionLocalTerm_mono (R i) (hUpper i)

private theorem smul_mono_of_posSemidef {n : Type*} {P : Matrix n n ℂ}
    (hP : P.PosSemidef) {a b : ℝ} (hab : a ≤ b) : (a : ℂ) • P ≤ (b : ℂ) • P := by
  rw [Matrix.le_iff, ← sub_smul, ← Complex.ofReal_sub]
  exact hP.smul (by exact_mod_cast sub_nonneg.mpr hab)

private theorem smul_le_smul_of_nonneg {n : Type*} {H K : Matrix n n ℂ}
    (hHK : H ≤ K) {a : ℝ} (ha : 0 ≤ a) : (a : ℂ) • H ≤ (a : ℂ) • K := by
  rw [Matrix.le_iff, ← smul_sub]
  exact hHK.smul (by exact_mod_cast ha)

/-- A finite collection of positive regional parent interactions has common
strictly positive comparison constants with the sum of canonical projectors.
Source: CPGSV21, arXiv:2011.12127, line 2170 and lines 2003–2011. -/
theorem exists_pos_regionParentHamiltonian_comparison (A : Tensor Γ d)
    (R : ι → Finset V)
    (h : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hh : ∀ i, IsRegionParentInteraction A (R i) (h i)) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧
      (κ : ℂ) • regionParentHamiltonian R (fun i => canonicalRegionParentInteraction A (R i)) ≤
        regionParentHamiltonian R h ∧
      regionParentHamiltonian R h ≤
        (C : ℂ) • regionParentHamiltonian R
          (fun i => canonicalRegionParentInteraction A (R i)) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, 1, zero_lt_one, zero_lt_one, by simp [regionParentHamiltonian]⟩
  · choose κ C hκ hC hLower hUpper using fun i => (hh i).exists_pos_comparison
    obtain ⟨iMin, _, hMin⟩ := Finset.exists_min_image Finset.univ κ Finset.univ_nonempty
    obtain ⟨iMax, _, hMax⟩ := Finset.exists_max_image Finset.univ C Finset.univ_nonempty
    refine ⟨κ iMin, C iMax, hκ iMin, hC iMax, ?_⟩
    apply regionParentHamiltonian_comparison
    · intro i
      exact (smul_mono_of_posSemidef (canonicalRegionParentInteraction_posSemidef A (R i))
        (hMin i (Finset.mem_univ i))).trans (hLower i)
    · intro i
      exact (hUpper i).trans
        (smul_mono_of_posSemidef (canonicalRegionParentInteraction_posSemidef A (R i))
          (hMax i (Finset.mem_univ i)))

/-- Any two positive PEPS parents on the same finite family of regions bound
one another by strictly positive constants. Source: CPGSV21,
arXiv:2011.12127, comparison with projections, line 2170. -/
theorem exists_pos_regionParentHamiltonian_comparison_between (A : Tensor Γ d)
    (R : ι → Finset V)
    (h k : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hh : ∀ i, IsRegionParentInteraction A (R i) (h i))
    (hk : ∀ i, IsRegionParentInteraction A (R i) (k i)) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧
      (κ : ℂ) • regionParentHamiltonian R k ≤ regionParentHamiltonian R h ∧
      regionParentHamiltonian R h ≤ (C : ℂ) • regionParentHamiltonian R k := by
  obtain ⟨κh, Ch, hκh, hCh, hLowerH, hUpperH⟩ :=
    exists_pos_regionParentHamiltonian_comparison A R h hh
  obtain ⟨κk, Ck, hκk, hCk, hLowerK, hUpperK⟩ :=
    exists_pos_regionParentHamiltonian_comparison A R k hk
  refine ⟨κh / Ck, Ch / κk, div_pos hκh hCk, div_pos hCh hκk, ?_, ?_⟩
  · calc
      ((κh / Ck : ℝ) : ℂ) • regionParentHamiltonian R k ≤
          ((κh / Ck : ℝ) : ℂ) • ((Ck : ℂ) • regionParentHamiltonian R
            (fun i => canonicalRegionParentInteraction A (R i))) :=
        smul_le_smul_of_nonneg hUpperK (div_nonneg hκh.le hCk.le)
      _ = (κh : ℂ) • regionParentHamiltonian R
          (fun i => canonicalRegionParentInteraction A (R i)) := by
        rw [smul_smul, ← Complex.ofReal_mul, div_mul_cancel₀ _ hCk.ne']
      _ ≤ regionParentHamiltonian R h := hLowerH
  · calc
      regionParentHamiltonian R h ≤ (Ch : ℂ) • regionParentHamiltonian R
          (fun i => canonicalRegionParentInteraction A (R i)) := hUpperH
      _ = ((Ch / κk : ℝ) : ℂ) • ((κk : ℂ) • regionParentHamiltonian R
          (fun i => canonicalRegionParentInteraction A (R i))) := by
        rw [smul_smul, ← Complex.ofReal_mul, div_mul_cancel₀ _ hκk.ne']
      _ ≤ ((Ch / κk : ℝ) : ℂ) • regionParentHamiltonian R k :=
        smul_le_smul_of_nonneg hLowerK (div_nonneg hCh.le hκk.le)

/-- Changing the positive regional interactions leaves the full Euclidean
ground space unchanged. Source: CPGSV21, arXiv:2011.12127, prescribed parent
kernels and frustration freeness, lines 2003–2011. -/
theorem ker_toEuclideanLin_regionParentHamiltonian_eq (A : Tensor Γ d)
    (R : ι → Finset V)
    (h k : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hh : ∀ i, IsRegionParentInteraction A (R i) (h i))
    (hk : ∀ i, IsRegionParentInteraction A (R i) (k i)) :
    (Matrix.toEuclideanLin (regionParentHamiltonian R h)).ker =
      (Matrix.toEuclideanLin (regionParentHamiltonian R k)).ker := by
  classical
  ext ψ
  have heq := (ker_regionParentHamiltonian A R h hh).trans
    (ker_regionParentHamiltonian A R k hk).symm
  have hmem := congrArg (fun S => WithLp.ofLp ψ ∈ S) heq
  simpa [LinearMap.mem_ker, Matrix.toEuclideanLin, Matrix.toLpLin] using hmem

/-- A Loewner lower comparison transfers a spectral norm gap between two PEPS
parents with the same regional kernels. The transferred gap is multiplied by
the lower comparison constant. This is the finite-dimensional consequence of
CPGSV21, arXiv:2011.12127, comparison with projections, line 2170. -/
theorem regionParentHamiltonian_norm_gap_of_comparison (A : Tensor Γ d)
    (R : ι → Finset V)
    (h k : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hh : ∀ i, IsRegionParentInteraction A (R i) (h i))
    (hk : ∀ i, IsRegionParentInteraction A (R i) (k i))
    {κ γ : ℝ} (hκ : 0 < κ) (hγ : 0 ≤ γ)
    (hLower : (κ : ℂ) • regionParentHamiltonian R k ≤ regionParentHamiltonian R h)
    (hGap : ∀ ψ ∈ (Matrix.toEuclideanLin (regionParentHamiltonian R k)).kerᗮ,
      γ * ‖ψ‖ ≤ ‖Matrix.toEuclideanLin (regionParentHamiltonian R k) ψ‖) :
    ∀ ψ ∈ (Matrix.toEuclideanLin (regionParentHamiltonian R h)).kerᗮ,
      (κ * γ) * ‖ψ‖ ≤ ‖Matrix.toEuclideanLin (regionParentHamiltonian R h) ψ‖ := by
  classical
  have hp := Matrix.isPositive_toEuclideanLin_iff.mpr
    (regionParentHamiltonian_posSemidef R k (fun i => (hk i).1))
  have hκ0 : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ.ne'
  have hpos := hp.smul_of_nonneg (c := (κ : ℂ)) (by exact_mod_cast hκ.le)
  have hle : (κ : ℂ) • Matrix.toEuclideanLin (regionParentHamiltonian R k) ≤
      Matrix.toEuclideanLin (regionParentHamiltonian R h) := by
    rw [LinearMap.le_def]
    simpa only [map_sub, map_smul] using
      Matrix.isPositive_toEuclideanLin_iff.mpr (Matrix.le_iff.mp hLower)
  have hker := (LinearMap.ker_smul _ (κ : ℂ) hκ0).trans
    (ker_toEuclideanLin_regionParentHamiltonian_eq A R k h hk hh)
  apply hpos.norm_gap_of_le_of_ker_eq (mul_nonneg hκ.le hγ) hle hker
  intro ψ hψ
  rw [LinearMap.ker_smul _ (κ : ℂ) hκ0] at hψ
  simpa only [LinearMap.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hκ, mul_assoc] using mul_le_mul_of_nonneg_left (hGap ψ hψ) hκ.le

/-- On a fixed finite region collection, existence of a positive norm gap on
the orthogonal complement of the ground space is independent of the choice
of positive parent interactions. The comparison constants may depend on the
interactions and the collection. Source: CPGSV21, arXiv:2011.12127,
comparison with projections, line 2170. -/
theorem regionParentHamiltonian_has_pos_norm_gap_iff (A : Tensor Γ d)
    (R : ι → Finset V)
    (h k : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hh : ∀ i, IsRegionParentInteraction A (R i) (h i))
    (hk : ∀ i, IsRegionParentInteraction A (R i) (k i)) :
    (∃ γ : ℝ, 0 < γ ∧
      ∀ ψ ∈ (Matrix.toEuclideanLin (regionParentHamiltonian R h)).kerᗮ,
        γ * ‖ψ‖ ≤ ‖Matrix.toEuclideanLin (regionParentHamiltonian R h) ψ‖) ↔
    (∃ γ : ℝ, 0 < γ ∧
      ∀ ψ ∈ (Matrix.toEuclideanLin (regionParentHamiltonian R k)).kerᗮ,
        γ * ‖ψ‖ ≤ ‖Matrix.toEuclideanLin (regionParentHamiltonian R k) ψ‖) := by
  constructor
  · rintro ⟨γ, hγ, hGap⟩
    obtain ⟨κ, C, hκ, hC, hLower, hUpper⟩ :=
      exists_pos_regionParentHamiltonian_comparison_between A R k h hk hh
    exact ⟨κ * γ, mul_pos hκ hγ,
      regionParentHamiltonian_norm_gap_of_comparison A R k h hk hh hκ hγ.le hLower hGap⟩
  · rintro ⟨γ, hγ, hGap⟩
    obtain ⟨κ, C, hκ, hC, hLower, hUpper⟩ :=
      exists_pos_regionParentHamiltonian_comparison_between A R h k hh hk
    exact ⟨κ * γ, mul_pos hκ hγ,
      regionParentHamiltonian_norm_gap_of_comparison A R h k hh hk hκ hγ.le hLower hGap⟩

end TNLean.PEPS
