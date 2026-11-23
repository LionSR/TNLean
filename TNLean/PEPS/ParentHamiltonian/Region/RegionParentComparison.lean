/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.Region.RegionParentInteraction
import TNLean.MPS.ParentHamiltonian.ParentInteraction.FiniteIntervalGapComparison

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

variable {ι : Type*} [Fintype ι]

/-- Common regional comparison constants also compare the full Hamiltonians.
Source: CPGSV21, arXiv:2011.12127, comparison with projections, line 2170,
and the PEPS parent sum, lines 2003–2011. -/
theorem hamiltonian_ofPlace_comparison (R : ι → Finset V)
    (h k : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ) (κ C : ℝ)
    (hLower : ∀ i, (κ : ℂ) • k i ≤ h i)
    (hUpper : ∀ i, h i ≤ (C : ℂ) • k i) :
    (κ : ℂ) • (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R k).hamiltonian ≤
        (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).hamiltonian ∧
      (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).hamiltonian ≤
        (C : ℂ) • (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R k).hamiltonian := by
  constructor
  · simp only [ManyBody.Interaction.hamiltonian_ofPlace, Finset.smul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [ManyBody.place_smul] using ManyBody.place_le_place (X := fun _ ↦ Fin _) (hLower i)
  · simp only [ManyBody.Interaction.hamiltonian_ofPlace, Finset.smul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [ManyBody.place_smul] using ManyBody.place_le_place (X := fun _ ↦ Fin _) (hUpper i)

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
theorem exists_pos_hamiltonian_ofPlace_comparison (A : Tensor Γ d)
    (R : ι → Finset V)
    (h : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hh : ∀ i, IsRegionParentInteraction A (R i) (h i)) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧
      (κ : ℂ) • (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R
          (fun i => canonicalRegionParentInteraction A (R i))).hamiltonian ≤
        (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).hamiltonian ∧
      (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).hamiltonian ≤
        (C : ℂ) • (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R
          (fun i => canonicalRegionParentInteraction A (R i))).hamiltonian := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, 1, zero_lt_one, zero_lt_one, by simp [ManyBody.Interaction.hamiltonian_ofPlace]⟩
  · choose κ C hκ hC hLower hUpper using fun i => (hh i).exists_pos_comparison
    obtain ⟨iMin, _, hMin⟩ := Finset.exists_min_image Finset.univ κ Finset.univ_nonempty
    obtain ⟨iMax, _, hMax⟩ := Finset.exists_max_image Finset.univ C Finset.univ_nonempty
    refine ⟨κ iMin, C iMax, hκ iMin, hC iMax, ?_⟩
    apply hamiltonian_ofPlace_comparison
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
theorem exists_pos_hamiltonian_ofPlace_comparison_between (A : Tensor Γ d)
    (R : ι → Finset V)
    (h k : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hh : ∀ i, IsRegionParentInteraction A (R i) (h i))
    (hk : ∀ i, IsRegionParentInteraction A (R i) (k i)) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧
      (κ : ℂ) • (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R k).hamiltonian ≤
          (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).hamiltonian ∧
        (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).hamiltonian ≤
          (C : ℂ) • (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R k).hamiltonian := by
  obtain ⟨κh, Ch, hκh, hCh, hLowerH, hUpperH⟩ :=
    exists_pos_hamiltonian_ofPlace_comparison A R h hh
  obtain ⟨κk, Ck, hκk, hCk, hLowerK, hUpperK⟩ :=
    exists_pos_hamiltonian_ofPlace_comparison A R k hk
  refine ⟨κh / Ck, Ch / κk, div_pos hκh hCk, div_pos hCh hκk, ?_, ?_⟩
  · calc
      ((κh / Ck : ℝ) : ℂ) • (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R k).hamiltonian ≤
          ((κh / Ck : ℝ) : ℂ) • ((Ck : ℂ) • (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R
            (fun i => canonicalRegionParentInteraction A (R i))).hamiltonian) :=
        smul_le_smul_of_nonneg hUpperK (div_nonneg hκh.le hCk.le)
      _ = (κh : ℂ) • (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R
          (fun i => canonicalRegionParentInteraction A (R i))).hamiltonian := by
        rw [smul_smul, ← Complex.ofReal_mul, div_mul_cancel₀ _ hCk.ne']
      _ ≤ (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).hamiltonian := hLowerH
  · calc
      (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).hamiltonian ≤
          (Ch : ℂ) • (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R
            (fun i => canonicalRegionParentInteraction A (R i))).hamiltonian := hUpperH
      _ = ((Ch / κk : ℝ) : ℂ) • ((κk : ℂ) • (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R
          (fun i => canonicalRegionParentInteraction A (R i))).hamiltonian) := by
        rw [smul_smul, ← Complex.ofReal_mul, div_mul_cancel₀ _ hκk.ne']
      _ ≤ ((Ch / κk : ℝ) : ℂ) •
          (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R k).hamiltonian :=
        smul_le_smul_of_nonneg hLowerK (div_nonneg hCh.le hκk.le)

/-- Changing the positive regional interactions leaves the full Euclidean
ground space unchanged. Source: CPGSV21, arXiv:2011.12127, prescribed parent
kernels and frustration freeness, lines 2003–2011. -/
theorem ker_toEuclideanLin_hamiltonian_ofPlace_eq (A : Tensor Γ d)
    (R : ι → Finset V)
    (h k : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hh : ∀ i, IsRegionParentInteraction A (R i) (h i))
    (hk : ∀ i, IsRegionParentInteraction A (R i) (k i)) :
    (Matrix.toEuclideanLin
        (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).hamiltonian).ker =
      (Matrix.toEuclideanLin
        (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R k).hamiltonian).ker := by
  classical
  ext ψ
  have heq := (ker_hamiltonian_ofPlace A R h hh).trans
    (ker_hamiltonian_ofPlace A R k hk).symm
  have hmem := congrArg (fun S => WithLp.ofLp ψ ∈ S) heq
  simpa [LinearMap.mem_ker, Matrix.toEuclideanLin, Matrix.toLpLin] using hmem

/-- A Loewner lower comparison transfers a spectral gap between two PEPS parents
with the same regional kernels: if every eigenvalue of \(H_k\) other than \(0\) is
at least \(γ\) and \(κ H_k ≤ H_h\) with \(κ > 0\), then every eigenvalue of \(H_h\)
other than \(0\) is at least \(κ γ\). This is the finite-dimensional consequence of
CPGSV21, arXiv:2011.12127, comparison with projections, line 2170. -/
theorem forall_hasEigenvalue_hamiltonian_ofPlace_of_comparison (A : Tensor Γ d)
    (R : ι → Finset V)
    (h k : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hh : ∀ i, IsRegionParentInteraction A (R i) (h i))
    (hk : ∀ i, IsRegionParentInteraction A (R i) (k i))
    {κ γ : ℝ} (hκ : 0 < κ)
    (hLower : (κ : ℂ) • (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R k).hamiltonian ≤
      (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).hamiltonian)
    (hGap : ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R k).hamiltonian) μ →
      μ = 0 ∨ (γ : ℂ) ≤ μ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h).hamiltonian) μ →
      μ = 0 ∨ ((κ * γ : ℝ) : ℂ) ≤ μ := by
  classical
  have hHk := ManyBody.Interaction.posSemidef_hamiltonian
    (Φ := ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R k)
    fun i ↦ ManyBody.posSemidef_place (X := fun _ ↦ Fin _) (hk i).1
  have hHh := ManyBody.Interaction.posSemidef_hamiltonian
    (Φ := ManyBody.Interaction.ofPlace (X := fun _ ↦ Fin d) R h)
    fun i ↦ ManyBody.posSemidef_place (X := fun _ ↦ Fin _) (hh i).1
  rw [ManyBody.forall_hasEigenvalue_iff_re_inner hHk] at hGap
  rw [ManyBody.forall_hasEigenvalue_iff_re_inner hHh]
  intro v hv
  rw [ker_toEuclideanLin_hamiltonian_ofPlace_eq A R h k hh hk] at hv
  have hD := (Matrix.isPositive_toEuclideanLin_iff.mpr
    (Matrix.le_iff.mp hLower)).re_inner_nonneg_right v
  rw [map_sub, LinearMap.sub_apply, inner_sub_right, map_smul, LinearMap.smul_apply,
    inner_smul_right, map_sub, RCLike.re_to_complex, RCLike.re_to_complex,
    Complex.re_ofReal_mul, sub_nonneg] at hD
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left (hGap v hv) hκ.le).trans hD

end TNLean.PEPS
