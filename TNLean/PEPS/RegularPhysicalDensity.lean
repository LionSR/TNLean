/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularPhysicalCutTransfer
import TNLean.Algebra.FlatDensityEntropy

/-!
# Reduced densities under supported physical maps

A physical map with positive scalar Gram on the support of a density preserves
its normalized spectrum. The unused physical directions cause no obstruction.
The hypotheses below are finite matrix identities; in the actual PEPS cut they
are derived from local G-isometry and the canonical invariant support.

Source: SCP10, arXiv:1001.3807, accessible virtual coordinates and the boundary
entropy calculation, local source lines 1765–1820 and 2043–2072.
-/

open scoped Matrix ComplexOrder

namespace TNLean.PEPS

variable {ι α : Type*} [Fintype ι] [Fintype α]

/-- The normalized physical image of a density supported where the physical
map has Gram scalar `c`. Source: SCP10, lines 1765–1820 and 2043–2072. -/
noncomputable def normalizedPhysicalImageDensity (c : ℝ) (T : Matrix α ι ℂ)
    (ρ : Matrix ι ι ℂ) : Matrix α α ℂ :=
  (c : ℂ)⁻¹ • (T * ρ * T.conjTranspose)

/-- A positive scalar Gram on the density's support preserves positivity,
trace, rank, and a flat spectrum. Source: SCP10, lines 1765–1820 and 2043–2072. -/
theorem normalizedPhysicalImageDensity_properties
    (T : Matrix α ι ℂ) (ρ : Matrix ι ι ℂ) (c : ℝ) (hc : 0 < c)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hGram : (T.conjTranspose * T) * ρ = (c : ℂ) • ρ)
    (r : ℝ) (hflat : ρ * ρ = (r : ℂ)⁻¹ • ρ) :
    (normalizedPhysicalImageDensity c T ρ).PosSemidef ∧
      (normalizedPhysicalImageDensity c T ρ).trace = 1 ∧
      (normalizedPhysicalImageDensity c T ρ).rank = ρ.rank ∧
      normalizedPhysicalImageDensity c T ρ * normalizedPhysicalImageDensity c T ρ =
        (r : ℂ)⁻¹ • normalizedPhysicalImageDensity c T ρ := by
  classical
  have hcn : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  have hright : ρ * (T.conjTranspose * T) = (c : ℂ) • ρ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hρ.isHermitian.eq, Matrix.conjTranspose_smul, Complex.star_def,
      Complex.conj_ofReal] using congrArg Matrix.conjTranspose hGram
  have hrestore : T.conjTranspose * normalizedPhysicalImageDensity c T ρ * T =
      (c : ℂ) • ρ := by
    simp only [normalizedPhysicalImageDensity, Matrix.mul_smul, Matrix.smul_mul]
    calc
      _ = (c : ℂ)⁻¹ • (((T.conjTranspose * T) * ρ) * (T.conjTranspose * T)) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hGram, Matrix.smul_mul, hright, smul_smul]
        field_simp
        simp only [one_smul]
  have hscale : (c : ℂ)⁻¹ • (T.conjTranspose *
      normalizedPhysicalImageDensity c T ρ * T) = ρ := by
    rw [hrestore, smul_smul, inv_mul_cancel₀ hcn, one_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hρ.mul_mul_conjTranspose_same T).smul (show (0 : ℂ) ≤ (c : ℂ)⁻¹ by
      exact_mod_cast inv_nonneg.mpr hc.le)
  · rw [normalizedPhysicalImageDensity, Matrix.trace_smul, Matrix.trace_mul_cycle,
      hGram, Matrix.trace_smul, htr]
    simp [hcn]
  · apply le_antisymm
    · rw [normalizedPhysicalImageDensity,
        Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero
          (inv_ne_zero hcn))]
      exact (Matrix.rank_mul_le_left (T * ρ) T.conjTranspose).trans
        (Matrix.rank_mul_le_right T ρ)
    · calc
        ρ.rank = ((c : ℂ)⁻¹ • (T.conjTranspose *
            normalizedPhysicalImageDensity c T ρ * T)).rank :=
          congrArg Matrix.rank hscale.symm
        _ = (T.conjTranspose * normalizedPhysicalImageDensity c T ρ * T).rank :=
          Matrix.rank_smul_of_mem_nonZeroDivisors _
            (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero hcn))
        _ ≤ (normalizedPhysicalImageDensity c T ρ).rank :=
          (Matrix.rank_mul_le_left _ T).trans (Matrix.rank_mul_le_right T.conjTranspose _)
  · simp only [normalizedPhysicalImageDensity, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
    have hmiddle : (T * ρ * T.conjTranspose) * (T * ρ * T.conjTranspose) =
        (c : ℂ) • (T * (ρ * ρ) * T.conjTranspose) := by
      calc
        _ = T * (ρ * ((T.conjTranspose * T) * ρ)) * T.conjTranspose := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hGram, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hmiddle, hflat, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    simp only [smul_smul]
    congr 1
    field_simp

/-- Supported physical transport leaves the flat-spectrum entropy unchanged.
Source: SCP10, boundary entropy calculation, lines 2043–2072. -/
theorem vonNeumannEntropy_normalizedPhysicalImageDensity [DecidableEq α]
    (T : Matrix α ι ℂ) (ρ : Matrix ι ι ℂ) (c : ℝ) (hc : 0 < c)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hGram : (T.conjTranspose * T) * ρ = (c : ℂ) • ρ)
    (r : ℝ) (hflat : ρ * ρ = (r : ℂ)⁻¹ • ρ) :
    vonNeumannEntropy (normalizedPhysicalImageDensity c T ρ)
        (normalizedPhysicalImageDensity_properties T ρ c hc hρ htr hGram r hflat).1.isHermitian =
      Real.log r := by
  have h := normalizedPhysicalImageDensity_properties T ρ c hc hρ htr hGram r hflat
  exact vonNeumannEntropy_of_mul_self_eq_inv_smul h.1 h.2.1 h.2.2.2

end TNLean.PEPS
