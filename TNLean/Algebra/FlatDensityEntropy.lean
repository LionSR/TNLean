/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Entropy

/-!
# Entropy of a density operator with flat spectrum

A positive semidefinite matrix `ρ` of trace one satisfying `ρ² = r⁻¹ ρ` has eigenvalues
`0` and `r⁻¹`. Consequently its von Neumann entropy is `log r`.

This elementary spectral calculation is the last step of Schuch, Cirac, and
Pérez-García, arXiv:1001.3807, Theorem 6.9 (`Papers/1001.3807/paper_v3.tex`,
lines 2062–2072), for the regular boundary density operator.
-/

open scoped BigOperators Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Hermitian quadratic flatness identity forces every eigenvalue to be zero
or the reciprocal flatness parameter. Source: SCP10, lines 2062–2072. -/
theorem Matrix.IsHermitian.eigenvalues_eq_zero_or_inv_of_mul_self_eq_inv_smul
    {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian)
    {r : ℝ} (hflat : ρ * ρ = (r : ℂ)⁻¹ • ρ) (i : ι) :
    hρ.eigenvalues i = 0 ∨ hρ.eigenvalues i = r⁻¹ := by
  let v : ι → ℂ := hρ.eigenvectorBasis i
  have hv : v ≠ 0 :=
    (WithLp.ofLp_eq_zero 2).ne.2 (hρ.eigenvectorBasis.orthonormal.ne_zero i)
  have heig : ρ *ᵥ v = (hρ.eigenvalues i : ℂ) • v := by
    simpa only [v, RCLike.real_smul_eq_coe_smul (K := ℂ)] using! hρ.mulVec_eigenvectorBasis i
  have h := congrArg (fun A => A *ᵥ v) hflat
  rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, heig, Matrix.mulVec_smul, heig,
    smul_smul, smul_smul] at h
  have hscalar := (smul_left_injective ℂ hv) h
  have hreal : hρ.eigenvalues i * hρ.eigenvalues i = r⁻¹ * hρ.eigenvalues i := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_mul, Complex.ofReal_inv] using hscalar
  have hz : hρ.eigenvalues i * (hρ.eigenvalues i - r⁻¹) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hz with hz | hz
  · exact Or.inl hz
  · exact Or.inr (sub_eq_zero.mp hz)

/-- A trace-one positive semidefinite matrix satisfying `ρ² = r⁻¹ ρ` has entropy `log r`.
Source: arXiv:1001.3807, the flat-spectrum entropy calculation in the proof of Theorem 6.9,
lines 2062–2072. -/
theorem vonNeumannEntropy_of_mul_self_eq_inv_smul {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) {r : ℝ}
    (hflat : ρ * ρ = (r : ℂ)⁻¹ • ρ) : vonNeumannEntropy ρ hρ.isHermitian = Real.log r := by
  have hsum := posSemidef_trace_one_eigenvalues_sum_one hρ htr
  have hterm (i : ι) :
      Real.negMulLog (hρ.isHermitian.eigenvalues i) =
        hρ.isHermitian.eigenvalues i * Real.log r := by
    rcases hρ.isHermitian.eigenvalues_eq_zero_or_inv_of_mul_self_eq_inv_smul hflat i with hi | hi
    · simp only [hi, Real.negMulLog_zero, zero_mul]
    · rw [hi, Real.negMulLog, Real.log_inv]
      ring
  change (∑ i, Real.negMulLog (hρ.isHermitian.eigenvalues i)) = Real.log r
  simp_rw [hterm]
  rw [← Finset.sum_mul, hsum, one_mul]
