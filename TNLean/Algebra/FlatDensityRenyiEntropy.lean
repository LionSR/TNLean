/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FlatDensityEntropy
import QICLean.Analysis.TraceCFC

/-!
# Rényi entropies of a flat density

For positive order different from one, the Rényi entropy is defined by the
spectral trace of the real power of the density. Order one is the von Neumann
entropy, and order zero is the logarithm of the rank. A flat trace-one density
has the same entropy at every nonnegative finite order.

Source: SCP10, arXiv:1001.3807, lines 2027–2037 and 2062–2072. These are spectral
matrix identities; they do not assert a PEPS boundary factorization.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The finite-order Rényi entropy, with the standard rank convention at zero
and von Neumann convention at one. For positive order away from one the real
power is the Hermitian spectral functional calculus. -/
noncomputable def renyiEntropy (ρ : Matrix ι ι ℂ) (hρ : ρ.IsHermitian) (α : ℝ) : ℝ :=
  if α = 0 then Real.log (ρ.rank : ℝ)
  else if α = 1 then vonNeumannEntropy ρ hρ
  else (1 - α)⁻¹ * Real.log ((hρ.cfc (fun x => x ^ α)).trace.re)

/-- The trace of a positive spectral power of a flat density is `r^(1-α)`.
Source: SCP10, lines 2027–2037 and 2062–2072. -/
theorem trace_cfc_rpow_of_mul_self_eq_inv_smul {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) {r α : ℝ} (hr : 0 < r) (hα : 0 < α)
    (hflat : ρ * ρ = (r : ℂ)⁻¹ • ρ) :
    (hρ.isHermitian.cfc (fun x => x ^ α)).trace.re = r ^ (1 - α) := by
  have hsum := posSemidef_trace_one_eigenvalues_sum_one hρ htr
  have hterm i : hρ.isHermitian.eigenvalues i ^ α =
      hρ.isHermitian.eigenvalues i * r ^ (1 - α) := by
    rcases hρ.isHermitian.eigenvalues_eq_zero_or_inv_of_mul_self_eq_inv_smul hflat i with hi | hi
    · simp only [hi, Real.zero_rpow hα.ne', zero_mul]
    · rw [hi, ← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_neg_one,
        ← Real.rpow_add hr]
      congr 1
      ring
  change RCLike.re ((hρ.isHermitian.cfc (fun x => x ^ α)).trace) = _
  rw [hρ.isHermitian.trace_cfc_eq_sum_re]
  simp_rw [hterm]
  rw [← Finset.sum_mul, hsum, one_mul]

/-- Every positive finite Rényi order of a flat trace-one density equals `log r`.
Source: SCP10, lines 2027–2037 and 2062–2072. -/
theorem renyiEntropy_of_mul_self_eq_inv_smul {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) {r α : ℝ} (hr : 0 < r) (hα : 0 < α)
    (hflat : ρ * ρ = (r : ℂ)⁻¹ • ρ) :
    renyiEntropy ρ hρ.isHermitian α = Real.log r := by
  by_cases hα1 : α = 1
  · simp only [renyiEntropy, hα1, one_ne_zero, ↓reduceIte]
    exact vonNeumannEntropy_of_mul_self_eq_inv_smul hρ htr hflat
  · simp only [renyiEntropy, hα.ne', hα1, ↓reduceIte]
    rw [trace_cfc_rpow_of_mul_self_eq_inv_smul hρ htr hr hα hflat, Real.log_rpow hr]
    rw [← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hα1)), one_mul]

/-- Including order zero, every nonnegative finite Rényi order of a flat density
is the logarithm of its rank. The rank identifies the zero-order convention.
Source: SCP10, lines 2027–2037 and 2062–2072. -/
theorem renyiEntropy_of_mul_self_eq_inv_smul_of_rank {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) {r α : ℝ} (hr : 0 < r) (hα : 0 ≤ α)
    (hflat : ρ * ρ = (r : ℂ)⁻¹ • ρ) (hrank : (ρ.rank : ℝ) = r) :
    renyiEntropy ρ hρ.isHermitian α = Real.log r := by
  rcases hα.eq_or_lt with hα0 | hαpos
  · simp only [← hα0, renyiEntropy, ↓reduceIte, hrank]
  · exact renyiEntropy_of_mul_self_eq_inv_smul hρ htr hr hαpos hflat
