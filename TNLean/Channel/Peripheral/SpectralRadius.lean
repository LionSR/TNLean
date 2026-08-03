/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Determinant.Bound
import TNLean.Channel.PerronFrobenius.Existence

/-!
# Spectral radius of positive maps — Wolf Proposition 6.1

**Wolf Proposition 6.1**: For a positive trace-preserving (or unital) map
$T: M_d(\mathbb{C}) \to M_d(\mathbb{C})$, the spectral radius is $1$, all eigenvalues
lie in the unit disk, and $1$ is an eigenvalue.

The eigenvalue modulus bound $|\lambda| \le 1$ is provided by
`IsPositiveMap.eigenvalue_norm_le_one_of_tracePreserving` in
`TNLean.Channel.Determinant.Bound`.  Eigenvalue-$1$ existence is proved here
using the Perron--Frobenius theorem (`exists_posSemidef_eigenvector`) together
with trace preservation.

The general $\varrho(T) \le \|T(\mathbf 1)\|_\infty$ bound for arbitrary
positive maps relies on the Russo--Dye theorem and is documented in
`docs/paper-gaps/wolf_prop61_russo_dye_factor.tex`.

## Main result

* `IsPositiveMap.eigenvalue_one_exists_of_tracePreserving`:
  nonzero PSD fixed point for positive trace-preserving maps.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 6.1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder
open Matrix

variable {D : ℕ}

namespace IsPositiveMap

/-- **Wolf Proposition 6.1** (eigenvalue-1 existence): For a positive trace-preserving
map on $M_D(\mathbb{C})$ with $D > 0$, there exists a nonzero PSD matrix $\rho$
such that $T(\rho) = \rho$.

This completes the trace-preserving case of Wolf's Proposition 6.1:
combined with `eigenvalue_norm_le_one_of_tracePreserving` (which gives
$|\lambda| \le 1$ for every eigenvalue), we get that the spectral radius is $1$
and $1$ is an eigenvalue.

The proof obtains a PSD eigenvector with eigenvalue $r > 0$ via
`exists_posSemidef_eigenvector` (Perron--Frobenius / Brouwer fixed point),
then forces $r = 1$ by trace preservation.

Source: Wolf, *Quantum Channels & Operations*, Proposition 6.1; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 73--91. -/
theorem eigenvalue_one_exists_of_tracePreserving
    [NeZero D] {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.PosSemidef ∧ ρ ≠ 0 ∧ T ρ = ρ := by
  -- For a trace-preserving positive map, nonzero PSD matrices cannot be annihilated
  -- (otherwise their trace would be 0, contradicting positivity)
  have hNZ : ∀ {ρ : Matrix (Fin D) (Fin D) ℂ}, ρ.PosSemidef → ρ ≠ 0 → T ρ ≠ 0 := by
    intro ρ hρ_psd hρ_ne hzero
    have htr_zero : trace (T ρ) = 0 := by simp [hzero]
    rw [hTP ρ] at htr_zero
    have htr_pos : 0 < trace ρ := by
      have h_nonneg := hρ_psd.trace_nonneg
      have h_ne_zero : trace ρ ≠ 0 := mt hρ_psd.trace_eq_zero_iff.mp hρ_ne
      exact h_nonneg.lt_of_ne h_ne_zero.symm
    linarith
  -- Get eigenvalue r > 0 with PSD eigenvector (Perron--Frobenius)
  obtain ⟨ρ, r, hρ_psd, hρ_ne, hr_pos, h_eig⟩ :=
    exists_posSemidef_eigenvector (D := D) T hPos (hNZ := hNZ)
  -- Trace preservation forces r = 1
  have hr_one : r = 1 := by
    have htr_eq : trace (T ρ) = trace ρ := hTP ρ
    rw [h_eig, trace_smul, smul_eq_mul] at htr_eq
    have htr_ne_zero : trace ρ ≠ 0 := mt hρ_psd.trace_eq_zero_iff.mp hρ_ne
    field_simp [htr_ne_zero] at htr_eq
    exact_mod_cast htr_eq
  refine ⟨ρ, hρ_psd, hρ_ne, ?_⟩
  simpa [hr_one, one_smul] using h_eig

end IsPositiveMap
