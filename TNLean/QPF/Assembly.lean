/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.QPF.PosDef
import TNLean.QPF.Uniqueness
import TNLean.MPS.Core.CPPrimitive
-- Needed for `IsChannel.exists_posSemidef_fixedPoint`.
-- The fixed-point existence theorem is used explicitly below.
import TNLean.Channel.FixedPoint.Cesaro

/-!
# Quantum Perron–Frobenius Theory for MPS Transfer Operators

This file provides the existence step and the final quantum Perron–Frobenius
theorem from its components:

1. **Positive definiteness** (`QPF.PosDef`): PSD fixed points → PD under injectivity
2. **Uniqueness** (`QPF.Uniqueness`): PSD fixed points are unique up to scalar
3. **Existence** (this file): via Cesàro mean / trace-preserving channel theory
4. **The quantum Perron–Frobenius theorem** (this file): the combined result

Together these formalize the core of **Wolf Theorem 6.3** (Spectral radius of
irreducible maps), specialized to the trace-preserving (spectral radius = 1) setting:
- Existence: there is a nonzero PSD fixed point (Wolf Theorem 6.11 / Proposition 6.3 route)
- PosDef: under irreducibility the fixed point is strictly positive (Wolf Theorem 6.3(2))
- Uniqueness: the eigenvalue 1 is non-degenerate (Wolf Theorem 6.3(2))

## Main results

* `exists_posSemidef_fixedPoint`: existence of a PSD fixed point
* `quantum_perron_frobenius`: the full QPF theorem
* `injective_transfer_unique_fixed_point'`: QPF without the `0 < D` hypothesis

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.2 Theorem 6.3,
  Section 6.4 Theorem 6.11][Wolf2012QChannels]
* [Evans, Høegh-Krohn, *Spectral properties of positive maps*, 1978][Evans1978Spectral]
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ## Part 3: Existence of PSD fixed point -/

section Existence

/-- Existence of a PSD fixed point for the transfer map of a normalized
MPS tensor.

**Mathematical content**: If `∑ Aᵢ† Aᵢ = 1`, then `transferMap A` is a
trace-preserving channel. Applying `IsChannel.exists_posSemidef_fixedPoint`
produces a nonzero PSD matrix `ρ` with `transferMap A ρ = ρ`.

**Proof method**: The channel fixed-point theorem used here is proved via the
Cesàro averages of iterates of a density matrix, so in the normalized case this
existence statement does not rely on Brouwer or Krein-Rutman.

**Note**: Injectivity is not used in this existence step; it enters later in
the positive-definiteness and uniqueness statements. For a general non-normalized
injective tensor, one instead expects the eigenvector statement
`∃ ρ c, ρ.PosSemidef ∧ ρ ≠ 0 ∧ 0 < c ∧ E(ρ) = c • ρ`, and then rescales to the
fixed-point setting. -/
theorem exists_posSemidef_fixedPoint
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hD : 0 < D) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.PosSemidef ∧ ρ ≠ 0 ∧
      transferMap (d := d) (D := D) A ρ = ρ :=
  (MPSTensor.transferMap_isChannel A hNorm).exists_posSemidef_fixedPoint
    (E := transferMap A) hD

end Existence

/-! ## Part 4: The quantum Perron–Frobenius theorem -/

section PerronFrobenius

/-- **The quantum Perron–Frobenius theorem for MPS transfer operators**
(Wolf Theorem 6.3, specialized to CP maps with spectral radius 1).

The transfer map of an injective MPS tensor has a unique PSD fixed point
(up to scalar), and it is positive definite. -/
theorem quantum_perron_frobenius [DecidableEq (Fin D)]
    (A : MPSTensor d D) (hA : IsInjective A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hD : 0 < D) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      HasUniqueFixedPoint (transferMap (d := d) (D := D) A) ρ := by
  obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix⟩ := exists_posSemidef_fixedPoint A (by convert hNorm) hD
  have hρ_pd := posSemidef_fixedPoint_isPosDef A hA ρ hρ_psd hρ_ne hρ_fix
  exact ⟨ρ, {
    fixed := hρ_fix
    pos_def := hρ_pd
    unique := fun σ hσ_psd hσ_fix => by
      by_cases hσ : σ = 0
      · exact ⟨0, by simp [hσ]⟩
      · exact posSemidef_fixedPoint_unique A hA ρ σ hρ_psd hρ_ne hσ_psd hσ hρ_fix hσ_fix
  }⟩

/-! ### Reduction: handle the `D = 0` edge case

`quantum_perron_frobenius` requires `0 < D`. The theorem below lifts this restriction. -/

/-- **Injectivity implies unique fixed point** (without the `0 < D` hypothesis).
Extends `quantum_perron_frobenius` to the case `D = 0`, which holds vacuously. -/
theorem injective_transfer_unique_fixed_point' [DecidableEq (Fin D)]
    (A : MPSTensor d D) (hA : IsInjective A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      HasUniqueFixedPoint (transferMap (d := d) (D := D) A) ρ := by
  by_cases hD : 0 < D
  · exact quantum_perron_frobenius A hA hNorm hD
  · push Not at hD
    interval_cases D
    exact ⟨0, {
      fixed := by ext i; exact Fin.elim0 i
      pos_def := Matrix.PosDef.of_dotProduct_mulVec_pos Matrix.isHermitian_zero
        (fun x hx => absurd (Subsingleton.elim x 0) hx)
      unique := fun σ _ _ => ⟨0, by ext i; exact Fin.elim0 i⟩
    }⟩

end PerronFrobenius

end MPSTensor
