/-
Copyright (c) 2025 MPSLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPSLean.QPF.PosDef
import MPSLean.QPF.Uniqueness

/-!
# Quantum Perron–Frobenius Theory for MPS Transfer Operators

This file assembles the quantum Perron–Frobenius theorem from its components:

1. **Positive definiteness** (`QPF.PosDef`): PSD fixed points → PD under injectivity
2. **Uniqueness** (`QPF.Uniqueness`): PSD fixed points are unique up to scalar
3. **Existence** (this file): via Cesàro mean / trace-preserving channel theory
4. **Assembly** (this file): the combined theorem

## Main results

* `exists_posSemidef_fixedPoint`: existence of a PSD fixed point
* `quantum_perron_frobenius`: the full QPF theorem
* `injective_transfer_unique_fixed_point'`: QPF without the `0 < D` hypothesis

## References

* [Evans, Høegh-Krohn, *Spectral properties of positive maps*, 1978][Evans1978Spectral]
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, 2012][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ## Part 3: Existence of PSD fixed point -/

section Existence

/-- Existence of a PSD fixed point for the transfer map of an injective
MPS tensor.

**Mathematical content**: By the Krein-Rutman theorem (finite-dimensional version),
the transfer map `E_A`, which preserves the PSD cone, has a PSD eigenvector for its
spectral radius `r`. After rescaling `A ↦ A/√r`, this eigenvector becomes a fixed
point of the rescaled transfer map.

**Status**: This requires either Brouwer's fixed point theorem or the
finite-dimensional Krein-Rutman theorem, neither of which is currently in Mathlib.

**Note**: Requires normalization `∑ Aᵢ† Aᵢ = 1`, which ensures the transfer map
is trace-preserving. For a general injective tensor, the conclusion should be
`∃ ρ c, ρ.PosSemidef ∧ ρ ≠ 0 ∧ 0 < c ∧ E(ρ) = c • ρ`. The fixed-point version
follows after rescaling so that the spectral radius equals 1. -/
theorem exists_posSemidef_fixedPoint
    (A : MPSTensor d D) (_hA : IsInjective A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hD : 0 < D) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.PosSemidef ∧ ρ ≠ 0 ∧
      transferMap (d := d) (D := D) A ρ = ρ := by
  have hCh := MPSTensor.transferMap_isChannel A hNorm
  exact hCh.exists_posSemidef_fixedPoint (E := transferMap A) hD

end Existence

/-! ## Part 4: Assembling the quantum PF theorem -/

section Assembly

/-- **The quantum Perron–Frobenius theorem for MPS transfer operators.**

The transfer map of an injective MPS tensor has a unique PSD fixed point
(up to scalar), and it is positive definite. -/
theorem quantum_perron_frobenius [DecidableEq (Fin D)]
    (A : MPSTensor d D) (hA : IsInjective A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hD : 0 < D) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      HasUniqueFixedPoint (transferMap (d := d) (D := D) A) ρ := by
  obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix⟩ := exists_posSemidef_fixedPoint A hA (by convert hNorm) hD
  have hρ_pd := posSemidef_fixedPoint_isPosDef A hA ρ hρ_psd hρ_ne hρ_fix
  exact ⟨ρ, {
    fixed := hρ_fix
    pos_def := hρ_pd
    unique := fun σ hσ_psd hσ_fix => by
      by_cases hσ : σ = 0
      · exact ⟨0, by simp [hσ]⟩
      · exact posSemidef_fixedPoint_unique A hA ρ σ hρ_psd hρ_ne hσ_psd hσ hρ_fix hσ_fix
  }⟩

/-! ### Bridge: handle the `D = 0` edge case

`quantum_perron_frobenius` requires `0 < D`. The theorem below lifts this restriction. -/

/-- For D = 0, the zero matrix is vacuously positive definite. -/
private lemma posDef_zero_fin0 : (0 : Matrix (Fin 0) (Fin 0) ℂ).PosDef :=
  Matrix.PosDef.of_dotProduct_mulVec_pos Matrix.isHermitian_zero
    (fun x hx => absurd (Subsingleton.elim x 0) hx)

/-- **Injectivity implies unique fixed point** (without the `0 < D` hypothesis).
Wraps `quantum_perron_frobenius` with a vacuous case for `D = 0`. -/
theorem injective_transfer_unique_fixed_point' [DecidableEq (Fin D)]
    (A : MPSTensor d D) (hA : IsInjective A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      HasUniqueFixedPoint (transferMap (d := d) (D := D) A) ρ := by
  by_cases hD : 0 < D
  · exact quantum_perron_frobenius A hA hNorm hD
  · push_neg at hD
    interval_cases D
    exact ⟨0, {
      fixed := by ext i; exact Fin.elim0 i
      pos_def := posDef_zero_fin0
      unique := fun σ _ _ => ⟨0, by ext i; exact Fin.elim0 i⟩
    }⟩

end Assembly

end MPSTensor
