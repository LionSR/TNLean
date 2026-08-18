/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Irreducible.FixedPointUniqueness
import TNLean.QPF.PosDef

/-!
# Quantum Perron–Frobenius: Uniqueness

Under injectivity, any two nonzero PSD fixed points of the transfer map
are proportional. The critical scalar / spectral shift argument lives at the
channel level in `TNLean.Channel.Irreducible.FixedPointUniqueness`; this file
states the transfer-map specializations.

This formalizes the non-degeneracy part of **Wolf Theorem 6.3**
(Spectral radius of irreducible maps), item 2: the spectral radius is a
*non-degenerate* eigenvalue (so the PSD eigenvector is unique up to scalar).
Item 3 (any positive eigenvalue with PSD eigenvector must equal the spectral
radius) is also a consequence.

## Main results

* `posSemidef_fixedPoint_unique`: uniqueness of PSD fixed points (Wolf Theorem 6.3(2))
* `posSemidef_fixedPoint_unique_of_irreducible`: same under irreducibility

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.2,
  Theorem 6.3 items 2–3][Wolf2012QChannels]
* [Evans, Høegh-Krohn, *Spectral properties of positive maps*, 1978][Evans1978Spectral]
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D : ℕ}

section Uniqueness

/-- **Uniqueness under irreducibility** (Wolf Theorem 6.3(2)): any PSD fixed point
of an irreducible transfer map is proportional to a fixed nonzero PSD fixed point. -/
theorem posSemidef_fixedPoint_unique_of_irreducible
    (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (transferMap (d := d) (D := D) A))
    (ρ σ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef) (hρ_ne : ρ ≠ 0)
    (hσ_psd : σ.PosSemidef)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ)
    (hσ_fix : transferMap (d := d) (D := D) A σ = σ) :
    ∃ c : ℂ, σ = c • ρ :=
  posSemidef_fixedPoint_unique_of_irreducible_cp _ (transferMap_isCPMap A) hIrr
    ρ σ hρ_psd hρ_ne hσ_psd hρ_fix hσ_fix

/-- **Uniqueness** (Wolf Theorem 6.3(2), non-degeneracy): any PSD fixed point
of an injective transfer map is proportional to a given nonzero PSD fixed point. -/
theorem posSemidef_fixedPoint_unique
    (A : MPSTensor d D) (hA : IsInjective A)
    (ρ σ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef) (hρ_ne : ρ ≠ 0)
    (hσ_psd : σ.PosSemidef)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ)
    (hσ_fix : transferMap (d := d) (D := D) A σ = σ) :
    ∃ c : ℂ, σ = c • ρ := by
  exact posSemidef_fixedPoint_unique_of_irreducible A
    (injective_implies_irreducibleCP A hA) ρ σ hρ_psd hρ_ne hσ_psd hρ_fix hσ_fix

end Uniqueness

end MPSTensor
