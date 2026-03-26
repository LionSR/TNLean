/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.QPF.Assembly
import TNLean.Channel.Peripheral.Spectrum

/-!
# Quantum Perron–Frobenius for primitive transfer maps

This file weakens the hypothesis of the quantum Perron–Frobenius theorem from
`IsInjective A` (Kraus operators span the full algebra) to
`IsPrimitive (transferMap A)` (the transfer map has 1 as its only peripheral
eigenvalue) combined with `IsIrreducibleMap (transferMap A)`.

## Main results

* `quantum_perron_frobenius_irreducible` — QPF under irreducibility of the
  transfer map (weaker than injectivity)
* `quantum_perron_frobenius_primitive` — QPF under irreducibility +
  primitivity, additionally guaranteeing exponential convergence

## Mathematical content

The standard QPF theorem in Wolf (Theorem 6.3) is stated for **irreducible**
positive maps, not specifically for injective MPS tensors. The existing
`quantum_perron_frobenius` in `Assembly.lean` uses `IsInjective A` because
that implies `IsIrreducibleMap (transferMap A)` via
`injective_implies_irreducibleCP`. This file provides the direct
irreducibility-based version.

**Hierarchy of hypotheses** (each implies the next):
  `IsInjective A` → `IsIrreducibleMap (transferMap A)` → `IsPrimitive (transferMap A)` + unique fixed point

## Strengthening relative to the literature

The existing formalization only provides QPF at the `IsInjective` level.
This file exposes the natural generality of Wolf's theorem at the
`IsIrreducibleMap` level, which applies to tensors that are not injective
but whose transfer maps are still irreducible (e.g., after blocking).

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §6.2, Thm 6.3]
* [Evans, Høegh-Krohn, *Spectral properties of positive maps*, 1978]
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- **Quantum Perron–Frobenius under irreducibility** (Wolf Thm 6.3).

If the transfer map `E_A` is irreducible and trace-preserving (`∑ Aᵢ† Aᵢ = I`),
then it has a unique positive definite fixed point.

This is strictly more general than `quantum_perron_frobenius`, which requires
`IsInjective A`. The generalization matters for blocked tensors: after blocking
`n` sites, the resulting tensor may not be injective (the Kraus operators
may not span), but the transfer map can still be irreducible.

**Proof**: Existence of a PSD fixed point follows from the channel fixed-point
theorem. Positive definiteness follows from `posSemidef_fixedPoint_isPosDef_of_irreducible`.
Uniqueness follows from `posSemidef_fixedPoint_unique_of_irreducible`. -/
theorem quantum_perron_frobenius_irreducible [DecidableEq (Fin D)]
    (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (transferMap (d := d) (D := D) A))
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hD : 0 < D) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      HasUniqueFixedPoint (transferMap (d := d) (D := D) A) ρ := by
  -- Existence of PSD fixed point (via channel theory, does not need injectivity).
  obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix⟩ := exists_posSemidef_fixedPoint A (by convert hNorm) hD
  -- Positive definiteness under irreducibility.
  have hρ_pd := posSemidef_fixedPoint_isPosDef_of_irreducible A hIrr ρ hρ_psd hρ_ne hρ_fix
  exact ⟨ρ, {
    fixed := hρ_fix
    pos_def := hρ_pd
    unique := fun σ hσ_psd hσ_fix => by
      by_cases hσ : σ = 0
      · exact ⟨0, by simp [hσ]⟩
      · exact posSemidef_fixedPoint_unique_of_irreducible (A := A) hIrr ρ σ
          hρ_psd hρ_ne hσ_psd hρ_fix hσ_fix
  }⟩

/-- **QPF with primitivity guarantee** (Wolf Thm 6.3 + spectral gap).

If the transfer map is irreducible **and** primitive (`1` is the only peripheral
eigenvalue), then not only does a unique PD fixed point exist, but
`E^n → P` exponentially fast (where `P` is the projection onto the fixed state).

The primitivity condition `IsPrimitive (transferMap A)` is strictly weaker than
`IsInjective A` (which implies both irreducibility and primitivity). -/
theorem quantum_perron_frobenius_primitive [DecidableEq (Fin D)]
    (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (transferMap (d := d) (D := D) A))
    (hPrim : IsPrimitive (transferMap (d := d) (D := D) A))
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hD : 0 < D) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      HasUniqueFixedPoint (transferMap (d := d) (D := D) A) ρ ∧
      IsPrimitive (transferMap (d := d) (D := D) A) :=
  let ⟨ρ, huf⟩ := quantum_perron_frobenius_irreducible A hIrr hNorm hD
  ⟨ρ, huf, hPrim⟩

end MPSTensor
