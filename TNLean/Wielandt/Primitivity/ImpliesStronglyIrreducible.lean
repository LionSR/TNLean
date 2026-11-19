/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.EigenspaceMap
import QICLean.Kraus.Wielandt.Primitivity.VectorSpreadPositivity
import QICLean.Kraus.Wielandt.Primitivity.VectorSpreadToPrimitive
import QICLean.Kraus.InvariantProjection
import QICLean.Channel.KrausMap
import QICLean.Kraus.Transfer
import TNLean.Wielandt.Primitivity.EasyDirections

/-!
# Spectral consequences of normality for the transfer map

A normal tensor spreads every nonzero vector to the whole space at one fixed
length (`MPSTensor.exists_vectorSpreadSpan_eq_top_of_isNormal`). This file
states the consequences of that spreading for the transfer map: irreducibility,
and, for a left-canonical tensor, a positive-definite fixed matrix and the
absence of peripheral eigenvalues other than one. The finite-Kraus proofs are in
`QICLean.Kraus.Wielandt.Primitivity.VectorSpreadPositivity` and
`QICLean.Kraus.Wielandt.Primitivity.VectorSpreadToPrimitive`.

These results are the direction (a) to (c) of Proposition 3 of Sanz,
Pérez-García, Wolf, and Cirac, arXiv:0909.5347, stated from the equivalent
clause (b). The proposition itself is `MPSTensor.primitivity_tfae` in
`TNLean.Wielandt.Primitivity.Equivalence`.

## Main results

* `MPSTensor.isIrreducibleMap_transferMap_of_isNormal` and
  `MPSTensor.isIrreducibleFamily_of_isNormal`: a normal tensor is irreducible.
* `MPSTensor.isPrimitive_transferMap_of_isNormal`: the transfer map of a normal
  left-canonical tensor has peripheral spectrum `{1}`.
* `MPSTensor.exists_posDef_fixedPoint_of_isNormal`: it has a positive-definite
  fixed matrix.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor Module

namespace MPSTensor

variable {d D : ℕ}

/-- The transfer map of a normal tensor has no nontrivial invariant orthogonal
projection. No normalization is needed.

Source: arXiv:0909.5347, Proposition 3, proof of (a)⟹(c). -/
theorem isIrreducibleMap_transferMap_of_isNormal
    (A : MPSTensor d D) (hA : Kraus.IsNormal A) :
    IsIrreducibleMap (Kraus.transferMap (d := d) (D := D) A) := by
  obtain ⟨q, _, hq⟩ := exists_vectorSpreadSpan_eq_top_of_isNormal A hA
  simpa only using Kraus.isIrreducibleMap_mapLM_of_vectorSpreadSpan_eq_top A hq

/-- A normal tensor has no nontrivial invariant orthogonal projection. -/
theorem isIrreducibleFamily_of_isNormal
    (A : MPSTensor d D) (hA : Kraus.IsNormal A) :
    Kraus.IsIrreducibleFamily A :=
  Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A
    (isIrreducibleMap_transferMap_of_isNormal A hA)

section SpectralPerturbation

/-! ### Step 6: Conclusion — existence of a Hermitian, nonzero, trace-zero E^p-fixed point -/

/-- **From a nontrivial peripheral eigenvector, extract a nonzero Hermitian trace-zero
fixed point of `E^p` that is not positive semidefinite.** -/
theorem exists_hermitian_ne_zero_trace_zero_pow_fixedPoint
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    {X : Matrix (Fin D) (Fin D) ℂ} {μ : ℂ}
    (hEig : Kraus.transferMap (d := d) (D := D) A X = μ • X)
    (hX_ne : X ≠ 0) (hμ_ne : μ ≠ 1) {p : ℕ} (hroot : μ ^ p = 1) :
    ∃ H : Matrix (Fin D) (Fin D) ℂ,
      H.IsHermitian ∧ H ≠ 0 ∧ H.trace = 0 ∧
      ((Kraus.transferMap (d := d) (D := D) A) ^ p) H = H ∧
      ¬H.PosSemidef := by
  obtain ⟨H, hH, hH_ne, hH_tr, hH_fix⟩ :=
    Kraus.exists_hermitian_ne_zero_trace_zero_pow_fixedPoint
      (Kraus.mapLM A) (Kraus.isChannel_mapLM A hNorm) hEig hX_ne hμ_ne hroot
  refine ⟨H, hH, hH_ne, hH_tr, ?_,
    fun hpsd => hH_ne ((Matrix.PosSemidef.trace_eq_zero_iff hpsd).mp hH_tr)⟩
  simpa only using hH_fix

end SpectralPerturbation

section Construction

/-- The transfer map of a normal left-canonical tensor has no eigenvalue of
modulus one other than one.

Source: arXiv:0909.5347, Proposition 3, (b)⟹(a)⟹(c); Wolf, Theorem 6.7. -/
theorem isPrimitive_transferMap_of_isNormal [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hA : Kraus.IsNormal A) :
    IsPrimitive (Kraus.transferMap (d := d) (D := D) A) := by
  obtain ⟨q, _, hq⟩ := exists_vectorSpreadSpan_eq_top_of_isNormal A hA
  simpa only using
    Kraus.isPrimitive_mapLM_of_isTP_of_vectorSpreadSpan_eq_top A hNorm hq

/-- The transfer map of a normal left-canonical tensor has a positive-definite
fixed matrix.

Source: arXiv:0909.5347, Proposition 3, (b)⟹(a)⟹(c). -/
theorem exists_posDef_fixedPoint_of_isNormal [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hA : Kraus.IsNormal A) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      ρ.PosDef ∧ Kraus.transferMap (d := d) (D := D) A ρ = ρ := by
  obtain ⟨q, _, hq⟩ := exists_vectorSpreadSpan_eq_top_of_isNormal A hA
  obtain ⟨ρ, hρ_pd, hρ_fix⟩ :=
    Kraus.exists_posDef_fixedPoint_of_isTP_of_vectorSpreadSpan_eq_top A hNorm hq
  exact ⟨ρ, hρ_pd, by simpa only using hρ_fix⟩

end Construction

end MPSTensor
