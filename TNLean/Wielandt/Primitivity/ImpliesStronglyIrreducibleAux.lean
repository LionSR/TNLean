/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.EigenspaceMap
import QICLean.Kraus.Wielandt.Primitivity.VectorSpreadToPrimitive
import QICLean.Kraus.TransferChannel
import TNLean.Wielandt.Primitivity.ImpliesStronglyIrreducible

/-!
# Proposition 3, direction (a) to (c): MPS formulations

This file retains the established transfer-map formulations of the spectral and
fixed-point lemmas used for Proposition 3 of Sanz, Pérez-García, Wolf, and Cirac,
arXiv:0909.5347. The concluding peripheral-primitivity and strong-irreducibility
theorems are reformulations of the finite-Kraus results in
`TNLean.Kraus.Wielandt.Primitivity.VectorSpreadToPrimitive`.

For the combined Proposition 3 statement, see
`TNLean.Wielandt.Primitivity.Equivalence`.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor Module

namespace MPSTensor

section SpectralPerturbation

variable {d D : ℕ}

/-! ### Step 5: Hermitian, nonzero, trace-zero matrix is not PSD -/

/-- A nonzero Hermitian matrix with trace zero is not positive semidefinite. -/
theorem not_posSemidef_of_hermitian_ne_zero_trace_eq_zero
    {H : Matrix (Fin D) (Fin D) ℂ}
    (_hH : H.IsHermitian) (hne : H ≠ 0) (htr : H.trace = 0) :
    ¬H.PosSemidef := fun hpsd =>
  hne ((Matrix.PosSemidef.trace_eq_zero_iff hpsd).mp htr)

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
    not_posSemidef_of_hermitian_ne_zero_trace_eq_zero hH hH_ne hH_tr⟩
  simpa only using hH_fix

end SpectralPerturbation

section Construction

variable {d D : ℕ}

/-- Proposition 3(a) to (c) of Sanz, Pérez-García, Wolf, and Cirac,
arXiv:0909.5347: paper-primitivity and normalization imply peripheral
primitivity of the transfer map. See also Wolf, Theorem 6.7. -/
theorem isPeripherallyPrimitive_of_isPrimitivePaper [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A) :
    IsPeripherallyPrimitive A := by
  obtain ⟨q, _, hq⟩ := hPrim
  change IsPrimitive (Kraus.transferMap (d := d) (D := D) A)
  simpa only using
    Kraus.isPrimitive_mapLM_of_isTP_of_vectorSpreadSpan_eq_top A hNorm hq

/-- Paper-primitivity and normalization imply a positive-definite fixed point,
peripheral primitivity, and irreducibility of the transfer map.

This is Proposition 3(a)→(c) of arXiv:0909.5347; the peripheral-spectral
ingredient is the finite-dimensional channel result of Wolf, Theorem 6.7. -/
theorem isStronglyIrreduciblePaper_of_isPrimitivePaper [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hPrim : IsPrimitivePaper A) :
    IsStronglyIrreduciblePaper A := by
  obtain ⟨q, hqpos, hq⟩ := hPrim
  obtain ⟨ρ, hρ_pd, hρ_fix⟩ :=
    Kraus.exists_posDef_fixedPoint_of_isTP_of_vectorSpreadSpan_eq_top A hNorm hq
  refine isStronglyIrreduciblePaper_of ρ hρ_pd ?_ ?_ ?_
  · simpa only using hρ_fix
  · exact isPeripherallyPrimitive_of_isPrimitivePaper A hNorm ⟨q, hqpos, hq⟩
  · simpa only using
      Kraus.isIrreducibleMap_mapLM_of_vectorSpreadSpan_eq_top A hq

end Construction

end MPSTensor
