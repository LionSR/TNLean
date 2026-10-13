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
import TNLean.Wielandt.Primitivity.Definitions

/-!
# Proposition 3, direction (a) to (c): MPS formulations

This file states the positivity, irreducibility, spectral and fixed-point
consequences of fixed-length vector spreading in transfer-map notation. Their
finite-Kraus proofs are provided by
`QICLean.Kraus.Wielandt.Primitivity.VectorSpreadPositivity` and
`QICLean.Kraus.Wielandt.Primitivity.VectorSpreadToPrimitive`.

These results form Proposition 3, direction (a) to (c), of Sanz,
Pérez-García, Wolf, and Cirac, arXiv:0909.5347. For the combined
Proposition 3 statement, see `TNLean.Wielandt.Primitivity.Equivalence`.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor Module

namespace MPSTensor

variable {d D : ℕ}

/-- Paper-primitivity implies that the tensor has no nontrivial invariant
orthogonal projection. -/
theorem isIrreducibleTensor_of_isPrimitivePaper
    (A : MPSTensor d D)
    (hPrim : IsPrimitivePaper A) :
    Kraus.IsIrreducibleFamily A := by
  obtain ⟨q, _, hq⟩ := hPrim
  exact Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A
    (Kraus.isIrreducibleMap_mapLM_of_vectorSpreadSpan_eq_top A hq)

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
