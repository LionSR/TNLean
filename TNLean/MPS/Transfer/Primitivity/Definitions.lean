/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Words.WordSpan
import QICLean.Kraus.Transfer
import QICLean.Channel.Peripheral.Spectrum.Spectrum
import QICLean.Channel.Irreducible.Basic
import TNLean.MPS.Tensor
import QICLean.Kraus.Wielandt.PrimitiveCriterion
import QICLean.Channel.Irreducible.InvariantProjection
import QICLean.Kraus.PrimitiveFixedPoint
import QICLean.Kraus.PrimitiveFixedPoint.FromPeripheral
import QICLean.Kraus.PrimitiveFixedPoint.Basic

/-!
# Normality from an irreducible transfer map without peripheral spectrum

The channel-generic proof is in
`QICLean.Kraus.Wielandt.Primitivity.StronglyIrreducibleToFullWordSpan`. This file
states its consequences for a left-canonical MPS tensor, in the three kept
notions: `Kraus.IsNormal`, `IsPrimitive` of the transfer map, and the
complementary fixed-point gap `Kraus.HasComplementaryFixedPointGap`.

## Main results

* `Kraus.isNormal_of_isIrreducibleMap_of_isPrimitive` (QICLean): an irreducible transfer map with
  peripheral spectrum `{1}` gives normality. This is the direction (c) to (b)
  of Proposition 3 of Sanz, Pérez-García, Wolf, and Cirac, arXiv:0909.5347.
* `exists_hasComplementaryFixedPointGap_posDef_of_isIrreducibleMap_of_isPrimitive`: the same
  hypotheses give a complementary fixed-point gap at a positive-definite fixed
  matrix.
* `isNormal_of_hasComplementaryFixedPointGap_with_posDef`: `Kraus.HasComplementaryFixedPointGap`
  plus a positive-definite fixed point implies normality.

## References

- Sanz, Pérez-García, Wolf, Cirac, arXiv:0909.5347, Proposition 3.
- Wolf, *Quantum Channels & Operations: Guided Tour*, Sections 6.2--6.4.
- Cirac, Pérez-García, Schuch, Verstraete, arXiv:1606.00608, Section 2.3.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- A left-canonical tensor whose transfer map is irreducible and has no
eigenvalue of modulus one other than one has a complementary fixed-point gap
at a positive-definite fixed matrix.

This connects the spectral characterization of Proposition 3(c) of
arXiv:0909.5347 to the complementary transfer-map gap used by the transfer-map
convergence theory. The proof chains:

1. `IsIrreducibleMap E → Kraus.IsIrreducibleFamily A`
2. `Kraus.hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible`
3. every nonzero positive semidefinite fixed point of an irreducible transfer
   map is positive definite, via
   `Kraus.HasComplementaryFixedPointGap.posDef_of_isIrreducibleMap`. -/
theorem exists_hasComplementaryFixedPointGap_posDef_of_isIrreducibleMap_of_isPrimitive [NeZero D]
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleMap (Kraus.transferMap (ι := Fin d) (n := Fin D) A))
    (hPrim : IsPrimitive (Kraus.transferMap (ι := Fin d) (n := Fin D) A)) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      Kraus.HasComplementaryFixedPointGap A ρ ∧ ρ.PosDef := by
  have hIrrT : Kraus.IsIrreducibleFamily A :=
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A hIrr
  obtain ⟨ρ, hP⟩ :=
    Kraus.hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible A hIrrT hNorm hPrim
  exact ⟨ρ, hP, hP.posDef_of_isIrreducibleMap hIrr⟩

/-- `Kraus.HasComplementaryFixedPointGap` plus a positive-definite fixed point implies normality. -/
theorem isNormal_of_hasComplementaryFixedPointGap_with_posDef [NeZero D]
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ)
    (hρ_pd : ρ.PosDef) :
    Kraus.IsNormal A :=
  Kraus.isNormal_of_isIrreducibleMap_of_isPrimitive A hP.norm
    (hP.isIrreducibleMap_of_posDef hρ_pd) hP.isPrimitive

end MPSTensor

/-!
# Index definitions for the quantum Wielandt theorem

This file defines the Kraus rank and the two indices of Sanz, Pérez-García,
Wolf and Cirac, *A quantum version of Wielandt's inequality* (arXiv:0909.5347),
in the notation of the source: `S_n(A)`, `i(A)` and `q(E_A)`.

## Main definitions

* `krausRank A`: the dimension of `S₁(A) = Kraus.wordSpan A 1`, i.e.
  `dim(span{A₁,…,Aₐ})`.
* `iIndex A`: `sInf {n | 0 < n ∧ S_n(A) = M_D(ℂ)}`, the positive
  full-Kraus-rank index `i(A)`.
* `qIndex A`: `sInf {q | 0 < q ∧ ∀ φ ≠ 0, H_q(A,φ) = ℂ^D}`, the positive
  primitivity index `q(E_A)`.

## The notions of primitivity

The source introduces three properties of a channel `E_A` (arXiv:0909.5347,
`Papers/0909.5347/main.tex`, lines 403–430): (a) primitivity, a uniform length
`q` with `H_q(A,φ) = ℂ^D` for every nonzero `φ`; (b) eventually full Kraus
rank, a length `n` with `S_n(A) = M_D(ℂ)`; (c) strong irreducibility, a unique
eigenvalue of modulus one whose eigenvector is positive definite. None of the
three has a predicate of its own. Property (b) is `Kraus.IsNormal A` by
definition, the peripheral part of (c) is `IsPrimitive (Kraus.transferMap A)`,
and Proposition 3 of the source, which says the three are equivalent for a
trace-preserving family, is the single theorem `MPSTensor.primitivity_tfae` of
`Primitivity/Equivalence.lean`, with each clause written out.

## References

- [Sanz, Pérez-García, Wolf, Cirac, *A quantum version of Wielandt's inequality*,
  arXiv:0909.5347](https://arxiv.org/abs/0909.5347), Section II & Proposition 3
- Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 6
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor Module

namespace MPSTensor

variable {d D : ℕ}

/-! ## Kraus rank -/

/-- **Kraus rank** of an MPS tensor: the dimension of `S₁(A)`, the span of
`{A₁, …, Aₐ}`.

Paper notation: this is `dim(S₁(A))`.
(arXiv:0909.5347, Section II) -/
noncomputable def krausRank (A : MPSTensor d D) : ℕ :=
  Module.finrank ℂ (Kraus.wordSpan A 1)

/-! ## Index definitions -/

/-- **Full-Kraus-rank index** `i(A)`: the smallest positive `i` such that
`S_i(A) = M_D(ℂ)`.

Paper: "i(A) := min{n : S_n(A) = M_D(ℂ)}."
(arXiv:0909.5347, after Proposition 3)

The paper takes its word lengths in `ℕ = {1, 2, …}`.  Accordingly this is
defined as `sInf {n | 0 < n ∧ Kraus.wordSpan A n = ⊤}`, the least length
witnessing `Kraus.IsNormal A`.  It returns 0 if no such `n` exists (as per
`Nat.sInf ∅ = 0`). -/
noncomputable def iIndex (A : MPSTensor d D) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ Kraus.wordSpan A n = ⊤}

/-- **Primitivity index** `q(E_A)`: the smallest positive `q` such that for all nonzero φ,
`H_q(A,φ) = ℂ^D`.

Paper: "q(E_A) := min{q : ∀ |φ⟩ ≠ 0, H_q(A,φ) = ℂ^D}."
(arXiv:0909.5347, Proposition 3)

The paper uses the same positive word-length convention as for `i(A)`.  Accordingly this
is `sInf {q | 0 < q ∧ ∀ φ ≠ 0, Kraus.vectorSpreadSpan A φ q = ⊤}`. It returns 0 if no such
`q` exists. -/
noncomputable def qIndex (A : MPSTensor d D) : ℕ :=
  sInf {q : ℕ | 0 < q ∧ ∀ φ : Fin D → ℂ, φ ≠ 0 →
    Kraus.vectorSpreadSpan A φ q = ⊤}

end MPSTensor
