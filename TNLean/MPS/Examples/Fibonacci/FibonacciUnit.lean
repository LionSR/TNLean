/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.CompressionPeriodic
import TNLean.MPS.Examples.Fibonacci.Fibonacci
import TNLean.MPS.Examples.Rings.GoldenCompression

/-!
# The unit laws of the Fibonacci algebra as compressions

The Fibonacci string-net matrix product operator algebra of Bultinck, Marien, Williamson,
Sahinoglu, Haegeman and Verstraete (arXiv:1511.08090, Appendix D.1) has two operator families,
the admissibility projector `O_1` of bond dimension two and the `τ` family of bond dimension
three. `Examples/Fibonacci.lean` formalizes the fusion `O_τ O_τ = O_1 + O_τ` as a multi-block
compression. This file formalizes the remaining three products of the two blocks as compressions
in the same exact arithmetic over `ℤ[σ]` (data file
`Notes/OpenProblemsTN/checks/asym_fibonacci_categorical_data.md`, §3.1-3.3, verified by
`checks/asym_fibonacci_categorical_verify.py`):

* `1 ⊗ 1 → 1`, bond dimension `4 = 2 + 2`: the admissibility projector is idempotent;
* `1 ⊗ τ → τ` and `τ ⊗ 1 → τ`, bond dimension `6 = 3 + 3`: the projector is the unit of the
  algebra on the `τ` family.

Each stacked product compresses onto a single block with the recorded number of zero slots, every
gauge and its inverse have entries in `ℤ[σ]`, and the conjugated letters are block diagonal, so
every extension splits. Together with the fusion rule this realises the full multiplication table
of the Fibonacci fusion ring on the periodic operators, `O_1^2 = O_1`, `O_1 O_τ = O_τ O_1 = O_τ`,
`O_τ^2 = O_1 + O_τ`.

**Local fix (positive length):** the source derives the fusion rules, among them the unit laws,
from the projector identity required for all `L` (`References/1511.08090/AnyonsPEPS.tex`
lines 152–160); at `L = 0` the periodic operators are the bond dimensions `2` and `3`, and
`O_1^0 O_1^0 = 4 ≠ 2`, `O_1^0 O_τ^0 = O_τ^0 O_1^0 = 6 ≠ 3`. The empty chain is read as a
degenerate case, and the unit laws are stated for every positive length; documented in
`docs/paper-gaps/bmwshv17_fibonacci_projector_positive_length.tex`.

## Main definitions

* `FibonacciCompression.fibOneOneStack`, `FibonacciCompression.fibOneTauStack`,
  `FibonacciCompression.fibTauOneStack`: the three stacked products.
* `FibonacciCompression.fibOneOne_compression`, `FibonacciCompression.fibOneTau_compression`,
  `FibonacciCompression.fibTauOne_compression`: their compression data.

## Main results

* `FibonacciCompression.fibOne_mul_fibOne`, `FibonacciCompression.fibOne_mul_fibTau`,
  `FibonacciCompression.fibTau_mul_fibOne`: the unit laws as identities of periodic operators at
  every positive system size.
* `FibonacciCompression.fibOneOne_remainder_eq_zero`,
  `FibonacciCompression.fibOneTau_remainder_eq_zero`,
  `FibonacciCompression.fibTauOne_remainder_eq_zero`: all three extensions split.
-/

noncomputable section

open scoped Matrix

namespace FibonacciCompression

open GoldenInt MPSTensor

/-! ### The square of the admissibility projector -/

/-- The stacked product tensor of `1 ⊗ 1`, of bond dimension 4 (data file §3.1). -/
def fibOneOneStack : MPSTensor 4 4 := (MPOTensor.mulTensor fibOne fibOne).toMPSTensor

/-- The golden matrices of the stacked product tensor of `1 ⊗ 1`, in the bond order of
`finProdFinEquiv` (data file §3.1). -/
def fibOneOneStackGolden : Fin 4 → Matrix (Fin 4) (Fin 4) GoldenInt
  | 0 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 1 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 2 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 3 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]

theorem fibOneOneStack_eq (a : Fin 4) :
    fibOneOneStack a = complexOfGolden (fibOneOneStackGolden a) := by
  have h : fibOneOneStack a = complexOfGolden (mulGoldenTensor fibOneGolden fibOneGolden
      (Fin.divNat (m := 2) (n := 2) a) (Fin.modNat (m := 2) (n := 2) a)) :=
    mulTensor_complexOfGolden fibOneGolden fibOneGolden _ _
  have hgolden : ∀ b : Fin 4, mulGoldenTensor fibOneGolden fibOneGolden
      (Fin.divNat (m := 2) (n := 2) b) (Fin.modNat (m := 2) (n := 2) b) =
        fibOneOneStackGolden b := by
    decide +kernel
  rw [h, hgolden]

/-- The inverse change of bond coordinates of `1 ⊗ 1`: its first 2 columns are the
sitewise right intertwiner onto the target block, the remaining 2 columns span the joint
kernel of the letters (data file §3.1). -/
def fibOneOneGaugeInvGolden : Matrix (Fin 4) (Fin 4) GoldenInt :=
  !![⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]

/-- The change of bond coordinates of `1 ⊗ 1` (data file §3.1). -/
def fibOneOneGaugeGolden : Matrix (Fin 4) (Fin 4) GoldenInt :=
  !![⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]

theorem fibOneOneGauge_mul_inv : fibOneOneGaugeGolden * fibOneOneGaugeInvGolden = 1 := by
  decide +kernel

theorem fibOneOneGaugeInv_mul : fibOneOneGaugeInvGolden * fibOneOneGaugeGolden = 1 := by
  decide +kernel

/-- The letters of the stacked product tensor of `1 ⊗ 1` in the block coordinates: block
diagonal, with the target block in the leading diagonal block and 2 one-by-one zero blocks
(data file §3.1). -/
def fibOneOneConjGolden : Fin 4 → Matrix (Fin 4) (Fin 4) GoldenInt
  | 0 =>
    !![⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 1 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 2 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 3 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]

/-- Every letter of the stacked product tensor of `1 ⊗ 1` carries the adapted basis into itself
block by block. -/
theorem fibOneOneStack_mul_gaugeInv (i : Fin 4) :
    fibOneOneStackGolden i * fibOneOneGaugeInvGolden =
      fibOneOneGaugeInvGolden * fibOneOneConjGolden i := by
  revert i
  decide +kernel

private theorem fibOneOne_triangular (i : Fin 4)
    (x y : BlockSpace (fun _ : Unit => 2) unitSlots 2)
    (h : unitOrd 2 y.1 < unitOrd 2 x.1) :
    fibOneOneConjGolden i (unitCoord 2 2 x) (unitCoord 2 2 y) = 0 := by
  revert i x y
  decide +kernel

private theorem fibOneOne_matched (i : Fin 4) (p q : Fin 2) :
    fibOneOneConjGolden i (unitCoord 2 2 ⟨Sum.inl unitSlot, p⟩)
      (unitCoord 2 2 ⟨Sum.inl unitSlot, q⟩) = fibOneGoldenMPS i p q := by
  revert i
  revert p q
  decide +kernel

private theorem fibOneOne_unmatched (i : Fin 4) (t : Fin 2) (p q : Fin 1) :
    fibOneOneConjGolden i (unitCoord 2 2 ⟨Sum.inr t, p⟩)
      (unitCoord 2 2 ⟨Sum.inr t, q⟩) = 0 := by
  revert i t p q
  decide +kernel

private theorem fibOneOne_offDiagonal (i : Fin 4)
    (x y : BlockSpace (fun _ : Unit => 2) unitSlots 2) (h : x.1 ≠ y.1) :
    fibOneOneConjGolden i (unitCoord 2 2 x) (unitCoord 2 2 y) = 0 := by
  revert i x y
  decide +kernel

/-- **The multi-block asymmetric compression datum of `1 ⊗ 1`** (P5 note, Theorem 7.7,
clauses (i)-(iii); data file §3.1): the stacked product compresses onto the single block
`fibOneMPS` with `z = 2` zero slots. -/
def fibOneOne_compression :
    MultiBlockCompression fibOneOneStack unitSlots (fun _ : Unit => fibOneMPS) :=
  MultiBlockCompression.ofGolden 2 (unitOrd 2) (unitCoord 2 2) fibOneOneStackGolden
    fibOneOneStack_eq (fun _ => fibOneGoldenMPS) (fun _ a => fibOneMPS_eq a) fibOneOneGaugeGolden
    fibOneOneGaugeInvGolden fibOneOneGauge_mul_inv fibOneOneGaugeInv_mul fibOneOneConjGolden
    fibOneOneStack_mul_gaugeInv fibOneOne_triangular
    (fun i s _ p q => by cases s; exact fibOneOne_matched i p q) fibOneOne_unmatched

/-- **The remainder of the compression of `1 ⊗ 1` vanishes**: the extension splits (data file
§3.1). -/
theorem fibOneOne_remainder_eq_zero (i : Fin 4) : fibOneOne_compression.remainder i = 0 :=
  fibOneOne_compression.remainder_eq_zero_of_goldenGauge (hG := fibOneOneGauge_mul_inv)
    (hG' := fibOneOneGaugeInv_mul) rfl fibOneOneStack_eq fibOneOneStack_mul_gaugeInv
    fibOneOne_offDiagonal i

/-- **The admissibility projector is idempotent**, `O_1 O_1 = O_1`, as an identity of periodic
operators at every positive system size (data file §2, §3.1). -/
theorem fibOne_mul_fibOne (L : ℕ) (hL : 0 < L) :
    MPOTensor.mpo fibOne L * MPOTensor.mpo fibOne L = MPOTensor.mpo fibOne L := by
  have h := MPOTensor.mpo_mul_eq_sum_of_multiBlockCompression (C := fun _ : Unit => fibOne)
    fibOneOne_compression L hL
  rwa [Fintype.sum_unique] at h

/-! ### The projector times the `τ` family -/

/-- The stacked product tensor of `1 ⊗ τ`, of bond dimension 6 (data file §3.2). -/
def fibOneTauStack : MPSTensor 4 6 := (MPOTensor.mulTensor fibOne fibTau).toMPSTensor

/-- The golden matrices of the stacked product tensor of `1 ⊗ τ`, in the bond order of
`finProdFinEquiv` (data file §3.2). -/
def fibOneTauStackGolden : Fin 4 → Matrix (Fin 6) (Fin 6) GoldenInt
  | 0 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 1 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 2 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 3 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, -1, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, -1, 0⟩]

theorem fibOneTauStack_eq (a : Fin 4) :
    fibOneTauStack a = complexOfGolden (fibOneTauStackGolden a) := by
  have h : fibOneTauStack a = complexOfGolden (mulGoldenTensor fibOneGolden fibTauGolden
      (Fin.divNat (m := 2) (n := 2) a) (Fin.modNat (m := 2) (n := 2) a)) :=
    mulTensor_complexOfGolden fibOneGolden fibTauGolden _ _
  have hgolden : ∀ b : Fin 4, mulGoldenTensor fibOneGolden fibTauGolden
      (Fin.divNat (m := 2) (n := 2) b) (Fin.modNat (m := 2) (n := 2) b) =
        fibOneTauStackGolden b := by
    decide +kernel
  rw [h, hgolden]

/-- The inverse change of bond coordinates of `1 ⊗ τ`: its first 3 columns are the
sitewise right intertwiner onto the target block, the remaining 3 columns span the joint
kernel of the letters (data file §3.2). -/
def fibOneTauGaugeInvGolden : Matrix (Fin 6) (Fin 6) GoldenInt :=
  !![⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -2, 0, -1⟩, ⟨0, 0, 0, 0⟩, ⟨0, -3, 0, -2⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 1⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩]

/-- The change of bond coordinates of `1 ⊗ τ` (data file §3.2). -/
def fibOneTauGaugeGolden : Matrix (Fin 6) (Fin 6) GoldenInt :=
  !![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, -1⟩, ⟨1, 0, -1, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨1, 0, -1, 0⟩, ⟨0, -1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, -1, 0, 1⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, -1, 0, 1⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]

theorem fibOneTauGauge_mul_inv : fibOneTauGaugeGolden * fibOneTauGaugeInvGolden = 1 := by
  decide +kernel

theorem fibOneTauGaugeInv_mul : fibOneTauGaugeInvGolden * fibOneTauGaugeGolden = 1 := by
  decide +kernel

/-- The letters of the stacked product tensor of `1 ⊗ τ` in the block coordinates: block
diagonal, with the target block in the leading diagonal block and 3 one-by-one zero blocks
(data file §3.2). -/
def fibOneTauConjGolden : Fin 4 → Matrix (Fin 6) (Fin 6) GoldenInt
  | 0 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 1 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 2 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 3 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]

/-- Every letter of the stacked product tensor of `1 ⊗ τ` carries the adapted basis into itself
block by block. -/
theorem fibOneTauStack_mul_gaugeInv (i : Fin 4) :
    fibOneTauStackGolden i * fibOneTauGaugeInvGolden =
      fibOneTauGaugeInvGolden * fibOneTauConjGolden i := by
  revert i
  decide +kernel

private theorem fibOneTau_triangular (i : Fin 4)
    (x y : BlockSpace (fun _ : Unit => 3) unitSlots 3)
    (h : unitOrd 3 y.1 < unitOrd 3 x.1) :
    fibOneTauConjGolden i (unitCoord 3 3 x) (unitCoord 3 3 y) = 0 := by
  revert i x y
  decide +kernel

private theorem fibOneTau_matched (i : Fin 4) (p q : Fin 3) :
    fibOneTauConjGolden i (unitCoord 3 3 ⟨Sum.inl unitSlot, p⟩)
      (unitCoord 3 3 ⟨Sum.inl unitSlot, q⟩) = fibTauGoldenMPS i p q := by
  revert i
  revert p q
  decide +kernel

private theorem fibOneTau_unmatched (i : Fin 4) (t : Fin 3) (p q : Fin 1) :
    fibOneTauConjGolden i (unitCoord 3 3 ⟨Sum.inr t, p⟩)
      (unitCoord 3 3 ⟨Sum.inr t, q⟩) = 0 := by
  revert i t p q
  decide +kernel

private theorem fibOneTau_offDiagonal (i : Fin 4)
    (x y : BlockSpace (fun _ : Unit => 3) unitSlots 3) (h : x.1 ≠ y.1) :
    fibOneTauConjGolden i (unitCoord 3 3 x) (unitCoord 3 3 y) = 0 := by
  revert i x y
  decide +kernel

/-- **The multi-block asymmetric compression datum of `1 ⊗ τ`** (P5 note, Theorem 7.7,
clauses (i)-(iii); data file §3.2): the stacked product compresses onto the single block
`fibTauMPS` with `z = 3` zero slots. -/
def fibOneTau_compression :
    MultiBlockCompression fibOneTauStack unitSlots (fun _ : Unit => fibTauMPS) :=
  MultiBlockCompression.ofGolden 3 (unitOrd 3) (unitCoord 3 3) fibOneTauStackGolden
    fibOneTauStack_eq (fun _ => fibTauGoldenMPS) (fun _ a => fibTauMPS_eq a) fibOneTauGaugeGolden
    fibOneTauGaugeInvGolden fibOneTauGauge_mul_inv fibOneTauGaugeInv_mul fibOneTauConjGolden
    fibOneTauStack_mul_gaugeInv fibOneTau_triangular
    (fun i s _ p q => by cases s; exact fibOneTau_matched i p q) fibOneTau_unmatched

/-- **The remainder of the compression of `1 ⊗ τ` vanishes**: the extension splits (data file
§3.2). -/
theorem fibOneTau_remainder_eq_zero (i : Fin 4) : fibOneTau_compression.remainder i = 0 :=
  fibOneTau_compression.remainder_eq_zero_of_goldenGauge (hG := fibOneTauGauge_mul_inv)
    (hG' := fibOneTauGaugeInv_mul) rfl fibOneTauStack_eq fibOneTauStack_mul_gaugeInv
    fibOneTau_offDiagonal i

/-- **The admissibility projector is a left unit on the `τ` family**, `O_1 O_τ = O_τ`, as an
identity of periodic operators at every positive system size (data file §2, §3.2). -/
theorem fibOne_mul_fibTau (L : ℕ) (hL : 0 < L) :
    MPOTensor.mpo fibOne L * MPOTensor.mpo fibTau L = MPOTensor.mpo fibTau L := by
  have h := MPOTensor.mpo_mul_eq_sum_of_multiBlockCompression (C := fun _ : Unit => fibTau)
    fibOneTau_compression L hL
  rwa [Fintype.sum_unique] at h

/-! ### The `τ` family times the projector -/

/-- The stacked product tensor of `τ ⊗ 1`, of bond dimension 6 (data file §3.3). -/
def fibTauOneStack : MPSTensor 4 6 := (MPOTensor.mulTensor fibTau fibOne).toMPSTensor

/-- The golden matrices of the stacked product tensor of `τ ⊗ 1`, in the bond order of
`finProdFinEquiv` (data file §3.3). -/
def fibTauOneStackGolden : Fin 4 → Matrix (Fin 6) (Fin 6) GoldenInt
  | 0 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 1 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 1, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 2 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 3 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, -1, 0⟩, ⟨0, 0, -1, 0⟩]

theorem fibTauOneStack_eq (a : Fin 4) :
    fibTauOneStack a = complexOfGolden (fibTauOneStackGolden a) := by
  have h : fibTauOneStack a = complexOfGolden (mulGoldenTensor fibTauGolden fibOneGolden
      (Fin.divNat (m := 2) (n := 2) a) (Fin.modNat (m := 2) (n := 2) a)) :=
    mulTensor_complexOfGolden fibTauGolden fibOneGolden _ _
  have hgolden : ∀ b : Fin 4, mulGoldenTensor fibTauGolden fibOneGolden
      (Fin.divNat (m := 2) (n := 2) b) (Fin.modNat (m := 2) (n := 2) b) =
        fibTauOneStackGolden b := by
    decide +kernel
  rw [h, hgolden]

/-- The inverse change of bond coordinates of `τ ⊗ 1`: its first 3 columns are the
sitewise right intertwiner onto the target block, the remaining 3 columns span the joint
kernel of the letters (data file §3.3). -/
def fibTauOneGaugeInvGolden : Matrix (Fin 6) (Fin 6) GoldenInt :=
  !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩;
     ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, 1, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, -1, 0, 0⟩, ⟨0, 0, 0, -1⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, -1, 0⟩]

/-- The change of bond coordinates of `τ ⊗ 1` (data file §3.3). -/
def fibTauOneGaugeGolden : Matrix (Fin 6) (Fin 6) GoldenInt :=
  !![⟨1, 0, -1, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩;
     ⟨-1, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨1, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩;
     ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩]

theorem fibTauOneGauge_mul_inv : fibTauOneGaugeGolden * fibTauOneGaugeInvGolden = 1 := by
  decide +kernel

theorem fibTauOneGaugeInv_mul : fibTauOneGaugeInvGolden * fibTauOneGaugeGolden = 1 := by
  decide +kernel

/-- The letters of the stacked product tensor of `τ ⊗ 1` in the block coordinates: block
diagonal, with the target block in the leading diagonal block and 3 one-by-one zero blocks
(data file §3.3). -/
def fibTauOneConjGolden : Fin 4 → Matrix (Fin 6) (Fin 6) GoldenInt
  | 0 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 1 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 2 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  | 3 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]

/-- Every letter of the stacked product tensor of `τ ⊗ 1` carries the adapted basis into itself
block by block. -/
theorem fibTauOneStack_mul_gaugeInv (i : Fin 4) :
    fibTauOneStackGolden i * fibTauOneGaugeInvGolden =
      fibTauOneGaugeInvGolden * fibTauOneConjGolden i := by
  revert i
  decide +kernel

private theorem fibTauOne_triangular (i : Fin 4)
    (x y : BlockSpace (fun _ : Unit => 3) unitSlots 3)
    (h : unitOrd 3 y.1 < unitOrd 3 x.1) :
    fibTauOneConjGolden i (unitCoord 3 3 x) (unitCoord 3 3 y) = 0 := by
  revert i x y
  decide +kernel

private theorem fibTauOne_matched (i : Fin 4) (p q : Fin 3) :
    fibTauOneConjGolden i (unitCoord 3 3 ⟨Sum.inl unitSlot, p⟩)
      (unitCoord 3 3 ⟨Sum.inl unitSlot, q⟩) = fibTauGoldenMPS i p q := by
  revert i
  revert p q
  decide +kernel

private theorem fibTauOne_unmatched (i : Fin 4) (t : Fin 3) (p q : Fin 1) :
    fibTauOneConjGolden i (unitCoord 3 3 ⟨Sum.inr t, p⟩)
      (unitCoord 3 3 ⟨Sum.inr t, q⟩) = 0 := by
  revert i t p q
  decide +kernel

private theorem fibTauOne_offDiagonal (i : Fin 4)
    (x y : BlockSpace (fun _ : Unit => 3) unitSlots 3) (h : x.1 ≠ y.1) :
    fibTauOneConjGolden i (unitCoord 3 3 x) (unitCoord 3 3 y) = 0 := by
  revert i x y
  decide +kernel

/-- **The multi-block asymmetric compression datum of `τ ⊗ 1`** (P5 note, Theorem 7.7,
clauses (i)-(iii); data file §3.3): the stacked product compresses onto the single block
`fibTauMPS` with `z = 3` zero slots. -/
def fibTauOne_compression :
    MultiBlockCompression fibTauOneStack unitSlots (fun _ : Unit => fibTauMPS) :=
  MultiBlockCompression.ofGolden 3 (unitOrd 3) (unitCoord 3 3) fibTauOneStackGolden
    fibTauOneStack_eq (fun _ => fibTauGoldenMPS) (fun _ a => fibTauMPS_eq a) fibTauOneGaugeGolden
    fibTauOneGaugeInvGolden fibTauOneGauge_mul_inv fibTauOneGaugeInv_mul fibTauOneConjGolden
    fibTauOneStack_mul_gaugeInv fibTauOne_triangular
    (fun i s _ p q => by cases s; exact fibTauOne_matched i p q) fibTauOne_unmatched

/-- **The remainder of the compression of `τ ⊗ 1` vanishes**: the extension splits (data file
§3.3). -/
theorem fibTauOne_remainder_eq_zero (i : Fin 4) : fibTauOne_compression.remainder i = 0 :=
  fibTauOne_compression.remainder_eq_zero_of_goldenGauge (hG := fibTauOneGauge_mul_inv)
    (hG' := fibTauOneGaugeInv_mul) rfl fibTauOneStack_eq fibTauOneStack_mul_gaugeInv
    fibTauOne_offDiagonal i

/-- **The admissibility projector is a right unit on the `τ` family**, `O_τ O_1 = O_τ`, as an
identity of periodic operators at every positive system size (data file §2, §3.3). -/
theorem fibTau_mul_fibOne (L : ℕ) (hL : 0 < L) :
    MPOTensor.mpo fibTau L * MPOTensor.mpo fibOne L = MPOTensor.mpo fibTau L := by
  have h := MPOTensor.mpo_mul_eq_sum_of_multiBlockCompression (C := fun _ : Unit => fibTau)
    fibTauOne_compression L hL
  rwa [Fintype.sum_unique] at h

end FibonacciCompression
