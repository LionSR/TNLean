/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.TwistedDimer

/-!
# The graded quantum-dimer twist: the fusion of the zero sector with the one sector

The multi-block asymmetric compression
(`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5, Theorem 7.7) of
the stacked product of the sector-`0` and sector-`1` tensors of the graded quantum-dimer twist
at `x = 7/8` (`Notes/OpenProblemsTN/checks/p6_examples_compression_data.md`, §1, the pair
`(f, f') = (0, 1)`). The sector tensors, the adapted gauge and the pair-generic reduction of the
letter identity to two exhaustive checks are those of `TwistedDimer`; this file carries out the
two checks for this pair of sectors and records the resulting compression datum.

The stacked product compresses onto the sector `1` with the weight `x/2 = 7/16` and onto the
sector `0` with the weight `y/2 = 1/16`, with eight zero slots left over and a vanishing
remainder, exactly as for the fusion of the zero sector with itself (strategy note
`Notes/OpenProblemsTN/strategies/p6_round44_graded_dimer_twist.tex`, `thm:p6-round44-z2`).

## Main results

* `P6Compression.dimerZeroOne_letter_int`: the integer letter identity of the pair.
* `P6Compression.dimerZeroOneCompression`: the compression datum of Theorem 7.7 for the pair, with
  `P6Compression.dimerZeroOne_remainder` its vanishing remainder.
* `P6Compression.dimerZeroOne_trace_evalWord`: the word-trace identity
  `tr(B^w) = (7/16)^{|w|} tr(M_1^w) + (1/16)^{|w|} tr(M_0^w)`.
* `P6Compression.dimerZeroOne_mul_right_eq_right_mul`,
  `P6Compression.dimerZeroOne_left_mul_eq_mul_left`: the sitewise intertwiners of each channel.
-/

open scoped Matrix Kronecker

namespace P6Compression

open MPSTensor

/-! ### The letter identity -/

private theorem dimerZeroOne_letter_int_even : ∀ a : Fin 64,
    dimerFlag (Fin.divNat (m := 8) (n := 8) a) = 0 →
      dimerFlag (Fin.modNat (m := 8) (n := 8) a) = 0 →
        (2 : ℤ) • dimerStackEven 0 1 (Fin.divNat (m := 8) (n := 8) a)
            (Fin.modNat (m := 8) (n := 8) a) =
          ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt 0 1) s a := by
  decide +kernel

private theorem dimerZeroOne_letter_int_odd : ∀ a : Fin 64,
    dimerFlag (Fin.divNat (m := 8) (n := 8) a) = 1 →
      dimerFlag (Fin.modNat (m := 8) (n := 8) a) = 1 →
        (2 : ℤ) • dimerStackOdd 0 1 (Fin.divNat (m := 8) (n := 8) a)
            (Fin.modNat (m := 8) (n := 8) a) =
          ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt 0 1) s a := by
  decide +kernel

/-- **The integer letter identity of the fusion of the zero sector with the one sector**
(`p6_examples_compression_data.md`, §1.3). -/
theorem dimerZeroOne_letter_int (a : Fin 64) :
    (2 : ℤ) • dimerStackedInt 0 1 a =
      ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt 0 1) s a :=
  dimer_letter_int_of_halves 0 1 dimerZeroOne_letter_int_even dimerZeroOne_letter_int_odd a

/-! ### The compression datum -/

/-- **The multi-block asymmetric compression datum** (P5 note, Theorem 7.7(i)–(iii)) for the
fusion of the zero sector with the one sector: the two inequivalent normal sectors `1` and `0` with
the weights `7/16` and `1/16`, and eight zero slots. -/
noncomputable def dimerZeroOneCompression :
    MultiBlockCompression (D := fun _ : Fin 2 => 4) (dimerStacked 0 1) pairSlots
      fun s => dimerWeights s • dimerBlocks 0 1 s :=
  dimerCompressionOfLetterIdentity 0 1 dimerZeroOne_letter_int

/-- **The remainder vanishes** (P5 note, Theorem 7.7(vi)): the conjugated tensor is block
diagonal, so the extension splits. -/
theorem dimerZeroOne_remainder : dimerZeroOneCompression.remainder = 0 :=
  remainder_dimerCompressionOfLetterIdentity 0 1 dimerZeroOne_letter_int

/-! ### Consequences -/

/-- **The word-trace identity of the fusion of the zero sector with the one sector**: the periodic
coefficient `c^{(L)} = (7/16)^L + (1/16)^L` (`p6_examples_compression_data.md`, §1.4). -/
theorem dimerZeroOne_trace_evalWord (w : List (Fin 64)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord (dimerStacked 0 1) w) =
      (7 / 16 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord (dimerTarget 1) w) +
        (1 / 16 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord (dimerTarget 0) w) :=
  dimer_trace_evalWord_of_compression 0 1 dimerZeroOneCompression w hw

/-- **Biorthogonal compression onto each fusion channel** (P5 note, Theorem 7.7(iv)–(v)). -/
theorem dimerZeroOne_isReduction (s : {s // s ∈ pairSlots}) :
    IsReduction (dimerStacked 0 1) (dimerWeights s.1 • dimerBlocks 0 1 s.1)
      (dimerZeroOneCompression.left s) (dimerZeroOneCompression.right s) :=
  dimerZeroOneCompression.isReduction s

/-- Two distinct fusion channels are biorthogonal (P5 note, Theorem 7.7(iv)). -/
theorem dimerZeroOne_left_mul_right_of_ne {s t : {s // s ∈ pairSlots}} (h : s ≠ t) :
    dimerZeroOneCompression.left s * dimerZeroOneCompression.right t = 0 :=
  dimerZeroOneCompression.left_mul_right_of_ne h

/-- **The sitewise right intertwiner of each channel**: `B^a V_s = V_s (μ_s M_s^a)`
(`p6_examples_compression_data.md`, §1.3). -/
theorem dimerZeroOne_mul_right_eq_right_mul (a : Fin 64) (s : {s // s ∈ pairSlots}) :
    dimerStacked 0 1 a * dimerZeroOneCompression.right s =
      dimerZeroOneCompression.right s * (dimerWeights s.1 • dimerBlocks 0 1 s.1) a :=
  dimerZeroOneCompression.mul_right_eq_right_mul dimerZeroOne_remainder a s

/-- **The sitewise left intertwiner of each channel**: `W_s B^a = (μ_s M_s^a) W_s`. -/
theorem dimerZeroOne_left_mul_eq_mul_left (a : Fin 64) (s : {s // s ∈ pairSlots}) :
    dimerZeroOneCompression.left s * dimerStacked 0 1 a =
      (dimerWeights s.1 • dimerBlocks 0 1 s.1) a * dimerZeroOneCompression.left s :=
  dimerZeroOneCompression.left_mul_eq_mul_left dimerZeroOne_remainder a s

/-- The fusion has eight zero slots. -/
theorem dimerZeroOne_z_eq : dimerZeroOneCompression.z = 8 := rfl

/-- **The dimension count of the fusion**: `16 = 4 + 4 + 8` (P5 note, Theorem 7.7(vii)). -/
theorem dimerZeroOne_dim_eq : (16 : ℕ) = ∑ _s ∈ pairSlots, 4 + 8 :=
  dimerZeroOneCompression.dim_eq

end P6Compression
