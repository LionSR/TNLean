/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.TwistedDimer

/-!
# The graded quantum-dimer twist: the fusion of the one sector with the zero sector

The multi-block asymmetric compression
(`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5, Theorem 7.7) of
the stacked product of the sector-`1` and sector-`0` tensors of the graded quantum-dimer twist
at `x = 7/8` (`Notes/OpenProblemsTN/checks/p6_examples_compression_data.md`, §1, the pair
`(f, f') = (1, 0)`). The sector tensors, the adapted gauge and the pair-generic reduction of the
letter identity to two exhaustive checks are those of `TwistedDimer`; this file carries out the
two checks for this pair of sectors and records the resulting compression datum.

The stacked product compresses onto the sector `1` with the weight `x/2 = 7/16` and onto the
sector `0` with the weight `y/2 = 1/16`, with eight zero slots left over and a vanishing
remainder, exactly as for the fusion of the zero sector with itself (strategy note
`Notes/OpenProblemsTN/strategies/p6_round44_graded_dimer_twist.tex`, `thm:p6-round44-z2`).

## Main results

* `P6Compression.dimerOneZero_letter_int`: the integer letter identity of the pair.
* `P6Compression.dimerOneZeroCompression`: the compression datum of Theorem 7.7 for the pair, with
  `P6Compression.dimerOneZero_remainder` its vanishing remainder.
* `P6Compression.dimerOneZero_trace_evalWord`: the word-trace identity
  `tr(B^w) = (7/16)^{|w|} tr(M_1^w) + (1/16)^{|w|} tr(M_0^w)`.
* `P6Compression.dimerOneZero_mul_right_eq_right_mul`,
  `P6Compression.dimerOneZero_left_mul_eq_mul_left`: the sitewise intertwiners of each channel.
-/

open scoped Matrix Kronecker

namespace P6Compression

open MPSTensor

/-! ### The letter identity -/

private theorem dimerOneZero_letter_int_even : ∀ a : Fin 64,
    dimerFlag (Fin.divNat (m := 8) (n := 8) a) = 0 →
      dimerFlag (Fin.modNat (m := 8) (n := 8) a) = 0 →
        (2 : ℤ) • dimerStackEven 1 0 (Fin.divNat (m := 8) (n := 8) a)
            (Fin.modNat (m := 8) (n := 8) a) =
          ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt 1 0) s a := by
  decide +kernel

private theorem dimerOneZero_letter_int_odd : ∀ a : Fin 64,
    dimerFlag (Fin.divNat (m := 8) (n := 8) a) = 1 →
      dimerFlag (Fin.modNat (m := 8) (n := 8) a) = 1 →
        (2 : ℤ) • dimerStackOdd 1 0 (Fin.divNat (m := 8) (n := 8) a)
            (Fin.modNat (m := 8) (n := 8) a) =
          ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt 1 0) s a := by
  decide +kernel

/-- **The integer letter identity of the fusion of the one sector with the zero sector**
(`p6_examples_compression_data.md`, §1.3). -/
theorem dimerOneZero_letter_int (a : Fin 64) :
    (2 : ℤ) • dimerStackedInt 1 0 a =
      ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt 1 0) s a :=
  dimer_letter_int_of_halves 1 0 dimerOneZero_letter_int_even dimerOneZero_letter_int_odd a

/-! ### The compression datum -/

/-- **The multi-block asymmetric compression datum** (P5 note, Theorem 7.7(i)–(iii)) for the
fusion of the one sector with the zero sector: the two inequivalent normal sectors `1` and `0` with
the weights `7/16` and `1/16`, and eight zero slots. -/
noncomputable def dimerOneZeroCompression :
    MultiBlockCompression (D := fun _ : Fin 2 => 4) (dimerStacked 1 0) pairSlots
      fun s => dimerWeights s • dimerBlocks 1 0 s :=
  dimerCompressionOfLetterIdentity 1 0 dimerOneZero_letter_int

/-- **The remainder vanishes** (P5 note, Theorem 7.7(vi)): the conjugated tensor is block
diagonal, so the extension splits. -/
theorem dimerOneZero_remainder : dimerOneZeroCompression.remainder = 0 :=
  remainder_dimerCompressionOfLetterIdentity 1 0 dimerOneZero_letter_int

/-! ### Consequences -/

/-- **The word-trace identity of the fusion of the one sector with the zero sector**: the periodic
coefficient `c^{(L)} = (7/16)^L + (1/16)^L` (`p6_examples_compression_data.md`, §1.4). -/
theorem dimerOneZero_trace_evalWord (w : List (Fin 64)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord (dimerStacked 1 0) w) =
      (7 / 16 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord (dimerTarget 1) w) +
        (1 / 16 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord (dimerTarget 0) w) :=
  dimer_trace_evalWord_of_compression 1 0 dimerOneZeroCompression w hw

/-- **Biorthogonal compression onto each fusion channel** (P5 note, Theorem 7.7(iv)–(v)). -/
theorem dimerOneZero_isReduction (s : {s // s ∈ pairSlots}) :
    IsReduction (dimerStacked 1 0) (dimerWeights s.1 • dimerBlocks 1 0 s.1)
      (dimerOneZeroCompression.left s) (dimerOneZeroCompression.right s) :=
  dimerOneZeroCompression.isReduction s

/-- Two distinct fusion channels are biorthogonal (P5 note, Theorem 7.7(iv)). -/
theorem dimerOneZero_left_mul_right_of_ne {s t : {s // s ∈ pairSlots}} (h : s ≠ t) :
    dimerOneZeroCompression.left s * dimerOneZeroCompression.right t = 0 :=
  dimerOneZeroCompression.left_mul_right_of_ne h

/-- **The sitewise right intertwiner of each channel**: `B^a V_s = V_s (μ_s M_s^a)`
(`p6_examples_compression_data.md`, §1.3). -/
theorem dimerOneZero_mul_right_eq_right_mul (a : Fin 64) (s : {s // s ∈ pairSlots}) :
    dimerStacked 1 0 a * dimerOneZeroCompression.right s =
      dimerOneZeroCompression.right s * (dimerWeights s.1 • dimerBlocks 1 0 s.1) a :=
  dimerOneZeroCompression.mul_right_eq_right_mul dimerOneZero_remainder a s

/-- **The sitewise left intertwiner of each channel**: `W_s B^a = (μ_s M_s^a) W_s`. -/
theorem dimerOneZero_left_mul_eq_mul_left (a : Fin 64) (s : {s // s ∈ pairSlots}) :
    dimerOneZeroCompression.left s * dimerStacked 1 0 a =
      (dimerWeights s.1 • dimerBlocks 1 0 s.1) a * dimerOneZeroCompression.left s :=
  dimerOneZeroCompression.left_mul_eq_mul_left dimerOneZero_remainder a s

/-- The fusion has eight zero slots. -/
theorem dimerOneZero_z_eq : dimerOneZeroCompression.z = 8 := rfl

/-- **The dimension count of the fusion**: `16 = 4 + 4 + 8` (P5 note, Theorem 7.7(vii)). -/
theorem dimerOneZero_dim_eq : (16 : ℕ) = ∑ _s ∈ pairSlots, 4 + 8 :=
  dimerOneZeroCompression.dim_eq

end P6Compression
