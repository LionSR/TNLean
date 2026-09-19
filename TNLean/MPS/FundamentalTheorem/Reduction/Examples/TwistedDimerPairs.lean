/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.TwistedDimerPairZeroOne
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.TwistedDimerPairOneZero
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.TwistedDimerPairOneOne

/-!
# The fusion rule of the graded quantum-dimer twist

The four pairwise letter identities of the graded quantum-dimer twist at `x = 7/8`
(`TwistedDimer` for the fusion of the zero sector with itself and `TwistedDimerPairZeroOne`,
`TwistedDimerPairOneZero`, `TwistedDimerPairOneOne` for the other three pairs) assembled into
one statement about every pair of sectors: the stacked product of the sectors `f` and `f'` is the
multi-block asymmetric compression
(`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5, Theorem 7.7) onto
the sector `f + f'` with the weight `x/2 = 7/16` and the sector `f + f' + 1` with the weight
`y/2 = 1/16`, with eight zero slots and a vanishing remainder. This is the
`ℤ/2`-graded fusion rule `M_f M_{f'} = (x/2) M_{f+f'} ⊕ (y/2) M_{f+f'+1} ⊕ 0` of the strategy note
(`Notes/OpenProblemsTN/strategies/p6_round44_graded_dimer_twist.tex`, `thm:p6-r44-z2`(v),
`eq:p6-r44-z2-fusion`), stated in normalized form as the P6 resolution `thm:p6-round44-z2` of
`Notes/OpenProblemsTN/problems/p6_rfp_structure_constant_l_dependence.tex` (exact data in
`Notes/OpenProblemsTN/checks/p6_examples_compression_data.md`, §1.2–1.4); its word traces give
the periodic coefficients `c^{(L)} = (7/16)^L + (1/16)^L` of every pair.

## Main results

* `P6Compression.dimerFusion_letter_int`: the integer letter identity of every pair of sectors.
* `P6Compression.dimerFusionCompression`: the compression datum of Theorem 7.7 for every pair,
  with `P6Compression.dimerFusion_remainder` its vanishing remainder.
* `P6Compression.dimerFusion_trace_evalWord`: the word-trace identity
  `tr((M_f M_{f'})^w) = (7/16)^{|w|} tr(M_{f+f'}^w) + (1/16)^{|w|} tr(M_{f+f'+1}^w)`.
* `P6Compression.dimerFusion_isReduction`, `P6Compression.dimerFusion_left_mul_right_of_ne`,
  `P6Compression.dimerFusion_mul_right_eq_right_mul`,
  `P6Compression.dimerFusion_left_mul_eq_mul_left`, `P6Compression.dimerFusion_z_eq`,
  `P6Compression.dimerFusion_dim_eq`: the reduction pairs, their biorthogonality, the sitewise
  intertwiners, the eight zero slots and the dimension count of every pair.
-/

open scoped Matrix Kronecker

namespace P6Compression

open MPSTensor

/-- **The integer letter identity of every pair of sectors** (`p6_examples_compression_data.md`,
§1.3): the four exhaustive checks assembled. -/
theorem dimerFusion_letter_int (f f' : Fin 2) (a : Fin 64) :
    (2 : ℤ) • dimerStackedInt f f' a =
      ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt f f') s a := by
  fin_cases f <;> fin_cases f'
  · exact dimer_letter_int a
  · exact dimerZeroOne_letter_int a
  · exact dimerOneZero_letter_int a
  · exact dimerOneOne_letter_int a

/-- **The multi-block asymmetric compression datum of every fusion of two sectors** (P5 note,
Theorem 7.7(i)–(iii)): the stacked product of the sectors `f` and `f'` compresses onto the two
normal sectors `f + f'` and `f + f' + 1` (not gauge equivalent by `dimerBlocks_not_gaugeEquiv`)
with the weights `7/16` and `1/16`, with eight zero slots. -/
noncomputable def dimerFusionCompression (f f' : Fin 2) :
    MultiBlockCompression (D := fun _ : Fin 2 => 4) (dimerStacked f f') pairSlots
      fun s => dimerWeights s • dimerBlocks f f' s :=
  dimerCompressionOfLetterIdentity f f' (dimerFusion_letter_int f f')

/-- **The remainder of every fusion vanishes** (P5 note, Theorem 7.7(vi)): the conjugated
tensor is block diagonal, so every extension splits. -/
theorem dimerFusion_remainder (f f' : Fin 2) : (dimerFusionCompression f f').remainder = 0 :=
  remainder_dimerCompressionOfLetterIdentity f f' (dimerFusion_letter_int f f')

/-- **The word-trace fusion rule of the graded dimer twist**: for every pair of sectors,
`tr((M_f M_{f'})^w) = (7/16)^{|w|} tr(M_{f+f'}^w) + (1/16)^{|w|} tr(M_{f+f'+1}^w)`, the fusion
rule `eq:p6-r44-z2-fusion` of the strategy note (`thm:p6-r44-z2`(v)) read on word traces at
`x = 7/8` (`p6_examples_compression_data.md`, §1.4). -/
theorem dimerFusion_trace_evalWord (f f' : Fin 2) (w : List (Fin 64)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord (dimerStacked f f') w) =
      (7 / 16 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord (dimerTarget (f + f')) w) +
        (1 / 16 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord (dimerTarget (f + f' + 1)) w) :=
  dimer_trace_evalWord_of_compression f f' (dimerFusionCompression f f') w hw

/-- **Biorthogonal compression onto each fusion channel of every fusion** (P5 note,
Theorem 7.7(iv)–(v)). -/
theorem dimerFusion_isReduction (f f' : Fin 2) (s : {s // s ∈ pairSlots}) :
    IsReduction (dimerStacked f f') (dimerWeights s.1 • dimerBlocks f f' s.1)
      ((dimerFusionCompression f f').left s) ((dimerFusionCompression f f').right s) :=
  (dimerFusionCompression f f').isReduction s

/-- Two distinct fusion channels of every fusion are biorthogonal (P5 note, Theorem 7.7(iv)). -/
theorem dimerFusion_left_mul_right_of_ne (f f' : Fin 2) {s t : {s // s ∈ pairSlots}}
    (h : s ≠ t) :
    (dimerFusionCompression f f').left s * (dimerFusionCompression f f').right t = 0 :=
  (dimerFusionCompression f f').left_mul_right_of_ne h

/-- **The sitewise right intertwiner of each channel of every fusion**:
`B^a V_s = V_s (μ_s M_s^a)` (`p6_examples_compression_data.md`, §1.3). -/
theorem dimerFusion_mul_right_eq_right_mul (f f' : Fin 2) (a : Fin 64)
    (s : {s // s ∈ pairSlots}) :
    dimerStacked f f' a * (dimerFusionCompression f f').right s =
      (dimerFusionCompression f f').right s * (dimerWeights s.1 • dimerBlocks f f' s.1) a :=
  (dimerFusionCompression f f').mul_right_eq_right_mul (dimerFusion_remainder f f') a s

/-- **The sitewise left intertwiner of each channel of every fusion**:
`W_s B^a = (μ_s M_s^a) W_s`. -/
theorem dimerFusion_left_mul_eq_mul_left (f f' : Fin 2) (a : Fin 64)
    (s : {s // s ∈ pairSlots}) :
    (dimerFusionCompression f f').left s * dimerStacked f f' a =
      (dimerWeights s.1 • dimerBlocks f f' s.1) a * (dimerFusionCompression f f').left s :=
  (dimerFusionCompression f f').left_mul_eq_mul_left (dimerFusion_remainder f f') a s

/-- Every fusion has eight zero slots. -/
theorem dimerFusion_z_eq (f f' : Fin 2) : (dimerFusionCompression f f').z = 8 := rfl

/-- **The dimension count of every fusion**: `16 = 4 + 4 + 8` (P5 note, Theorem 7.7(vii)). -/
theorem dimerFusion_dim_eq (f f' : Fin 2) : (16 : ℕ) = ∑ _s ∈ pairSlots, 4 + 8 :=
  (dimerFusionCompression f f').dim_eq

end P6Compression
