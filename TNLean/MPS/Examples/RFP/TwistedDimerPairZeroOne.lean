/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.RFP.TwistedDimer

/-!
# The graded quantum-dimer twist: the fusion of the zero sector with the one sector

The integer letter identity of the stacked product of the sector-`0` and sector-`1` tensors
of the graded quantum-dimer twist at `x = 7/8`
(`Notes/OpenProblemsTN/checks/p6_examples_compression_data.md`, §1, the pair
`(f, f') = (0, 1)`), the input to the multi-block asymmetric compression
(`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5, Theorem 7.7) of
this pair. The sector tensors, the adapted gauge and the pair-generic reduction of the letter
identity to two exhaustive checks are those of `TwistedDimer`; this file carries out the two
checks for this pair of sectors.

The stacked product compresses onto the sector `1` with the weight `x/2 = 7/16` and onto the
sector `0` with the weight `y/2 = 1/16`, with eight zero slots left over and a vanishing
remainder, exactly as for the fusion of the zero sector with itself: this is one case of the
fusion rule `M_f M_{f'} = (x/2) M_{f+f'} ⊕ (y/2) M_{f+f'+1} ⊕ 0` of the strategy note
(`Notes/OpenProblemsTN/strategies/p6_round44_graded_dimer_twist.tex`, `thm:p6-r44-z2`(v),
`eq:p6-r44-z2-fusion`), which the P6 resolution `thm:p6-round44-z2` of
`Notes/OpenProblemsTN/problems/p6_rfp_structure_constant_l_dependence.tex` states in normalized
form and `TwistedDimerPairs` records uniformly for every pair of sectors.

**Source.** Project construction, not printed in Cirac, Pérez-García, Schuch, Verstraete 2017
(arXiv:1606.00608); it bears on the open question at `Papers/1606.00608/MPDO-22-12-17-2.tex`
line 995 on structure coefficients of Theorem 4.14 (lines 972--993) that depend on the length
`L`. The full source discussion and its scope are in the header of `TwistedDimer`.

## Main results

* `P6Compression.dimerZeroOne_letter_int`: the integer letter identity of the pair.

The compression datum of this pair, its vanishing remainder, its reduction pairs, their
biorthogonality, the sitewise intertwiners, the dimension count and the word-trace identity
are stated uniformly for every pair of sectors in `TwistedDimerPairs`.

## Provenance

The fusion rule and its exact data were first recorded in the notes cited above under
`Notes/OpenProblemsTN/`; they are verification records, not the source.
-/

open scoped Matrix Kronecker

namespace P6Compression

open MPSTensor
open MPOTensor.TwistedDimer (bitF)

/-! ### The letter identity -/

private theorem dimerZeroOne_letter_int_even : ∀ a : Fin 64,
    bitF (Fin.divNat (m := 8) (n := 8) a) = 0 →
      bitF (Fin.modNat (m := 8) (n := 8) a) = 0 →
        (2 : ℤ) • dimerStackEven 0 1 (Fin.divNat (m := 8) (n := 8) a)
            (Fin.modNat (m := 8) (n := 8) a) =
          ∑ s, dimerCoefInt s • pairBlockInt (dimerBlockInt 0 1) s a := by
  decide +kernel

private theorem dimerZeroOne_letter_int_odd : ∀ a : Fin 64,
    bitF (Fin.divNat (m := 8) (n := 8) a) = 1 →
      bitF (Fin.modNat (m := 8) (n := 8) a) = 1 →
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

end P6Compression
