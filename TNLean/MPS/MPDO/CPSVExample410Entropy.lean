/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVExample410Spectrum

/-!
# Finite-ring entropy obstruction for corrected CPSV16 Example 4.10

This module derives the four natural-logarithm block entropies of the corrected left-right
correlated-flip tensor at flip probability one quarter from its established characteristic-
polynomial roots. The resulting mutual-information difference is the exact positive logarithmic
ratio certified in the correlated-flip arithmetic. Hence the corrected tensor has source zero
correlation length but does not satisfy saturation of the area law.

**Local fix (left-right correlated flip):** CPSV16 lines 901--902 repeat the left-qubit label. The
tensor used here flips the left and right qubits of the same spin, as required by the Bell-pair
network and the entropy values printed at source line 904. See
`docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`.

**Scope restriction (fixed parameter and finite ring):** the spectra and exact entropy identities
below are project-derived consequences of the corrected tensor at $p=1/4$ on the four-site ring.
They do not assert the universal-in-$p$ statement printed in CPSV16 Example 4.10. See
`docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`.

## Main results

* `blockEntropy_one` through `blockEntropy_four`: the four block entropies equal the established
  correlated-flip window entropies.
* `mutualInfo_two_sub_one`: the exact logarithmic mutual-information difference.
* `mutualInfo_two_sub_one_pos`: strict positivity from the certified arithmetic comparison.
* `M_not_isSAL`: the corrected tensor does not satisfy saturation of the area law.
* `M_isSourceZCL_and_not_isSAL`: the corrected tensor has source zero correlation length but is
  not SAL.

## Reference

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Example 4.10,
  lines 897--905.
-/

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace MPOTensor.CPSVExample410Entropy

open CPSVExample410Operator CPSVExample410Spectrum

/-- The one-site block entropy of the corrected $p=1/4$ tensor on the four-site ring equals the
one-spin correlated-flip window entropy. This is a project-derived consequence of the spectrum,
not a universal-in-$p$ claim from CPSV16. -/
theorem blockEntropy_one :
    blockEntropy M 4 1 (by omega) (M_isMPDO 4 (by omega)) =
      CPSVExample410CorrelatedFlip.entropyOne := by
  rw [blockEntropy_of_charpoly_roots_eq M (by omega) (M_isMPDO 4 (by omega))
    (4 • {(1 / 4 : ℝ)})]
  · rw [CPSVExample410CorrelatedFlip.entropyOne]
    simp only [Multiset.map_nsmul, Multiset.map_singleton, Multiset.sum_nsmul,
      Multiset.sum_singleton]
    norm_num [CPSVExample410CorrelatedFlip.windowWeightOne, Fintype.sum_prod_type,
      Fintype.sum_bool]
  · rw [charpoly_roots_one]
    simp only [Multiset.map_nsmul, Multiset.map_singleton]
    norm_num

/-- The two-site block entropy of the corrected $p=1/4$ tensor on the four-site ring equals the
two-spin correlated-flip window entropy. This identity is project-derived from the exact
spectrum. -/
theorem blockEntropy_two :
    blockEntropy M 4 2 (by omega) (M_isMPDO 4 (by omega)) =
      CPSVExample410CorrelatedFlip.entropyTwo := by
  rw [blockEntropy_of_charpoly_roots_eq M (by omega) (M_isMPDO 4 (by omega))
    (8 • {(0 : ℝ)} + 4 • {(5 / 32 : ℝ)} + 4 • {(3 / 32 : ℝ)})]
  · rw [CPSVExample410CorrelatedFlip.entropyTwo]
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul,
      Multiset.sum_nsmul, Multiset.map_singleton, Multiset.sum_singleton]
    norm_num [CPSVExample410CorrelatedFlip.windowWeightTwo,
      CPSVExample410CorrelatedFlip.oneBondWeight_false,
      CPSVExample410CorrelatedFlip.oneBondWeight_true, Fintype.sum_prod_type,
      Fintype.sum_bool, Real.negMulLog]
    ring
  · rw [charpoly_roots_two]
    simp only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_singleton]
    norm_num

/-- The three-site block entropy of the corrected $p=1/4$ tensor on the four-site ring equals the
three-spin correlated-flip window entropy. This identity is project-derived from the exact
spectrum. -/
theorem blockEntropy_three :
    blockEntropy M 4 3 (by omega) (M_isMPDO 4 (by omega)) =
      CPSVExample410CorrelatedFlip.entropyThree := by
  rw [blockEntropy_of_charpoly_roots_eq M (by omega) (M_isMPDO 4 (by omega))
    (48 • {(0 : ℝ)} + 4 • {(7 / 64 : ℝ)} + 12 • {(3 / 64 : ℝ)})]
  · rw [CPSVExample410CorrelatedFlip.entropyThree]
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul,
      Multiset.sum_nsmul, Multiset.map_singleton, Multiset.sum_singleton]
    norm_num [CPSVExample410CorrelatedFlip.windowWeightThree,
      CPSVExample410CorrelatedFlip.twoBondWeight_false_false,
      CPSVExample410CorrelatedFlip.twoBondWeight_of_pair_ne_false_false,
      Fintype.sum_prod_type, Fintype.sum_bool, Real.negMulLog]
    ring
  · rw [charpoly_roots_three]
    simp only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_singleton]
    norm_num

/-- The four-site block entropy of the corrected $p=1/4$ tensor equals the bond-pattern entropy.
This identity is project-derived from the exact full-state spectrum. -/
theorem blockEntropy_four :
    blockEntropy M 4 4 (by omega) (M_isMPDO 4 (by omega)) =
      CPSVExample410CorrelatedFlip.entropyFour := by
  rw [blockEntropy_of_charpoly_roots_eq M (by omega) (M_isMPDO 4 (by omega))
    (248 • {(0 : ℝ)} + {(41 / 128 : ℝ)} + 4 • {(15 / 128 : ℝ)} +
      3 • {(9 / 128 : ℝ)})]
  · rw [CPSVExample410CorrelatedFlip.entropyFour,
      CPSVExample410CorrelatedFlip.bondWeight_eq_bondWeightValue]
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul,
      Multiset.sum_nsmul, Multiset.map_singleton, Multiset.sum_singleton]
    norm_num [CPSVExample410CorrelatedFlip.bondWeightValue, Fintype.sum_prod_type,
      Fintype.sum_bool, Real.negMulLog]
    ring
  · rw [charpoly_roots_four]
    simp only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_singleton]
    norm_num

/-- On the four-site ring, the difference $I_2-I_1$ for the corrected $p=1/4$ tensor is one
sixteenth of the logarithm of the exact project-derived rational ratio. -/
theorem mutualInfo_two_sub_one :
    mutualInfoChain M 4 2 (by omega) (M_isMPDO 4 (by omega)) -
        mutualInfoChain M 4 1 (by omega) (M_isMPDO 4 (by omega)) =
      (1 / 16 : ℝ) * Real.log (((2 : ℝ) ^ 32 * 7 ^ 7) / (3 ^ 3 * 5 ^ 20)) := by
  rw [mutualInfoChain, mutualInfoChain, blockEntropy_one, blockEntropy_two,
    blockEntropy_three, blockEntropy_four]
  simpa [CPSVExample410CorrelatedFlip.mutualInfoOne,
    CPSVExample410CorrelatedFlip.mutualInfoTwo, two_mul] using
    CPSVExample410CorrelatedFlip.mutualInfoTwo_sub_mutualInfoOne_eq

/-- The exact mutual-information difference of the corrected $p=1/4$ tensor on the four-site
ring is strictly positive. -/
theorem mutualInfo_two_sub_one_pos :
    0 < mutualInfoChain M 4 2 (by omega) (M_isMPDO 4 (by omega)) -
      mutualInfoChain M 4 1 (by omega) (M_isMPDO 4 (by omega)) := by
  rw [mutualInfo_two_sub_one]
  exact mul_pos (by norm_num)
    CPSVExamples410411Arithmetic.example410_log_ratio_pos

/-- The corrected $p=1/4$ tensor from CPSV16 Example 4.10 does not satisfy saturation of the
area law. -/
theorem M_not_isSAL : ¬ IsSAL M := by
  intro hSAL
  have hEq := mutualInfoChain_eq_of_isSAL M hSAL (N := 4) (L := 1) (L' := 2)
    (by omega) (by omega) (by omega) (by omega)
  have hPos := mutualInfo_two_sub_one_pos
  rw [hEq] at hPos
  linarith

/-- The corrected $p=1/4$ left-right correlated-flip tensor has the source zero-correlation-
length relation but does not satisfy saturation of the area law. This fixed-parameter conclusion
does not assert the universal-in-$p$ statement printed in CPSV16 Example 4.10. -/
theorem M_isSourceZCL_and_not_isSAL : IsSourceZCL M ∧ ¬ IsSAL M :=
  ⟨CPSVExample410Operator.M_isSourceZCL, M_not_isSAL⟩

end MPOTensor.CPSVExample410Entropy
