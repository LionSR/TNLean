/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVExample411Spectrum
import TNLean.MPS.MPDO.CPSVExamples410411Arithmetic
import TNLean.MPS.MPDO.PhysicalSupportSALTransport

/-!
# Finite-ring entropy obstruction for CPSV16 Example 4.11

This module derives the natural-logarithm block entropies of the effective binary model on a
four-site ring from its previously established characteristic-polynomial roots. Their mutual
information difference is the logarithm of the exact positive ratio certified separately in the
arithmetic module. Hence the effective tensor does not satisfy saturation of the area law, and the
same conclusion holds after its isometric inclusion into the two-qubit one-site space.

These are project-derived finite-periodic consequences of the neighboring operators printed in
CPSV16 Example 4.11. They do not assert zero correlation length or a thermodynamic-limit claim.
See `docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`.

## Main results

* `M_isMPDO`: the effective binary tensor generates positive semidefinite operators.
* `blockEntropy_one` through `blockEntropy_four`: the four exact natural-logarithm entropies.
* `mutualInfo_two_sub_one`: the exact logarithmic mutual-information difference.
* `mutualInfo_two_sub_one_pos`: strict positivity from the certified integer comparison.
* `M_not_isSAL`: the effective binary tensor does not satisfy saturation of the area law.
* `ambientM_not_isSAL`: neither does its isometric inclusion into the two-qubit site space.
-/

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace MPOTensor.CPSVExample411Entropy

open CPSVExample411BinarySupport CPSVExample411Spectrum

private theorem weightMatrix_nonneg (i j : Fin 2) :
    (0 : ℂ) ≤ weightMatrix i j := by
  fin_cases i <;> fin_cases j
  · norm_num [weightMatrix]
  · simp [weightMatrix]
  · simp [weightMatrix]
  · norm_num [weightMatrix]

private theorem cycleWeight_nonneg {N : ℕ} [NeZero N] (σ : Fin N → Fin 2) :
    (0 : ℂ) ≤ cycleWeight σ := by
  exact Finset.prod_nonneg fun n _ ↦ weightMatrix_nonneg (σ n) (σ (n + 1))

/-- The effective binary tensor generates positive semidefinite periodic operators at every
positive length. -/
theorem M_isMPDO : IsMPDO M := by
  intro N hN
  let : NeZero N := ⟨hN.ne'⟩
  rw [mpo_M_eq_diagonal]
  exact Matrix.PosSemidef.diagonal cycleWeight_nonneg

/-- The one-site block entropy on the four-site ring is $\log 2$. -/
theorem blockEntropy_one :
    blockEntropy M 4 1 (by omega) (M_isMPDO 4 (by omega)) = Real.log 2 := by
  rw [blockEntropy_of_charpoly_roots_eq M M_isMPDO (by omega) (by omega)
    (2 • {(1 / 2 : ℝ)})]
  · simp only [Multiset.map_nsmul, Multiset.map_singleton, Multiset.sum_nsmul,
      Multiset.sum_singleton, Real.negMulLog]
    rw [Real.log_div (by norm_num) (by norm_num)]
    simp only [Real.log_one]
    ring
  · rw [effective_charpoly_roots_one]
    simp only [Multiset.map_nsmul, Multiset.map_singleton]
    norm_num

/-- The two-site block entropy on the four-site ring is the entropy sum of its two root values. -/
theorem blockEntropy_two :
    blockEntropy M 4 2 (by omega) (M_isMPDO 4 (by omega)) =
      2 * Real.negMulLog (14 / 41) + 2 * Real.negMulLog (13 / 82) := by
  rw [blockEntropy_of_charpoly_roots_eq M M_isMPDO (by omega) (by omega)
    (2 • {(14 / 41 : ℝ)} + 2 • {(13 / 82 : ℝ)})]
  · simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul,
      Multiset.sum_nsmul, Multiset.map_singleton, Multiset.sum_singleton]
    norm_num
  · rw [effective_charpoly_roots_two]
    simp only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_singleton]
    norm_num

/-- The three-site block entropy on the four-site ring is the entropy sum of its three root
values. -/
theorem blockEntropy_three :
    blockEntropy M 4 3 (by omega) (M_isMPDO 4 (by omega)) =
      2 * Real.negMulLog (10 / 41) + 4 * Real.negMulLog (4 / 41) +
        2 * Real.negMulLog (5 / 82) := by
  rw [blockEntropy_of_charpoly_roots_eq M M_isMPDO (by omega) (by omega)
    (2 • {(10 / 41 : ℝ)} + 4 • {(4 / 41 : ℝ)} + 2 • {(5 / 82 : ℝ)})]
  · simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul,
      Multiset.sum_nsmul, Multiset.map_singleton, Multiset.sum_singleton]
    norm_num
  · rw [effective_charpoly_roots_three]
    simp only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_singleton]
    norm_num

/-- The four-site entropy is the entropy sum of the three root values of the full state. -/
theorem blockEntropy_four :
    blockEntropy M 4 4 (by omega) (M_isMPDO 4 (by omega)) =
      2 * Real.negMulLog (8 / 41) + 12 * Real.negMulLog (2 / 41) +
        2 * Real.negMulLog (1 / 82) := by
  rw [blockEntropy_of_charpoly_roots_eq M M_isMPDO (by omega) (by omega)
    (2 • {(8 / 41 : ℝ)} + 12 • {(2 / 41 : ℝ)} + 2 • {(1 / 82 : ℝ)})]
  · simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul,
      Multiset.sum_nsmul, Multiset.map_singleton, Multiset.sum_singleton]
    norm_num
  · rw [effective_charpoly_roots_four]
    simp only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_singleton]
    norm_num

/-- On the four-site ring, the difference $I_2-I_1$ is the natural logarithm of the exact
positive rational ratio arising from the root multisets. -/
theorem mutualInfo_two_sub_one :
    mutualInfoChain M 4 2 (by omega) (M_isMPDO 4 (by omega)) -
        mutualInfoChain M 4 1 (by omega) (M_isMPDO 4 (by omega)) =
      (1 / 82 : ℝ) * Real.log
        (((41 : ℝ) ^ 82 * 5 ^ 50) / (2 ^ 48 * 13 ^ 52 * 7 ^ 112)) := by
  have hlog : Real.log
      (((41 : ℝ) ^ 82 * 5 ^ 50) / (2 ^ 48 * 13 ^ 52 * 7 ^ 112)) =
      82 * Real.log 41 + 50 * Real.log 5 -
        (48 * Real.log 2 + 52 * Real.log 13 + 112 * Real.log 7) := by
    rw [Real.log_div (by norm_num : ((41 : ℝ) ^ 82 * 5 ^ 50) ≠ 0)
      (by norm_num : ((2 : ℝ) ^ 48 * 13 ^ 52 * 7 ^ 112) ≠ 0),
      Real.log_mul (by norm_num : (41 : ℝ) ^ 82 ≠ 0)
        (by norm_num : (5 : ℝ) ^ 50 ≠ 0),
      Real.log_mul (by norm_num : (2 : ℝ) ^ 48 * 13 ^ 52 ≠ 0)
        (by norm_num : (7 : ℝ) ^ 112 ≠ 0),
      Real.log_mul (by norm_num : (2 : ℝ) ^ 48 ≠ 0)
        (by norm_num : (13 : ℝ) ^ 52 ≠ 0)]
    simp only [Real.log_pow]
    ring
  rw [mutualInfoChain, mutualInfoChain, blockEntropy_one, blockEntropy_two,
    blockEntropy_three, blockEntropy_four, hlog]
  simp only [Real.negMulLog]
  rw [Real.log_div (by norm_num : (14 : ℝ) ≠ 0) (by norm_num : (41 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (13 : ℝ) ≠ 0) (by norm_num : (82 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (10 : ℝ) ≠ 0) (by norm_num : (41 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (41 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (5 : ℝ) ≠ 0) (by norm_num : (82 : ℝ) ≠ 0)]
  have h14 : Real.log (14 : ℝ) = Real.log 2 + Real.log 7 := by
    rw [show (14 : ℝ) = 2 * 7 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (7 : ℝ) ≠ 0)]
  have h82 : Real.log (82 : ℝ) = Real.log 2 + Real.log 41 := by
    rw [show (82 : ℝ) = 2 * 41 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (41 : ℝ) ≠ 0)]
  have h10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]
  have h4 : Real.log (4 : ℝ) = Real.log 2 + Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  rw [h14, h82, h10, h4]
  ring

/-- The exact mutual-information difference on the four-site ring is strictly positive. -/
theorem mutualInfo_two_sub_one_pos :
    0 < mutualInfoChain M 4 2 (by omega) (M_isMPDO 4 (by omega)) -
      mutualInfoChain M 4 1 (by omega) (M_isMPDO 4 (by omega)) := by
  rw [mutualInfo_two_sub_one]
  positivity [CPSVExamples410411Arithmetic.example411_log_ratio_pos]

/-- The effective binary finite-ring tensor does not satisfy saturation of the area law. -/
theorem M_not_isSAL : ¬ IsSAL M := by
  intro hSAL
  have hEq := mutualInfoChain_eq_of_isSAL M hSAL (N := 4) (L := 1) (L' := 2)
    (by omega) (by omega) (by omega) (by omega)
  have hPos := mutualInfo_two_sub_one_pos
  rw [hEq] at hPos
  linarith

/-- The isometrically included two-qubit-site tensor also does not satisfy saturation of the area
law. -/
theorem ambientM_not_isSAL : ¬ IsSAL CPSVExample411Ambient.ambientM := by
  intro hSAL
  apply M_not_isSAL
  exact isSAL_of_changePhysicalBasis_isSAL_of_isometry
    CPSVExample411Ambient.inclusion CPSVExample411Ambient.inclusion_isometry M hSAL

end MPOTensor.CPSVExample411Entropy
