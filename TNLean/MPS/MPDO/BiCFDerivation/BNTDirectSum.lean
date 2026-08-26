/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.BNT.DirectSumSelectors

/-!
# BNT input for the equal-size direct-sum branch

This file connects the same-dimension BNT separation hypothesis to the
parent-Hamiltonian uniqueness input in the direct-sum proof of
arXiv:quant-ph/0608197, lines 1346--1408.

The intermediate statements keep the direct-sum hypotheses explicit:
`BlocksNotGaugePhaseEquiv` gives the long-chain non-proportional MPV witness,
while injectivity and finite-length block injectivity are separate inputs to
the parent-Hamiltonian argument. The final theorem derives these inputs from a
BNT canonical form and proves the source bound \(3D^5\).
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d L : ℕ}

/-- The elementary numerical estimate in the sharp BNT block-separation bound. -/
theorem three_mul_pred_mul_pow_four_add_one_le_three_mul_pow_five
    {D : ℕ} (hD : 0 < D) :
    3 * ((D - 1) * (D ^ 4 + 1)) ≤ 3 * D ^ 5 := by
  have hDleD4 : D ≤ D ^ 4 := by
    simpa using (pow_le_pow_right' (a := D) hD (by omega : 1 ≤ 4))
  have hDsubLeD4 : D - 1 ≤ D ^ 4 :=
    (Nat.sub_le D 1).trans hDleD4
  have hCore : (D - 1) * (D ^ 4 + 1) ≤ D ^ 5 := by
    calc
      (D - 1) * (D ^ 4 + 1) = (D - 1) * D ^ 4 + (D - 1) := by ring
      _ ≤ (D - 1) * D ^ 4 + D ^ 4 := Nat.add_le_add_left hDsubLeD4 _
      _ = (D - 1) * D ^ 4 + 1 * D ^ 4 := by rw [one_mul]
      _ = ((D - 1) + 1) * D ^ 4 := (Nat.add_mul (D - 1) 1 (D ^ 4)).symm
      _ = D * D ^ 4 := by rw [Nat.sub_add_cancel (by omega)]
      _ = D ^ 5 := by ring
  exact Nat.mul_le_mul_left 3 hCore

namespace IsBNTCanonicalForm

variable {P : SectorDecomposition d}

/-- A BNT canonical form has a simultaneous representative word span at some
positive length at most \(3D^5\), where \(D\) is the total bond dimension.

For two or more representatives, this is the source estimate
\(3(g-1)(D^4+1)\leq 3D^5\). For one representative, ordinary block
injectivity at \(D^4\) gives the conclusion. This is the sharp
block-injectivity proposition of arXiv:1606.00608, lines 340--345. -/
theorem exists_basis_wordTupleSpanTop_le_three_totalDim_pow_five
    (hCF : IsBNTCanonicalForm P) :
    ∃ N : ℕ, 0 < N ∧ N ≤ 3 * P.totalDim ^ 5 ∧ WordTupleSpanTop P.basis N := by
  classical
  obtain ⟨j₀, _q₀, _hweight⟩ := hCF.weight_unit_exists
  have hDpos : 0 < P.totalDim :=
    lt_of_lt_of_le (hCF.basis_dim_pos j₀) (P.basisDim_le_totalDim j₀)
  have hD4pos : 0 < P.totalDim ^ 4 := Nat.pow_pos hDpos
  have hBlk0 : ∀ j : Fin P.basisCount,
      Kraus.IsNBlkInjective (P.basis j) (P.totalDim ^ 4) :=
    hCF.basis_isNBlkInjective_totalDim_pow_four
  by_cases hCountOne : P.basisCount = 1
  · refine ⟨P.totalDim ^ 4, hD4pos, ?_, ?_⟩
    · calc
        P.totalDim ^ 4 = P.totalDim ^ 4 * 1 := by simp
        _ ≤ P.totalDim ^ 4 * (3 * P.totalDim) := by
          exact Nat.mul_le_mul_left _ (by omega)
        _ = 3 * P.totalDim ^ 5 := by ring
    · exact wordTupleSpanTop_of_card_eq_one_of_isNBlkInjective
        P.basis hCountOne hBlk0
  · have hCountTwo : 2 ≤ P.basisCount := by
      have hCountPos : 0 < P.basisCount :=
        lt_of_le_of_lt (Nat.zero_le j₀) j₀.isLt
      omega
    let : ∀ j : Fin P.basisCount, NeZero (P.basisDim j) :=
      fun j ↦ ⟨(hCF.basis_dim_pos j).ne'⟩
    have hBlk1 : ∀ j : Fin P.basisCount,
        Kraus.IsNBlkInjective (P.basis j) (P.totalDim ^ 4 + 1) := by
      intro j
      exact isNBlkInjective_of_le hD4pos (hBlk0 j) (by omega)
    have hBlk3 : ∀ j : Fin P.basisCount,
        Kraus.IsNBlkInjective (P.basis j)
          ((P.totalDim ^ 4 + 1) +
            ((P.totalDim ^ 4 + 1) + (P.totalDim ^ 4 + 1))) := by
      intro j
      exact isNBlkInjective_of_le hD4pos (hBlk0 j) (by omega)
    have hIrr : HasIrreducibleBlocks (d := d) P.basis :=
      HasIrreducibleBlocks.ofForall hCF.basis_irreducible
    have hLeft : IsLeftCanonicalBlockFamily (d := d) P.basis :=
      IsLeftCanonicalBlockFamily.ofForall hCF.basis_left_canonical
    have hOverlap : HasNormalizedSelfOverlap (d := d) P.basis :=
      HasNormalizedSelfOverlap.ofForall hCF.basis_normalized_self_overlap
    have hSpan : WordTupleSpanTop P.basis
        ((P.basisCount - 1) *
          ((P.totalDim ^ 4 + 1) +
            ((P.totalDim ^ 4 + 1) + (P.totalDim ^ 4 + 1)))) :=
      wordTupleSpanTop_threeBlock_mul_pred_of_blocksNotGaugePhaseEquiv_c1
        P.basis hIrr hLeft hOverlap hCF.basis_distinct
        hBlk0 hBlk1 hBlk3 hD4pos hCountTwo
    refine ⟨(P.basisCount - 1) *
      ((P.totalDim ^ 4 + 1) +
        ((P.totalDim ^ 4 + 1) + (P.totalDim ^ 4 + 1))), ?_, ?_, hSpan⟩
    · exact Nat.mul_pos (by omega) (by omega)
    · have hCountLe : P.basisCount ≤ P.totalDim :=
        P.basisCount_le_totalDim hCF.basis_dim_pos
      have hPredLe : P.basisCount - 1 ≤ P.totalDim - 1 :=
        Nat.sub_le_sub_right hCountLe 1
      have hFirst :
          (P.basisCount - 1) *
              ((P.totalDim ^ 4 + 1) +
                ((P.totalDim ^ 4 + 1) + (P.totalDim ^ 4 + 1))) ≤
            (P.totalDim - 1) *
              ((P.totalDim ^ 4 + 1) +
                ((P.totalDim ^ 4 + 1) + (P.totalDim ^ 4 + 1))) :=
        Nat.mul_le_mul_right _ hPredLe
      refine hFirst.trans ?_
      calc
        (P.totalDim - 1) *
            ((P.totalDim ^ 4 + 1) +
              ((P.totalDim ^ 4 + 1) + (P.totalDim ^ 4 + 1))) =
            3 * ((P.totalDim - 1) * (P.totalDim ^ 4 + 1)) := by ring
        _ ≤ 3 * P.totalDim ^ 5 :=
          three_mul_pred_mul_pow_four_add_one_le_three_mul_pow_five hDpos

end IsBNTCanonicalForm

end MPSTensor
