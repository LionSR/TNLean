/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CyclicActiveRetainedCoordinates
import TNLean.MPS.MPDO.SectorChainFiberContraction

/-!
# Contraction of a nonempty discarded suffix

This file evaluates the contraction over an arbitrary nonempty discarded
suffix in retained open-edge coordinates. It also records the three-site
specialization used for cyclic-active sectors.

## Reference

* arXiv:1606.00608, Appendix C.2, Proposition 4to2, lines 1606--1617.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

private theorem suffixContraction_internal_index {n N : ℕ} (i : Fin n) :
    Fin.castAdd N (Fin.castAdd 1 i) =
      Fin.castAdd N ((Fin.last n).succAbove i) := by
  ext
  simp [Fin.succAbove_last]

private theorem suffixContraction_internal_succ_index {n N : ℕ} (i : Fin n) :
    Fin.castAdd N (Fin.castAdd 1 i) + 1 =
      Fin.castAdd N ((Fin.last n).succAbove i + 1) := by
  rw [Fin.succAbove_last]
  apply Fin.ext
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have honeBig : ((1 : Fin (n + 1 + N)) : ℕ) = 1 := by
    change 1 % (n + 1 + N) = 1
    exact Nat.mod_eq_of_lt <| lt_of_lt_of_le (Nat.succ_lt_succ hn) <| by omega
  have honeSmall : ((1 : Fin (n + 1)) : ℕ) = 1 := by
    change 1 % (n + 1) = 1
    exact Nat.mod_eq_of_lt (Nat.succ_lt_succ hn)
  simp only [Fin.val_castAdd, Fin.val_add, Fin.val_castSucc,
    honeBig, honeSmall]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem suffixContraction_last_retained_index {n N : ℕ} :
    Fin.castAdd N (Fin.natAdd n (0 : Fin 1)) =
      Fin.castAdd N (Fin.last n) := by
  ext
  rfl

private theorem suffixContraction_first_suffix_index {n m : ℕ} :
    Fin.castAdd (m + 1) (Fin.natAdd n (0 : Fin 1)) + 1 =
      Fin.natAdd (n + 1) (0 : Fin (m + 1)) := by
  apply Fin.ext
  have hone : ((1 : Fin (n + 1 + (m + 1))) : ℕ) = 1 := by
    change 1 % (n + 1 + (m + 1)) = 1
    exact Nat.mod_eq_of_lt (by omega)
  simp only [Fin.val_add, Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero, hone]
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem suffixContraction_suffix_succ {n m : ℕ} (i : Fin m) :
    Fin.natAdd (n + 1) (Fin.castAdd 1 i) + 1 =
      Fin.natAdd (n + 1) i.succ := by
  apply Fin.ext
  have hone : ((1 : Fin (n + 1 + (m + 1))) : ℕ) = 1 := by
    change 1 % (n + 1 + (m + 1)) = 1
    exact Nat.mod_eq_of_lt (by omega)
  simp only [Fin.val_add, Fin.val_natAdd, Fin.val_castAdd, Fin.val_succ, hone]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

private theorem suffixContraction_suffix_last_succ {n m : ℕ} :
    Fin.natAdd (n + 1) (Fin.natAdd m (0 : Fin 1)) + 1 =
      Fin.castAdd (m + 1) (Fin.last n + 1) := by
  apply Fin.ext
  have hone : ((1 : Fin (n + 1 + (m + 1))) : ℕ) = 1 := by
    change 1 % (n + 1 + (m + 1)) = 1
    exact Nat.mod_eq_of_lt (by omega)
  simp only [Fin.val_add, Fin.val_natAdd, Fin.val_zero, Fin.last_add_one,
    Fin.val_castAdd, hone]
  simp only [Nat.add_zero]
  rw [show n + 1 + m + 1 = n + 1 + (m + 1) by omega, Nat.mod_self]

private theorem suffixContraction_last_suffix_index {m : ℕ} :
    Fin.natAdd m (0 : Fin 1) = Fin.last m := by
  ext
  rfl

private theorem suffixContraction_castAdd_one_eq_castSucc {m : ℕ} (i : Fin m) :
    Fin.castAdd 1 i = i.castSucc := by
  ext
  rfl

private theorem fourthRegion_retained_internal_index {n : ℕ} (i : Fin n) :
    Fin.castAdd 1 i = (Fin.last n).succAbove i := by
  ext
  simp [Fin.succAbove_last]

private theorem rightTensor_eq_of_heq
    (F : PhysicalSectorFactorization K) {k h : Fin F.sectorCount}
    (kh : k = h) (a : Fin D)
    {x y : Fin (F.rightDim k)} {x' y' : Fin (F.rightDim h)}
    (hx : HEq x x') (hy : HEq y y') :
    F.rightTensor k a x y = F.rightTensor h a x' y' := by
  subst h
  cases hx
  cases hy
  rfl

private theorem leftTensor_eq_of_heq
    (F : PhysicalSectorFactorization K) {k h : Fin F.sectorCount}
    (kh : k = h) (a : Fin D)
    {x y : Fin (F.leftDim k)} {x' y' : Fin (F.leftDim h)}
    (hx : HEq x x') (hy : HEq y y') :
    F.leftTensor k a x y = F.leftTensor h a x' y' := by
  subst h
  cases hx
  cases hy
  rfl

private theorem partialTraceRight_neighboringOperator_eq_of_right
    (F : PhysicalSectorFactorization K)
    (k h h' : Fin F.sectorCount) (hh : h = h')
    (x y : Fin (F.rightDim k)) :
    Matrix.partialTraceRight (F.neighboringOperator k h) x y =
      Matrix.partialTraceRight (F.neighboringOperator k h') x y := by
  subst h'
  rfl

private theorem partialTraceLeft_neighboringOperator_eq_of_left
    (F : PhysicalSectorFactorization K)
    (k k' h : Fin F.sectorCount) (hk : k = k')
    (x y : Fin (F.leftDim h)) :
    Matrix.partialTraceLeft (F.neighboringOperator k h) x y =
      Matrix.partialTraceLeft (F.neighboringOperator k' h) x y := by
  subst k'
  rfl

private theorem neighboringOperator_trace_eq_of_eq
    (F : PhysicalSectorFactorization K)
    (k k' h h' : Fin F.sectorCount) (hk : k = k') (hh : h = h') :
    (F.neighboringOperator k h).trace =
      (F.neighboringOperator k' h').trace := by
  subst k'
  subst h'
  rfl

private theorem sectorIndex_fst_heq_of_heq
    (F : PhysicalSectorFactorization K) {k h : Fin F.sectorCount}
    (kh : k = h) {x : F.SectorIndex k} {y : F.SectorIndex h}
    (hxy : x ≍ y) : x.1 ≍ y.1 := by
  subst h
  exact heq_of_eq (congrArg Prod.fst (eq_of_heq hxy))

private theorem sectorIndex_snd_heq_of_heq
    (F : PhysicalSectorFactorization K) {k h : Fin F.sectorCount}
    (kh : k = h) {x : F.SectorIndex k} {y : F.SectorIndex h}
    (hxy : x ≍ y) : x.2 ≍ y.2 := by
  subst h
  exact heq_of_eq (congrArg Prod.snd (eq_of_heq hxy))

private theorem dependent_prod_fst_heq {ι : Type*} {α β : ι → Type*}
    (f : (i : ι) → α i × β i) {i j : ι} (h : i = j) :
    (f i).1 ≍ (f j).1 := by
  subst j
  rfl

private theorem dependent_prod_snd_heq {ι : Type*} {α β : ι → Type*}
    (f : (i : ι) → α i × β i) {i j : ι} (h : i = j) :
    (f i).2 ≍ (f j).2 := by
  subst j
  rfl

private theorem appendSectorFiber_castAdd_heq
    (F : PhysicalSectorFactorization K)
    {L R : ℕ} {k : Fin L → Fin F.sectorCount}
    {t : Fin R → Fin F.sectorCount}
    (x : F.SectorChainFiber k) (z : F.SectorChainFiber t) (i : Fin L) :
    F.appendSectorFiber x z (Fin.castAdd R i) ≍ x i := by
  simp only [appendSectorFiber, Fin.addCases_left]
  exact cast_heq _ _

private theorem appendSectorFiber_natAdd_heq
    (F : PhysicalSectorFactorization K)
    {L R : ℕ} {k : Fin L → Fin F.sectorCount}
    {t : Fin R → Fin F.sectorCount}
    (x : F.SectorChainFiber k) (z : F.SectorChainFiber t) (i : Fin R) :
    F.appendSectorFiber x z (Fin.natAdd L i) ≍ z i := by
  simp only [appendSectorFiber, Fin.addCases_right]
  exact cast_heq _ _

private theorem appendSectorFiber_fst_castAdd_heq
    (F : PhysicalSectorFactorization K)
    {L R : ℕ} {k : Fin L → Fin F.sectorCount}
    {t : Fin R → Fin F.sectorCount}
    (x : F.SectorChainFiber k) (z : F.SectorChainFiber t)
    {j : Fin (L + R)} (i : Fin L) (h : j = Fin.castAdd R i) :
    (F.appendSectorFiber x z j).1 ≍ (x i).1 := by
  refine (dependent_prod_fst_heq (F.appendSectorFiber x z) h).trans ?_
  exact sectorIndex_fst_heq_of_heq F (by simp)
    (F.appendSectorFiber_castAdd_heq x z i)

private theorem appendSectorFiber_snd_castAdd_heq
    (F : PhysicalSectorFactorization K)
    {L R : ℕ} {k : Fin L → Fin F.sectorCount}
    {t : Fin R → Fin F.sectorCount}
    (x : F.SectorChainFiber k) (z : F.SectorChainFiber t)
    {j : Fin (L + R)} (i : Fin L) (h : j = Fin.castAdd R i) :
    (F.appendSectorFiber x z j).2 ≍ (x i).2 := by
  refine (dependent_prod_snd_heq (F.appendSectorFiber x z) h).trans ?_
  exact sectorIndex_snd_heq_of_heq F (by simp)
    (F.appendSectorFiber_castAdd_heq x z i)

private theorem appendSectorFiber_fst_natAdd_heq
    (F : PhysicalSectorFactorization K)
    {L R : ℕ} {k : Fin L → Fin F.sectorCount}
    {t : Fin R → Fin F.sectorCount}
    (x : F.SectorChainFiber k) (z : F.SectorChainFiber t)
    {j : Fin (L + R)} (i : Fin R) (h : j = Fin.natAdd L i) :
    (F.appendSectorFiber x z j).1 ≍ (z i).1 := by
  refine (dependent_prod_fst_heq (F.appendSectorFiber x z) h).trans ?_
  exact sectorIndex_fst_heq_of_heq F (by simp)
    (F.appendSectorFiber_natAdd_heq x z i)

private theorem appendSectorFiber_snd_natAdd_heq
    (F : PhysicalSectorFactorization K)
    {L R : ℕ} {k : Fin L → Fin F.sectorCount}
    {t : Fin R → Fin F.sectorCount}
    (x : F.SectorChainFiber k) (z : F.SectorChainFiber t)
    {j : Fin (L + R)} (i : Fin R) (h : j = Fin.natAdd L i) :
    (F.appendSectorFiber x z j).2 ≍ (z i).2 := by
  refine (dependent_prod_snd_heq (F.appendSectorFiber x z) h).trans ?_
  exact sectorIndex_snd_heq_of_heq F (by simp)
    (F.appendSectorFiber_natAdd_heq x z i)

private theorem suffixContraction_retained_neighboring_entry
    (F : PhysicalSectorFactorization K) {n N : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount)
    (t : Fin N → Fin F.sectorCount)
    (x y : F.RetainedOpenEdgeIndex k)
    (z : F.SectorChainFiber t) (i : Fin n) :
    F.neighboringOperator
        (Fin.append k t (Fin.castAdd N (Fin.castAdd 1 i)))
        (Fin.append k t (Fin.castAdd N (Fin.castAdd 1 i) + 1))
        ((F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm x) z
            (Fin.castAdd N (Fin.castAdd 1 i))).2,
          (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm x) z
            (Fin.castAdd N (Fin.castAdd 1 i) + 1)).1)
        ((F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm y) z
            (Fin.castAdd N (Fin.castAdd 1 i))).2,
          (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm y) z
            (Fin.castAdd N (Fin.castAdd 1 i) + 1)).1) =
      F.neighboringOperator
        (k ((Fin.last n).succAbove i))
        (k ((Fin.last n).succAbove i + 1)) (x.1 i) (y.1 i) := by
  simp only [PhysicalSectorFactorization.neighboringOperator_apply]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  · apply rightTensor_eq_of_heq F (by simp [suffixContraction_internal_index]) a
    · refine (F.appendSectorFiber_snd_castAdd_heq _ _ (Fin.castAdd 1 i) rfl).trans ?_
      refine (dependent_prod_snd_heq ((F.retainedOpenEdgeEquiv k).symm x)
        (fourthRegion_retained_internal_index i)).trans ?_
      exact heq_of_eq (congrArg Prod.fst
        (F.retainedOpenEdgeEquiv_symm_internal_edge k x i))
    · refine (F.appendSectorFiber_snd_castAdd_heq _ _ (Fin.castAdd 1 i) rfl).trans ?_
      refine (dependent_prod_snd_heq ((F.retainedOpenEdgeEquiv k).symm y)
        (fourthRegion_retained_internal_index i)).trans ?_
      exact heq_of_eq (congrArg Prod.fst
        (F.retainedOpenEdgeEquiv_symm_internal_edge k y i))
  · apply leftTensor_eq_of_heq F (by simp [suffixContraction_internal_succ_index]) a
    · refine (F.appendSectorFiber_fst_castAdd_heq _ _
        ((Fin.last n).succAbove i + 1)
          (suffixContraction_internal_succ_index i)).trans ?_
      exact heq_of_eq (congrArg Prod.snd
        (F.retainedOpenEdgeEquiv_symm_internal_edge k x i))
    · refine (F.appendSectorFiber_fst_castAdd_heq _ _
        ((Fin.last n).succAbove i + 1)
          (suffixContraction_internal_succ_index i)).trans ?_
      exact heq_of_eq (congrArg Prod.snd
        (F.retainedOpenEdgeEquiv_symm_internal_edge k y i))

private theorem suffixContraction_leftBoundary_neighboring_entry
    (F : PhysicalSectorFactorization K) {n m : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount)
    (t : Fin (m + 1) → Fin F.sectorCount)
    (x y : F.RetainedOpenEdgeIndex k)
    (z : F.SectorChainFiber t) :
    F.neighboringOperator
        (Fin.append k t (Fin.castAdd (m + 1) (Fin.natAdd n (0 : Fin 1))))
        (Fin.append k t
          (Fin.castAdd (m + 1) (Fin.natAdd n (0 : Fin 1)) + 1))
        ((F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm x) z
            (Fin.castAdd (m + 1) (Fin.natAdd n (0 : Fin 1)))).2,
          (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm x) z
            (Fin.castAdd (m + 1) (Fin.natAdd n (0 : Fin 1)) + 1)).1)
        ((F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm y) z
            (Fin.castAdd (m + 1) (Fin.natAdd n (0 : Fin 1)))).2,
          (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm y) z
            (Fin.castAdd (m + 1) (Fin.natAdd n (0 : Fin 1)) + 1)).1) =
      F.neighboringOperator (k (Fin.last n)) (t 0)
        (x.2.1, (z 0).1) (y.2.1, (z 0).1) := by
  simp only [PhysicalSectorFactorization.neighboringOperator_apply]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  · apply rightTensor_eq_of_heq F
      (by simp [suffixContraction_last_retained_index]) a
    · refine (F.appendSectorFiber_snd_castAdd_heq _ _ (Fin.last n)
        suffixContraction_last_retained_index).trans ?_
      exact heq_of_eq (F.retainedOpenEdgeEquiv_symm_last_right k x)
    · refine (F.appendSectorFiber_snd_castAdd_heq _ _ (Fin.last n)
        suffixContraction_last_retained_index).trans ?_
      exact heq_of_eq (F.retainedOpenEdgeEquiv_symm_last_right k y)
  · apply leftTensor_eq_of_heq F
      (by simp [suffixContraction_first_suffix_index]) a
    · exact F.appendSectorFiber_fst_natAdd_heq _ _ 0
        suffixContraction_first_suffix_index
    · exact F.appendSectorFiber_fst_natAdd_heq _ _ 0
        suffixContraction_first_suffix_index

private theorem suffixContraction_internalSuffix_neighboring_entry
    (F : PhysicalSectorFactorization K) {n m : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount)
    (t : Fin (m + 1) → Fin F.sectorCount)
    (x y : F.RetainedOpenEdgeIndex k)
    (z : F.SectorChainFiber t) (i : Fin m) :
    F.neighboringOperator
        (Fin.append k t (Fin.natAdd (n + 1) (Fin.castAdd 1 i)))
        (Fin.append k t (Fin.natAdd (n + 1) (Fin.castAdd 1 i) + 1))
        ((F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm x) z
            (Fin.natAdd (n + 1) (Fin.castAdd 1 i))).2,
          (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm x) z
            (Fin.natAdd (n + 1) (Fin.castAdd 1 i) + 1)).1)
        ((F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm y) z
            (Fin.natAdd (n + 1) (Fin.castAdd 1 i))).2,
          (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm y) z
            (Fin.natAdd (n + 1) (Fin.castAdd 1 i) + 1)).1) =
      F.neighboringOperator (t (Fin.castAdd 1 i)) (t i.succ)
        ((z (Fin.castAdd 1 i)).2, (z i.succ).1)
        ((z (Fin.castAdd 1 i)).2, (z i.succ).1) := by
  simp only [PhysicalSectorFactorization.neighboringOperator_apply]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  · apply rightTensor_eq_of_heq F (by simp) a <;>
      exact F.appendSectorFiber_snd_natAdd_heq _ _ (Fin.castAdd 1 i) rfl
  · apply leftTensor_eq_of_heq F
      (by simp [suffixContraction_suffix_succ]) a <;>
      exact F.appendSectorFiber_fst_natAdd_heq _ _ i.succ
        (suffixContraction_suffix_succ i)

private theorem suffixContraction_rightBoundary_neighboring_entry
    (F : PhysicalSectorFactorization K) {n m : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount)
    (t : Fin (m + 1) → Fin F.sectorCount)
    (x y : F.RetainedOpenEdgeIndex k)
    (z : F.SectorChainFiber t) :
    F.neighboringOperator
        (Fin.append k t
          (Fin.natAdd (n + 1) (Fin.natAdd m (0 : Fin 1))))
        (Fin.append k t
          (Fin.natAdd (n + 1) (Fin.natAdd m (0 : Fin 1)) + 1))
        ((F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm x) z
            (Fin.natAdd (n + 1) (Fin.natAdd m (0 : Fin 1)))).2,
          (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm x) z
            (Fin.natAdd (n + 1) (Fin.natAdd m (0 : Fin 1)) + 1)).1)
        ((F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm y) z
            (Fin.natAdd (n + 1) (Fin.natAdd m (0 : Fin 1)))).2,
          (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm y) z
            (Fin.natAdd (n + 1) (Fin.natAdd m (0 : Fin 1)) + 1)).1) =
      F.neighboringOperator (t (Fin.last m)) (k (Fin.last n + 1))
        ((z (Fin.last m)).2, x.2.2) ((z (Fin.last m)).2, y.2.2) := by
  simp only [PhysicalSectorFactorization.neighboringOperator_apply]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  · apply rightTensor_eq_of_heq F (by
      rw [Fin.append_right, suffixContraction_last_suffix_index]) a
    · refine (F.appendSectorFiber_snd_natAdd_heq _ _
        (Fin.natAdd m (0 : Fin 1)) rfl).trans ?_
      exact dependent_prod_snd_heq z suffixContraction_last_suffix_index
    · refine (F.appendSectorFiber_snd_natAdd_heq _ _
        (Fin.natAdd m (0 : Fin 1)) rfl).trans ?_
      exact dependent_prod_snd_heq z suffixContraction_last_suffix_index
  · have hsector :
        Fin.append k t
            (Fin.natAdd (n + 1) (Fin.natAdd m (0 : Fin 1)) + 1) =
          k (Fin.last n + 1) := by
      rw [suffixContraction_suffix_last_succ, Fin.append_left]
    apply leftTensor_eq_of_heq F hsector a
    · refine (F.appendSectorFiber_fst_castAdd_heq _ _ (Fin.last n + 1)
        suffixContraction_suffix_last_succ).trans ?_
      exact heq_of_eq (F.retainedOpenEdgeEquiv_symm_first_left k x)
    · refine (F.appendSectorFiber_fst_castAdd_heq _ _ (Fin.last n + 1)
        suffixContraction_suffix_last_succ).trans ?_
      exact heq_of_eq (F.retainedOpenEdgeEquiv_symm_first_left k y)

/-- Trace a suffix of fixed length from a retained sector block of the cyclic
neighboring product, summing over all discarded sector labels and fibers.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (adjacent marginal comparison):** The source argument uses
adjacent suffix lengths; the length-three specialization is later restricted
to cyclic-active sector labels. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def suffixSectorContraction
    (F : PhysicalSectorFactorization K) (R : ℕ) [NeZero R] {L : ℕ}
    (k : Fin L → Fin F.sectorCount) :
    Matrix (F.SectorChainFiber k) (F.SectorChainFiber k) ℂ :=
  fun x y ↦
    ∑ t : Fin R → Fin F.sectorCount,
      ∑ z : F.SectorChainFiber t,
        F.cyclicNeighboringProduct (Fin.append k t)
          (F.appendSectorFiber x z) (F.appendSectorFiber y z)

/-- Trace the last three site fibers of a fixed retained sector block of the
cyclic neighboring product, summing over all three discarded sector labels.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** The suffix sum is later restricted
to cyclic-active sector labels, producing the restricted two-step
coefficient. See `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable abbrev threeSuffixSectorContraction
    (F : PhysicalSectorFactorization K) {L : ℕ}
    (k : Fin L → Fin F.sectorCount) :
    Matrix (F.SectorChainFiber k) (F.SectorChainFiber k) ℂ :=
  F.suffixSectorContraction 3 k

/-- Contracting a nonempty suffix fiber in retained open-edge coordinates
leaves the retained bulk product, the two boundary partial traces, and the
product of the internal suffix-edge traces.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617. -/
theorem sum_suffixFiber_cyclicNeighboringProduct
    (F : PhysicalSectorFactorization K) {n m : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount)
    (t : Fin (m + 1) → Fin F.sectorCount)
    (x y : F.RetainedOpenEdgeIndex k) :
    (∑ z : F.SectorChainFiber t,
        F.cyclicNeighboringProduct (Fin.append k t)
          (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm x) z)
          (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm y) z)) =
      F.retainedBulkProduct k x.1 y.1 *
        (Matrix.partialTraceRight
            (F.neighboringOperator (k (Fin.last n)) (t 0)) ⊗ₖ
          Matrix.partialTraceLeft
            (F.neighboringOperator (t (Fin.last m)) (k (Fin.last n + 1))))
          x.2 y.2 *
        ∏ i : Fin m,
          (F.neighboringOperator (t i.castSucc) (t i.succ)).trace := by
  classical
  simp only [cyclicNeighboringProduct]
  simp_rw [Fin.prod_univ_add]
  simp_rw [Fin.prod_univ_one]
  simp_rw [suffixContraction_retained_neighboring_entry]
  simp_rw [suffixContraction_leftBoundary_neighboring_entry]
  simp_rw [suffixContraction_internalSuffix_neighboring_entry]
  simp_rw [suffixContraction_rightBoundary_neighboring_entry]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  simp only [retainedBulkProduct, Matrix.kroneckerMap_apply,
    Matrix.partialTraceRight_apply, Matrix.partialTraceLeft_apply]
  congr 1
  convert F.sum_sectorChainFiber_neighboringOperator_diag t
    (fun a ↦ F.neighboringOperator (k (Fin.last n)) (t 0)
      (x.2.1, a) (y.2.1, a))
    (fun b ↦ F.neighboringOperator (t (Fin.last m)) (k (Fin.last n + 1))
      (b, x.2.2) (b, y.2.2)) using 1
  · apply Finset.sum_congr rfl
    intro z hz
    have hprod :
        (∏ i : Fin m,
          F.neighboringOperator (t (Fin.castAdd 1 i)) (t i.succ)
            ((z (Fin.castAdd 1 i)).2, (z i.succ).1)
            ((z (Fin.castAdd 1 i)).2, (z i.succ).1)) =
          ∏ i : Fin m,
            F.neighboringOperator (t i.castSucc) (t i.succ)
              ((z i.castSucc).2, (z i.succ).1)
              ((z i.castSucc).2, (z i.succ).1) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [suffixContraction_castAdd_one_eq_castSucc]
    rw [hprod]
    ring
  · ring

private theorem sum_threeSuffixFiber_cyclicNeighboringProduct
    (F : PhysicalSectorFactorization K) {n : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount)
    (t : Fin 3 → Fin F.sectorCount)
    (x y : F.RetainedOpenEdgeIndex k) :
    (∑ z : F.SectorChainFiber t,
        F.cyclicNeighboringProduct (Fin.append k t)
          (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm x) z)
          (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm y) z)) =
      F.retainedBulkProduct k x.1 y.1 *
        (Matrix.partialTraceRight
            (F.neighboringOperator (k (Fin.last n)) (t 0)) ⊗ₖ
          Matrix.partialTraceLeft
            (F.neighboringOperator (t 2) (k (Fin.last n + 1))))
          x.2 y.2 *
        (F.neighboringOperator (t 0) (t 1)).trace *
        (F.neighboringOperator (t 1) (t 2)).trace := by
  calc
    _ = F.retainedBulkProduct k x.1 y.1 *
          (Matrix.partialTraceRight
              (F.neighboringOperator (k (Fin.last n)) (t 0)) ⊗ₖ
            Matrix.partialTraceLeft
              (F.neighboringOperator (t 2) (k (Fin.last n + 1))))
            x.2 y.2 *
          ((F.neighboringOperator (t 0) (t 1)).trace *
            (F.neighboringOperator (t 1) (t 2)).trace) := by
      convert F.sum_suffixFiber_cyclicNeighboringProduct k t x y using 1
      rw [Fin.prod_univ_two]
      rw [show Fin.last 2 = (2 : Fin 3) by rfl,
        show Fin.castSucc (0 : Fin 2) = (0 : Fin 3) by rfl,
        show Fin.succ (0 : Fin 2) = (1 : Fin 3) by rfl,
        show Fin.castSucc (1 : Fin 2) = (1 : Fin 3) by rfl,
        show Fin.succ (1 : Fin 2) = (2 : Fin 3) by rfl]
    _ = _ := by ring


/-- A retained sector word is cyclic-active when every one of its sectors
lies on a positive-length directed cycle.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** The source sum is represented on
the sectors occurring in nonzero cyclic products. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
def IsCyclicActiveRetainedWord
    (F : PhysicalSectorFactorization K) {n : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount) : Prop :=
  ∀ i, F.IsCyclicActiveSector (k i)

/-- Regard a cyclic-active retained word as a word in the cyclic-active
subtype.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** This word belongs to the restricted
sector set used in the fourth-region formula. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
def cyclicActiveRetainedWord
    (F : PhysicalSectorFactorization K) {n : ℕ}
    {k : Fin (n + 1) → Fin F.sectorCount}
    (hk : F.IsCyclicActiveRetainedWord k) :
    Fin (n + 1) → F.CyclicActiveSector :=
  fun i ↦ ⟨k i, (F.cyclicActiveWeight_ne_zero_iff (k i)).2 (hk i)⟩



/-- In complete physical-sector coordinates, the marginal obtained by
discarding a suffix of arbitrary length is the direct sum of the corresponding
suffix contractions of the cyclic neighboring products.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (adjacent marginal comparison):** The arbitrary suffix length
simultaneously covers the adjacent source marginals and the later
three-suffix cyclic-active restriction. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem reindex_reducedBlockState_add_eq_suffixSectorContraction
    (F : PhysicalSectorFactorization K) (L R : ℕ) [NeZero R] :
    Matrix.reindex (F.sectorCoordinateChainEquiv L)
        (F.sectorCoordinateChainEquiv L)
        (F.sectorCoordinateTensor.reducedBlockState (L + R) L (by omega)) =
      ((Matrix.trace (mpo F.sectorCoordinateTensor (L + R)))⁻¹ : ℂ) •
        Matrix.blockDiagonal' (fun k ↦ F.suffixSectorContraction R k) := by
  classical
  have hblock :
      F.sectorCoordinateTensor.reducedBlockState (L + R) L (by omega) =
        blockReducedState (Fintype.card (SectorSiteIndex F)) L R
          (F.sectorCoordinateTensor.normalizedMPO (L + R)) := by
    rw [MPOTensor.reducedBlockState]
    simpa only [blockReindexEquiv] using
      blockReducedState_submatrix_finCongr
        (show L + R = L + (L + R - L) by omega)
        (F.sectorCoordinateTensor.normalizedMPO (L + R))
  rw [hblock]
  ext s t
  obtain ⟨k, x⟩ := s
  obtain ⟨h, y⟩ := t
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    blockReducedState, Matrix.partialTraceRight_apply,
    normalizedMPO, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  simp only [blockSplitEquiv_symm_apply]
  change (∑ i : Fin R → Fin (Fintype.card (SectorSiteIndex F)),
      mpo F.sectorCoordinateTensor (L + R)
        (Fin.append ((F.sectorCoordinateChainEquiv L).symm ⟨k, x⟩) i)
        (Fin.append ((F.sectorCoordinateChainEquiv L).symm ⟨h, y⟩) i)) = _
  have hconfig
      (p : Fin L → Fin F.sectorCount) (u : F.SectorChainFiber p)
      (q : Fin R → Fin F.sectorCount) (z : F.SectorChainFiber q) :
      Fin.append ((F.sectorCoordinateChainEquiv L).symm ⟨p, u⟩)
          ((F.sectorCoordinateChainEquiv R).symm ⟨q, z⟩) =
        (F.sectorCoordinateChainEquiv (L + R)).symm
          ⟨Fin.append p q, F.appendSectorFiber u z⟩ := by
    funext i
    refine Fin.addCases (motive := fun i' : Fin (L + R) ↦
      Fin.append ((F.sectorCoordinateChainEquiv L).symm ⟨p, u⟩)
          ((F.sectorCoordinateChainEquiv R).symm ⟨q, z⟩) i' =
        (F.sectorCoordinateChainEquiv (L + R)).symm
          ⟨Fin.append p q, F.appendSectorFiber u z⟩ i')
      (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp [F.sectorCoordinateChainEquiv_symm_apply, appendSectorFiber]
    · simp [F.sectorCoordinateChainEquiv_symm_apply, appendSectorFiber]
  calc
    _ = ∑ s : F.SectorChainIndex R,
        mpo F.sectorCoordinateTensor (L + R)
          (Fin.append ((F.sectorCoordinateChainEquiv L).symm ⟨k, x⟩)
            ((F.sectorCoordinateChainEquiv R).symm s))
          (Fin.append ((F.sectorCoordinateChainEquiv L).symm ⟨h, y⟩)
            ((F.sectorCoordinateChainEquiv R).symm s)) := by
      apply Fintype.sum_equiv (F.sectorCoordinateChainEquiv R)
      intro i
      rw [Equiv.symm_apply_apply]
    _ = _ := by
      rw [Fintype.sum_sigma]
      by_cases hkh : k = h
      · subst h
        rw [Matrix.blockDiagonal'_apply_eq]
        simp only [suffixSectorContraction]
        apply Finset.sum_congr rfl
        intro q _
        apply Finset.sum_congr rfl
        intro z _
        rw [hconfig k x q z, hconfig k y q z]
        have hentry := congrFun (congrFun
          (F.reindex_mpo_sectorCoordinateTensor_eq_blockDiagonal
            (N := L + R))
          ⟨Fin.append k q, F.appendSectorFiber x z⟩)
          ⟨Fin.append k q, F.appendSectorFiber y z⟩
        simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
          Matrix.blockDiagonal'_apply_eq] using hentry
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkh]
        apply Finset.sum_eq_zero
        intro q _
        apply Finset.sum_eq_zero
        intro z _
        rw [hconfig k x q z, hconfig h y q z]
        have happend_ne : Fin.append k q ≠ Fin.append h q := by
          intro heq
          apply hkh
          funext i
          have hi := congrFun heq (Fin.castAdd R i)
          simpa using hi
        have hentry := congrFun (congrFun
          (F.reindex_mpo_sectorCoordinateTensor_eq_blockDiagonal
            (N := L + R))
          ⟨Fin.append k q, F.appendSectorFiber x z⟩)
          ⟨Fin.append h q, F.appendSectorFiber y z⟩
        simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
          Matrix.blockDiagonal'_apply_ne _ _ _ happend_ne] using hentry

/-- In complete physical-sector coordinates, the marginal obtained by
discarding three suffix sites is the direct sum of the corresponding
three-suffix contractions of the cyclic neighboring products.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** The direct sum is subsequently
reduced to retained cyclic-active sector words. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem reindex_reducedBlockState_add_three_eq_threeSuffixSectorContraction
    (F : PhysicalSectorFactorization K) (L : ℕ) :
    Matrix.reindex (F.sectorCoordinateChainEquiv L)
        (F.sectorCoordinateChainEquiv L)
        (F.sectorCoordinateTensor.reducedBlockState (L + 3) L (by omega)) =
      ((Matrix.trace (mpo F.sectorCoordinateTensor (L + 3)))⁻¹ : ℂ) •
        Matrix.blockDiagonal' (fun k ↦ F.threeSuffixSectorContraction k) :=
  F.reindex_reducedBlockState_add_eq_suffixSectorContraction L 3

/-- Source ZCL marginal replacement is preserved by the physical coordinate
isometry defining the sector-coordinate tensor.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** This replacement supplies the
extra marginal step used before restricting the sector sum. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem sectorCoordinateTensor_reducedBlockState_add_three_eq_succ_of_isSourceZCL
    (F : PhysicalSectorFactorization K) (hZCL : K.IsSourceZCL) (L : ℕ) :
    F.sectorCoordinateTensor.reducedBlockState (L + 3) L (by omega) =
      F.sectorCoordinateTensor.reducedBlockState (L + 1) L (by omega) := by
  rw [F.sectorCoordinateTensor_eq_changePhysicalBasis]
  rw [reducedBlockState_changePhysicalBasis_of_isometry
    F.physicalCoordinateMatrix F.physicalCoordinateMatrix_isometry]
  rw [reducedBlockState_changePhysicalBasis_of_isometry
    F.physicalCoordinateMatrix F.physicalCoordinateMatrix_isometry]
  rw [K.reducedBlockState_add_three_eq_succ_of_isSourceZCL hZCL]

/-- The three-site sector word determined by three cyclic-active sectors.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** The word ranges over the restricted
cyclic-active sector set. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
def activeThreeSectorWord
    (F : PhysicalSectorFactorization K)
    (q r h : F.CyclicActiveSector) : Fin 3 → Fin F.sectorCount :=
  Fin.cons q <| Fin.cons r <| Fin.cons h finZeroElim

/-- The first entry of the cyclic-active three-site word.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** This projection identifies the
first sector of the restricted suffix. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem activeThreeSectorWord_zero
    (F : PhysicalSectorFactorization K) (q r h : F.CyclicActiveSector) :
    F.activeThreeSectorWord q r h 0 = q := by
  rfl

/-- The second entry of the cyclic-active three-site word.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** This projection identifies the
middle sector of the restricted suffix. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem activeThreeSectorWord_one
    (F : PhysicalSectorFactorization K) (q r h : F.CyclicActiveSector) :
    F.activeThreeSectorWord q r h 1 = r := by
  rfl

/-- The third entry of the cyclic-active three-site word.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** This projection identifies the
last sector of the restricted suffix. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem activeThreeSectorWord_two
    (F : PhysicalSectorFactorization K) (q r h : F.CyclicActiveSector) :
    F.activeThreeSectorWord q r h 2 = h := by
  rfl

/-- Contract a three-site suffix whose sector labels are cyclic-active.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** The contraction is evaluated only
on the sectors surviving cyclic-active deletion. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem sum_threeSuffixFiber_cyclicNeighboringProduct_active
    (F : PhysicalSectorFactorization K) {n : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount)
    (q r h : F.CyclicActiveSector)
    (x y : F.RetainedOpenEdgeIndex k) :
    (∑ z : F.SectorChainFiber (F.activeThreeSectorWord q r h),
        F.cyclicNeighboringProduct
          (Fin.append k (F.activeThreeSectorWord q r h))
          (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm x) z)
          (F.appendSectorFiber ((F.retainedOpenEdgeEquiv k).symm y) z)) =
      F.retainedBulkProduct k x.1 y.1 *
        (Matrix.partialTraceRight
            (F.neighboringOperator (k (Fin.last n)) q) ⊗ₖ
          Matrix.partialTraceLeft
            (F.neighboringOperator h (k (Fin.last n + 1))))
          x.2 y.2 *
        (F.neighboringOperator q r).trace *
        (F.neighboringOperator r h).trace := by
  calc
    _ = F.retainedBulkProduct k x.1 y.1 *
          (Matrix.partialTraceRight
              (F.neighboringOperator (k (Fin.last n))
                (F.activeThreeSectorWord q r h 0)) ⊗ₖ
            Matrix.partialTraceLeft
              (F.neighboringOperator (F.activeThreeSectorWord q r h 2)
                (k (Fin.last n + 1)))) x.2 y.2 *
          (F.neighboringOperator (F.activeThreeSectorWord q r h 0)
            (F.activeThreeSectorWord q r h 1)).trace *
          (F.neighboringOperator (F.activeThreeSectorWord q r h 1)
            (F.activeThreeSectorWord q r h 2)).trace :=
      F.sum_threeSuffixFiber_cyclicNeighboringProduct k
        (F.activeThreeSectorWord q r h) x y
    _ = _ := by
      simp only [Matrix.kroneckerMap_apply]
      rw [F.partialTraceRight_neighboringOperator_eq_of_right
          (k (Fin.last n)) (F.activeThreeSectorWord q r h 0) q
          (F.activeThreeSectorWord_zero q r h) x.2.1 y.2.1,
        F.partialTraceLeft_neighboringOperator_eq_of_left
          (F.activeThreeSectorWord q r h 2) h (k (Fin.last n + 1))
          (F.activeThreeSectorWord_two q r h) x.2.2 y.2.2,
        F.neighboringOperator_trace_eq_of_eq
          (F.activeThreeSectorWord q r h 0) q
          (F.activeThreeSectorWord q r h 1) r
          (F.activeThreeSectorWord_zero q r h)
          (F.activeThreeSectorWord_one q r h),
        F.neighboringOperator_trace_eq_of_eq
          (F.activeThreeSectorWord q r h 1) r
          (F.activeThreeSectorWord q r h 2) h
          (F.activeThreeSectorWord_one q r h)
          (F.activeThreeSectorWord_two q r h)]

end MPOTensor.PhysicalSectorFactorization
