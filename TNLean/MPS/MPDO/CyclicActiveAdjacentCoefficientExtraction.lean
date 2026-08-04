/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PerronFrobenius.SupportStabilization
import TNLean.MPS.MPDO.CyclicActiveSuffixMarginal
import TNLean.MPS.MPDO.SelectedFixedProductSectorVisibility
import TNLean.MPS.MPDO.CyclicActiveTraceProductIdentities

/-!
# Coefficients of adjacent cyclic-active suffix marginals

This file extracts the square--cube relation for the cyclic-active trace
matrix from equality of the normalized marginals obtained by discarding one
and two adjacent suffix sites.

## Reference

* arXiv:1606.00608, Appendix C.2, Proposition 4to2, lines 1606--1617.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

private theorem reducedBlockState_eq_of_mpo_eq_smul
    {E : ℕ} (M : MPOTensor d D) (C : MPOTensor d E)
    (N L : ℕ) (hL : L ≤ N) (c : ℂ) (hc : c ≠ 0)
    (hmpo : mpo M N = c • mpo C N) :
    M.reducedBlockState N L hL = C.reducedBlockState N L hL := by
  have hnormalized : normalizedMPO M N = normalizedMPO C N := by
    rw [normalizedMPO, normalizedMPO, hmpo, Matrix.trace_smul,
      smul_smul, smul_eq_mul]
    congr 1
    field_simp
  unfold reducedBlockState
  rw [hnormalized]

private theorem sum_eq_sum_subtype_of_eq_zero
    {α M : Type*} [Fintype α] [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] (f : α → M)
    (hzero : ∀ x, ¬p x → f x = 0) :
    ∑ x, f x = ∑ x : {x // p x}, f x := by
  classical
  calc
    _ = ∑ x ∈ Finset.univ.filter p, f x := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro x hx hxnot
      rw [hzero x]
      simpa using hxnot
    _ = _ := Finset.sum_subtype _ (by simp) f

private def cyclicActiveSectorSubtypeEquiv
    (F : PhysicalSectorFactorization K) :
    {q : Fin F.sectorCount // F.IsCyclicActiveSector q} ≃
      F.CyclicActiveSector where
  toFun q := ⟨q, (F.cyclicActiveWeight_ne_zero_iff q).2 q.2⟩
  invFun q := ⟨q, (F.cyclicActiveWeight_ne_zero_iff q).1 q.2⟩
  left_inv q := by ext; rfl
  right_inv q := by ext; rfl

<<<<<<< HEAD
/-- The trace of the cyclic tensor product of neighboring operators equals
the product of their individual traces.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1586--1589. -/
theorem trace_cyclicNeighboringProduct_eq_prod_trace
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N]
    (k : Fin N → Fin F.sectorCount) :
    Matrix.trace (F.cyclicNeighboringProduct k) =
      ∏ i : Fin N, Matrix.trace (F.neighboringOperator (k i) (k (i + 1))) := by
  classical
  rw [Matrix.trace]
  calc
    (∑ x : F.SectorChainFiber k, Matrix.diag (F.cyclicNeighboringProduct k) x) =
        ∑ x : (i : Fin N) → F.NeighborIndex (k i) (k (i + 1)),
          Matrix.diag (F.cyclicNeighboringProduct k)
            ((F.cyclicEdgeEquiv k).symm x) := by
      apply Fintype.sum_equiv (F.cyclicEdgeEquiv k)
      intro x
      rw [Equiv.symm_apply_apply]
    _ = ∑ x : (i : Fin N) → F.NeighborIndex (k i) (k (i + 1)),
          ∏ i : Fin N, F.neighboringOperator (k i) (k (i + 1)) (x i) (x i) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [Matrix.diag_apply, cyclicNeighboringProduct]
      apply Finset.prod_congr rfl
      intro i _
      have hx := congrFun ((F.cyclicEdgeEquiv k).apply_symm_apply x) i
      simpa only [cyclicEdgeEquiv_apply] using
        congrArg₂ (F.neighboringOperator (k i) (k (i + 1))) hx hx
    _ = _ := by
      simp_rw [Matrix.trace, Matrix.diag_apply]
      rw [Finset.prod_univ_sum
        (fun i : Fin N ↦
          (Finset.univ : Finset (F.NeighborIndex (k i) (k (i + 1)))))
        (fun i x ↦ F.neighboringOperator (k i) (k (i + 1)) x x)]
      simp only [Fintype.piFinset_univ]

=======
>>>>>>> 17724c7ed (refactor(MPS/MPDO): split cyclic-active trace identities and cite source notes)

private def appendSectorFiberEquiv
    (F : PhysicalSectorFactorization K)
    {L R : ℕ} {k : Fin L → Fin F.sectorCount}
    {t : Fin R → Fin F.sectorCount} :
    F.SectorChainFiber k × F.SectorChainFiber t ≃
      F.SectorChainFiber (Fin.append k t) where
  toFun xz := F.appendSectorFiber xz.1 xz.2
  invFun w :=
    (fun i ↦ by
      simpa using w (Fin.castAdd R i),
    fun i ↦ by
      simpa using w (Fin.natAdd L i))
  left_inv xz := by
    apply Prod.ext
    · funext i
      simp [appendSectorFiber]
    · funext i
      simp [appendSectorFiber]
  right_inv w := by
    funext i
    refine Fin.addCases (motive := fun i' : Fin (L + R) ↦
      F.appendSectorFiber
        (fun j ↦ by simpa using w (Fin.castAdd R j))
        (fun j ↦ by simpa using w (Fin.natAdd L j)) i' = w i')
      (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp [appendSectorFiber]
    · simp [appendSectorFiber]

private theorem trace_suffixSectorContraction_eq_sum_prod_trace
    (F : PhysicalSectorFactorization K) (R : ℕ) [NeZero R]
    {L : ℕ} (k : Fin L → Fin F.sectorCount) :
    Matrix.trace (F.suffixSectorContraction R k) =
      ∑ t : Fin R → Fin F.sectorCount,
        ∏ i : Fin (L + R),
          Matrix.trace (F.neighboringOperator
            (Fin.append k t i) (Fin.append k t (i + 1))) := by
  classical
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, suffixSectorContraction]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  calc
    (∑ x : F.SectorChainFiber k, ∑ z : F.SectorChainFiber t,
        F.cyclicNeighboringProduct (Fin.append k t)
          (F.appendSectorFiber x z) (F.appendSectorFiber x z)) =
        ∑ xz : F.SectorChainFiber k × F.SectorChainFiber t,
          F.cyclicNeighboringProduct (Fin.append k t)
            (F.appendSectorFiber xz.1 xz.2)
            (F.appendSectorFiber xz.1 xz.2) := by
      simp only [Fintype.sum_prod_type]
    _ = Matrix.trace (F.cyclicNeighboringProduct (Fin.append k t)) := by
      rw [Matrix.trace]
      apply Fintype.sum_equiv (F.appendSectorFiberEquiv)
      intro xz
      simp only [Matrix.diag_apply]
      rfl
    _ = _ := F.trace_cyclicNeighboringProduct_eq_prod_trace (Fin.append k t)

private noncomputable def retainedTraceProduct
    (F : PhysicalSectorFactorization K) {n : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount) : ℂ :=
  ∏ i : Fin n,
    Matrix.trace (F.neighboringOperator (k i.castSucc) (k i.succ))

private theorem trace_oneSuffixSectorContraction_eq
    (F : PhysicalSectorFactorization K) {n : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount) :
    Matrix.trace (F.oneSuffixSectorContraction k) =
      F.retainedTraceProduct k *
        ∑ r : Fin F.sectorCount,
          Matrix.trace (F.neighboringOperator (k (Fin.last n)) r) *
            Matrix.trace (F.neighboringOperator r (k 0)) := by
  rw [oneSuffixSectorContraction,
    F.trace_suffixSectorContraction_eq_sum_prod_trace]
  simp_rw [Fin.prod_univ_add]
  simp only [Fin.prod_univ_one]
  have hinternal (t : Fin 1 → Fin F.sectorCount) (i : Fin n) :
      Matrix.trace (F.neighboringOperator
        (Fin.append k t (Fin.castAdd 1 (Fin.castAdd 1 i)))
        (Fin.append k t (Fin.castAdd 1 (Fin.castAdd 1 i) + 1))) =
      Matrix.trace (F.neighboringOperator (k i.castSucc) (k i.succ)) := by
    have hleft :
        Fin.append k t (Fin.castAdd 1 (Fin.castAdd 1 i)) = k i.castSucc := by
      rw [Fin.append_left]
      congr 1
    have hright :
        Fin.append k t (Fin.castAdd 1 (Fin.castAdd 1 i) + 1) = k i.succ := by
      have hindex :
          Fin.castAdd 1 i.succ = Fin.castAdd 1 (Fin.castAdd 1 i) + 1 := by
        apply Fin.ext
        rw [Fin.val_add_eq_of_add_lt]
        · rfl
        · change i.val + 1 < n + 1 + 1
          omega
      rw [← hindex, Fin.append_left]
    rw [hleft, hright]
  simp_rw [hinternal]
  have hlast (t : Fin 1 → Fin F.sectorCount) :
      Matrix.trace (F.neighboringOperator
        (Fin.append k t (Fin.castAdd 1 (Fin.natAdd n 0)))
        (Fin.append k t (Fin.castAdd 1 (Fin.natAdd n 0) + 1))) =
      Matrix.trace (F.neighboringOperator (k (Fin.last n)) (t 0)) := by
    have hleft :
        Fin.append k t (Fin.castAdd 1 (Fin.natAdd n 0)) = k (Fin.last n) := by
      rw [Fin.append_left]
      congr 1
    have hindex :
        Fin.castAdd 1 (Fin.natAdd n 0) + 1 = Fin.natAdd (n + 1) 0 := by
      apply Fin.ext
      simp [Fin.add_def]
    rw [hleft, hindex, Fin.append_right]
  simp_rw [hlast]
  have hfirst (t : Fin 1 → Fin F.sectorCount) :
      Matrix.trace (F.neighboringOperator
        (Fin.append k t (Fin.natAdd (n + 1) 0))
        (Fin.append k t (Fin.natAdd (n + 1) 0 + 1))) =
      Matrix.trace (F.neighboringOperator (t 0) (k 0)) := by
    have hindex : Fin.natAdd (n + 1) 0 + 1 = (0 : Fin (n + 1 + 1)) := by
      apply Fin.ext
      simp [Fin.add_def]
    rw [Fin.append_right, hindex]
    rw [show (0 : Fin (n + 1 + 1)) = Fin.castAdd 1 (0 : Fin (n + 1)) by rfl,
      Fin.append_left]
  simp_rw [hfirst]
  simp only [retainedTraceProduct]
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin F.sectorCount))
  intro t
  change F.retainedTraceProduct k *
      Matrix.trace (F.neighboringOperator (k (Fin.last n)) (t 0)) *
        Matrix.trace (F.neighboringOperator (t 0) (k 0)) =
    F.retainedTraceProduct k *
      (Matrix.trace (F.neighboringOperator (k (Fin.last n)) (t 0)) *
        Matrix.trace (F.neighboringOperator (t 0) (k 0)))
  ring

private theorem trace_twoSuffixSectorContraction_eq
    (F : PhysicalSectorFactorization K) {n : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount) :
    Matrix.trace (F.twoSuffixSectorContraction k) =
      F.retainedTraceProduct k *
        ∑ q : Fin F.sectorCount, ∑ r : Fin F.sectorCount,
          Matrix.trace (F.neighboringOperator (k (Fin.last n)) q) *
            Matrix.trace (F.neighboringOperator q r) *
              Matrix.trace (F.neighboringOperator r (k 0)) := by
  rw [twoSuffixSectorContraction,
    F.trace_suffixSectorContraction_eq_sum_prod_trace]
  simp_rw [Fin.prod_univ_add]
  simp only [Fin.prod_univ_one, Fin.prod_univ_two]
  have hinternal (t : Fin 2 → Fin F.sectorCount) (i : Fin n) :
      Matrix.trace (F.neighboringOperator
        (Fin.append k t (Fin.castAdd 2 (Fin.castAdd 1 i)))
        (Fin.append k t (Fin.castAdd 2 (Fin.castAdd 1 i) + 1))) =
      Matrix.trace (F.neighboringOperator (k i.castSucc) (k i.succ)) := by
    have hleft :
        Fin.append k t (Fin.castAdd 2 (Fin.castAdd 1 i)) = k i.castSucc := by
      rw [Fin.append_left]
      congr 1
    have hindex :
        Fin.castAdd 2 i.succ = Fin.castAdd 2 (Fin.castAdd 1 i) + 1 := by
      apply Fin.ext
      rw [Fin.val_add_eq_of_add_lt]
      · rfl
      · change i.val + 1 < n + 1 + 2
        omega
    rw [hleft, ← hindex, Fin.append_left]
  simp_rw [hinternal]
  have hlast (t : Fin 2 → Fin F.sectorCount) :
      Matrix.trace (F.neighboringOperator
        (Fin.append k t (Fin.castAdd 2 (Fin.natAdd n 0)))
        (Fin.append k t (Fin.castAdd 2 (Fin.natAdd n 0) + 1))) =
      Matrix.trace (F.neighboringOperator (k (Fin.last n)) (t 0)) := by
    have hleft :
        Fin.append k t (Fin.castAdd 2 (Fin.natAdd n 0)) = k (Fin.last n) := by
      rw [Fin.append_left]
      congr 1
    have hindex :
        Fin.castAdd 2 (Fin.natAdd n 0) + 1 = Fin.natAdd (n + 1) 0 := by
      apply Fin.ext
      rw [Fin.val_add_eq_of_add_lt]
      · rfl
      · norm_num [Fin.natAdd]
    rw [hleft, hindex, Fin.append_right]
  simp_rw [hlast]
  have hmiddle (t : Fin 2 → Fin F.sectorCount) :
      Matrix.trace (F.neighboringOperator
        (Fin.append k t (Fin.natAdd (n + 1) 0))
        (Fin.append k t (Fin.natAdd (n + 1) 0 + 1))) =
      Matrix.trace (F.neighboringOperator (t 0) (t 1)) := by
    have hindex :
        Fin.natAdd (n + 1) (0 : Fin 2) + 1 =
          Fin.natAdd (n + 1) (1 : Fin 2) := by
      apply Fin.ext
      rw [Fin.val_add_eq_of_add_lt]
      · rfl
      · norm_num [Fin.natAdd]
    rw [Fin.append_right, hindex, Fin.append_right]
  simp_rw [hmiddle]
  have hfirst (t : Fin 2 → Fin F.sectorCount) :
      Matrix.trace (F.neighboringOperator
        (Fin.append k t (Fin.natAdd (n + 1) 1))
        (Fin.append k t (Fin.natAdd (n + 1) 1 + 1))) =
      Matrix.trace (F.neighboringOperator (t 1) (k 0)) := by
    have hindex : Fin.natAdd (n + 1) 1 + 1 = (0 : Fin (n + 1 + 2)) := by
      apply Fin.ext
      simp [Fin.add_def]
    rw [Fin.append_right, hindex]
    rw [show (0 : Fin (n + 1 + 2)) = Fin.castAdd 2 (0 : Fin (n + 1)) by rfl,
      Fin.append_left]
  simp_rw [hfirst]
  simp only [retainedTraceProduct]
  calc
    _ = ∑ qr : Fin F.sectorCount × Fin F.sectorCount,
        F.retainedTraceProduct k *
          (Matrix.trace (F.neighboringOperator (k (Fin.last n)) qr.1) *
            Matrix.trace (F.neighboringOperator qr.1 qr.2) *
              Matrix.trace (F.neighboringOperator qr.2 (k 0))) := by
      apply Fintype.sum_equiv (finTwoArrowEquiv (Fin F.sectorCount))
      intro t
      change F.retainedTraceProduct k *
          Matrix.trace (F.neighboringOperator (k (Fin.last n)) (t 0)) *
            (Matrix.trace (F.neighboringOperator (t 0) (t 1)) *
              Matrix.trace (F.neighboringOperator (t 1) (k 0))) =
        F.retainedTraceProduct k *
          (Matrix.trace (F.neighboringOperator (k (Fin.last n)) (t 0)) *
            Matrix.trace (F.neighboringOperator (t 0) (t 1)) *
              Matrix.trace (F.neighboringOperator (t 1) (k 0)))
      ring
    _ = _ := by
      simp only [Fintype.sum_prod_type]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      change F.retainedTraceProduct k *
          (Matrix.trace (F.neighboringOperator (k (Fin.last n)) q) *
            Matrix.trace (F.neighboringOperator q r) *
              Matrix.trace (F.neighboringOperator r (k 0))) =
        F.retainedTraceProduct k *
          (Matrix.trace (F.neighboringOperator (k (Fin.last n)) q) *
            Matrix.trace (F.neighboringOperator q r) *
              Matrix.trace (F.neighboringOperator r (k 0)))
      rfl

private theorem sum_sector_trace_two_eq_cyclicActive_pow_two
    (F : PhysicalSectorFactorization K)
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (q h : F.CyclicActiveSector)
    (hreach : Relation.ReflTransGen
      (fun a b : F.CyclicActiveSector ↦ F.neighboringOperator a b ≠ 0) h q) :
    ∑ r : Fin F.sectorCount,
        Matrix.trace (F.neighboringOperator q r) *
          Matrix.trace (F.neighboringOperator r h) =
      ((F.cyclicActiveSectorTraceMatrix ^ 2) q h : ℂ) := by
  classical
  have hreachRaw : Relation.ReflTransGen
      (fun a b : Fin F.sectorCount ↦ F.neighboringOperator a b ≠ 0) h q := by
    induction hreach with
    | refl => exact .refl
    | tail hab hbc ih => exact ih.tail hbc
  calc
    _ = ∑ r : {r : Fin F.sectorCount // F.IsCyclicActiveSector r},
        Matrix.trace (F.neighboringOperator q r) *
          Matrix.trace (F.neighboringOperator r h) := by
      apply sum_eq_sum_subtype_of_eq_zero
      intro r hr
      by_contra hne
      have hmul := mul_ne_zero_iff.mp hne
      apply hr
      exact ⟨h, fun hzero ↦ hmul.2 (by simp [hzero]),
        hreachRaw.tail (fun hzero ↦ hmul.1 (by simp [hzero]))⟩
    _ = ∑ r : F.CyclicActiveSector,
        Matrix.trace (F.neighboringOperator q r) *
          Matrix.trace (F.neighboringOperator r h) := by
      apply Fintype.sum_equiv F.cyclicActiveSectorSubtypeEquiv
      intro r
      rfl
    _ = _ := F.sum_cyclicActive_trace_mul_trace_eq_pow_two hpos q h

private theorem sum_sector_trace_three_eq_cyclicActive_pow_three
    (F : PhysicalSectorFactorization K)
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (q h : F.CyclicActiveSector)
    (hreach : Relation.ReflTransGen
      (fun a b : F.CyclicActiveSector ↦ F.neighboringOperator a b ≠ 0) h q) :
    ∑ a : Fin F.sectorCount, ∑ b : Fin F.sectorCount,
        Matrix.trace (F.neighboringOperator q a) *
          Matrix.trace (F.neighboringOperator a b) *
            Matrix.trace (F.neighboringOperator b h) =
      ((F.cyclicActiveSectorTraceMatrix ^ 3) q h : ℂ) := by
  classical
  have hreachRaw : Relation.ReflTransGen
      (fun a b : Fin F.sectorCount ↦ F.neighboringOperator a b ≠ 0) h q := by
    induction hreach with
    | refl => exact .refl
    | tail hab hbc ih => exact ih.tail hbc
  calc
    _ = ∑ a : {a : Fin F.sectorCount // F.IsCyclicActiveSector a},
        ∑ b : Fin F.sectorCount,
          Matrix.trace (F.neighboringOperator q a) *
            Matrix.trace (F.neighboringOperator a b) *
              Matrix.trace (F.neighboringOperator b h) := by
      apply sum_eq_sum_subtype_of_eq_zero
      intro a ha
      apply Finset.sum_eq_zero
      intro b _
      by_contra hne
      have habc := mul_ne_zero_iff.mp hne
      have hab := mul_ne_zero_iff.mp habc.1
      have hqa : F.neighboringOperator q a ≠ 0 := fun hzero ↦
        hab.1 (by rw [hzero, Matrix.trace_zero])
      have habEdge : F.neighboringOperator a b ≠ 0 := fun hzero ↦
        hab.2 (by rw [hzero, Matrix.trace_zero])
      have hbh : F.neighboringOperator b h ≠ 0 := fun hzero ↦
        habc.2 (by rw [hzero, Matrix.trace_zero])
      have hbhPath : Relation.ReflTransGen
          (fun x y : Fin F.sectorCount ↦ F.neighboringOperator x y ≠ 0) b h :=
        Relation.ReflTransGen.single hbh
      have hreturn : Relation.ReflTransGen
          (fun x y : Fin F.sectorCount ↦ F.neighboringOperator x y ≠ 0) b a :=
        hbhPath.trans (hreachRaw.tail hqa)
      apply ha
      exact ⟨b, habEdge, hreturn⟩
    _ = ∑ a : {a : Fin F.sectorCount // F.IsCyclicActiveSector a},
        ∑ b : {b : Fin F.sectorCount // F.IsCyclicActiveSector b},
          Matrix.trace (F.neighboringOperator q a) *
            Matrix.trace (F.neighboringOperator a b) *
              Matrix.trace (F.neighboringOperator b h) := by
      apply Finset.sum_congr rfl
      intro a _
      apply sum_eq_sum_subtype_of_eq_zero
      intro b hb
      by_contra hne
      have habc := mul_ne_zero_iff.mp hne
      have hab := mul_ne_zero_iff.mp habc.1
      have hqa : F.neighboringOperator q a ≠ 0 := fun hzero ↦
        hab.1 (by rw [hzero, Matrix.trace_zero])
      have habEdge : F.neighboringOperator a b ≠ 0 := fun hzero ↦
        hab.2 (by rw [hzero, Matrix.trace_zero])
      have hbh : F.neighboringOperator b h ≠ 0 := fun hzero ↦
        habc.2 (by rw [hzero, Matrix.trace_zero])
      apply hb
      exact ⟨h, hbh, (hreachRaw.tail hqa).tail habEdge⟩
    _ = ∑ a : F.CyclicActiveSector, ∑ b : F.CyclicActiveSector,
        Matrix.trace (F.neighboringOperator q a) *
          Matrix.trace (F.neighboringOperator a b) *
            Matrix.trace (F.neighboringOperator b h) := by
      apply Fintype.sum_equiv F.cyclicActiveSectorSubtypeEquiv
      intro a
      apply Fintype.sum_equiv F.cyclicActiveSectorSubtypeEquiv
      intro b
      rfl
    _ = _ := by
      simp_rw [F.neighboringOperator_trace_eq_cyclicActiveSectorTraceMatrix hpos]
      rw [show F.cyclicActiveSectorTraceMatrix ^ 3 =
        F.cyclicActiveSectorTraceMatrix *
          F.cyclicActiveSectorTraceMatrix *
            F.cyclicActiveSectorTraceMatrix by simp [pow_succ]]
      simp only [Matrix.mul_apply]
      simp_rw [Finset.sum_mul]
      norm_cast
      rw [Finset.sum_comm]

private theorem normalized_trace_twoSuffix_eq_oneSuffix_of_reducedBlockState_eq
    (F : PhysicalSectorFactorization K) (L : ℕ)
    (hmarg :
      F.sectorCoordinateTensor.reducedBlockState (L + 2) L (by omega) =
        F.sectorCoordinateTensor.reducedBlockState (L + 1) L (by omega))
    (k : Fin L → Fin F.sectorCount) :
    ((Matrix.trace (mpo F.sectorCoordinateTensor (L + 2)))⁻¹ : ℂ) *
        Matrix.trace (F.twoSuffixSectorContraction k) =
      ((Matrix.trace (mpo F.sectorCoordinateTensor (L + 1)))⁻¹ : ℂ) *
        Matrix.trace (F.oneSuffixSectorContraction k) := by
  classical
  have hblocks :
      ((Matrix.trace (mpo F.sectorCoordinateTensor (L + 2)))⁻¹ : ℂ) •
          Matrix.blockDiagonal'
            (fun k : Fin L → Fin F.sectorCount ↦ F.twoSuffixSectorContraction k) =
        ((Matrix.trace (mpo F.sectorCoordinateTensor (L + 1)))⁻¹ : ℂ) •
          Matrix.blockDiagonal'
            (fun k : Fin L → Fin F.sectorCount ↦ F.oneSuffixSectorContraction k) := by
    rw [← F.reindex_reducedBlockState_add_two_eq_twoSuffixSectorContraction,
      ← F.reindex_reducedBlockState_add_one_eq_oneSuffixSectorContraction]
    exact congrArg
      (Matrix.reindex (F.sectorCoordinateChainEquiv L)
        (F.sectorCoordinateChainEquiv L)) hmarg
  have hk :
      ((Matrix.trace (mpo F.sectorCoordinateTensor (L + 2)))⁻¹ : ℂ) •
          F.twoSuffixSectorContraction k =
        ((Matrix.trace (mpo F.sectorCoordinateTensor (L + 1)))⁻¹ : ℂ) •
          F.oneSuffixSectorContraction k := by
    ext x y
    have hxy := congrFun (congrFun hblocks ⟨k, x⟩) ⟨k, y⟩
    simpa [Matrix.blockDiagonal'_apply_eq] using hxy
  have htrace := congrArg Matrix.trace hk
  simpa [Matrix.trace_smul] using htrace

private theorem exists_retainedTraceProduct_ne_zero_of_reflTransGen
    (F : PhysicalSectorFactorization K)
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (q h : F.CyclicActiveSector)
    (hreach : Relation.ReflTransGen
      (fun a b : F.CyclicActiveSector ↦ F.neighboringOperator a b ≠ 0) h q) :
    ∃ n : ℕ, ∃ k : Fin (n + 1) → Fin F.sectorCount,
      k 0 = h ∧ k (Fin.last n) = q ∧ F.retainedTraceProduct k ≠ 0 := by
  classical
  have hreachRaw : Relation.ReflTransGen
      (fun a b : Fin F.sectorCount ↦ F.neighboringOperator a b ≠ 0) h q := by
    induction hreach with
    | refl => exact .refl
    | tail hab hbc ih => exact ih.tail hbc
  obtain ⟨l, hchain, hlast⟩ :=
    List.exists_isChain_cons_of_relationReflTransGen hreachRaw
  let n := l.length
  let k : Fin (n + 1) → Fin F.sectorCount := fun i ↦ (h.1 :: l).get i
  have hk0 : k 0 = h := by simp [k]
  have hklast : k (Fin.last n) = q := by
    change (h.1 :: l).get (Fin.last n) = q
    simpa [n, List.get_eq_getElem, List.getLast_eq_getElem] using hlast
  have hedge : ∀ j : Fin n,
      F.neighboringOperator (k j.castSucc) (k j.succ) ≠ 0 := by
    intro j
    have hj1 : (j : ℕ) + 1 < (h.1 :: l).length := by
      simp [n]
    have hj0 : (j : ℕ) < (h.1 :: l).length := by omega
    have hj := (List.isChain_iff_getElem.mp hchain) (j : ℕ) hj1
    have hleft : k j.castSucc = (h.1 :: l)[(j : ℕ)]'hj0 := by
      simp [k, List.get_eq_getElem]
    have hright : k j.succ = (h.1 :: l)[(j : ℕ) + 1]'hj1 := by
      simp [k, List.get_eq_getElem]
    rw [hleft, hright]
    exact hj
  refine ⟨n, k, hk0, hklast, ?_⟩
  rw [retainedTraceProduct]
  exact Finset.prod_ne_zero_iff.mpr fun j _ ↦
    ne_of_gt ((hpos _ _).trace_pos_of_ne_zero (hedge j))

private theorem cyclicActiveSectorTraceMatrix_isIrreducible_of_reflTransGen
    (F : PhysicalSectorFactorization K)
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (hreach : ∀ q h : F.CyclicActiveSector,
      Relation.ReflTransGen
        (fun a b : F.CyclicActiveSector ↦ F.neighboringOperator a b ≠ 0) q h) :
    Matrix.IsIrreducible F.cyclicActiveSectorTraceMatrix := by
  classical
  letI : Quiver F.CyclicActiveSector :=
    Matrix.toQuiver F.cyclicActiveSectorTraceMatrix
  refine ⟨F.activeSectorTraceMatrix_nonneg F.cyclicActiveWeight hpos, ?_⟩
  have hconnected : Quiver.IsStronglyConnected F.CyclicActiveSector := by
    intro q h
    have hqh := hreach q h
    induction hqh with
    | refl => exact ⟨Quiver.Path.nil⟩
    | tail hab hbc ih =>
        exact ⟨ih.some.cons (PLift.up
          ((F.activeSectorTraceMatrix_pos_iff F.cyclicActiveWeight hpos _ _).2 hbc))⟩
  cases isEmpty_or_nonempty F.CyclicActiveSector with
  | inl hempty =>
      intro q
      exact isEmptyElim q
  | inr hnonempty =>
      let q : F.CyclicActiveSector := Classical.choice hnonempty
      have hqactive : F.IsCyclicActiveSector q :=
        (F.cyclicActiveWeight_ne_zero_iff q).1 q.2
      obtain ⟨h, hqh, hhq⟩ := hqactive
      have hhactive : F.IsCyclicActiveSector h := by
        obtain ⟨l, hchain, hlast⟩ :=
          List.exists_isChain_cons_of_relationReflTransGen hhq
        cases l with
        | nil =>
            have heq : h = q := by simpa using hlast
            subst h
            exact ⟨q, hqh, .refl⟩
        | cons a l =>
            have hha : F.neighboringOperator h a ≠ 0 := by
              simpa using hchain.rel
            have htail : List.IsChain
                (fun x y ↦ F.neighboringOperator x y ≠ 0) (a :: l) :=
              hchain.tail
            have halast : (a :: l).getLast (by simp) = q := by
              simpa using hlast
            have haq : Relation.ReflTransGen
                (fun x y ↦ F.neighboringOperator x y ≠ 0) a q :=
              List.relationReflTransGen_of_exists_isChain_cons l htail halast
            exact ⟨a, hha, haq.tail hqh⟩
      let h' : F.CyclicActiveSector :=
        ⟨h, (F.cyclicActiveWeight_ne_zero_iff h).2 hhactive⟩
      exact hconnected.isSStronglyConnected_of_hom
        (PLift.up
          ((F.activeSectorTraceMatrix_pos_iff F.cyclicActiveWeight hpos q h').2 hqh))

/-- Adjacent normalized marginal equality makes the square of the
cyclic-active trace matrix strictly positive, provided every ordered pair of
cyclic-active sectors is visible in a retained block.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (retained-path visibility):** The theorem isolates the
coefficient-extraction argument and takes recurrent retained-path visibility
as an explicit hypothesis. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActiveSectorTraceMatrix_pow_two_pos_of_adjacent_marginals
    (F : PhysicalSectorFactorization K)
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (hreach : ∀ q h : F.CyclicActiveSector,
      Relation.ReflTransGen
        (fun a b : F.CyclicActiveSector ↦ F.neighboringOperator a b ≠ 0) q h)
    (hmarg : ∀ L, 0 < L →
      F.sectorCoordinateTensor.reducedBlockState (L + 2) L (by omega) =
        F.sectorCoordinateTensor.reducedBlockState (L + 1) L (by omega))
    (htrace : ∀ N, 2 ≤ N → ∃ z : ℝ, 0 < z ∧
      Matrix.trace (mpo F.sectorCoordinateTensor N) = (z : ℂ)) :
    ∀ q h, 0 < (F.cyclicActiveSectorTraceMatrix ^ 2) q h := by
  classical
  have hirr : Matrix.IsIrreducible F.cyclicActiveSectorTraceMatrix :=
    F.cyclicActiveSectorTraceMatrix_isIrreducible_of_reflTransGen hpos hreach
  apply hirr.pow_two_pos_of_pow_two_support_eq_pow_three_support
  intro q h
  obtain ⟨n, k, hk0, hklast, hkne⟩ :=
    F.exists_retainedTraceProduct_ne_zero_of_reflTransGen
      hpos q h (hreach h q)
  obtain ⟨z₂, hz₂, htrace₂⟩ := htrace (n + 3) (by omega)
  obtain ⟨z₁, hz₁, htrace₁⟩ := htrace (n + 2) (by omega)
  have hnorm :=
    F.normalized_trace_twoSuffix_eq_oneSuffix_of_reducedBlockState_eq
      (n + 1) (hmarg (n + 1) (by omega)) k
  rw [F.trace_twoSuffixSectorContraction_eq,
    F.trace_oneSuffixSectorContraction_eq, hklast, hk0,
    F.sum_sector_trace_three_eq_cyclicActive_pow_three hpos q h (hreach h q),
    F.sum_sector_trace_two_eq_cyclicActive_pow_two hpos q h (hreach h q)] at hnorm
  have htrace₂ne :
      Matrix.trace (mpo F.sectorCoordinateTensor (n + 3)) ≠ 0 := by
    rw [htrace₂]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hz₂)
  have htrace₁ne :
      Matrix.trace (mpo F.sectorCoordinateTensor (n + 2)) ≠ 0 := by
    rw [htrace₁]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hz₁)
  have hzero :
      ((F.cyclicActiveSectorTraceMatrix ^ 2) q h : ℂ) = 0 ↔
        ((F.cyclicActiveSectorTraceMatrix ^ 3) q h : ℂ) = 0 := by
    constructor
    · intro hsquare
      have hlhs :
          (Matrix.trace (mpo F.sectorCoordinateTensor (n + 3)))⁻¹ *
              (F.retainedTraceProduct k *
                ((F.cyclicActiveSectorTraceMatrix ^ 3) q h : ℂ)) = 0 := by
        rw [hnorm, hsquare, mul_zero, mul_zero]
      have hproduct :
          F.retainedTraceProduct k *
              ((F.cyclicActiveSectorTraceMatrix ^ 3) q h : ℂ) = 0 :=
        (mul_eq_zero.mp hlhs).resolve_left (inv_ne_zero htrace₂ne)
      exact (mul_eq_zero.mp hproduct).resolve_left hkne
    · intro hcube
      have hrhs :
          (Matrix.trace (mpo F.sectorCoordinateTensor (n + 2)))⁻¹ *
              (F.retainedTraceProduct k *
                ((F.cyclicActiveSectorTraceMatrix ^ 2) q h : ℂ)) = 0 := by
        rw [← hnorm, hcube, mul_zero, mul_zero]
      have hproduct :
          F.retainedTraceProduct k *
              ((F.cyclicActiveSectorTraceMatrix ^ 2) q h : ℂ) = 0 :=
        (mul_eq_zero.mp hrhs).resolve_left (inv_ne_zero htrace₁ne)
      exact (mul_eq_zero.mp hproduct).resolve_left hkne
  have hsquareNonneg :=
    Matrix.pow_apply_nonneg hirr.nonneg 2 q h
  have hcubeNonneg :=
    Matrix.pow_apply_nonneg hirr.nonneg 3 q h
  constructor
  · intro hsquare
    have hsquareNe :
        ((F.cyclicActiveSectorTraceMatrix ^ 2) q h : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hsquare)
    have hcubeNe :
        ((F.cyclicActiveSectorTraceMatrix ^ 3) q h : ℂ) ≠ 0 :=
      mt hzero.mpr hsquareNe
    exact lt_of_le_of_ne hcubeNonneg
      (Ne.symm (Complex.ofReal_ne_zero.mp hcubeNe))
  · intro hcube
    have hcubeNe :
        ((F.cyclicActiveSectorTraceMatrix ^ 3) q h : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hcube)
    have hsquareNe :
        ((F.cyclicActiveSectorTraceMatrix ^ 2) q h : ℂ) ≠ 0 :=
      mt hzero.mp hcubeNe
    exact lt_of_le_of_ne hsquareNonneg
      (Ne.symm (Complex.ofReal_ne_zero.mp hsquareNe))

/-- Adjacent normalized marginal equality determines a common positive
normalization for which the square and cube of the cyclic-active trace matrix
coincide.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (coefficient extraction):** Recurrent visibility and
positivity are stated explicitly. The theorem proves the square--cube
identity, but does not include the later rank-one reconstruction. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem exists_normalized_cyclicActiveSectorTraceMatrix_pow_two_eq_pow_three_of_adjacent_marginals
    (F : PhysicalSectorFactorization K)
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef)
    (hreach : ∀ q h : F.CyclicActiveSector,
      Relation.ReflTransGen
        (fun a b : F.CyclicActiveSector ↦ F.neighboringOperator a b ≠ 0) q h)
    (hmarg : ∀ L, 0 < L →
      F.sectorCoordinateTensor.reducedBlockState (L + 2) L (by omega) =
        F.sectorCoordinateTensor.reducedBlockState (L + 1) L (by omega))
    (htrace : ∀ N, 2 ≤ N → ∃ z : ℝ, 0 < z ∧
      Matrix.trace (mpo F.sectorCoordinateTensor N) = (z : ℂ)) :
    ∃ lam : ℝ, 0 < lam ∧
      (lam⁻¹ • F.cyclicActiveSectorTraceMatrix) ^ 2 =
        (lam⁻¹ • F.cyclicActiveSectorTraceMatrix) ^ 3 := by
  classical
  let T := F.cyclicActiveSectorTraceMatrix
  have hirr : Matrix.IsIrreducible F.cyclicActiveSectorTraceMatrix :=
    F.cyclicActiveSectorTraceMatrix_isIrreducible_of_reflTransGen hpos hreach
  have hTtwo : ∀ q h, 0 < (T ^ 2) q h :=
    F.cyclicActiveSectorTraceMatrix_pow_two_pos_of_adjacent_marginals
      hpos hreach hmarg htrace
  obtain ⟨z₅, hz₅, htrace₅⟩ := htrace 5 (by omega)
  obtain ⟨z₄, hz₄, htrace₄⟩ := htrace 4 (by omega)
  let lam := z₅ / z₄
  have hlam : 0 < lam := div_pos hz₅ hz₄
  refine ⟨lam, hlam, ?_⟩
  have hscale : T ^ 3 = lam • T ^ 2 := by
    ext q h
    have hTtwohq := hTtwo h q
    rw [pow_two, Matrix.mul_apply] at hTtwohq
    obtain ⟨r, -, hprod⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun r _ ↦
        mul_nonneg (hirr.nonneg h r) (hirr.nonneg r q))).1 hTtwohq
    have hhr : 0 < T h r :=
      pos_of_mul_pos_left hprod (hirr.nonneg r q)
    have hrq : 0 < T r q :=
      pos_of_mul_pos_right hprod (hirr.nonneg h r)
    let k : Fin 3 → Fin F.sectorCount := ![h.1, r.1, q.1]
    have hk0 : k 0 = h := by simp [k]
    have hklast : k (Fin.last 2) = q := by simp [k]
    have hkne : F.retainedTraceProduct k ≠ 0 := by
      rw [retainedTraceProduct]
      have htracehr :
          Matrix.trace (F.neighboringOperator h r) ≠ 0 := by
        rw [F.neighboringOperator_trace_eq_cyclicActiveSectorTraceMatrix hpos]
        exact Complex.ofReal_ne_zero.mpr (ne_of_gt hhr)
      have htracerq :
          Matrix.trace (F.neighboringOperator r q) ≠ 0 := by
        rw [F.neighboringOperator_trace_eq_cyclicActiveSectorTraceMatrix hpos]
        exact Complex.ofReal_ne_zero.mpr (ne_of_gt hrq)
      simp only [Fin.prod_univ_two]
      dsimp [k]
      change Matrix.trace (F.neighboringOperator h r) *
        Matrix.trace (F.neighboringOperator r q) ≠ 0
      exact mul_ne_zero htracehr htracerq
    have hnorm :=
      F.normalized_trace_twoSuffix_eq_oneSuffix_of_reducedBlockState_eq
        3 (hmarg 3 (by omega)) k
    rw [F.trace_twoSuffixSectorContraction_eq,
      F.trace_oneSuffixSectorContraction_eq, hklast, hk0,
      F.sum_sector_trace_three_eq_cyclicActive_pow_three hpos q h (hreach h q),
      F.sum_sector_trace_two_eq_cyclicActive_pow_two hpos q h (hreach h q),
      htrace₅, htrace₄] at hnorm
    have hnorm' := hnorm
    field_simp at hnorm'
    have hnormReal :
        (T ^ 3) q h * z₄ = z₅ * (T ^ 2) q h := by
      exact_mod_cast hnorm'
    have hcancel :
        ((T ^ 3) q h : ℂ) = ((lam • T ^ 2) q h : ℝ) := by
      change ((T ^ 3) q h : ℂ) = ((lam * (T ^ 2) q h : ℝ) : ℂ)
      norm_cast
      dsimp [lam]
      rw [div_mul_eq_mul_div]
      exact (eq_div_iff (ne_of_gt hz₄)).2 hnormReal
    exact_mod_cast hcancel
  rw [smul_pow, smul_pow, hscale, smul_smul]
  congr 1
  field_simp

end MPOTensor.PhysicalSectorFactorization

namespace MPOTensor.EtaLocalStructureData

variable {d D : ℕ} {K : MPOTensor d D}

/-- At every realized chain length, the selected fixed-product tensor and
the source tensor in the selected physical coordinates have the same
normalized reduced states.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1597--1613. -/
theorem selectedFixedProduct_reducedBlockState_eq_changePhysicalBasis
    (data : EtaLocalStructureData K)
    (N L : ℕ) (hN : 2 ≤ N) (hL : L ≤ N) :
    let F :=
      data.bondData.fixedProductTensorDataPhysicalSectorFactorization
    F.sectorCoordinateTensor.reducedBlockState N L hL =
      (PhysicalSectorFactorization.changePhysicalBasis
        F.physicalCoordinateMatrix K).reducedBlockState N L hL := by
  let F :=
    data.bondData.fixedProductTensorDataPhysicalSectorFactorization
  let M :=
    PhysicalSectorFactorization.changePhysicalBasis
      F.physicalCoordinateMatrix K
  obtain ⟨c, hc, hclosed⟩ :=
    data.exists_positive_scalar_mpo_changePhysicalBasis_eq_smul_selected N hN
  exact (PhysicalSectorFactorization.reducedBlockState_eq_of_mpo_eq_smul
    M F.sectorCoordinateTensor N L hL (c : ℂ)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hc)) hclosed).symm

private theorem selectedFixedProduct_reducedBlockState_eq_of_source_eq
    (data : EtaLocalStructureData K)
    (N₁ N₂ L : ℕ) (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂)
    (hL₁ : L ≤ N₁) (hL₂ : L ≤ N₂)
    (hsource :
      K.reducedBlockState N₁ L hL₁ =
        K.reducedBlockState N₂ L hL₂) :
    let F :=
      data.bondData.fixedProductTensorDataPhysicalSectorFactorization
    F.sectorCoordinateTensor.reducedBlockState N₁ L hL₁ =
      F.sectorCoordinateTensor.reducedBlockState N₂ L hL₂ := by
  let F :=
    data.bondData.fixedProductTensorDataPhysicalSectorFactorization
  let U := F.physicalCoordinateMatrix
  let M := PhysicalSectorFactorization.changePhysicalBasis U K
  calc
    F.sectorCoordinateTensor.reducedBlockState N₁ L hL₁ =
        M.reducedBlockState N₁ L hL₁ :=
      data.selectedFixedProduct_reducedBlockState_eq_changePhysicalBasis
        N₁ L hN₁ hL₁
    _ = singleKrausMap (sitewisePhysicalMatrix U L)
        (K.reducedBlockState N₁ L hL₁) :=
      reducedBlockState_changePhysicalBasis_of_isometry
        U F.physicalCoordinateMatrix_isometry K N₁ L hL₁
    _ = singleKrausMap (sitewisePhysicalMatrix U L)
        (K.reducedBlockState N₂ L hL₂) := by rw [hsource]
    _ = M.reducedBlockState N₂ L hL₂ := by
      symm
      exact reducedBlockState_changePhysicalBasis_of_isometry
        U F.physicalCoordinateMatrix_isometry K N₂ L hL₂
    _ = F.sectorCoordinateTensor.reducedBlockState N₂ L hL₂ :=
      (data.selectedFixedProduct_reducedBlockState_eq_changePhysicalBasis
        N₂ L hN₂ hL₂).symm

/-- Source zero correlation length transports adjacent normalized marginal
stability to the selected fixed-product tensor in its physical-sector
coordinates.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1603--1613. -/
theorem selectedFixedProduct_reducedBlockState_succ_succ_eq_succ_of_isSourceZCL
    (data : EtaLocalStructureData K) (hZCL : K.IsSourceZCL)
    (L : ℕ) (hL : 0 < L) :
    let F :=
      data.bondData.fixedProductTensorDataPhysicalSectorFactorization
    F.sectorCoordinateTensor.reducedBlockState (L + 2) L (by omega) =
      F.sectorCoordinateTensor.reducedBlockState (L + 1) L (by omega) := by
  apply data.selectedFixedProduct_reducedBlockState_eq_of_source_eq
      (hN₁ := by omega) (hN₂ := by omega)
  exact K.reducedBlockState_succ_succ_eq_succ_of_isSourceZCL hZCL L

/-- Source zero correlation length transports the three-suffix/one-suffix
normalized marginal identity to the selected fixed-product tensor.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1613.

**Scope restriction (cyclic-active restriction):** This is the additional marginal
replacement used to expose the two-step cyclic-active coefficient. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem selectedFixedProduct_reducedBlockState_add_three_eq_succ_of_isSourceZCL
    (data : EtaLocalStructureData K) (hZCL : K.IsSourceZCL)
    (L : ℕ) (hL : 0 < L) :
    let F :=
      data.bondData.fixedProductTensorDataPhysicalSectorFactorization
    F.sectorCoordinateTensor.reducedBlockState (L + 3) L (by omega) =
      F.sectorCoordinateTensor.reducedBlockState (L + 1) L (by omega) := by
  apply data.selectedFixedProduct_reducedBlockState_eq_of_source_eq
      (hN₁ := by omega) (hN₂ := by omega)
  exact K.reducedBlockState_add_three_eq_succ_of_isSourceZCL hZCL L

/-- Every selected fixed-product periodic operator of length at least two has
a strictly positive real trace under source zero correlation length.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1597--1613. -/
theorem exists_pos_trace_mpo_selectedFixedProduct_of_isSourceZCL
    (data : EtaLocalStructureData K) (hZCL : K.IsSourceZCL)
    (N : ℕ) (hN : 2 ≤ N) :
    let F :=
      data.bondData.fixedProductTensorDataPhysicalSectorFactorization
    ∃ z : ℝ, 0 < z ∧
      Matrix.trace (mpo F.sectorCoordinateTensor N) = (z : ℂ) := by
  let F :=
    data.bondData.fixedProductTensorDataPhysicalSectorFactorization
  let U := F.physicalCoordinateMatrix
  let M := PhysicalSectorFactorization.changePhysicalBasis U K
  letI : NeZero N := ⟨by omega⟩
  have hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef :=
    data.bondData.fixedProductTensorDataPhysicalSectorFactorization_neighboring_pos
  obtain ⟨c, _, hclosed⟩ :=
    data.exists_positive_scalar_mpo_changePhysicalBasis_eq_smul_selected N hN
  have hsourceTraceNe : Matrix.trace (mpo K N) ≠ 0 :=
    trace_mpo_ne_zero_of_isSourceZCL K hZCL (by omega)
  have hchangeTraceNe : Matrix.trace (mpo M N) ≠ 0 := by
    rw [trace_mpo_changePhysicalBasis_of_isometry
      U F.physicalCoordinateMatrix_isometry K N]
    exact hsourceTraceNe
  have hclosedTrace := congrArg Matrix.trace hclosed
  rw [Matrix.trace_smul] at hclosedTrace
  have hselectedTraceNe :
      Matrix.trace (mpo F.sectorCoordinateTensor N) ≠ 0 := by
    intro hzero
    apply hchangeTraceNe
    rw [hclosedTrace, hzero, smul_eq_mul, mul_zero]
  have hselectedPos :
      0 < Matrix.trace (mpo F.sectorCoordinateTensor N) :=
    (F.mpo_sectorCoordinateTensor_posSemidef hpos).trace_pos_of_ne_zero
      (fun hzero ↦ hselectedTraceNe (by rw [hzero, Matrix.trace_zero]))
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hselectedPos
  refine ⟨(Matrix.trace (mpo F.sectorCoordinateTensor N)).re, hre, ?_⟩
  apply Complex.ext
  · rfl
  · simpa using him.symm

/-- For the selected fixed-product realization of an eta-local source-ZCL
tensor, the cyclic-active trace matrix admits a positive normalization whose
square equals its cube.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1597--1619.

**Scope restriction (coefficient extraction):** This is the square--cube
coefficient identity preceding the rank-one conclusion of Proposition
`4to2`. It does not assume injectivity or source zero correlation length for
the selected tensor. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem exists_normalized_selectedFixedProduct_cyclicActiveSectorTraceMatrix_pow_two_eq_pow_three
    (hK : K.IsInjective) (data : EtaLocalStructureData K)
    (hZCL : K.IsSourceZCL) :
    let F :=
      data.bondData.fixedProductTensorDataPhysicalSectorFactorization
    ∃ lam : ℝ, 0 < lam ∧
      (lam⁻¹ • F.cyclicActiveSectorTraceMatrix) ^ 2 =
        (lam⁻¹ • F.cyclicActiveSectorTraceMatrix) ^ 3 := by
  classical
  let F :=
    data.bondData.fixedProductTensorDataPhysicalSectorFactorization
  have hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef :=
    data.bondData.fixedProductTensorDataPhysicalSectorFactorization_neighboring_pos
  have hreach : ∀ q h : F.CyclicActiveSector,
      Relation.ReflTransGen
        (fun a b : F.CyclicActiveSector ↦ F.neighboringOperator a b ≠ 0) q h := by
    intro q h
    exact data.selectedFixedProduct_cyclicActive_reflTransGen_neighboringOperator_ne_zero
      hK q h
  have hmarg : ∀ L, 0 < L →
      F.sectorCoordinateTensor.reducedBlockState (L + 2) L (by omega) =
        F.sectorCoordinateTensor.reducedBlockState (L + 1) L (by omega) := by
    intro L hL
    exact data.selectedFixedProduct_reducedBlockState_succ_succ_eq_succ_of_isSourceZCL
      hZCL L hL
  have htrace : ∀ N, 2 ≤ N → ∃ z : ℝ, 0 < z ∧
      Matrix.trace (mpo F.sectorCoordinateTensor N) = (z : ℂ) := by
    intro N hN
    exact data.exists_pos_trace_mpo_selectedFixedProduct_of_isSourceZCL hZCL N hN
  exact F.exists_normalized_cyclicActiveSectorTraceMatrix_pow_two_eq_pow_three_of_adjacent_marginals
    hpos hreach hmarg htrace

end MPOTensor.EtaLocalStructureData
