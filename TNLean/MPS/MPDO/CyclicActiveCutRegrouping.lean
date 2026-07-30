/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CyclicActiveCutStates

/-!
# Regrouping the cyclic-active fourth-region blocks

This file proves that separating a retained chain at one site transforms each
fourth-region block into the corresponding Kronecker product of left and right
path factors.

## Reference

* arXiv:1606.00608, Appendix C.2, Proposition 4to2, lines 1606--1617.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor.PhysicalSectorFactorization

universe u

variable {d D : ℕ} {K : MPOTensor d D}

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

private theorem neighboringOperator_entry_eq_of_heq
    (F : PhysicalSectorFactorization K)
    {k k' h h' : Fin F.sectorCount} (hk : k = k') (hh : h = h')
    {x y : F.NeighborIndex k h} {x' y' : F.NeighborIndex k' h'}
    (hx : x ≍ x') (hy : y ≍ y') :
    F.neighboringOperator k h x y =
      F.neighboringOperator k' h' x' y' := by
  subst k'
  subst h'
  cases hx
  cases hy
  rfl

private theorem cyclicActiveLeftBoundary_entry_eq_of_heq
    (F : PhysicalSectorFactorization K)
    (b : F.CyclicActiveSector → ℝ) {k h : F.CyclicActiveSector}
    (hkh : k = h) {x y : Fin (F.leftDim k)}
    {x' y' : Fin (F.leftDim h)} (hx : x ≍ x') (hy : y ≍ y') :
    F.cyclicActiveLeftBoundary b k x y =
      F.cyclicActiveLeftBoundary b h x' y' := by
  subst h
  cases hx
  cases hy
  rfl

private theorem cyclicActiveRightBoundary_entry_eq_of_heq
    (F : PhysicalSectorFactorization K)
    (a : F.CyclicActiveSector → ℝ) {k h : F.CyclicActiveSector}
    (hkh : k = h) {x y : Fin (F.rightDim k)}
    {x' y' : Fin (F.rightDim h)} (hx : x ≍ x') (hy : y ≍ y') :
    F.cyclicActiveRightBoundary a k x y =
      F.cyclicActiveRightBoundary a h x' y' := by
  subst h
  cases hx
  cases hy
  rfl

private theorem neighborIndex_heq_of_components
    (F : PhysicalSectorFactorization K)
    {k k' h h' : Fin F.sectorCount} (hk : k = k') (hh : h = h')
    {x₁ : Fin (F.rightDim k)} {x₂ : Fin (F.leftDim h)}
    {y₁ : Fin (F.rightDim k')} {y₂ : Fin (F.leftDim h')}
    (h₁ : x₁ ≍ y₁) (h₂ : x₂ ≍ y₂) :
    (x₁, x₂) ≍ (y₁, y₂) := by
  subst k'
  subst h'
  cases h₁
  cases h₂
  rfl

private theorem dependent_apply_heq {ι : Type} {α : ι → Type}
    (f : (i : ι) → α i) {i j : ι} (h : i = j) : f i ≍ f j := by
  subst j
  rfl

private theorem retainedLeftNeighboringEntry_eq
    (F : PhysicalSectorFactorization K) {A C : ℕ}
    (j : Fin F.sectorCount)
    (k : Fin ((A + 1) + C + 1) → Fin F.sectorCount)
    (kL : Fin (A + 1) → Fin F.sectorCount)
    (z z' : F.RetainedOpenEdgeIndex (n := (A + 1) + C) k)
    (zL zL' : F.LeftOpenEdgeIndex (F.leftSectorWord j kL))
    (hkLeft : ∀ i : Fin (A + 1), k ⟨i, by omega⟩ = kL i)
    (hkMiddle : k ⟨A + 1, by omega⟩ = j)
    (hu : ∀ i : Fin (A + 1),
      (F.retainedOpenEdgeEquiv k).symm z ⟨i, by omega⟩ ≍
        ((F.leftFiberOpenEdgeEquiv (F.leftSectorWord j kL)).symm zL).1 i)
    (hu' : ∀ i : Fin (A + 1),
      (F.retainedOpenEdgeEquiv k).symm z' ⟨i, by omega⟩ ≍
        ((F.leftFiberOpenEdgeEquiv (F.leftSectorWord j kL)).symm zL').1 i)
    (huM : ((F.retainedOpenEdgeEquiv k).symm z ⟨A + 1, by omega⟩).1 ≍
      ((F.leftFiberOpenEdgeEquiv (F.leftSectorWord j kL)).symm zL).2)
    (huM' : ((F.retainedOpenEdgeEquiv k).symm z' ⟨A + 1, by omega⟩).1 ≍
      ((F.leftFiberOpenEdgeEquiv (F.leftSectorWord j kL)).symm zL').2)
    (i : Fin (A + 1)) :
    let e := Fin.castAdd C i
    F.neighboringOperator
        (k ((Fin.last (A + 1 + C)).succAbove e))
        (k ((Fin.last (A + 1 + C)).succAbove e + 1))
        (z.1 e) (z'.1 e) =
      F.neighboringOperator
        (F.leftSectorWord j kL i.castSucc)
        (F.leftSectorWord j kL i.succ)
        (zL.2 i) (zL'.2 i) := by
  classical
  refine Fin.lastCases ?_ (fun p ↦ ?_) i
  · let e := Fin.castAdd C (Fin.last A)
    let v := (F.retainedOpenEdgeEquiv k).symm z
    let v' := (F.retainedOpenEdgeEquiv k).symm z'
    have he0 : (Fin.last (A + 1 + C)).succAbove e =
        ⟨Fin.last A, by omega⟩ := by
      ext
      simp [e]
    have he1 : (Fin.last (A + 1 + C)).succAbove e + 1 =
        ⟨A + 1, by omega⟩ := by
      ext
      simp [e]
    have hq : k ((Fin.last (A + 1 + C)).succAbove e) =
        F.leftSectorWord j kL (Fin.last A).castSucc := by
      rw [he0, hkLeft]
      simp [leftSectorWord]
    have hh : k ((Fin.last (A + 1 + C)).succAbove e + 1) =
        F.leftSectorWord j kL (Fin.last A).succ := by
      rw [he1, hkMiddle]
      simp [leftSectorWord]
    have hg := F.retainedOpenEdgeEquiv_symm_internal_edge k z e
    have hg' := F.retainedOpenEdgeEquiv_symm_internal_edge k z' e
    have huM_v : (v ⟨A + 1, by omega⟩).1 ≍
        ((F.leftFiberOpenEdgeEquiv (F.leftSectorWord j kL)).symm zL).2 := huM
    have huM_v' : (v' ⟨A + 1, by omega⟩).1 ≍
        ((F.leftFiberOpenEdgeEquiv (F.leftSectorWord j kL)).symm zL').2 := huM'
    apply neighboringOperator_entry_eq_of_heq F hq hh
    · apply neighborIndex_heq_of_components F hq hh
      · refine (heq_of_eq (congrArg Prod.fst hg).symm).trans ?_
        exact (sectorIndex_snd_heq_of_heq F hq
          ((dependent_apply_heq v he0).trans (hu (Fin.last A)))).trans
            (heq_of_eq (F.leftFiberOpenEdgeEquiv_symm_edge_fst
              (F.leftSectorWord j kL) zL (Fin.last A)))
      · refine (heq_of_eq (congrArg Prod.snd hg).symm).trans ?_
        exact ((sectorIndex_fst_heq_of_heq F (congrArg k he1)
          (dependent_apply_heq v he1)).trans huM_v).trans (heq_of_eq
            (F.leftFiberOpenEdgeEquiv_symm_edge_snd_last
              (F.leftSectorWord j kL) zL))
    · apply neighborIndex_heq_of_components F hq hh
      · refine (heq_of_eq (congrArg Prod.fst hg').symm).trans ?_
        exact (sectorIndex_snd_heq_of_heq F hq
          ((dependent_apply_heq v' he0).trans (hu' (Fin.last A)))).trans
            (heq_of_eq (F.leftFiberOpenEdgeEquiv_symm_edge_fst
              (F.leftSectorWord j kL) zL' (Fin.last A)))
      · refine (heq_of_eq (congrArg Prod.snd hg').symm).trans ?_
        exact ((sectorIndex_fst_heq_of_heq F (congrArg k he1)
          (dependent_apply_heq v' he1)).trans huM_v').trans (heq_of_eq
            (F.leftFiberOpenEdgeEquiv_symm_edge_snd_last
              (F.leftSectorWord j kL) zL'))
  · let e := Fin.castAdd C p.castSucc
    let v := (F.retainedOpenEdgeEquiv k).symm z
    let v' := (F.retainedOpenEdgeEquiv k).symm z'
    have he0 : (Fin.last (A + 1 + C)).succAbove e =
        ⟨p.castSucc, by omega⟩ := by
      ext
      simp [e]
    have he1 : (Fin.last (A + 1 + C)).succAbove e + 1 =
        ⟨p.succ, by omega⟩ := by
      ext
      simp [e]
    have hq : k ((Fin.last (A + 1 + C)).succAbove e) =
        F.leftSectorWord j kL p.castSucc.castSucc := by
      rw [he0, hkLeft]
      simp [leftSectorWord]
    have hh : k ((Fin.last (A + 1 + C)).succAbove e + 1) =
        F.leftSectorWord j kL p.castSucc.succ := by
      rw [he1, hkLeft]
      change kL p.succ = Fin.lastCases j kL p.castSucc.succ
      symm
      exact Fin.lastCases_castSucc p.succ
    have hg := F.retainedOpenEdgeEquiv_symm_internal_edge k z e
    have hg' := F.retainedOpenEdgeEquiv_symm_internal_edge k z' e
    apply neighboringOperator_entry_eq_of_heq F hq hh
    · apply neighborIndex_heq_of_components F hq hh
      · refine (heq_of_eq (congrArg Prod.fst hg).symm).trans ?_
        exact (sectorIndex_snd_heq_of_heq F hq
          ((dependent_apply_heq v he0).trans (hu p.castSucc))).trans
            (heq_of_eq (F.leftFiberOpenEdgeEquiv_symm_edge_fst
              (F.leftSectorWord j kL) zL p.castSucc))
      · refine (heq_of_eq (congrArg Prod.snd hg).symm).trans ?_
        exact (sectorIndex_fst_heq_of_heq F hh
          ((dependent_apply_heq v he1).trans (hu p.succ))).trans (heq_of_eq
            (F.leftFiberOpenEdgeEquiv_symm_edge_snd_castSucc
              (F.leftSectorWord j kL) zL p))
    · apply neighborIndex_heq_of_components F hq hh
      · refine (heq_of_eq (congrArg Prod.fst hg').symm).trans ?_
        exact (sectorIndex_snd_heq_of_heq F hq
          ((dependent_apply_heq v' he0).trans (hu' p.castSucc))).trans
            (heq_of_eq (F.leftFiberOpenEdgeEquiv_symm_edge_fst
              (F.leftSectorWord j kL) zL' p.castSucc))
      · refine (heq_of_eq (congrArg Prod.snd hg').symm).trans ?_
        exact (sectorIndex_fst_heq_of_heq F hh
          ((dependent_apply_heq v' he1).trans (hu' p.succ))).trans (heq_of_eq
            (F.leftFiberOpenEdgeEquiv_symm_edge_snd_castSucc
              (F.leftSectorWord j kL) zL' p))

private theorem retainedRightNeighboringEntry_eq
    (F : PhysicalSectorFactorization K) {A C : ℕ}
    (j : Fin F.sectorCount)
    (k : Fin (A + (C + 1) + 1) → Fin F.sectorCount)
    (kR : Fin (C + 1) → Fin F.sectorCount)
    (z z' : F.RetainedOpenEdgeIndex (n := A + (C + 1)) k)
    (zR zR' : F.RightOpenEdgeIndex (F.rightSectorWord j kR))
    (hkMiddle : k ⟨A, by omega⟩ = j)
    (hkRight : ∀ i : Fin (C + 1), k ⟨A + 1 + i, by omega⟩ = kR i)
    (hu : ∀ i : Fin (C + 1),
      (F.retainedOpenEdgeEquiv k).symm z ⟨A + 1 + i, by omega⟩ ≍
        ((F.rightFiberOpenEdgeEquiv (F.rightSectorWord j kR)).symm zR).2 i)
    (hu' : ∀ i : Fin (C + 1),
      (F.retainedOpenEdgeEquiv k).symm z' ⟨A + 1 + i, by omega⟩ ≍
        ((F.rightFiberOpenEdgeEquiv (F.rightSectorWord j kR)).symm zR').2 i)
    (huM : ((F.retainedOpenEdgeEquiv k).symm z ⟨A, by omega⟩).2 ≍
      ((F.rightFiberOpenEdgeEquiv (F.rightSectorWord j kR)).symm zR).1)
    (huM' : ((F.retainedOpenEdgeEquiv k).symm z' ⟨A, by omega⟩).2 ≍
      ((F.rightFiberOpenEdgeEquiv (F.rightSectorWord j kR)).symm zR').1)
    (i : Fin (C + 1)) :
    let e := Fin.natAdd A i
    F.neighboringOperator
        (k ((Fin.last (A + (C + 1))).succAbove e))
        (k ((Fin.last (A + (C + 1))).succAbove e + 1))
        (z.1 e) (z'.1 e) =
      F.neighboringOperator
        (F.rightSectorWord j kR i.castSucc)
        (F.rightSectorWord j kR i.succ)
        (zR.1 i) (zR'.1 i) := by
  classical
  refine Fin.cases ?_ (fun p ↦ ?_) i
  · let e := Fin.natAdd A (0 : Fin (C + 1))
    let v := (F.retainedOpenEdgeEquiv k).symm z
    let v' := (F.retainedOpenEdgeEquiv k).symm z'
    have he0 : (Fin.last (A + (C + 1))).succAbove e = ⟨A, by omega⟩ := by
      ext
      simp [e]
    have he1 : (Fin.last (A + (C + 1))).succAbove e + 1 =
        ⟨A + 1, by omega⟩ := by
      rw [he0]
      apply Fin.ext
      change (A + (1 % (A + (C + 1) + 1))) % (A + (C + 1) + 1) = A + 1
      rw [Nat.mod_eq_of_lt (by omega : 1 < A + (C + 1) + 1)]
      rw [Nat.mod_eq_of_lt (by omega : A + 1 < A + (C + 1) + 1)]
    have hq : k ((Fin.last (A + (C + 1))).succAbove e) =
        F.rightSectorWord j kR (0 : Fin (C + 1)).castSucc := by
      rw [he0, hkMiddle]
      simp [rightSectorWord]
    have hh : k ((Fin.last (A + (C + 1))).succAbove e + 1) =
        F.rightSectorWord j kR (0 : Fin (C + 1)).succ := by
      rw [he1]
      calc
        k ⟨A + 1, by omega⟩ = k ⟨A + 1 + (0 : Fin (C + 1)), by omega⟩ := by
          congr 1
        _ = kR 0 := hkRight 0
        _ = F.rightSectorWord j kR (0 : Fin (C + 1)).succ := by
          change kR (0 : Fin (C + 1)) =
            Fin.cases j kR (Fin.succ (0 : Fin (C + 1)))
          exact (@Fin.cases_succ (C + 1) (fun _ ↦ Fin F.sectorCount)
            j kR 0).symm
    have hg := F.retainedOpenEdgeEquiv_symm_internal_edge k z e
    have hg' := F.retainedOpenEdgeEquiv_symm_internal_edge k z' e
    have huM_v : (v ⟨A, by omega⟩).2 ≍
        ((F.rightFiberOpenEdgeEquiv (F.rightSectorWord j kR)).symm zR).1 := huM
    have huM_v' : (v' ⟨A, by omega⟩).2 ≍
        ((F.rightFiberOpenEdgeEquiv (F.rightSectorWord j kR)).symm zR').1 := huM'
    apply neighboringOperator_entry_eq_of_heq F hq hh
    · apply neighborIndex_heq_of_components F hq hh
      · refine (heq_of_eq (congrArg Prod.fst hg).symm).trans ?_
        exact ((sectorIndex_snd_heq_of_heq F (congrArg k he0)
          (dependent_apply_heq v he0)).trans huM_v).trans (heq_of_eq
            (F.rightFiberOpenEdgeEquiv_symm_edge_fst_zero
              (F.rightSectorWord j kR) zR))
      · refine (heq_of_eq (congrArg Prod.snd hg).symm).trans ?_
        exact (sectorIndex_fst_heq_of_heq F hh
          ((dependent_apply_heq v he1).trans (hu 0))).trans
            (heq_of_eq (F.rightFiberOpenEdgeEquiv_symm_edge_snd
              (F.rightSectorWord j kR) zR 0))
    · apply neighborIndex_heq_of_components F hq hh
      · refine (heq_of_eq (congrArg Prod.fst hg').symm).trans ?_
        exact ((sectorIndex_snd_heq_of_heq F (congrArg k he0)
          (dependent_apply_heq v' he0)).trans huM_v').trans (heq_of_eq
            (F.rightFiberOpenEdgeEquiv_symm_edge_fst_zero
              (F.rightSectorWord j kR) zR'))
      · refine (heq_of_eq (congrArg Prod.snd hg').symm).trans ?_
        exact (sectorIndex_fst_heq_of_heq F hh
          ((dependent_apply_heq v' he1).trans (hu' 0))).trans
            (heq_of_eq (F.rightFiberOpenEdgeEquiv_symm_edge_snd
              (F.rightSectorWord j kR) zR' 0))
  · let e := Fin.natAdd A p.succ
    let v := (F.retainedOpenEdgeEquiv k).symm z
    let v' := (F.retainedOpenEdgeEquiv k).symm z'
    have he0 : (Fin.last (A + (C + 1))).succAbove e =
        ⟨A + 1 + p, by omega⟩ := by
      ext
      simp [e]
      omega
    have he1 : (Fin.last (A + (C + 1))).succAbove e + 1 =
        ⟨A + 1 + p.succ, by omega⟩ := by
      rw [he0]
      apply Fin.ext
      change (A + 1 + p.val + (1 % (A + (C + 1) + 1))) %
          (A + (C + 1) + 1) = A + 1 + (p.val + 1)
      rw [Nat.mod_eq_of_lt (by omega : 1 < A + (C + 1) + 1)]
      rw [Nat.mod_eq_of_lt (by omega :
        A + 1 + p.val + 1 < A + (C + 1) + 1)]
      omega
    have hq : k ((Fin.last (A + (C + 1))).succAbove e) =
        F.rightSectorWord j kR p.succ.castSucc := by
      rw [he0]
      calc
        k ⟨A + 1 + p, by omega⟩ =
            k ⟨A + 1 + (p.castSucc : Fin (C + 1)), by omega⟩ := by
          congr 1
        _ = kR p.castSucc := hkRight p.castSucc
        _ = F.rightSectorWord j kR p.succ.castSucc := by
          rw [show p.succ.castSucc = p.castSucc.succ by rfl]
          change kR p.castSucc = Fin.cases j kR (Fin.succ p.castSucc)
          exact (@Fin.cases_succ (C + 1) (fun _ ↦ Fin F.sectorCount)
            j kR p.castSucc).symm
    have hh : k ((Fin.last (A + (C + 1))).succAbove e + 1) =
        F.rightSectorWord j kR p.succ.succ := by
      rw [he1]
      calc
        k ⟨A + 1 + p.succ, by omega⟩ =
            k ⟨A + 1 + (p.succ : Fin (C + 1)), by omega⟩ := by
          congr 1
        _ = kR p.succ := hkRight p.succ
        _ = F.rightSectorWord j kR p.succ.succ := by
          simp only [rightSectorWord, Fin.cases_succ]
    have hg := F.retainedOpenEdgeEquiv_symm_internal_edge k z e
    have hg' := F.retainedOpenEdgeEquiv_symm_internal_edge k z' e
    apply neighboringOperator_entry_eq_of_heq F hq hh
    · apply neighborIndex_heq_of_components F hq hh
      · refine (heq_of_eq (congrArg Prod.fst hg).symm).trans ?_
        exact (sectorIndex_snd_heq_of_heq F hq
          ((dependent_apply_heq v he0).trans (hu p.castSucc))).trans (heq_of_eq
            (F.rightFiberOpenEdgeEquiv_symm_edge_fst_succ
              (F.rightSectorWord j kR) zR p))
      · refine (heq_of_eq (congrArg Prod.snd hg).symm).trans ?_
        exact (sectorIndex_fst_heq_of_heq F hh
          ((dependent_apply_heq v he1).trans (hu p.succ))).trans
            (heq_of_eq (F.rightFiberOpenEdgeEquiv_symm_edge_snd
              (F.rightSectorWord j kR) zR p.succ))
    · apply neighborIndex_heq_of_components F hq hh
      · refine (heq_of_eq (congrArg Prod.fst hg').symm).trans ?_
        exact (sectorIndex_snd_heq_of_heq F hq
          ((dependent_apply_heq v' he0).trans (hu' p.castSucc))).trans (heq_of_eq
            (F.rightFiberOpenEdgeEquiv_symm_edge_fst_succ
              (F.rightSectorWord j kR) zR' p))
      · refine (heq_of_eq (congrArg Prod.snd hg').symm).trans ?_
        exact (sectorIndex_fst_heq_of_heq F hh
          ((dependent_apply_heq v' he1).trans (hu' p.succ))).trans
            (heq_of_eq (F.rightFiberOpenEdgeEquiv_symm_edge_snd
              (F.rightSectorWord j kR) zR' p.succ))


/-- Separating a retained chain at one physical site turns the complete
fourth-region block into a direct sum of left and right path factors.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Scope restriction (cyclic-active restriction):** The blocks are those of the
restricted two-step cyclic-active coefficient. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem reindex_cyclicActiveFourthRegionBlock_eq_cutRaw
    (F : PhysicalSectorFactorization K) (A C : ℕ)
    (lam : ℝ) (a b : F.CyclicActiveSector → ℝ) :
    Matrix.reindex (F.retainedCutEquiv A C) (F.retainedCutEquiv A C)
        (Matrix.blockDiagonal' fun k : Fin (A + C + 1) → Fin F.sectorCount ↦
          F.cyclicActiveFourthRegionBlock (n := A + C) lam a b k) =
      Matrix.blockDiagonal' fun j : Fin F.sectorCount ↦
        F.cyclicActiveLeftCutRaw A lam b j ⊗ₖ
          F.cyclicActiveRightCutRaw C a j := by
  classical
  ext x y
  obtain ⟨j, l, r⟩ := x
  obtain ⟨j', l', r'⟩ := y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  by_cases hj : j = j'
  · subst j'
    simp only [Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply]
    simp only [cyclicActiveLeftCutRaw, cyclicActiveRightCutRaw,
      Matrix.reindex_apply, Matrix.submatrix_apply]
    simp only [Equiv.symm_symm]
    generalize hg : (F.retainedCutEquiv A C).symm ⟨j, (l, r)⟩ = g
    generalize hg' : (F.retainedCutEquiv A C).symm ⟨j, (l', r')⟩ = g'
    generalize hsL : F.leftSectorOpenEdgeEquiv A j l = sL
    generalize hsL' : F.leftSectorOpenEdgeEquiv A j l' = sL'
    generalize hsR : F.rightSectorOpenEdgeEquiv C j r = sR
    generalize hsR' : F.rightSectorOpenEdgeEquiv C j r' = sR'
    obtain ⟨k, z⟩ := g
    obtain ⟨k', z'⟩ := g'
    obtain ⟨kL, zL⟩ := sL
    obtain ⟨kL', zL'⟩ := sL'
    obtain ⟨kR, zR⟩ := sR
    obtain ⟨kR', zR'⟩ := sR'
    by_cases hkL : kL = kL'
    · subst kL'
      by_cases hkR : kR = kR'
      · subst kR'
        have hword :
            ((F.retainedCutEquiv A C).symm ⟨j, (l, r)⟩).1 =
              ((F.retainedCutEquiv A C).symm ⟨j, (l', r')⟩).1 := by
          funext i
          rcases lt_trichotomy i.val A with hi | hi | hi
          · let iA : Fin A := ⟨i, hi⟩
            calc
              _ = kL iA := by
                rw [F.retainedCutEquiv_symm_left_sector A C j l r iA]
                simpa [hsL] using (congrFun
                  (F.leftSectorOpenEdgeEquiv_apply_fst A j l) iA).symm
              _ = _ := by
                rw [F.retainedCutEquiv_symm_left_sector A C j l' r' iA]
                simpa [hsL'] using congrFun
                  (F.leftSectorOpenEdgeEquiv_apply_fst A j l') iA
          · have hii : i = ⟨A, by omega⟩ := Fin.ext hi
            rw [hii]
            rw [F.retainedCutEquiv_symm_middle_sector A C j l r,
              F.retainedCutEquiv_symm_middle_sector A C j l' r']
          · let iC : Fin C := ⟨i.val - (A + 1), by omega⟩
            have hii : i = ⟨A + 1 + iC, by omega⟩ := by ext; simp [iC]; omega
            rw [hii]
            calc
              _ = kR iC := by
                rw [F.retainedCutEquiv_symm_right_sector A C j l r iC]
                simpa [hsR] using (congrFun
                  (F.rightSectorOpenEdgeEquiv_apply_fst C j r) iC).symm
              _ = _ := by
                rw [F.retainedCutEquiv_symm_right_sector A C j l' r' iC]
                simpa [hsR'] using congrFun
                  (F.rightSectorOpenEdgeEquiv_apply_fst C j r') iC
        have hkk : k = k' := by simpa [hg, hg'] using hword
        subst k'
        simp only [Matrix.blockDiagonal'_apply_eq]
        have hkLeft (i : Fin A) : k ⟨i, by omega⟩ = kL i := by
          have hglobal := F.retainedCutEquiv_symm_left_sector A C j l r i
          rw [hg] at hglobal
          have hlocal := congrFun
            (F.leftSectorOpenEdgeEquiv_apply_fst A j l) i
          rw [hsL] at hlocal
          exact hglobal.trans hlocal.symm
        have hkMiddle : k ⟨A, by omega⟩ = j := by
          simpa [hg] using F.retainedCutEquiv_symm_middle_sector A C j l r
        have hkRight (i : Fin C) : k ⟨A + 1 + i, by omega⟩ = kR i := by
          have hglobal := F.retainedCutEquiv_symm_right_sector A C j l r i
          rw [hg] at hglobal
          have hlocal := congrFun
            (F.rightSectorOpenEdgeEquiv_apply_fst C j r) i
          rw [hsR] at hlocal
          exact hglobal.trans hlocal.symm
        have hkActive : F.IsCyclicActiveRetainedWord k ↔
            F.IsCyclicActiveRetainedWord (F.leftSectorWord j kL) ∧
              F.IsCyclicActiveRetainedWord (F.rightSectorWord j kR) := by
          constructor
          · intro hk
            constructor
            · intro i
              refine Fin.lastCases ?_ (fun p ↦ ?_) i
              · simpa [leftSectorWord, hkMiddle] using hk ⟨A, by omega⟩
              · simpa [leftSectorWord, hkLeft p] using hk ⟨p, by omega⟩
            · intro i
              refine Fin.cases ?_ (fun p ↦ ?_) i
              · simpa [rightSectorWord, hkMiddle] using hk ⟨A, by omega⟩
              · simpa [rightSectorWord, hkRight p] using
                  hk ⟨A + 1 + p, by omega⟩
          · rintro ⟨hL, hR⟩ i
            rcases lt_trichotomy i.val A with hi | hi | hi
            · let iA : Fin A := ⟨i, hi⟩
              have hii : i = ⟨iA, by omega⟩ := by ext; rfl
              rw [hii, hkLeft iA]
              simpa [leftSectorWord] using hL iA.castSucc
            · have hii : i = ⟨A, by omega⟩ := Fin.ext hi
              rw [hii, hkMiddle]
              simpa [rightSectorWord] using hR 0
            · let iC : Fin C := ⟨i.val - (A + 1), by omega⟩
              have hii : i = ⟨A + 1 + iC, by omega⟩ := by ext; simp [iC]; omega
              rw [hii, hkRight iC]
              simpa [rightSectorWord] using hR iC.succ
        by_cases hL : F.IsCyclicActiveRetainedWord (F.leftSectorWord j kL)
        · by_cases hR : F.IsCyclicActiveRetainedWord (F.rightSectorWord j kR)
          · let v := (F.retainedOpenEdgeEquiv k).symm z
            let v' := (F.retainedOpenEdgeEquiv k).symm z'
            let wL := (F.leftFixedFiberOpenEdgeEquiv j kL).symm zL
            let wL' := (F.leftFixedFiberOpenEdgeEquiv j kL).symm zL'
            let wR := (F.rightFixedFiberOpenEdgeEquiv j kR).symm zR
            let wR' := (F.rightFixedFiberOpenEdgeEquiv j kR).symm zR'
            let uL := (F.leftFiberOpenEdgeEquiv
              (F.leftSectorWord j kL)).symm zL
            let uL' := (F.leftFiberOpenEdgeEquiv
              (F.leftSectorWord j kL)).symm zL'
            let uR := (F.rightFiberOpenEdgeEquiv
              (F.rightSectorWord j kR)).symm zR
            let uR' := (F.rightFiberOpenEdgeEquiv
              (F.rightSectorWord j kR)).symm zR'
            have hvL (i : Fin A) : v ⟨i, by omega⟩ ≍ wL.1 i := by
              have h := F.retainedCutEquiv_symm_left_fiber_heq A C j l r i
              rw [hg, hsL] at h
              exact h
            have hvL' (i : Fin A) : v' ⟨i, by omega⟩ ≍ wL'.1 i := by
              have h := F.retainedCutEquiv_symm_left_fiber_heq A C j l' r' i
              rw [hg', hsL'] at h
              exact h
            have hvR (i : Fin C) : v ⟨A + 1 + i, by omega⟩ ≍ wR.2 i := by
              have h := F.retainedCutEquiv_symm_right_fiber_heq A C j l r i
              rw [hg, hsR] at h
              exact h
            have hvR' (i : Fin C) : v' ⟨A + 1 + i, by omega⟩ ≍ wR'.2 i := by
              have h := F.retainedCutEquiv_symm_right_fiber_heq A C j l' r' i
              rw [hg', hsR'] at h
              exact h
            have hvM : v ⟨A, by omega⟩ ≍ (wL.2, wR.1) := by
              have hm := F.retainedCutEquiv_symm_middle_fiber_heq A C j l r
              have hl2 := F.leftSectorOpenEdgeEquiv_symm_last_eq A j l
              have hr1 := F.rightSectorOpenEdgeEquiv_symm_first_eq C j r
              dsimp only at hm hl2 hr1
              rw [hg] at hm
              rw [hsL] at hl2
              rw [hsR] at hr1
              simpa [v, wL, wR, hl2, hr1] using hm
            have hvM' : v' ⟨A, by omega⟩ ≍ (wL'.2, wR'.1) := by
              have hm := F.retainedCutEquiv_symm_middle_fiber_heq A C j l' r'
              have hl2 := F.leftSectorOpenEdgeEquiv_symm_last_eq A j l'
              have hr1 := F.rightSectorOpenEdgeEquiv_symm_first_eq C j r'
              dsimp only at hm hl2 hr1
              rw [hg'] at hm
              rw [hsL'] at hl2
              rw [hsR'] at hr1
              simpa [v', wL', wR', hl2, hr1] using hm
            have huL (i : Fin A) : v ⟨i, by omega⟩ ≍ uL.1 i :=
              (hvL i).trans
                (F.leftFiberOpenEdgeEquiv_symm_fst_heq j kL zL i).symm
            have huL' (i : Fin A) : v' ⟨i, by omega⟩ ≍ uL'.1 i :=
              (hvL' i).trans
                (F.leftFiberOpenEdgeEquiv_symm_fst_heq j kL zL' i).symm
            have huR (i : Fin C) : v ⟨A + 1 + i, by omega⟩ ≍ uR.2 i :=
              (hvR i).trans
                (F.rightFiberOpenEdgeEquiv_symm_snd_heq j kR zR i).symm
            have huR' (i : Fin C) : v' ⟨A + 1 + i, by omega⟩ ≍ uR'.2 i :=
              (hvR' i).trans
                (F.rightFiberOpenEdgeEquiv_symm_snd_heq j kR zR' i).symm
            have huML : (v ⟨A, by omega⟩).1 ≍ uL.2 :=
              (sectorIndex_fst_heq_of_heq F hkMiddle hvM).trans
                (F.leftFiberOpenEdgeEquiv_symm_snd_heq j kL zL).symm
            have huML' : (v' ⟨A, by omega⟩).1 ≍ uL'.2 :=
              (sectorIndex_fst_heq_of_heq F hkMiddle hvM').trans
                (F.leftFiberOpenEdgeEquiv_symm_snd_heq j kL zL').symm
            have huMR : (v ⟨A, by omega⟩).2 ≍ uR.1 :=
              (sectorIndex_snd_heq_of_heq F hkMiddle hvM).trans
                (F.rightFiberOpenEdgeEquiv_symm_fst_heq j kR zR).symm
            have huMR' : (v' ⟨A, by omega⟩).2 ≍ uR'.1 :=
              (sectorIndex_snd_heq_of_heq F hkMiddle hvM').trans
                (F.rightFiberOpenEdgeEquiv_symm_fst_heq j kR zR').symm
            simp only [cyclicActiveFourthRegionBlock,
              cyclicActiveLeftOpenBlock, cyclicActiveRightOpenBlock,
              dif_pos (hkActive.mpr ⟨hL, hR⟩), dif_pos hL, dif_pos hR,
              Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply,
              Matrix.finKronecker_apply]
            rw [F.cyclicActiveSeparatedBoundary_eq_right_kronecker_left]
            simp only [Matrix.kroneckerMap_apply]
            rw [retainedBulkProduct, Fin.prod_univ_add]
            have hprodL :
                (∏ i : Fin A,
                  F.neighboringOperator
                    (k ((Fin.last (A + C)).succAbove (Fin.castAdd C i)))
                    (k ((Fin.last (A + C)).succAbove (Fin.castAdd C i) + 1))
                    (z.1 (Fin.castAdd C i)) (z'.1 (Fin.castAdd C i))) =
                  ∏ i : Fin A,
                    F.neighboringOperator
                      (F.leftSectorWord j kL i.castSucc)
                      (F.leftSectorWord j kL i.succ) (zL.2 i) (zL'.2 i) := by
              cases A with
              | zero => simp
              | succ A =>
                  apply Fintype.prod_congr
                  intro i
                  exact retainedLeftNeighboringEntry_eq F j k kL z z' zL zL'
                    hkLeft hkMiddle huL huL' huML huML' i
            have hprodR :
                (∏ i : Fin C,
                  F.neighboringOperator
                    (k ((Fin.last (A + C)).succAbove (Fin.natAdd A i)))
                    (k ((Fin.last (A + C)).succAbove (Fin.natAdd A i) + 1))
                    (z.1 (Fin.natAdd A i)) (z'.1 (Fin.natAdd A i))) =
                  ∏ i : Fin C,
                    F.neighboringOperator
                      (F.rightSectorWord j kR i.castSucc)
                      (F.rightSectorWord j kR i.succ) (zR.1 i) (zR'.1 i) := by
              cases C with
              | zero => simp
              | succ C =>
                  apply Fintype.prod_congr
                  intro i
                  exact retainedRightNeighboringEntry_eq F j k kR z z' zR zR'
                    hkMiddle hkRight huR huR' huMR huMR' i
            rw [hprodL, hprodR]
            simp only [PhysicalSectorFactorization.neighboringOperator_apply]
            have hfirst :
                F.cyclicActiveRetainedWord (hkActive.mpr ⟨hL, hR⟩)
                    (Fin.last (A + C) + 1) =
                  F.cyclicActiveRetainedWord hL 0 := by
              apply Subtype.ext
              change k (Fin.last (A + C) + 1) = F.leftSectorWord j kL 0
              rw [show Fin.last (A + C) + 1 = (0 : Fin (A + C + 1)) by
                ext
                simp]
              by_cases hA : A = 0
              · subst A
                calc
                  k 0 = j := hkMiddle
                  _ = F.leftSectorWord j kL 0 := by
                    rw [show (0 : Fin 1) = Fin.last 0 by rfl]
                    exact (@Fin.lastCases_last 0 (fun _ ↦ Fin F.sectorCount)
                      j kL).symm
              · obtain ⟨A, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hA
                calc
                  k 0 = kL 0 := hkLeft 0
                  _ = F.leftSectorWord j kL 0 := by
                    rw [show (0 : Fin (A + 2)) =
                      Fin.castSucc (0 : Fin (A + 1)) by rfl]
                    exact (@Fin.lastCases_castSucc (A + 1)
                      (fun _ ↦ Fin F.sectorCount) j kL 0).symm
            have hlast :
                F.cyclicActiveRetainedWord (hkActive.mpr ⟨hL, hR⟩)
                    (Fin.last (A + C)) =
                  F.cyclicActiveRetainedWord hR (Fin.last C) := by
              apply Subtype.ext
              change k (Fin.last (A + C)) =
                F.rightSectorWord j kR (Fin.last C)
              by_cases hC : C = 0
              · subst C
                have he : Fin.last A = ⟨A, by omega⟩ := by
                  ext
                  simp
                calc
                  k (Fin.last A) = k ⟨A, by omega⟩ := congrArg k he
                  _ = j := hkMiddle
                  _ = F.rightSectorWord j kR (Fin.last 0) := by
                    exact (@Fin.cases_zero 0 (fun _ ↦ Fin F.sectorCount)
                      j kR).symm
              · obtain ⟨C, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hC
                have he : Fin.last (A + (C + 1)) =
                    ⟨A + 1 + Fin.last C, by omega⟩ := by
                  ext
                  simp
                  omega
                calc
                  k (Fin.last (A + (C + 1))) =
                      k ⟨A + 1 + Fin.last C, by omega⟩ := congrArg k he
                  _ = kR (Fin.last C) := hkRight (Fin.last C)
                  _ = F.rightSectorWord j kR (Fin.last (C + 1)) := by
                    rw [show Fin.last (C + 1) = (Fin.last C).succ by
                      ext
                      simp]
                    exact (@Fin.cases_succ (C + 1)
                      (fun _ ↦ Fin F.sectorCount) j kR (Fin.last C)).symm
            have hzLeft : z.2.2 ≍ zL.1 := by
              refine (heq_of_eq
                (F.retainedOpenEdgeEquiv_symm_first_left k z).symm).trans ?_
              have he : Fin.last (A + C) + 1 = (0 : Fin (A + C + 1)) := by
                ext
                simp
              by_cases hA : A = 0
              · subst A
                exact ((sectorIndex_fst_heq_of_heq F (congrArg k he)
                  (dependent_apply_heq v he)).trans huML).trans (heq_of_eq
                  (F.leftFiberOpenEdgeEquiv_symm_boundary_zero
                    (F.leftSectorWord j kL) zL))
              · obtain ⟨A, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hA
                have hk0 : k (Fin.last (A + 1 + C) + 1) =
                    F.leftSectorWord j kL 0 := by
                  calc
                    k (Fin.last (A + 1 + C) + 1) = k 0 := congrArg k he
                    _ = kL 0 := hkLeft 0
                    _ = F.leftSectorWord j kL 0 := by
                      rw [show (0 : Fin (A + 2)) =
                        Fin.castSucc (0 : Fin (A + 1)) by rfl]
                      exact (@Fin.lastCases_castSucc (A + 1)
                        (fun _ ↦ Fin F.sectorCount) j kL 0).symm
                exact (sectorIndex_fst_heq_of_heq F hk0
                  ((dependent_apply_heq v he).trans (huL 0))).trans (heq_of_eq
                    (F.leftFiberOpenEdgeEquiv_symm_boundary_succ
                      (F.leftSectorWord j kL) zL))
            have hzLeft' : z'.2.2 ≍ zL'.1 := by
              refine (heq_of_eq
                (F.retainedOpenEdgeEquiv_symm_first_left k z').symm).trans ?_
              have he : Fin.last (A + C) + 1 = (0 : Fin (A + C + 1)) := by
                ext
                simp
              by_cases hA : A = 0
              · subst A
                exact ((sectorIndex_fst_heq_of_heq F (congrArg k he)
                  (dependent_apply_heq v' he)).trans huML').trans (heq_of_eq
                  (F.leftFiberOpenEdgeEquiv_symm_boundary_zero
                    (F.leftSectorWord j kL) zL'))
              · obtain ⟨A, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hA
                have hk0 : k (Fin.last (A + 1 + C) + 1) =
                    F.leftSectorWord j kL 0 := by
                  calc
                    k (Fin.last (A + 1 + C) + 1) = k 0 := congrArg k he
                    _ = kL 0 := hkLeft 0
                    _ = F.leftSectorWord j kL 0 := by
                      rw [show (0 : Fin (A + 2)) =
                        Fin.castSucc (0 : Fin (A + 1)) by rfl]
                      exact (@Fin.lastCases_castSucc (A + 1)
                        (fun _ ↦ Fin F.sectorCount) j kL 0).symm
                exact (sectorIndex_fst_heq_of_heq F hk0
                  ((dependent_apply_heq v' he).trans (huL' 0))).trans (heq_of_eq
                    (F.leftFiberOpenEdgeEquiv_symm_boundary_succ
                      (F.leftSectorWord j kL) zL'))
            have hzRight : z.2.1 ≍ zR.2 := by
              refine (heq_of_eq
                (F.retainedOpenEdgeEquiv_symm_last_right k z).symm).trans ?_
              by_cases hC : C = 0
              · subst C
                have he : Fin.last A = ⟨A, by omega⟩ := by
                  ext
                  simp
                exact ((sectorIndex_snd_heq_of_heq F (congrArg k he)
                  (dependent_apply_heq v he)).trans huMR).trans (heq_of_eq
                    (F.rightFiberOpenEdgeEquiv_symm_boundary_zero
                      (F.rightSectorWord j kR) zR))
              · obtain ⟨C, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hC
                have he : Fin.last (A + (C + 1)) =
                    ⟨A + 1 + Fin.last C, by omega⟩ := by
                  ext
                  simp
                  omega
                have hkLast : k (Fin.last (A + (C + 1))) =
                    F.rightSectorWord j kR (Fin.last (C + 1)) := by
                  calc
                    k (Fin.last (A + (C + 1))) =
                        k ⟨A + 1 + Fin.last C, by omega⟩ := congrArg k he
                    _ = kR (Fin.last C) := hkRight (Fin.last C)
                    _ = F.rightSectorWord j kR (Fin.last (C + 1)) := by
                      rw [show Fin.last (C + 1) = (Fin.last C).succ by
                        ext
                        simp]
                      exact (@Fin.cases_succ (C + 1)
                        (fun _ ↦ Fin F.sectorCount) j kR (Fin.last C)).symm
                exact (sectorIndex_snd_heq_of_heq F hkLast
                  ((dependent_apply_heq v he).trans (huR (Fin.last C)))).trans
                    (heq_of_eq (F.rightFiberOpenEdgeEquiv_symm_boundary_succ
                      (F.rightSectorWord j kR) zR))
            have hzRight' : z'.2.1 ≍ zR'.2 := by
              refine (heq_of_eq
                (F.retainedOpenEdgeEquiv_symm_last_right k z').symm).trans ?_
              by_cases hC : C = 0
              · subst C
                have he : Fin.last A = ⟨A, by omega⟩ := by
                  ext
                  simp
                exact ((sectorIndex_snd_heq_of_heq F (congrArg k he)
                  (dependent_apply_heq v' he)).trans huMR').trans (heq_of_eq
                    (F.rightFiberOpenEdgeEquiv_symm_boundary_zero
                      (F.rightSectorWord j kR) zR'))
              · obtain ⟨C, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hC
                have he : Fin.last (A + (C + 1)) =
                    ⟨A + 1 + Fin.last C, by omega⟩ := by
                  ext
                  simp
                  omega
                have hkLast : k (Fin.last (A + (C + 1))) =
                    F.rightSectorWord j kR (Fin.last (C + 1)) := by
                  calc
                    k (Fin.last (A + (C + 1))) =
                        k ⟨A + 1 + Fin.last C, by omega⟩ := congrArg k he
                    _ = kR (Fin.last C) := hkRight (Fin.last C)
                    _ = F.rightSectorWord j kR (Fin.last (C + 1)) := by
                      rw [show Fin.last (C + 1) = (Fin.last C).succ by
                        ext
                        simp]
                      exact (@Fin.cases_succ (C + 1)
                        (fun _ ↦ Fin F.sectorCount) j kR (Fin.last C)).symm
                exact (sectorIndex_snd_heq_of_heq F hkLast
                  ((dependent_apply_heq v' he).trans (huR' (Fin.last C)))).trans
                    (heq_of_eq (F.rightFiberOpenEdgeEquiv_symm_boundary_succ
                      (F.rightSectorWord j kR) zR'))
            have hboundaryLeft := cyclicActiveLeftBoundary_entry_eq_of_heq
              F b hfirst hzLeft hzLeft'
            have hboundaryRight := cyclicActiveRightBoundary_entry_eq_of_heq
              F a hlast hzRight hzRight'
            rw [hboundaryLeft, hboundaryRight]
            ring
          · simp [cyclicActiveFourthRegionBlock, cyclicActiveLeftOpenBlock,
              cyclicActiveRightOpenBlock, hkActive, hL, hR]
        · simp [cyclicActiveFourthRegionBlock, cyclicActiveLeftOpenBlock,
            cyclicActiveRightOpenBlock, hkActive, hL]
      · have hword :
            ((F.retainedCutEquiv A C).symm ⟨j, (l, r)⟩).1 ≠
              ((F.retainedCutEquiv A C).symm ⟨j, (l', r')⟩).1 := by
          intro hword
          apply hkR
          funext i
          have hi := congrFun hword ⟨A + 1 + i, by omega⟩
          rw [F.retainedCutEquiv_symm_right_sector A C j l r,
            F.retainedCutEquiv_symm_right_sector A C j l' r'] at hi
          calc
            kR i = (F.sectorCoordinateChainEquiv C
                (finFunctionFinEquiv.symm r.2)).1 i := by
              simpa [hsR] using congrFun
                (F.rightSectorOpenEdgeEquiv_apply_fst C j r) i
            _ = (F.sectorCoordinateChainEquiv C
                (finFunctionFinEquiv.symm r'.2)).1 i := hi
            _ = kR' i := by
              simpa [hsR'] using (congrFun
                (F.rightSectorOpenEdgeEquiv_apply_fst C j r') i).symm
        have hkk : k ≠ k' := by simpa [hg, hg'] using hword
        rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkk,
          Matrix.blockDiagonal'_apply_ne _ _ _ hkR, mul_zero]
    · have hword :
          ((F.retainedCutEquiv A C).symm ⟨j, (l, r)⟩).1 ≠
            ((F.retainedCutEquiv A C).symm ⟨j, (l', r')⟩).1 := by
        intro hword
        apply hkL
        funext i
        have hi := congrFun hword ⟨i, by omega⟩
        rw [F.retainedCutEquiv_symm_left_sector A C j l r,
          F.retainedCutEquiv_symm_left_sector A C j l' r'] at hi
        calc
          kL i = (F.sectorCoordinateChainEquiv A
              (finFunctionFinEquiv.symm l.1)).1 i := by
            simpa [hsL] using congrFun
              (F.leftSectorOpenEdgeEquiv_apply_fst A j l) i
          _ = (F.sectorCoordinateChainEquiv A
              (finFunctionFinEquiv.symm l'.1)).1 i := hi
          _ = kL' i := by
            simpa [hsL'] using (congrFun
              (F.leftSectorOpenEdgeEquiv_apply_fst A j l') i).symm
      have hkk : k ≠ k' := by simpa [hg, hg'] using hword
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkk,
        Matrix.blockDiagonal'_apply_ne _ _ _ hkL, zero_mul]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hj]
    have hword :
        ((F.retainedCutEquiv A C).symm ⟨j, (l, r)⟩).1 ≠
          ((F.retainedCutEquiv A C).symm ⟨j', (l', r')⟩).1 := by
      intro h
      apply hj
      rw [← F.retainedCutEquiv_symm_middle_sector A C j l r,
        ← F.retainedCutEquiv_symm_middle_sector A C j' l' r', h]
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hword]


end MPOTensor.PhysicalSectorFactorization
