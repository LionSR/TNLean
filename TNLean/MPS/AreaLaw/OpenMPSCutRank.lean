/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.OpenMPSRank

/-!
# Cut ranks of open-boundary matrix product states

Splitting a rectangular tensor contraction at a virtual bond factors the cut matrix
through that bond space. Thus an internal cut of an open-boundary matrix product state
of bond dimension at most `D` has rank at most `D`, including when `D = 0`.
Together with the construction from cut ranks, this characterizes `IsOpenMPS`.
The endpoint cuts have rank at most one and impose no condition on `D`.

## References

* SWVC07, arXiv:0705.0292v2, `paper_v2.tex`, lines 234–264: the cut-rank bound
  used in the lower bound on approximation error.
* TNLean one-dimensional note, Part IIa, Proposition `prop:VC`, lines 39–62.
-/

open scoped BigOperators
open Matrix

namespace TNLean.MPS.AreaLaw

/-- Join the bond indices strictly to the left and right of a cut with its fixed bond index. -/
private def joinBondPath {L : ℕ} (B : Fin (L + 1) → Type*) (k : Fin (L + 1))
    (z : B k) (l : (j : {j : Fin (L + 1) // j < k}) → B j)
    (r : (j : {j : Fin (L + 1) // k < j}) → B j) (j : Fin (L + 1)) : B j :=
  if h : j < k then l ⟨j, h⟩ else
    if h' : j = k then h'.symm ▸ z else r ⟨j, lt_of_le_of_ne (le_of_not_gt h) (Ne.symm h')⟩

/-- A bond path is determined by its index at the cut and its restrictions to either side. -/
private def bondPathEquiv {L : ℕ} (B : Fin (L + 1) → Type*) (k : Fin (L + 1)) :
    ((j : Fin (L + 1)) → B j) ≃
      B k × ((j : {j : Fin (L + 1) // j < k}) → B j) ×
        ((j : {j : Fin (L + 1) // k < j}) → B j) where
  toFun p := (p k, (fun j ↦ p j), fun j ↦ p j)
  invFun p := joinBondPath B k p.1 p.2.1 p.2.2
  left_inv := by
    intro p
    funext j
    simp only [joinBondPath, dite_eq_ite, ite_eq_left_iff]
    intro h
    split_ifs with he <;> subst_vars <;> rfl
  right_inv := by
    rintro ⟨z, l, r⟩
    simp +contextual [joinBondPath, funext_iff, lt_asymm, ne_of_gt]

/-- Extend the left bond path to the cut by assigning the prescribed cut index. -/
private def leftBondPath {L : ℕ} (B : Fin (L + 1) → Type*) (k : Fin (L + 1))
    (z : B k) (l : (j : {j : Fin (L + 1) // j < k}) → B j)
    (j : Fin (L + 1)) (hj : j ≤ k) : B j :=
  if h : j < k then l ⟨j, h⟩ else (le_antisymm hj (le_of_not_gt h)).symm ▸ z

/-- Extend the right bond path to the cut by assigning the prescribed cut index. -/
private def rightBondPath {L : ℕ} (B : Fin (L + 1) → Type*) (k : Fin (L + 1))
    (z : B k) (r : (j : {j : Fin (L + 1) // k < j}) → B j)
    (j : Fin (L + 1)) (hj : k ≤ j) : B j :=
  if h : k < j then r ⟨j, h⟩ else (le_antisymm (le_of_not_gt h) hj).symm ▸ z

/-- On or to the left of the cut, the joined path agrees with the extended left path. -/
private theorem joinBondPath_of_le {L : ℕ} (B : Fin (L + 1) → Type*)
    (k : Fin (L + 1)) (z : B k)
    (l : (j : {j : Fin (L + 1) // j < k}) → B j)
    (r : (j : {j : Fin (L + 1) // k < j}) → B j)
    (j : Fin (L + 1)) (hj : j ≤ k) :
    joinBondPath B k z l r j = leftBondPath B k z l j hj := by
  by_cases h : j < k
  · simp [joinBondPath, leftBondPath, h]
  · have he : j = k := le_antisymm hj (le_of_not_gt h)
    subst j
    simp [joinBondPath, leftBondPath]

/-- On or to the right of the cut, the joined path agrees with the extended right path. -/
private theorem joinBondPath_of_ge {L : ℕ} (B : Fin (L + 1) → Type*)
    (k : Fin (L + 1)) (z : B k)
    (l : (j : {j : Fin (L + 1) // j < k}) → B j)
    (r : (j : {j : Fin (L + 1) // k < j}) → B j)
    (j : Fin (L + 1)) (hj : k ≤ j) :
    joinBondPath B k z l r j = rightBondPath B k z r j hj := by
  by_cases h : k < j
  · simp [joinBondPath, rightBondPath, h, not_lt_of_ge hj, ne_of_gt h]
  · obtain rfl := le_antisymm (le_of_not_gt h) hj
    simp [joinBondPath, rightBondPath]

/-- Contract the tensors strictly to the left of the cut, keeping its bond index fixed. -/
private noncomputable def leftContraction {L q D : ℕ} (A : OBCChainTensor q D L)
    (k : Fin (L + 1)) (a : (v : {v : Fin L // v ∈ leftBlock L k}) → Fin q)
    (z : Fin (A.bondDim k)) : ℂ :=
  ∑ l : (j : {j : Fin (L + 1) // j < k}) → Fin (A.bondDim j),
    ∏ i : {i : Fin L // i ∈ leftBlock L k},
      A.tensor i (a i)
        (leftBondPath (fun j ↦ Fin (A.bondDim j)) k z l i.1.castSucc
          (by simpa only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] using
            (Nat.le_of_lt (mem_leftBlock.mp i.2))))
        (leftBondPath (fun j ↦ Fin (A.bondDim j)) k z l i.1.succ
          (by simpa only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] using
            (Nat.succ_le_of_lt (mem_leftBlock.mp i.2))))

/-- Contract the tensors on the right of the cut, keeping its bond index fixed. -/
private noncomputable def rightContraction {L q D : ℕ} (A : OBCChainTensor q D L)
    (k : Fin (L + 1)) (b : (v : {v : Fin L // v ∉ leftBlock L k}) → Fin q)
    (z : Fin (A.bondDim k)) : ℂ :=
  ∑ r : (j : {j : Fin (L + 1) // k < j}) → Fin (A.bondDim j),
    ∏ i : {i : Fin L // i ∉ leftBlock L k},
      A.tensor i (b i)
        (rightBondPath (fun j ↦ Fin (A.bondDim j)) k z r i.1.castSucc
          (by simpa only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] using
            (Nat.le_of_not_lt (mt mem_leftBlock.mpr i.2))))
        (rightBondPath (fun j ↦ Fin (A.bondDim j)) k z r i.1.succ
          (by simpa only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] using
            (Nat.le_succ_of_le (Nat.le_of_not_lt (mt mem_leftBlock.mpr i.2)))))

/-- The full contraction is the sum over the cut bond of the two partial contractions.
This is the bond splitting underlying SWVC07, arXiv:0705.0292v2, lines 234–264. -/
private theorem coeff_eq_sum_left_mul_right {L q D : ℕ} (A : OBCChainTensor q D L)
    (k : Fin (L + 1)) (a : (v : {v : Fin L // v ∈ leftBlock L k}) → Fin q)
    (b : (v : {v : Fin L // v ∉ leftBlock L k}) → Fin q) :
    A.coeff ((Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k)).symm (a, b)) =
      ∑ z, leftContraction A k a z * rightContraction A k b z := by
  classical
  rw [OBCChainTensor.coeff, ← (bondPathEquiv (fun j ↦ Fin (A.bondDim j)) k).symm.sum_comp]
  simp only [Fintype.sum_prod_type, bondPathEquiv, Equiv.coe_fn_symm_mk,
    leftContraction, rightContraction, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun l _ ↦
    Finset.sum_congr rfl fun r _ ↦ ?_
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Fin L ↦ i ∈ leftBlock L k)]
  congr 1
  · refine Finset.prod_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) fun i _ ↦ ?_
    rw [Entropy.cutEquiv_symm_apply_mem (n := fun _ : Fin L ↦ q) a b i.2]
    exact congrArg₂ (fun x y ↦ A.tensor i (a i) x y)
      (joinBondPath_of_le _ _ _ _ _ _ _) (joinBondPath_of_le _ _ _ _ _ _ _)
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Entropy.cutEquiv_symm_apply_not_mem (n := fun _ : Fin L ↦ q) a b i.2]
    exact congrArg₂ (fun x y ↦ A.tensor i (b i) x y)
      (joinBondPath_of_ge _ _ _ _ _ _ _) (joinBondPath_of_ge _ _ _ _ _ _ _)

/-- The cut matrix factors through the virtual bond space, with any overall scalar absorbed
into the left factor. Source: SWVC07, arXiv:0705.0292v2, lines 234–264. -/
private theorem exists_cutMatrix_factorization {L q D : ℕ}
    (A : OBCChainTensor q D L) (c : ℂ)
    (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (hψ : ∀ x, ψ x = c * A.coeff x)
    (k : Fin (L + 1)) :
    ∃ (U : Matrix ((v : {v : Fin L // v ∈ leftBlock L k}) → Fin q)
        (Fin (A.bondDim k)) ℂ)
      (V : Matrix (Fin (A.bondDim k))
        ((v : {v : Fin L // v ∉ leftBlock L k}) → Fin q) ℂ),
      cutMatrix ψ k = U * V := by
  classical
  refine ⟨Matrix.of (fun a z ↦ c * leftContraction A k a z),
    Matrix.of (fun z b ↦ rightContraction A k b z), ?_⟩
  ext a b
  rw [cutMatrix_apply, hψ, Matrix.mul_apply]
  simp only [Matrix.of_apply, mul_assoc, ← Finset.mul_sum]
  exact congrArg (c * ·) (coeff_eq_sum_left_mul_right A k a b)

/-- A cut matrix of a scalar multiple of an open-boundary contraction has rank at most
the dimension of the actual virtual bond, including a zero-dimensional bond.
Source: SWVC07, arXiv:0705.0292v2, lines 234–264; the one-dimensional note,
Part IIa, Proposition `prop:VC`, lines 39–62. -/
theorem rank_cutMatrix_le_bondDim {L q D : ℕ} (A : OBCChainTensor q D L) (c : ℂ)
    (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (hψ : ∀ x, ψ x = c * A.coeff x)
    (k : Fin (L + 1)) : (cutMatrix ψ k).rank ≤ A.bondDim k := by
  obtain ⟨U, V, hUV⟩ := exists_cutMatrix_factorization A c ψ hψ k
  rw [hUV]
  simpa using (rank_mul_le_left U V).trans (rank_le_card_width U)

/-- Every internal cut of an open-boundary MPS has rank bounded by its internal
bond dimension. No normalization or positivity assumption on `D` is needed.
Source: SWVC07, arXiv:0705.0292v2, lines 234–264; the one-dimensional note,
Part IIa, Proposition `prop:VC`, lines 39–62. -/
theorem IsOpenMPS.rank_cutMatrix_le {L q D : ℕ}
    {ψ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hψ : IsOpenMPS L q D (fun x ↦ ψ x)) {k : ℕ} (hk0 : 0 < k) (hkL : k < L) :
    (cutMatrix ψ k).rank ≤ D := by
  obtain ⟨A, c, hD, hA⟩ := hψ
  exact (rank_cutMatrix_le_bondDim A c ψ hA ⟨k, by omega⟩).trans
    (hD ⟨k, by omega⟩ hk0 hkL)

/-- Internal cut ranks characterize open-boundary matrix product states, also for
empty and one-site chains and for `D = 0`.
Source: SWVC07, arXiv:0705.0292v2, lines 234–264; the one-dimensional note,
Part IIa, Proposition `prop:VC`, lines 39–62. -/
theorem isOpenMPS_iff_internal_cutMatrix_rank_le {L q D : ℕ}
    (ψ : EuclideanSpace ℂ (Fin L → Fin q)) :
    IsOpenMPS L q D (fun x ↦ ψ x) ↔
      ∀ k : ℕ, 0 < k → k < L → (cutMatrix ψ k).rank ≤ D := by
  exact ⟨fun h k hk0 hkL ↦ h.rank_cutMatrix_le hk0 hkL,
    isOpenMPS_of_internal_cutMatrix_rank_le ψ⟩

end TNLean.MPS.AreaLaw
