/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.LeftCoordinates
import QICLean.Entropy.RegionalRightContraction

/-!
# Cut decompositions with bounded left-factor bonds

One operator with simultaneous cut-rank bounds admits a product decomposition at any
chosen cut whose left factors retain those bounds at every earlier cut. The factors
are constructed by linear functionals on the right operator-block span. No matrix
product presentation or prescribed family of suitable factors is assumed.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, Claim
`c:errorreduction`, decomposition `e:decomp`, lines 584--591.
-/

open Matrix
open scoped Kronecker

namespace TNLean.MPS.AreaLaw

/-- Internal cut ranks of a left operator agree in the chain and regional coordinates.
LVV13, `algo53.tex`, the internal bond assertion in Claim `c:errorreduction`, line 591. -/
theorem operatorSchmidtRank_cutOperator_leftConfigOfFin {L q i k : ℕ}
    (hi : i ≤ L) (hk : k ≤ i) (A : LeftBlockMatrix L q i) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
      (A.submatrix leftConfigOfFin leftConfigOfFin)) =
    operatorSchmidtRank (A.reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono hk))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono hk))) := by
  classical
  let eL : {v : Fin i // v ∈ leftBlock i k} ≃ {v : Fin L // v ∈ leftBlock L k} :=
    { toFun := fun v ↦ ⟨⟨v.1.val, lt_of_lt_of_le v.1.isLt hi⟩,
        mem_leftBlock.mpr ((mem_leftBlock (L := i)).mp v.2)⟩
      invFun := fun v ↦ ⟨⟨v.1.val, lt_of_lt_of_le (mem_leftBlock.mp v.2) hk⟩,
        mem_leftBlock.mpr ((mem_leftBlock (L := L)).mp v.2)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let eR : {v : Fin i // v ∉ leftBlock i k} ≃
      {v : Fin L // v ∈ leftBlock L i \ leftBlock L k} :=
    { toFun := fun v ↦ ⟨⟨v.1.val, lt_of_lt_of_le v.1.isLt hi⟩,
        Finset.mem_sdiff.mpr ⟨mem_leftBlock.mpr v.1.isLt,
          fun h ↦ v.2 (mem_leftBlock.mpr ((mem_leftBlock (L := L)).mp h))⟩⟩
      invFun := fun v ↦ ⟨⟨v.1.val, mem_leftBlock.mp (Finset.mem_sdiff.mp v.2).1⟩,
        fun h ↦ (Finset.mem_sdiff.mp v.2).2
          (mem_leftBlock.mpr ((mem_leftBlock (L := i)).mp h))⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let fL := eL.arrowCongr (Equiv.refl (Fin q))
  let fR := eR.arrowCongr (Equiv.refl (Fin q))
  let e := Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (L := L) hk)
  let c := Entropy.cutEquiv (fun _ : Fin i ↦ q) (leftBlock i k)
  have hcoord : (leftConfigOfFinEquiv hi).trans e = c.trans (fL.prodCongr fR) := by
    ext x <;> rfl
  have hinv (x) : leftConfigOfFin (c.symm ((fL.prodCongr fR).symm x)) = e.symm x := by
    apply e.injective
    rw [Equiv.apply_symm_apply]
    change ((leftConfigOfFinEquiv hi).trans e)
      (c.symm ((fL.prodCongr fR).symm x)) = x
    rw [hcoord, Equiv.trans_apply, Equiv.apply_symm_apply]
    exact (fL.prodCongr fR).apply_symm_apply x
  have hmat : (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
      (A.submatrix leftConfigOfFin leftConfigOfFin)).reindex
      (fL.prodCongr fR) (fL.prodCongr fR) = A.reindex e e := by
    ext x y
    change A (leftConfigOfFin (c.symm ((fL.prodCongr fR).symm x)))
      (leftConfigOfFin (c.symm ((fL.prodCongr fR).symm y))) = A (e.symm x) (e.symm y)
    rw [hinv, hinv]
  rw [← hmat]
  exact (operatorSchmidtRank_reindex_prodCongr _ fL fR).symm

/-- A simultaneous global cut-rank bound gives a shortest decomposition at the chosen
cut, and every left factor retains the same bound at its internal cuts. The all-cuts
hypothesis includes endpoints and therefore also covers chains of length at most one
and the bound zero. LVV13, `algo53.tex`, `e:decomp`, lines 584--591. -/
theorem exists_cutDecomposition_of_operatorSchmidtRank_le {L q i R : ℕ}
    (hi : i ≤ L) (K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hK : ∀ k : ℕ, operatorSchmidtRank
      (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) K) ≤ R) :
    ∃ (N : ℕ) (A : Fin N → LeftBlockMatrix L q i)
      (B : Fin N → Matrix ((v : {v : Fin L // v ∉ leftBlock L i}) → Fin q)
        ((v : {v : Fin L // v ∉ leftBlock L i}) → Fin q) ℂ),
      N ≤ R ∧ Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) K =
        ∑ j, A j ⊗ₖ B j ∧
      ∀ j k, 0 < k → k < i → operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
          ((A j).submatrix leftConfigOfFin leftConfigOfFin)) ≤ R := by
  classical
  obtain ⟨φ, B, hdecomp⟩ := exists_operatorRightContraction_decomposition
    (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) K)
  refine ⟨_, fun j ↦ operatorRightContraction (φ j)
    (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) K), B,
    hK i, hdecomp, ?_⟩
  intro j k _ hki
  rw [operatorSchmidtRank_cutOperator_leftConfigOfFin hi hki.le]
  exact (Entropy.operatorSchmidtRank_rightContraction_subset_le
    (leftBlock_mono hki.le) K (φ j)).trans (hK k)

end TNLean.MPS.AreaLaw
