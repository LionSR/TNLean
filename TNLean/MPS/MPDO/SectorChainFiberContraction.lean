/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorChainDecomposition

/-!
# Contraction of a finite chain fiber

This file records the finite Fubini identity underlying contractions over the
left--right fibers of a nonempty sector word.

## Reference

* arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines 1606--1617.
-/

open scoped BigOperators

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

private def piProdEquiv {ι : Type*} (α β : ι → Type*) :
    ((i : ι) → α i × β i) ≃
      ((i : ι) → α i) × ((i : ι) → β i) where
  toFun z := (fun i ↦ (z i).1, fun i ↦ (z i).2)
  invFun z i := (z.1 i, z.2 i)
  left_inv z := by
    funext i
    rfl
  right_inv z := rfl

/-- Summing a nearest-neighbor product over all left--right coordinates of a
nonempty finite chain factors into its left boundary sum, its internal edge
sums, and its right boundary sum.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617. -/
theorem sum_pi_prod_eq_mul_prod_mul
    {m : ℕ}
    (α β : Fin (m + 1) → Type*)
    [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (left : α 0 → ℂ) (right : β (Fin.last m) → ℂ)
    (edge : (i : Fin m) → β i.castSucc → α i.succ → ℂ) :
    (∑ z : (i : Fin (m + 1)) → α i × β i,
        left (z 0).1 *
          (∏ i : Fin m, edge i (z i.castSucc).2 (z i.succ).1) *
          right (z (Fin.last m)).2) =
      (∑ a, left a) *
        (∏ i : Fin m, ∑ b, ∑ a, edge i b a) *
        ∑ b, right b := by
  classical
  calc
    _ = ∑ z : ((i : Fin (m + 1)) → α i) ×
          ((i : Fin (m + 1)) → β i),
        left (z.1 0) *
          (∏ i : Fin m, edge i (z.2 i.castSucc) (z.1 i.succ)) *
          right (z.2 (Fin.last m)) := by
      apply Fintype.sum_equiv (piProdEquiv α β)
      intro z
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      have hleft (r : (i : Fin (m + 1)) → β i) :
          (∑ l : (i : Fin (m + 1)) → α i,
              left (l 0) *
                ∏ i : Fin m, edge i (r i.castSucc) (l i.succ)) =
            (∑ a, left a) *
              ∏ i : Fin m, ∑ a, edge i (r i.castSucc) a := by
        let f : (i : Fin (m + 1)) → α i → ℂ :=
          Fin.cases left fun i a ↦ edge i (r i.castSucc) a
        calc
          _ = ∑ l : (i : Fin (m + 1)) → α i, ∏ i, f i (l i) := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [Fin.prod_univ_succ]
            rfl
          _ = ∏ i, ∑ a, f i a := by
            symm
            simpa only [Fintype.piFinset_univ] using
              (Finset.prod_univ_sum
                (fun i : Fin (m + 1) ↦ (Finset.univ : Finset (α i))) f)
          _ = _ := by
            rw [Fin.prod_univ_succ]
            rfl
      have hright :
          (∑ r : (i : Fin (m + 1)) → β i,
              (∏ i : Fin m, ∑ a, edge i (r i.castSucc) a) *
                right (r (Fin.last m))) =
            (∏ i : Fin m, ∑ b, ∑ a, edge i b a) *
              ∑ b, right b := by
        let f : (i : Fin (m + 1)) → β i → ℂ :=
          Fin.lastCases right fun i b ↦ ∑ a, edge i b a
        calc
          _ = ∑ r : (i : Fin (m + 1)) → β i, ∏ i, f i (r i) := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [Fin.prod_univ_castSucc]
            simp [f]
          _ = ∏ i, ∑ b, f i b := by
            symm
            simpa only [Fintype.piFinset_univ] using
              (Finset.prod_univ_sum
                (fun i : Fin (m + 1) ↦ (Finset.univ : Finset (β i))) f)
          _ = _ := by
            rw [Fin.prod_univ_castSucc]
            simp [f]
      simp_rw [← Finset.sum_mul, hleft, mul_assoc]
      rw [← Finset.mul_sum, hright]

/-- Contracting the diagonal neighboring-operator entries along a nonempty
sector-chain fiber leaves the two boundary sums and the product of the
internal neighboring-operator traces.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617. -/
theorem sum_sectorChainFiber_neighboringOperator_diag
    (F : PhysicalSectorFactorization K)
    {m : ℕ} (t : Fin (m + 1) → Fin F.sectorCount)
    (left : Fin (F.leftDim (t 0)) → ℂ)
    (right : Fin (F.rightDim (t (Fin.last m))) → ℂ) :
    (∑ z : F.SectorChainFiber t,
        left (z 0).1 *
          (∏ i : Fin m,
            F.neighboringOperator (t i.castSucc) (t i.succ)
              ((z i.castSucc).2, (z i.succ).1)
              ((z i.castSucc).2, (z i.succ).1)) *
          right (z (Fin.last m)).2) =
      (∑ a, left a) *
        (∏ i : Fin m,
          (F.neighboringOperator (t i.castSucc) (t i.succ)).trace) *
        ∑ b, right b := by
  simpa only [SectorChainFiber, Matrix.trace, Matrix.diag_apply,
    Fintype.sum_prod_type] using
    (sum_pi_prod_eq_mul_prod_mul
      (fun i ↦ Fin (F.leftDim (t i)))
      (fun i ↦ Fin (F.rightDim (t i)))
      left right
      (fun i b a ↦
        F.neighboringOperator (t i.castSucc) (t i.succ) (b, a) (b, a)))

end MPOTensor.PhysicalSectorFactorization
