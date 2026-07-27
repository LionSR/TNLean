/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.InvariantProjection
import TNLean.MPS.MPDO.SectorTrace

/-!
# First-site sector-compression separation

This file isolates the common algebraic consequence of a first-site Lemma L:
a nonzero vertical corner is detected by a finite-chain compression.  It does
not assume positivity or a particular canonical-form predicate.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Appendix C.3,
  Lemma L, lines 1835--1858, and Proposition 4.13, line 1898.
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- A first-site Lemma L separates every nonzero vertical corner by a finite-chain
sector compression.

If all compressions by `P` vanished, their matrix entries would show that the
two-sided first-site action by `P` agrees with zero on every matrix product vector.
The supplied Lemma L then makes the inserted tensor zero, hence every corner
$P\widetilde M_vP$ vanishes.  This is the separation argument in the proof of
Proposition 4.13 of arXiv:1606.00608, line 1898, using Appendix C.3, Lemma L,
lines 1835--1858. -/
theorem exists_sectorCompression_ne_zero_of_corner_of_insertedTensor_eq
    (M : MPOTensor d D)
    (hLemmaL : ∀ {Y Z : Matrix (Fin (d * d)) (Fin (d * d)) ℂ},
      MPSTensor.FirstSiteActionAgree M.toMPSTensor Y Z →
        MPSTensor.insertedTensor Y M.toMPSTensor =
          MPSTensor.insertedTensor Z M.toMPSTensor)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (hcorner : ∃ v, P * verticalTensor M v * P ≠ 0) :
    ∃ N, sectorCompression M P N ≠ 0 := by
  by_contra hnone
  simp only [not_exists, not_not] at hnone
  have hAct : MPSTensor.FirstSiteActionAgree M.toMPSTensor
      (MPSTensor.ketLeftBraRightAction P) 0 := by
    intro N ρ
    rw [MPSTensor.ketLeftBraRightAction_mpv]
    simp only [Matrix.zero_apply, zero_mul, Finset.sum_const_zero]
    have hentry := Matrix.ext_iff.mpr (hnone N)
      (Fin.cons (ρ 0).divNat fun n => (ρ (Fin.succ n)).divNat)
      (Fin.cons (ρ 0).modNat fun n => (ρ (Fin.succ n)).modNat)
    rw [sectorCompression_def, mul_firstSiteMatrix_apply] at hentry
    simp only [firstSiteMatrix_mul_apply] at hentry
    simp only [Fin.cons_zero, Function.comp_def, Fin.cons_succ,
      Matrix.zero_apply] at hentry
    rw [← hentry]
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  have hInserted := hLemmaL hAct
  have hTensor : ((M.ketLeftMul P).braRightMul P).toMPSTensor = 0 := by
    rw [← insertedTensor_ketLeftBraRightAction_toMPSTensor]
    rw [hInserted]
    ext v a b
    simp [MPSTensor.insertedTensor]
  have hMzero : (M.ketLeftMul P).braRightMul P = 0 := by
    funext i j
    have hij := congrFun hTensor (finProdFinEquiv (i, j))
    simpa [toMPSTensor] using hij
  obtain ⟨v, hv⟩ := hcorner
  apply hv
  have hv0 : verticalTensor ((M.ketLeftMul P).braRightMul P) v = 0 := by
    rw [hMzero]
    rfl
  rw [verticalTensor_braRightMul, verticalTensor_ketLeftMul] at hv0
  exact hv0

end MPOTensor
