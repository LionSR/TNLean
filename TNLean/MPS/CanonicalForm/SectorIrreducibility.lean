/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.CyclicSectors
import TNLean.MPS.Irreducible.FormII
import TNLean.MPS.Irreducible.Adjoint
import TNLean.MPS.Irreducible.PeriodicBlocking

/-!
# Sector irreducibility helpers

This file isolates the remaining channel-to-MPS bridge for cyclic-sector
irreducibility.

At present it provides:

* a reusable orthogonality lemma for orthogonal projections summing to `1`;
* a corner-preservation lemma for adjoint transfer maps fixed on an orthogonal
  projection;
* the easy orbit-sum fixed-point calculation `T (∑ₗ T^[l](Q)) = ∑ₗ T^[l](Q)`;
* an MPS-level wrapper reducing sector irreducibility to the `hLift`
  hypothesis required by
  `Channel.Peripheral.CyclicDecomposition.isIrreducible_restriction_of_cyclic_decomp`.

What still remains for the full orbit-sum lift is the genuinely missing part:
showing that, for a cyclic sector subprojection `Q`, the orbit iterates
`T^[l](Q)` stay orthogonal projections in the shifted sectors. Once those
sublemmas are available, the wrapper theorem here immediately yields sector
irreducibility for the MPS adjoint transfer map.

Concretely, the missing MPS/channel lemmas are the following three pieces:

* `orbit_iterate_supported_on_shifted_sector`:
  `T^[l](Q)` lies in the expected cyclic sector;
* `orbit_iterate_isOrthogonalProjection`:
  `T^[l](Q)` is again an orthogonal projection;
* `orbitSumProjection_eq_one_of_full_sector`:
  for `Q = P_k`, the orbit sum is the full identity.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset Complex

namespace MPSTensor

variable {d D m : ℕ}

/-- Orthogonal projections summing to `1` are pairwise orthogonal. -/
theorem pairwise_mul_zero_of_orthogonalProjection_sum_one
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1) :
    Pairwise fun i j : Fin m => P i * P j = 0 := by
  intro i j hij
  have hsum_i : ∑ k : Fin m, P i * P k * P i = P i := by
    calc
      ∑ k : Fin m, P i * P k * P i
          = P i * (∑ k : Fin m, P k) * P i := by
              simp [Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]
      _ = P i * 1 * P i := by rw [hPsum]
      _ = P i := by simp [Matrix.mul_assoc, (hPproj i).2]
  have hsum_erase : ∑ k in Finset.univ.erase i, P i * P k * P i = 0 := by
    rw [Finset.sum_erase_add _ (Finset.mem_univ i)] at hsum_i
    have hiii : P i * P i * P i = P i := by
      simp [Matrix.mul_assoc, (hPproj i).2]
    rw [hiii] at hsum_i
    exact add_right_cancel (by simpa using hsum_i)
  let B : Fin m → MatrixAlg D := fun k => if k = i then 0 else P i * P k
  have hsum_B : ∑ k : Fin m, B k * (B k)ᴴ = 0 := by
    classical
    rw [Finset.sum_erase_add _ (Finset.mem_univ i)]
    have hzero_i : B i * (B i)ᴴ = 0 := by simp [B]
    rw [hzero_i, add_zero]
    calc
      ∑ k in Finset.univ.erase i, B k * (B k)ᴴ
          = ∑ k in Finset.univ.erase i, P i * P k * P i := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              have hki : k ≠ i := by
                exact Finset.mem_erase.mp hk |>.1
              simp [B, hki, Matrix.mul_assoc, (hPproj i).1.eq, (hPproj k).1.eq, (hPproj k).2]
      _ = 0 := hsum_erase
  have hB_zero := eq_zero_of_sum_mul_conjTranspose_eq_zero B hsum_B
  have hPiPj : P i * P j = 0 := by
    by_cases hji : j = i
    · exact False.elim (hij hji.symm)
    · simpa [B, hji] using hB_zero j
  exact hPiPj

/-- If an orthogonal projection is fixed by the adjoint transfer map of a TP
tensor, then the corresponding corner is invariant. -/
theorem preservesCorner_of_adjoint_fixed_projection
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    {P : MatrixAlg D}
    (hP : IsOrthogonalProjection P)
    (hFix : transferMap (d := d) (D := D) (fun i => (A i)ᴴ) P = P) :
    PreservesCorner P (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) := by
  have hComm : ∀ i : Fin d, P * A i = A i * P :=
    commutes_letters_of_adjoint_fixed_projection (A := A) hTP (hP := hP) hFix
  have hCommAdj : ∀ i : Fin d, P * (A i)ᴴ = (A i)ᴴ * P := by
    intro i
    have h := congrArg Matrix.conjTranspose (hComm i)
    simpa [Matrix.conjTranspose_mul] using h.symm
  intro X
  simp only [transferMap_apply, Finset.mul_sum, Finset.sum_mul]
  congr 1
  ext i
  calc
    P * ((A i)ᴴ * (P * X * P) * A i) * P
        = (P * (A i)ᴴ) * (P * X * P) * (A i * P) := by
            simp [Matrix.mul_assoc]
    _ = ((A i)ᴴ * P) * (P * X * P) * (P * A i) := by
          rw [hCommAdj i, hComm i]
    _ = (A i)ᴴ * (P * X * P) * A i := by
          simp [Matrix.mul_assoc, (hP.2)]

/-- The orbit sum `∑ₗ T^[l](Q)` is fixed by `T` as soon as `Q` is fixed by
`T^[m]`. -/
theorem orbitSumProjection_fixed_of_pow_fix
    [NeZero m]
    {T : MatrixEnd D} {Q : MatrixAlg D}
    (hQfix : (T ^ m) Q = Q) :
    T (orbitSumProjection (D := D) (m := m) T Q) =
      orbitSumProjection (D := D) (m := m) T Q := by
  classical
  have hm_pos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  let f : ℕ → MatrixAlg D := fun n => (T ^ n) Q
  have hm_pred_succ : (m - 1) + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
  have hdecomp_left :
      Finset.sum (Finset.range (m - 1)) (fun j : ℕ => f (j + 1)) + f 0 =
        Finset.sum (Finset.range m) (fun j : ℕ => f j) := by
    simpa [hm_pred_succ, f] using
      (Finset.sum_range_succ' (fun j : ℕ => f j) (m - 1)).symm
  have hdecomp_right :
      Finset.sum (Finset.range (m - 1)) (fun j : ℕ => f (j + 1)) + f m =
        Finset.sum (Finset.range m) (fun j : ℕ => f (j + 1)) := by
    simpa [hm_pred_succ, f] using
      (Finset.sum_range_succ' (fun j : ℕ => f (j + 1)) (m - 1)).symm
  have hshift :
      Finset.sum (Finset.range m) (fun j : ℕ => f (j + 1)) =
        Finset.sum (Finset.range m) (fun j : ℕ => f j) := by
    rw [← hdecomp_left, ← hdecomp_right, hQfix]
    simp [f]
  calc
    ∑ l : Fin m, T (((T ^ (l : ℕ)) Q))
        = ∑ l : Fin m, (T ^ ((l : ℕ) + 1)) Q := by
            congr 1
            ext l
            simp [pow_succ']
    _ = ∑ j in Finset.range m, f (j + 1) := by
          simp [Fin.sum_univ_eq_sum_range, f]
    _ = ∑ j in Finset.range m, f j := hshift
    _ = ∑ l : Fin m, (T ^ (l : ℕ)) Q := by
          simp [Fin.sum_univ_eq_sum_range, f]

/-- MPS-specialized wrapper: once the orbit-sum lift is constructed in the
shape required by `isIrreducible_restriction_of_cyclic_decomp`, sector
irreducibility follows immediately. -/
theorem isIrreducibleOnCorner_of_cyclic_decomp_mps_of_hLift
    {A : MPSTensor d D}
    [NeZero m]
    (hIrr :
      IsIrreducibleMap (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)))
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic :
      ∀ k : Fin m,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hLift :
      ∀ k : Fin m, ∀ Q : MatrixAlg D,
        IsOrthogonalProjection Q →
        Q * P k = Q →
        P k * Q = Q →
        PreservesCorner Q ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) →
        ∃ R : MatrixAlg D,
          IsOrthogonalProjection R ∧
          PreservesCorner R (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ∧
          (Q = 0 ↔ R = 0) ∧
          (Q = P k ↔ R = 1)) :
    ∀ k : Fin m,
      IsIrreducibleOnCorner
        (P k) ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) := by
  exact
    isIrreducible_restriction_of_cyclic_decomp
      (T := transferMap (d := d) (D := D) (fun i => (A i)ᴴ))
      hIrr P hPproj hPsum hcyclic hLift

end MPSTensor
