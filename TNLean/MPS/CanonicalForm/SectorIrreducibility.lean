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

## General results (outside `MPSTensor` namespace)

* `pairwise_mul_zero_of_orthogonalProjection_sum_one`: orthogonal projections
  summing to `1` are pairwise orthogonal (`P_i P_j = 0` for `i ≠ j`).
* `preservesCorner_of_adjoint_fixed_projection`: if an orthogonal projection is
  fixed by the adjoint transfer map of a TP tensor, then the corresponding
  corner algebra is invariant.

## MPS-specific results

* the easy orbit-sum fixed-point calculation `T (∑ₗ T^[l](Q)) = ∑ₗ T^[l](Q)`;
* an MPS-level wrapper reducing sector irreducibility to the `hLift`
  hypothesis required by
  `Channel.Peripheral.CyclicDecomposition.isIrreducible_restriction_of_cyclic_decomp`.

The orbit-sum lift sublemmas completing the `hLift` construction are:

* `orbit_iterate_supported_on_shifted_sector`:
  `T^[l](Q)` lies in the expected cyclic sector;
* `orbit_iterate_isOrthogonalProjection`:
  `T^[l](Q)` is again an orthogonal projection;
* `orbitSumProjection_eq_one_of_full_sector`:
  for `Q = P_k`, the orbit sum is the full identity.

Together with the orbit-sum fixed-point calculation and the MPS wrapper,
these yield sector irreducibility for the MPS adjoint transfer map.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset Complex

/-! ### Orthogonal-projection pairwise orthogonality -/

variable {D m : ℕ}

/-- If a finite family of orthogonal projections sums to the identity, then
distinct projections are orthogonal: `P i * P j = 0` for `i ≠ j`.

This is a standard fact about orthogonal decompositions of the identity. The
proof sandwiches the sum between `P i` to isolate the diagonal, then extracts
each off-diagonal term via positivity (`B B* = 0 → B = 0`). -/
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
      _ = P i := by simp [(hPproj i).2]
  have hsum_erase : ∑ k ∈ Finset.univ.erase i, P i * P k * P i = 0 := by
    rw [← Finset.sum_erase_add Finset.univ (fun k => P i * P k * P i) (Finset.mem_univ i)] at hsum_i
    have hiii : P i * P i * P i = P i := by
      simp [(hPproj i).2]
    rw [hiii] at hsum_i
    simpa using hsum_i
  let B : Fin m → MatrixAlg D := fun k => if k = i then 0 else P i * P k
  have hsum_B : ∑ k : Fin m, B k * (B k)ᴴ = 0 := by
    classical
    rw [← Finset.sum_erase_add Finset.univ (fun k => B k * (B k)ᴴ) (Finset.mem_univ i)]
    have hzero_i : B i * (B i)ᴴ = 0 := by simp [B]
    rw [hzero_i, add_zero]
    calc
      ∑ k ∈ Finset.univ.erase i, B k * (B k)ᴴ
          = ∑ k ∈ Finset.univ.erase i, P i * P k * P i := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              have hki : k ≠ i := by
                exact Finset.mem_erase.mp hk |>.1
              calc
                B k * (B k)ᴴ = (P i * P k) * ((P i * P k)ᴴ) := by
                  simp [B, hki]
                _ = P i * P k * P i := by
                  calc
                    (P i * P k) * ((P i * P k)ᴴ)
                        = P i * (P k * (P k * P i)) := by
                            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, (hPproj i).1.eq,
                              (hPproj k).1.eq]
                    _ = P i * ((P k * P k) * P i) := by simp [Matrix.mul_assoc]
                    _ = P i * (P k * P i) := by rw [(hPproj k).2]
                    _ = P i * P k * P i := by simp [Matrix.mul_assoc]
      _ = 0 := hsum_erase
  have hB_zero := eq_zero_of_sum_mul_conjTranspose_eq_zero B hsum_B
  have hPiPj : P i * P j = 0 := by
    by_cases hji : j = i
    · exact False.elim (hij hji.symm)
    · simpa [B, hji] using hB_zero j
  exact hPiPj

/-! ### Corner preservation from adjoint fixed projections -/

variable {d : ℕ}

/-- If an orthogonal projection `P` is fixed by the adjoint transfer map
`T†(·) = ∑ᵢ Aᵢ† · Aᵢ` of a TP tensor, then `T†` preserves the corner
algebra `P · M_D(ℂ) · P`.

The proof derives `[P, Aᵢ] = 0` from
`MPSTensor.commutes_letters_of_adjoint_fixed_projection`, then threads the
idempotent relation `P² = P` through the corner sandwich. -/
theorem preservesCorner_of_adjoint_fixed_projection
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    {P : MatrixAlg D}
    (hP : IsOrthogonalProjection P)
    (hFix : MPSTensor.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) P = P) :
    PreservesCorner P (MPSTensor.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) := by
  have hComm : ∀ i : Fin d, P * A i = A i * P :=
    MPSTensor.commutes_letters_of_adjoint_fixed_projection (A := A) hTP (hP := hP) hFix
  have hCommAdj : ∀ i : Fin d, P * (A i)ᴴ = (A i)ᴴ * P := by
    intro i
    have h := congrArg Matrix.conjTranspose (hComm i)
    simpa [Matrix.conjTranspose_mul, hP.1.eq] using h.symm
  intro X
  simp only [MPSTensor.transferMap_apply, Finset.mul_sum, Finset.sum_mul,
    Matrix.conjTranspose_conjTranspose]
  refine Finset.sum_congr rfl ?_
  intro i _
  calc
    P * ((A i)ᴴ * (P * X * P) * A i) * P
        = (P * (A i)ᴴ) * (P * X * P) * (A i * P) := by
            simp [Matrix.mul_assoc]
    _ = ((A i)ᴴ * P) * (P * X * P) * (P * A i) := by
          rw [hCommAdj i, ← hComm i]
    _ = (A i)ᴴ * ((P * P) * X * P) * (P * A i) := by
          simp [Matrix.mul_assoc]
    _ = (A i)ᴴ * (P * X * P) * (P * A i) := by
          simp [Matrix.mul_assoc, hP.2]
    _ = (A i)ᴴ * (P * X * P) * A i := by
          calc
            (A i)ᴴ * (P * X * P) * (P * A i)
                = (A i)ᴴ * ((P * X * P) * P) * A i := by
                    simp [Matrix.mul_assoc]
            _ = (A i)ᴴ * (P * X * P) * A i := by
                    simp [Matrix.mul_assoc, hP.2]

namespace MPSTensor

variable {d D m : ℕ}

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
      (Finset.sum_range_succ (fun j : ℕ => f (j + 1)) (m - 1)).symm
  have hshift :
      Finset.sum (Finset.range m) (fun j : ℕ => f (j + 1)) =
        Finset.sum (Finset.range m) (fun j : ℕ => f j) := by
    rw [← hdecomp_left, ← hdecomp_right]
    simp [f, hQfix]
  change T (∑ l : Fin m, (T ^ (l : ℕ)) Q) = ∑ l : Fin m, (T ^ (l : ℕ)) Q
  calc
    T (∑ l : Fin m, (T ^ (l : ℕ)) Q)
        = ∑ l : Fin m, T (((T ^ (l : ℕ)) Q)) := by
            rw [map_sum]
    _ = ∑ l : Fin m, (T ^ ((l : ℕ) + 1)) Q := by
            refine Finset.sum_congr rfl ?_
            intro l _
            simp [pow_succ']
    _ = ∑ j ∈ Finset.range m, f (j + 1) := by
          simpa [f] using
            (Fin.sum_univ_eq_sum_range (fun n : ℕ => (T ^ (n + 1)) Q) m)
    _ = ∑ j ∈ Finset.range m, f j := by
          simpa using hshift
    _ = ∑ l : Fin m, (T ^ (l : ℕ)) Q := by
          simpa [f] using
            (Fin.sum_univ_eq_sum_range (fun n : ℕ => (T ^ n) Q) m).symm

/-- If `Q` is supported on the cyclic sector `P k`, then its `l`-th orbit iterate is supported
on the shifted sector `P (k - l)`.

The proof is a direct induction on `l`, using the same left/right multiplicative-domain
identities that appear in `preserves_corner_pow_of_cyclic_decomp`. -/
theorem orbit_iterate_supported_on_shifted_sector
    [NeZero m]
    {T : MatrixEnd D}
    (P : Fin m → MatrixAlg D)
    (hcyclic : ∀ k : Fin m, T (P (k + 1)) = P k)
    (hMulLeft : ∀ k : Fin m, ∀ X : MatrixAlg D, T (P k * X) = T (P k) * T X)
    (hMulRight : ∀ k : Fin m, ∀ X : MatrixAlg D, T (X * P k) = T X * T (P k))
    {k : Fin m} {Q : MatrixAlg D}
    (hQP : Q * P k = Q)
    (hPQ : P k * Q = Q) :
    ∀ l : Fin m,
      ((T ^ (l : ℕ)) Q) * P (k - l) = ((T ^ (l : ℕ)) Q) ∧
      P (k - l) * ((T ^ (l : ℕ)) Q) = ((T ^ (l : ℕ)) Q) := by
  suffices hmain :
      ∀ n : ℕ, ∀ hn : n < m,
        ((T ^ n) Q) * P (k - ⟨n, hn⟩) = ((T ^ n) Q) ∧
        P (k - ⟨n, hn⟩) * ((T ^ n) Q) = ((T ^ n) Q) by
    intro l
    simpa using hmain (l : ℕ) l.is_lt
  intro n
  induction n with
  | zero =>
      intro _hn
      simpa using And.intro hQP hPQ
  | succ n ih =>
      intro hn1
      have hn : n < m := Nat.lt_of_succ_lt hn1
      let j : Fin m := k - ⟨n, hn⟩
      have hsupp := ih hn
      have hright_j : ((T ^ n) Q) * P j = ((T ^ n) Q) := by
        simpa [j] using hsupp.1
      have hleft_j : P j * ((T ^ n) Q) = ((T ^ n) Q) := by
        simpa [j] using hsupp.2
      have hcyclic_j : T (P j) = P (j - 1) := by
        simpa [j] using hcyclic (j - 1)
      have hright :
          ((T ^ (n + 1)) Q) * P (j - 1) = ((T ^ (n + 1)) Q) := by
        calc
          ((T ^ (n + 1)) Q) * P (j - 1)
              = T (((T ^ n) Q)) * P (j - 1) := by
                  simp [pow_succ']
          _ = T (((T ^ n) Q)) * T (P j) := by rw [hcyclic_j]
          _ = T (((T ^ n) Q) * P j) := by
                rw [← hMulRight j ((T ^ n) Q)]
          _ = T (((T ^ n) Q)) := by rw [hright_j]
          _ = ((T ^ (n + 1)) Q) := by
                simp [pow_succ']
      have hleft :
          P (j - 1) * ((T ^ (n + 1)) Q) = ((T ^ (n + 1)) Q) := by
        calc
          P (j - 1) * ((T ^ (n + 1)) Q)
              = T (P j) * T (((T ^ n) Q)) := by
                  rw [hcyclic_j]
                  simp [pow_succ']
          _ = T (P j * ((T ^ n) Q)) := by
                rw [← hMulLeft j ((T ^ n) Q)]
          _ = T (((T ^ n) Q)) := by rw [hleft_j]
          _ = ((T ^ (n + 1)) Q) := by
                simp [pow_succ']
      have hsucc_fin : (⟨n, hn⟩ : Fin m) + 1 = ⟨n + 1, hn1⟩ := by
        ext
        simp [Fin.val_add, Nat.mod_eq_of_lt hn1]
      have hshift : j - 1 = k - ⟨n + 1, hn1⟩ := by
        calc
          j - 1 = k - (⟨n, hn⟩ : Fin m) - 1 := by rfl
          _ = k - ((⟨n, hn⟩ : Fin m) + 1) := by abel
          _ = k - ⟨n + 1, hn1⟩ := by rw [hsucc_fin]
      simpa [hshift] using And.intro hright hleft

/-- Iterating a one-step projection-preservation statement along the cyclic sectors.

For a general linear map, corner preservation alone does not imply that the image of an
orthogonal projection is again an orthogonal projection. The hypothesis `hProjStep` isolates the
one-step input actually needed for the orbit induction. -/
theorem orbit_iterate_isOrthogonalProjection
    [NeZero m]
    {T : MatrixEnd D}
    (P : Fin m → MatrixAlg D)
    (hcyclic : ∀ k : Fin m, T (P (k + 1)) = P k)
    (hMulLeft : ∀ k : Fin m, ∀ X : MatrixAlg D, T (P k * X) = T (P k) * T X)
    (hMulRight : ∀ k : Fin m, ∀ X : MatrixAlg D, T (X * P k) = T X * T (P k))
    (hProjStep :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        IsOrthogonalProjection X →
        X * P k = X →
        P k * X = X →
        IsOrthogonalProjection (T X))
    {k : Fin m} {Q : MatrixAlg D}
    (hQproj : IsOrthogonalProjection Q)
    (hQP : Q * P k = Q)
    (hPQ : P k * Q = Q) :
    ∀ l : Fin m, IsOrthogonalProjection ((T ^ (l : ℕ)) Q) := by
  have hsupp :=
    orbit_iterate_supported_on_shifted_sector
      (P := P) hcyclic hMulLeft hMulRight (k := k) (Q := Q) hQP hPQ
  suffices hmain : ∀ n : ℕ, ∀ hn : n < m, IsOrthogonalProjection ((T ^ n) Q) by
    intro l
    simpa using hmain (l : ℕ) l.is_lt
  intro n
  induction n with
  | zero =>
      intro _hn
      simpa using hQproj
  | succ n ih =>
      intro hn1
      have hn : n < m := Nat.lt_of_succ_lt hn1
      have hproj_n : IsOrthogonalProjection ((T ^ n) Q) := ih hn
      have hsupp_n := hsupp ⟨n, hn⟩
      simpa [pow_succ'] using
        hProjStep (k - ⟨n, hn⟩) ((T ^ n) Q) hproj_n hsupp_n.1 hsupp_n.2

/-- The orbit sum of a full cyclic sector projection is the identity. -/
theorem orbitSumProjection_eq_one_of_full_sector
    [NeZero m]
    {T : MatrixEnd D}
    (P : Fin m → MatrixAlg D)
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic : ∀ k : Fin m, T (P (k + 1)) = P k)
    (k : Fin m) :
    orbitSumProjection (D := D) (m := m) T (P k) = 1 := by
  have hiter :
      ∀ l : Fin m, (T ^ (l : ℕ)) (P k) = P (k - l) := by
    suffices hmain :
        ∀ n : ℕ, ∀ hn : n < m,
          (T ^ n) (P k) = P (k - ⟨n, hn⟩) by
      intro l
      simpa using hmain (l : ℕ) l.is_lt
    intro n
    induction n with
    | zero =>
        intro _hn
        simp
    | succ n ih =>
        intro hn1
        have hn : n < m := Nat.lt_of_succ_lt hn1
        let j : Fin m := k - ⟨n, hn⟩
        have hcyclic_j : T (P j) = P (j - 1) := by
          simpa [j] using hcyclic (j - 1)
        have hsucc_fin : (⟨n, hn⟩ : Fin m) + 1 = ⟨n + 1, hn1⟩ := by
          ext
          simp [Fin.val_add, Nat.mod_eq_of_lt hn1]
        have hshift : j - 1 = k - ⟨n + 1, hn1⟩ := by
          calc
            j - 1 = k - (⟨n, hn⟩ : Fin m) - 1 := by rfl
            _ = k - ((⟨n, hn⟩ : Fin m) + 1) := by abel
            _ = k - ⟨n + 1, hn1⟩ := by rw [hsucc_fin]
        calc
          (T ^ (n + 1)) (P k) = T ((T ^ n) (P k)) := by
              simp [pow_succ']
          _ = T (P j) := by rw [ih hn]
          _ = P (j - 1) := hcyclic_j
          _ = P (k - ⟨n + 1, hn1⟩) := by rw [hshift]
  calc
    orbitSumProjection (D := D) (m := m) T (P k)
        = ∑ l : Fin m, P (k - l) := by
            refine Finset.sum_congr rfl ?_
            intro l _
            exact hiter l
    _ = ∑ j : Fin m, P j := by
          refine Fintype.sum_equiv (Equiv.subLeft k) (fun l : Fin m => P (k - l)) P ?_
          intro l
          simp [Equiv.subLeft_apply]
    _ = 1 := hPsum

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
