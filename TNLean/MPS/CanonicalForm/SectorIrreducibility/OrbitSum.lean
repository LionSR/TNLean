/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.SectorIrreducibility.ProjectionOrtho

/-!
# Sector irreducibility: orbit-sum lemmas

This file contains the orbit-sum calculations used in the
sector-irreducibility argument. Starting from cyclic sector projections, it
shows that orbit iterates stay in the expected sector, remain orthogonal
projections under the abstract one-step hypothesis `hProjStep`, and that the
full orbit sum of a cyclic sector projection is `1`.

## Main statements

* `orbitSumProjection_fixed_of_pow_fix` — the orbit sum is fixed by `T` when
  `Q` is fixed by `T^[m]`.
* `orbit_iterate_supported_on_shifted_sector` — the `l`-th iterate stays in the
  shifted sector.
* `orbit_iterate_isOrthogonalProjection` — orthogonal-projection structure is
  preserved along the orbit under `hProjStep`.
* `orbitSumProjection_eq_one_of_full_sector` — the orbit sum of a full sector
  projection is the identity.

## Tags

matrix product states, cyclic sectors, orbit sums
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset Complex

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

end MPSTensor
