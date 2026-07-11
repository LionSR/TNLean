/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Peripheral.CyclicDecomposition.Basic

/-!
# Cyclic shift of the Kraus operators across the cyclic projections

For an irreducible map with nontrivial peripheral spectrum, Wolf Theorem 6.6
produces orthogonal projections $P_0,\dots,P_{m-1}$ summing to the identity
and permuted by the map, $\mathcal E(P_{k+1}) = P_k$.  This file derives the
letter-level consequence: each Kraus operator of $\mathcal E$ intertwines
consecutive projections, $K_v P_{k+1} = P_k K_v$, so a word of length $\ell$
shifts every projection by $\ell$ steps and a word of length $m$ commutes
with each projection.

## Main statements

* `one_sub_mul_kraus_mul_eq_zero_of_transferMap_proj` — each Kraus operator
  maps the range of `P'` into the range of `P` when the map sends `P'` to `P`.
* `orthogonalProjection_mul_eq_zero_of_sum_eq_one` — orthogonal projections
  summing to the identity are mutually orthogonal.
* `kraus_mul_cyclicProj` — the letter-level cyclic shift
  `K v * P (k + 1) = P k * K v`.
* `evalWord_mul_cyclicProj` — the word-level shift
  `evalWord K w * P k = P (k - w.length) * evalWord K w`.
* `cyclicProj_ne_zero` — no cyclic projection vanishes.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.6]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Fin.NatCast
open Matrix Finset Complex

namespace MPSTensor

variable {r n m : ℕ}

/-- **Kraus operators respect a transfer-mapped projection pair.**  If the
transfer map of the Kraus family `K` sends the orthogonal projection `P'` to
the orthogonal projection `P`, then each Kraus operator maps the range of
`P'` into the range of `P`: `(1 - P) * K v * P' = 0`.

This is the letter-level step in the proof of Wolf Theorem 6.6: compressing
$\sum_v K_v P' K_v^\dagger = P$ by $1-P$ exhibits a vanishing sum of positive
semidefinite matrices, so each summand vanishes. -/
theorem one_sub_mul_kraus_mul_eq_zero_of_transferMap_proj
    (K : Fin r → MatrixAlg n) {P P' : MatrixAlg n}
    (hP : IsOrthogonalProjection P) (hP' : IsOrthogonalProjection P')
    (hmap : transferMap (d := r) (D := n) K P' = P) :
    ∀ v, (1 - P) * K v * P' = 0 := by
  classical
  set T : Fin r → MatrixAlg n := fun w => (1 - P) * K w * P' with hT
  have h1P : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.1.eq]
  -- Each `T w * (T w)ᴴ` is the `w`-th summand of `(1-P) E(P') (1-P)`.
  have hexp : ∀ w, T w * (T w)ᴴ = (1 - P) * (K w * P' * (K w)ᴴ) * (1 - P) := by
    intro w
    calc T w * (T w)ᴴ
        = (1 - P) * K w * (P' * P'ᴴ) * (K w)ᴴ * (1 - P)ᴴ := by
          simp only [hT, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (1 - P) * (K w * P' * (K w)ᴴ) * (1 - P) := by
          rw [hP'.1.eq, hP'.2, h1P]
          simp only [Matrix.mul_assoc]
  -- The sum of these PSD matrices is `(1-P) P (1-P) = 0`.
  have hsum : ∑ w : Fin r, T w * (T w)ᴴ = 0 := by
    have h1PP : (1 - P) * P = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, hP.2, sub_self]
    calc ∑ w : Fin r, T w * (T w)ᴴ
        = (1 - P) * (∑ w : Fin r, K w * P' * (K w)ᴴ) * (1 - P) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun w _ => hexp w
      _ = (1 - P) * P * (1 - P) := by
          rw [show ∑ w : Fin r, K w * P' * (K w)ᴴ = P from by
            simpa [transferMap_apply] using hmap]
      _ = 0 := by rw [h1PP, Matrix.zero_mul]
  -- Trace positivity extracts each summand.
  intro v
  have htr_sum : ∑ w : Fin r, (T w * (T w)ᴴ).trace = 0 := by
    rw [← Matrix.trace_sum, hsum, Matrix.trace_zero]
  have htr : (T v * (T v)ᴴ).trace = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun w _ =>
      (Matrix.posSemidef_self_mul_conjTranspose (T w)).trace_nonneg).mp
      htr_sum v (Finset.mem_univ v)
  exact Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp htr

/-- **Orthogonal projections summing to the identity are mutually
orthogonal**: `P k * P l = 0` for `k ≠ l`.  Compressing the resolution of the
identity by `P k` exhibits a vanishing sum of positive semidefinite
matrices. -/
theorem orthogonalProjection_mul_eq_zero_of_sum_eq_one
    (P : Fin m → MatrixAlg n)
    (hproj : ∀ k, IsOrthogonalProjection (P k))
    (hsum : ∑ k : Fin m, P k = 1) :
    ∀ {k l : Fin m}, k ≠ l → P k * P l = 0 := by
  classical
  -- It suffices to prove `P l * P k = 0` for `l ≠ k` and take adjoints.
  suffices h : ∀ k l : Fin m, k ≠ l → P l * P k = 0 by
    intro k l hkl
    have := congrArg Matrix.conjTranspose (h k l hkl)
    simpa [Matrix.conjTranspose_mul, (hproj k).1.eq, (hproj l).1.eq] using this
  intro k l hkl
  -- `∑ j ≠ k, P k P j P k = P k - P k = 0`, a vanishing sum of PSD matrices.
  have hzero : ∑ j ∈ Finset.univ.erase k, P k * P j * P k = 0 := by
    have hfull : ∑ j : Fin m, P k * P j * P k = P k := by
      calc ∑ j : Fin m, P k * P j * P k
          = P k * (∑ j : Fin m, P j) * P k := by
            rw [Finset.mul_sum, Finset.sum_mul]
        _ = P k := by rw [hsum, Matrix.mul_one, (hproj k).2]
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun j => P k * P j * P k) (Finset.mem_univ k)
    rw [hfull] at hsplit
    have hkk : P k * P k * P k = P k := by rw [(hproj k).2, (hproj k).2]
    rw [hkk] at hsplit
    have hsplit' : P k + ∑ j ∈ Finset.univ.erase k, P k * P j * P k = P k + 0 := by
      rw [add_zero]; exact hsplit
    exact add_left_cancel hsplit'
  -- Each summand is `(P j P k)ᴴ (P j P k)`, hence PSD with nonnegative trace.
  have hexp : ∀ j, P k * P j * P k = (P j * P k)ᴴ * (P j * P k) := by
    intro j
    rw [Matrix.conjTranspose_mul, (hproj j).1.eq, (hproj k).1.eq]
    calc P k * P j * P k = P k * (P j * P j) * P k := by rw [(hproj j).2]
      _ = P k * P j * (P j * P k) := by simp only [Matrix.mul_assoc]
  have htr_sum : ∑ j ∈ Finset.univ.erase k, ((P j * P k)ᴴ * (P j * P k)).trace = 0 := by
    rw [← Matrix.trace_sum, ← Finset.sum_congr rfl fun j _ => hexp j, hzero,
      Matrix.trace_zero]
  have htr : ((P l * P k)ᴴ * (P l * P k)).trace = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      (Matrix.posSemidef_conjTranspose_mul_self (P j * P k)).trace_nonneg).mp
      htr_sum l (Finset.mem_erase.mpr ⟨Ne.symm hkl, Finset.mem_univ l⟩)
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr

variable [NeZero m]

/-- **Letter-level cyclic shift** (Wolf Theorem 6.6).  For a cyclic family of
orthogonal projections summing to the identity and permuted by the transfer
map, `E(P (k+1)) = P k`, each Kraus operator intertwines consecutive
projections: `K v * P (k + 1) = P k * K v`. -/
theorem kraus_mul_cyclicProj
    (K : Fin r → MatrixAlg n) (P : Fin m → MatrixAlg n)
    (hproj : ∀ k, IsOrthogonalProjection (P k))
    (hsum : ∑ k : Fin m, P k = 1)
    (hcyclic : ∀ k : Fin m, transferMap (d := r) (D := n) K (P (k + 1)) = P k) :
    ∀ (v : Fin r) (k : Fin m), K v * P (k + 1) = P k * K v := by
  intro v k
  -- One-sided containment for every consecutive pair.
  have hinto : ∀ j : Fin m, K v * P (j + 1) = P j * (K v * P (j + 1)) := by
    intro j
    have h := one_sub_mul_kraus_mul_eq_zero_of_transferMap_proj K
      (hproj j) (hproj (j + 1)) (hcyclic j) v
    have h' : K v * P (j + 1) - P j * (K v * P (j + 1)) = 0 := by
      calc K v * P (j + 1) - P j * (K v * P (j + 1))
          = (1 - P j) * K v * P (j + 1) := by
            rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
        _ = 0 := h
    exact sub_eq_zero.mp h'
  -- Off-diagonal compressions vanish: `P j * K v * P (l+1) = 0` for `j ≠ l`.
  have hoff : ∀ j l : Fin m, j ≠ l → P j * (K v * P (l + 1)) = 0 := by
    intro j l hjl
    rw [hinto l, ← Matrix.mul_assoc,
      orthogonalProjection_mul_eq_zero_of_sum_eq_one P hproj hsum hjl,
      Matrix.zero_mul]
  -- Expand `P k * K v` through the resolution of the identity.
  have hone : (∑ l : Fin m, P (l + 1)) = 1 := by
    rw [← hsum]
    exact Fintype.sum_equiv (Equiv.addRight (1 : Fin m)) _ _ fun l => rfl
  have hexpand : P k * K v = ∑ l : Fin m, P k * (K v * P (l + 1)) := by
    calc P k * K v
        = (P k * K v) * (∑ l : Fin m, P (l + 1)) := by rw [hone, Matrix.mul_one]
      _ = ∑ l : Fin m, P k * (K v * P (l + 1)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by rw [Matrix.mul_assoc]
  rw [hexpand, Finset.sum_eq_single k (fun l _ hlk => hoff k l (Ne.symm hlk))
    (fun h => absurd (Finset.mem_univ k) h)]
  exact hinto k

/-- **Word-level cyclic shift**: a word of length `ℓ` moves each cyclic
projection back by `ℓ` steps, `evalWord K w * P k = P (k - ℓ) * evalWord K w`.
In particular a word of length `m` commutes with every cyclic projection. -/
theorem evalWord_mul_cyclicProj
    (K : Fin r → MatrixAlg n) (P : Fin m → MatrixAlg n)
    (hproj : ∀ k, IsOrthogonalProjection (P k))
    (hsum : ∑ k : Fin m, P k = 1)
    (hcyclic : ∀ k : Fin m, transferMap (d := r) (D := n) K (P (k + 1)) = P k) :
    ∀ (w : List (Fin r)) (k : Fin m),
      evalWord K w * P k = P (k - (w.length : Fin m)) * evalWord K w := by
  intro w
  induction w with
  | nil =>
    intro k
    simp
  | cons v w ih =>
    intro k
    have hstep : K v * P (k - (w.length : Fin m)) =
        P (k - (w.length : Fin m) - 1) * K v := by
      have := kraus_mul_cyclicProj K P hproj hsum hcyclic v (k - (w.length : Fin m) - 1)
      rwa [sub_add_cancel] at this
    calc evalWord K (v :: w) * P k
        = K v * (evalWord K w * P k) := by rw [evalWord_cons, Matrix.mul_assoc]
      _ = K v * (P (k - (w.length : Fin m)) * evalWord K w) := by rw [ih k]
      _ = (K v * P (k - (w.length : Fin m))) * evalWord K w := by
          rw [Matrix.mul_assoc]
      _ = P (k - (w.length : Fin m) - 1) * (K v * evalWord K w) := by
          rw [hstep, Matrix.mul_assoc]
      _ = P (k - ((v :: w).length : Fin m)) * evalWord K (v :: w) := by
          rw [evalWord_cons]
          congr 2
          rw [List.length_cons, Nat.cast_add, Nat.cast_one, sub_sub]

/-- **No cyclic projection vanishes.**  If one projection of a cyclic family
summing to the identity vanished, the cyclic action `E(P (k+1)) = P k` would
propagate the vanishing to every projection, contradicting the resolution of
the identity. -/
theorem cyclicProj_ne_zero [NeZero n]
    (K : Fin r → MatrixAlg n) (P : Fin m → MatrixAlg n)
    (hsum : ∑ k : Fin m, P k = 1)
    (hcyclic : ∀ k : Fin m, transferMap (d := r) (D := n) K (P (k + 1)) = P k) :
    ∀ k : Fin m, P k ≠ 0 := by
  by_contra! h
  obtain ⟨k₀, hk₀⟩ := h
  -- Vanishing propagates backwards through the cyclic action.
  have hback : ∀ j : Fin m, P (j + 1) = 0 → P j = 0 := fun j hj => by
    rw [← hcyclic j, hj, map_zero]
  -- Every projection vanishes: induct on the backward distance to `k₀`.
  have hall : ∀ j : Fin m, P j = 0 := by
    suffices hs : ∀ N : ℕ, N < m → ∀ j : Fin m, (k₀ - j).val = N → P j = 0 by
      intro j
      exact hs _ (k₀ - j).isLt j rfl
    intro N
    induction N with
    | zero =>
      intro _ j hj
      have hj0 : k₀ - j = 0 := by
        ext
        simpa using hj
      have : k₀ = j := by
        have := sub_eq_zero.mp hj0
        exact this
      subst this
      exact hk₀
    | succ N ih =>
      intro hN j hj
      apply hback j
      apply ih (by omega) (j + 1)
      have h_eq : k₀ - (j + 1) = (k₀ - j) - 1 := by abel
      rw [h_eq, Fin.val_sub_one_of_ne_zero (by intro h0; simp [h0] at hj)]
      omega
  have hzero : (1 : MatrixAlg n) = 0 := by
    rw [← hsum]
    exact Finset.sum_eq_zero fun k _ => hall k
  exact one_ne_zero (α := ℂ) (by
    simpa using congrFun (congrFun hzero ⟨0, NeZero.pos n⟩) ⟨0, NeZero.pos n⟩)

end MPSTensor
