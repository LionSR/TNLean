/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Peripheral.CyclicDecomposition.Basic

/-!
# Cyclic projections of a finite-order peripheral unitary

This file constructs the Fourier spectral projections attached to a unitary of
finite order and states their cyclic behavior under a linear map.

## Main statements

* `exists_cyclic_projections_of_peripheral_unitary` — the cyclic projection
  family associated with a finite-order peripheral unitary.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.6]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

section CyclicProjections

variable {D m : ℕ} [NeZero m]

/-- The Fourier-type spectral projection associated with the `k`-th peripheral phase. -/
private noncomputable def cyclicProjection {γ : ℂ}
    (U : Matrix.unitaryGroup (Fin D) ℂ) (k : Fin m) : MatrixAlg D :=
  ((↑m : ℂ)⁻¹) • Finset.sum (Finset.range m)
    (fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j))

/-- Index of `(1 : Fin m)` as a natural number; used as the "next cyclic step" index. -/
private abbrev cyclicOneIdx (m : ℕ) [NeZero m] : ℕ := ((1 : Fin m) : ℕ)

/-- A primitive root has unit modulus, written as `star γ * γ = 1`. -/
private lemma star_mul_self_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m) :
    star γ * γ = 1 := by
  have hm0 : m ≠ 0 := NeZero.ne m
  have hγ_norm : ‖γ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hγprim.pow_eq_one hm0
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  simp only [normSq_eq_norm_sq, hγ_norm, one_pow, ofReal_one]

/-- A primitive root has unit modulus, written as `γ * star γ = 1`. -/
private lemma self_mul_star_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m) :
    γ * star γ = 1 := by
  simpa [mul_comm] using star_mul_self_of_primitiveRoot (m := m) hγprim

/-- For a primitive root, complex conjugation agrees with inversion. -/
private lemma star_eq_inv_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m) :
    star γ = γ⁻¹ := by
  exact eq_inv_of_mul_eq_one_right (self_mul_star_of_primitiveRoot (m := m) hγprim)

/-- The phase `γ ^ n` cancels against its conjugate power. -/
private lemma pow_mul_star_pow_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (n : ℕ) : γ ^ n * (star γ) ^ n = 1 := by
  simpa [mul_pow] using congrArg (fun z : ℂ => z ^ n)
    (self_mul_star_of_primitiveRoot (m := m) hγprim)

/-- The conjugate phase `(star γ) ^ n` cancels against `γ ^ n`. -/
private lemma star_pow_mul_pow_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (n : ℕ) : (star γ) ^ n * γ ^ n = 1 := by
  simpa [mul_pow] using congrArg (fun z : ℂ => z ^ n)
    (star_mul_self_of_primitiveRoot (m := m) hγprim)

/-- The distinguished index `((1 : Fin m) : ℕ)` still represents the exponent `1`. -/
private lemma pow_oneIdx_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m) :
    γ ^ cyclicOneIdx (m := m) = γ := by
  by_cases hm1 : m = 1
  · subst hm1
    simp only [
      IsPrimitiveRoot.one_right_iff.mp hγprim, cyclicOneIdx, Fin.isValue, Fin.val_eq_zero,
      pow_zero
    ]
  · have hm0 : m ≠ 0 := NeZero.ne m
    have hm_gt : 1 < m := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hm0, hm1⟩
    simp only [cyclicOneIdx, Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt hm_gt, pow_one]

/-- The distinguished index `((1 : Fin m) : ℕ)` leaves the unitary unchanged. -/
private lemma unitary_pow_oneIdx_of_pow_eq_one
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1) :
    ((U : MatrixAlg D) ^ cyclicOneIdx (m := m)) = (U : MatrixAlg D) := by
  by_cases hm1 : m = 1
  · subst hm1
    have hUeq : (U : MatrixAlg D) = 1 := by simpa using hUm
    simp only [hUeq, cyclicOneIdx, Fin.isValue, Fin.val_eq_zero, pow_zero]
  · have hm0 : m ≠ 0 := NeZero.ne m
    have hm_gt : 1 < m := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hm0, hm1⟩
    simp only [cyclicOneIdx, Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt hm_gt, pow_one]

omit [NeZero m] in
/-- Finite geometric sums on `Fin m` collapse when the `m`-th power is `1`. -/
private lemma sum_powers_fin_of_pow_eq_one (x : ℂ) (hxpow : x ^ m = 1) :
    ∑ k : Fin m, x ^ (k : ℕ) = if x = 1 then (m : ℂ) else 0 := by
  by_cases hx : x = 1
  · subst hx
    rw [if_pos rfl, Fin.sum_univ_eq_sum_range]
    simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
  · rw [if_neg hx, Fin.sum_univ_eq_sum_range]
    have hmul : (Finset.sum (Finset.range m) fun i => x ^ i) * (x - 1) = 0 := by
      simpa [hxpow] using (geom_sum_mul x m)
    exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hx)

/-- The Fourier coefficients for the projection sum vanish away from the zero mode. -/
private lemma coeff_sum_proj_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (j : ℕ) (hj : j < m) :
    ∑ k : Fin m, ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) = if j = 0 then (m : ℂ) else 0 := by
  have hγinv_prim : IsPrimitiveRoot (γ⁻¹) m := hγprim.inv
  have hpowm : ((((star γ) ^ j : ℂ)) ^ m) = 1 := by
    calc
      ((((star γ) ^ j : ℂ)) ^ m) = (star γ : ℂ) ^ (j * m) := by rw [← pow_mul]
      _ = (star γ : ℂ) ^ (m * j) := by rw [Nat.mul_comm]
      _ = (((star γ : ℂ) ^ m) ^ j) := by rw [pow_mul]
      _ = 1 := by
          rw [star_eq_inv_of_primitiveRoot (m := m) hγprim]
          simp only [inv_pow, hγprim.pow_eq_one, inv_one, one_pow]
  have hrewrite :
      ∑ k : Fin m, ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) =
        ∑ k : Fin m, ((((star γ) ^ j) ^ (k : ℕ) : ℂ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    calc
      ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) = (star γ : ℂ) ^ ((k : ℕ) * j) := by rw [← pow_mul]
      _ = (star γ : ℂ) ^ (j * (k : ℕ)) := by rw [Nat.mul_comm]
      _ = ((((star γ) ^ j) ^ (k : ℕ) : ℂ)) := by rw [pow_mul]
  rw [hrewrite, sum_powers_fin_of_pow_eq_one (m := m) ((star γ) ^ j) hpowm]
  by_cases hj0 : j = 0
  · subst hj0
    simp only [RCLike.star_def, pow_zero, ↓reduceIte]
  · have hne : ((star γ) ^ j : ℂ) ≠ 1 := by
      intro hpow
      have hdvd : m ∣ j :=
        (hγinv_prim.pow_eq_one_iff_dvd j).mp (by
          simpa [star_eq_inv_of_primitiveRoot (m := m) hγprim] using hpow)
      exact hj0 (Nat.eq_zero_of_dvd_of_lt hdvd hj)
    rw [if_neg hne, if_neg hj0]

/-- Convert the spectral reconstruction coefficients to a finite geometric sum. -/
private lemma cyclic_projection_step1_coeff_sum_spec_geometric {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m) (j : ℕ) :
    ∑ k : Fin m, (γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) =
      if γ * (star γ) ^ j = 1 then (m : ℂ) else 0 := by
  have hpowm : (γ * (star γ) ^ j) ^ m = 1 := by
    calc
      (γ * (star γ) ^ j) ^ m = γ ^ m * ((((star γ) ^ j : ℂ)) ^ m) := by
        rw [mul_pow]
      _ = γ ^ m * (((star γ : ℂ) ^ m) ^ j) := by
        congr 1
        calc
          ((((star γ) ^ j : ℂ)) ^ m) = (star γ : ℂ) ^ (j * m) := by
            rw [← pow_mul]
          _ = (star γ : ℂ) ^ (m * j) := by
            rw [Nat.mul_comm]
          _ = (((star γ : ℂ) ^ m) ^ j) := by
            rw [pow_mul]
      _ = 1 := by
        rw [star_eq_inv_of_primitiveRoot (m := m) hγprim]
        simp only [hγprim.pow_eq_one, inv_pow, inv_one, one_pow, mul_one]
  have hrewrite :
      ∑ k : Fin m, (γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) =
        ∑ k : Fin m, (γ * (star γ) ^ j) ^ (k : ℕ) := by
    apply Finset.sum_congr rfl
    intro k hk
    calc
      γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))
          = γ ^ (k : ℕ) * ((((star γ) ^ j) ^ (k : ℕ) : ℂ)) := by
              congr 1
              calc
                ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) =
                    (star γ : ℂ) ^ ((k : ℕ) * j) := by
                  rw [← pow_mul]
                _ = (star γ : ℂ) ^ (j * (k : ℕ)) := by
                  rw [Nat.mul_comm]
                _ = ((((star γ) ^ j) ^ (k : ℕ) : ℂ)) := by
                  rw [pow_mul]
      _ = (γ * (star γ) ^ j) ^ (k : ℕ) := by
        rw [mul_pow]
  rw [hrewrite, sum_powers_fin_of_pow_eq_one (m := m) (γ * (star γ) ^ j) hpowm]

/-- The Fourier coefficients for the spectral expansion isolate the `oneIdx` mode. -/
private lemma coeff_sum_spec_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (j : ℕ) (hj : j < m) :
    ∑ k : Fin m, (γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) =
      if j = cyclicOneIdx (m := m) then (m : ℂ) else 0 := by
  have honeIdx_lt : cyclicOneIdx (m := m) < m := by
    simpa [cyclicOneIdx] using ((1 : Fin m).is_lt)
  have honeIdx_mem : cyclicOneIdx (m := m) ∈ Finset.range m := by
    exact Finset.mem_range.mpr honeIdx_lt
  rw [cyclic_projection_step1_coeff_sum_spec_geometric (m := m) hγprim j]
  by_cases hjeq : j = cyclicOneIdx (m := m)
  · subst hjeq
    have hx : γ * (star γ) ^ cyclicOneIdx (m := m) = 1 := by
      calc
        γ * (star γ) ^ cyclicOneIdx (m := m) =
            γ ^ cyclicOneIdx (m := m) * (star γ) ^ cyclicOneIdx (m := m) := by
          rw [pow_oneIdx_of_primitiveRoot (m := m) hγprim]
        _ = 1 := pow_mul_star_pow_of_primitiveRoot (m := m) hγprim (cyclicOneIdx (m := m))
    rw [if_pos hx, if_pos rfl]
  · have hne : γ * (star γ) ^ j ≠ 1 := by
      intro hx
      have hpoweq : γ ^ cyclicOneIdx (m := m) = γ ^ j := by
        calc
          γ ^ cyclicOneIdx (m := m) = γ := pow_oneIdx_of_primitiveRoot (m := m) hγprim
          _ = γ * 1 := by simp only [mul_one]
          _ = γ * ((star γ) ^ j * γ ^ j) := by
                rw [star_pow_mul_pow_of_primitiveRoot (m := m) hγprim j]
          _ = (γ * (star γ) ^ j) * γ ^ j := by rw [mul_assoc]
          _ = 1 * γ ^ j := by rw [hx]
          _ = γ ^ j := by simp only [one_mul]
      have hidxeq : cyclicOneIdx (m := m) = j :=
        hγprim.injOn_pow honeIdx_mem (by simp only [coe_range, Set.mem_Iio, hj]) hpoweq
      exact hjeq hidxeq.symm
    rw [if_neg hne, if_neg hjeq]

/-- Multiplying by `γ` shifts the conjugate phase by one cyclic step. -/
private lemma base_cyclic_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (k : Fin m) : ((star γ) ^ (((k + 1 : Fin m) : ℕ)) : ℂ) * γ = (star γ) ^ (k : ℕ) := by
  have hm0 : m ≠ 0 := NeZero.ne m
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
  by_cases hk : (k : ℕ) + 1 < m
  · have hval : (((k + 1 : Fin m) : ℕ)) = (k : ℕ) + 1 := by
      simp only [Fin.val_add, Fin.coe_ofNat_eq_mod, Nat.add_mod_mod, Nat.mod_eq_of_lt hk]
    rw [hval, pow_succ, mul_assoc, star_mul_self_of_primitiveRoot (m := m) hγprim]
    simp only [RCLike.star_def, mul_one]
  · have hk_eq : (k : ℕ) + 1 = m := by
      have hle : m ≤ (k : ℕ) + 1 := by
        exact Nat.le_of_not_gt (by simpa using hk)
      exact le_antisymm (Nat.succ_le_of_lt k.is_lt) hle
    have hval0 : (((k + 1 : Fin m) : ℕ)) = 0 := by
      simp only [Fin.val_add, Fin.coe_ofNat_eq_mod, Nat.add_mod_mod, hk_eq, Nat.mod_self]
    rw [hval0, pow_zero, one_mul]
    have hkval : (k : ℕ) = m - 1 := Nat.eq_sub_of_add_eq hk_eq
    rw [hkval]
    have hpowm_star : (star γ : ℂ) ^ m = 1 := by
      rw [star_eq_inv_of_primitiveRoot (m := m) hγprim]
      simp only [inv_pow, hγprim.pow_eq_one, inv_one]
    have hmul : (star γ : ℂ) ^ (m - 1) * star γ = 1 := by
      calc
        (star γ : ℂ) ^ (m - 1) * star γ = (star γ : ℂ) ^ ((m - 1) + 1) := by
          simp only [RCLike.star_def, pow_succ]
        _ = 1 := by
          have hm' : (m - 1) + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
          simpa [hm'] using hpowm_star
    have hpred : (star γ : ℂ) ^ (m - 1) = γ := by
      calc
        (star γ : ℂ) ^ (m - 1) = (star γ : ℂ)⁻¹ := eq_inv_of_mul_eq_one_left hmul
        _ = γ := by rw [star_eq_inv_of_primitiveRoot (m := m) hγprim, inv_inv]
    simpa using hpred.symm

/-- The cyclic projections are permuted by the peripheral map. -/
private lemma cyclic_action_of_cyclicProjection
    (T : MatrixEnd D) {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ)
    (hPow : ∀ k : ℕ, T ((U : MatrixAlg D) ^ k) = γ ^ k • ((U : MatrixAlg D) ^ k)) :
    ∀ k : Fin m, T (cyclicProjection (m := m) (γ := γ) U (k + 1)) =
      cyclicProjection (m := m) (γ := γ) U k := by
  intro k
  dsimp [cyclicProjection]
  calc
    T (((↑m : ℂ)⁻¹) • Finset.sum (Finset.range m)
        (fun j => ((((star γ) ^ (((k + 1 : Fin m) : ℕ))) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)))
        = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
            (fun j => ((((star γ) ^ (((k + 1 : Fin m) : ℕ))) ^ j : ℂ)) •
              T ((U : MatrixAlg D) ^ j)) := by
            simp only [RCLike.star_def, map_smul, map_sum]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j => (((((star γ) ^ (((k + 1 : Fin m) : ℕ))) ^ j : ℂ) * γ ^ j)) •
            ((U : MatrixAlg D) ^ j)) := by
          congr 2
          ext j
          rw [hPow j, smul_smul]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)) := by
          congr 2
          ext j
          have hcoef :
              ((((star γ) ^ (((k + 1 : Fin m) : ℕ))) ^ j : ℂ) * γ ^ j) =
                ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) := by
            calc
              ((((star γ) ^ (((k + 1 : Fin m) : ℕ))) ^ j : ℂ) * γ ^ j)
                  = ((((star γ) ^ (((k + 1 : Fin m) : ℕ)) : ℂ) * γ) ^ j : ℂ) := by
                      rw [← mul_pow]
              _ = ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) := by
                      rw [base_cyclic_of_primitiveRoot (m := m) hγprim k]
          rw [hcoef]

/-- The coefficients in the spectral sum satisfy the recursive step relation. -/
private lemma coeff_step_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (k : Fin m) (j : ℕ) :
    γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ (j + 1) : ℂ)) =
      ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) := by
  calc
    γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ (j + 1) : ℂ))
        = γ ^ (k : ℕ) * (((star γ) ^ (k : ℕ)) * (((star γ) ^ (k : ℕ)) ^ j)) := by
            rw [pow_succ']
    _ = (γ ^ (k : ℕ) * ((star γ) ^ (k : ℕ))) * (((star γ) ^ (k : ℕ)) ^ j) := by
            rw [mul_assoc]
    _ = ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) := by
            rw [pow_mul_star_pow_of_primitiveRoot (m := m) hγprim (k : ℕ)]
            simp only [RCLike.star_def, one_mul]

/-- The last coefficient in the spectral sum closes the cyclic recursion. -/
private lemma coeff_last_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (k : Fin m) : ((((star γ) ^ (k : ℕ)) ^ (m - 1) : ℂ)) = γ ^ (k : ℕ) := by
  have hm0 : m ≠ 0 := NeZero.ne m
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
  have hpowm : ((((star γ) ^ (k : ℕ) : ℂ)) ^ m) = 1 := by
    calc
      ((((star γ) ^ (k : ℕ) : ℂ)) ^ m) = (star γ : ℂ) ^ ((k : ℕ) * m) := by rw [← pow_mul]
      _ = (star γ : ℂ) ^ (m * (k : ℕ)) := by rw [Nat.mul_comm]
      _ = (((star γ : ℂ) ^ m) ^ (k : ℕ)) := by rw [pow_mul]
      _ = 1 := by
          rw [star_eq_inv_of_primitiveRoot (m := m) hγprim]
          simp only [inv_pow, hγprim.pow_eq_one, inv_one, one_pow]
  have hmul : ((((star γ) ^ (k : ℕ) : ℂ)) ^ (m - 1)) * ((star γ) ^ (k : ℕ)) = 1 := by
    calc
      ((((star γ) ^ (k : ℕ) : ℂ)) ^ (m - 1)) * ((star γ) ^ (k : ℕ))
          = (((star γ) ^ (k : ℕ) : ℂ)) ^ ((m - 1) + 1) := by
              simp only [RCLike.star_def, pow_succ]
      _ = 1 := by
          have hm' : (m - 1) + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
          simpa [hm'] using hpowm
  calc
    ((((star γ) ^ (k : ℕ) : ℂ)) ^ (m - 1)) = (((star γ) ^ (k : ℕ) : ℂ))⁻¹ :=
      eq_inv_of_mul_eq_one_left hmul
    _ = γ ^ (k : ℕ) := by
      rw [star_eq_inv_of_primitiveRoot (m := m) hγprim, inv_pow]
      simp only [inv_inv]

/-- Move the unitary through the Fourier sum, leaving the cyclically shifted coefficients. -/
private lemma cyclic_projection_step2_left_mul_shifted_sum {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1)
    (k : Fin m) :
    (U : MatrixAlg D) * cyclicProjection (m := m) (γ := γ) U k =
      (↑m : ℂ)⁻¹ •
        (Finset.sum (Finset.range (m - 1))
            (fun j => (γ ^ (k : ℕ) *
              ((((star γ) ^ (k : ℕ)) ^ (j + 1) : ℂ))) •
                ((U : MatrixAlg D) ^ (j + 1))) +
          γ ^ (k : ℕ) • (1 : MatrixAlg D)) := by
  let a : ℕ → ℂ := fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ))
  have hm0 : m ≠ 0 := NeZero.ne m
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
  have hm_pred_succ : (m - 1) + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
  dsimp [cyclicProjection]
  change
    (U : MatrixAlg D) *
        ((↑m : ℂ)⁻¹ • Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ j))) =
      (↑m : ℂ)⁻¹ •
        (Finset.sum (Finset.range (m - 1))
            (fun j => (γ ^ (k : ℕ) * a (j + 1)) • ((U : MatrixAlg D) ^ (j + 1))) +
          γ ^ (k : ℕ) • (1 : MatrixAlg D))
  calc
    (U : MatrixAlg D) *
        ((↑m : ℂ)⁻¹ • Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ j)))
        = (↑m : ℂ)⁻¹ •
            ((U : MatrixAlg D) *
              Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ j))) := by
              rw [Matrix.mul_smul]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j => a j • ((U : MatrixAlg D) * ((U : MatrixAlg D) ^ j))) := by
          congr 1
          simp only [mul_sum, Algebra.mul_smul_comm]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j => a j • ((U : MatrixAlg D) ^ (j + 1))) := by
          congr 2
          ext j
          rw [pow_succ']
    _ = (↑m : ℂ)⁻¹ •
          (Finset.sum (Finset.range (m - 1)) (fun j => a j • ((U : MatrixAlg D) ^ (j + 1))) +
            a (m - 1) • ((U : MatrixAlg D) ^ m)) := by
          have hsplit :
              Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ (j + 1))) =
                Finset.sum (Finset.range (m - 1))
                  (fun j => a j • ((U : MatrixAlg D) ^ (j + 1))) +
                  a (m - 1) • ((U : MatrixAlg D) ^ m) := by
            simpa [hm_pred_succ] using
              (Finset.sum_range_succ
                (fun j : ℕ => a j • ((U : MatrixAlg D) ^ (j + 1)))
                (m - 1))
          rw [hsplit]
    _ = (↑m : ℂ)⁻¹ •
          (Finset.sum (Finset.range (m - 1))
              (fun j => (γ ^ (k : ℕ) * a (j + 1)) • ((U : MatrixAlg D) ^ (j + 1))) +
            γ ^ (k : ℕ) • (1 : MatrixAlg D)) := by
          congr 2
          · apply Finset.sum_congr rfl
            intro j hj
            have ha : a j = γ ^ (k : ℕ) * a (j + 1) := by
              dsimp [a]
              exact (coeff_step_of_primitiveRoot (m := m) hγprim k j).symm
            rw [ha]
          · change
              ((((star γ) ^ (k : ℕ)) ^ (m - 1) : ℂ)) • ((U : MatrixAlg D) ^ m) =
                γ ^ (k : ℕ) • (1 : MatrixAlg D)
            rw [coeff_last_of_primitiveRoot (m := m) hγprim k, hUm]

/-- Reassemble the shifted Fourier sum as scalar multiplication of the cyclic projection. -/
private lemma cyclic_projection_step3_shifted_sum_eq_smul {γ : ℂ}
    (U : Matrix.unitaryGroup (Fin D) ℂ) (k : Fin m) :
    (↑m : ℂ)⁻¹ •
      (Finset.sum (Finset.range (m - 1))
          (fun j => (γ ^ (k : ℕ) *
            ((((star γ) ^ (k : ℕ)) ^ (j + 1) : ℂ))) •
              ((U : MatrixAlg D) ^ (j + 1))) +
        γ ^ (k : ℕ) • (1 : MatrixAlg D)) =
      γ ^ (k : ℕ) • cyclicProjection (m := m) (γ := γ) U k := by
  let a : ℕ → ℂ := fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ))
  have hm0 : m ≠ 0 := NeZero.ne m
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
  have hm_pred_succ : (m - 1) + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
  have hdecomp :
      Finset.sum (Finset.range (m - 1))
          (fun j => a (j + 1) • ((U : MatrixAlg D) ^ (j + 1))) + 1 =
        Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ j)) := by
    simpa [hm_pred_succ, a] using
      (Finset.sum_range_succ' (fun j : ℕ => a j • ((U : MatrixAlg D) ^ j)) (m - 1)).symm
  have hfactor :
      Finset.sum (Finset.range (m - 1))
          (fun j => (γ ^ (k : ℕ) * a (j + 1)) • ((U : MatrixAlg D) ^ (j + 1))) =
        γ ^ (k : ℕ) • Finset.sum (Finset.range (m - 1))
          (fun j => a (j + 1) • ((U : MatrixAlg D) ^ (j + 1))) := by
    calc
      Finset.sum (Finset.range (m - 1))
          (fun j => (γ ^ (k : ℕ) * a (j + 1)) • ((U : MatrixAlg D) ^ (j + 1)))
          = Finset.sum (Finset.range (m - 1))
              (fun j => γ ^ (k : ℕ) • (a (j + 1) • ((U : MatrixAlg D) ^ (j + 1)))) := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [smul_smul]
      _ = γ ^ (k : ℕ) • Finset.sum (Finset.range (m - 1))
              (fun j => a (j + 1) • ((U : MatrixAlg D) ^ (j + 1))) := by
                rw [Finset.smul_sum]
  dsimp [cyclicProjection]
  change
    (↑m : ℂ)⁻¹ •
      (Finset.sum (Finset.range (m - 1))
          (fun j => (γ ^ (k : ℕ) * a (j + 1)) • ((U : MatrixAlg D) ^ (j + 1))) +
        γ ^ (k : ℕ) • (1 : MatrixAlg D)) =
      γ ^ (k : ℕ) •
        ((↑m : ℂ)⁻¹ • Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ j)))
  calc
    (↑m : ℂ)⁻¹ •
        (Finset.sum (Finset.range (m - 1))
            (fun j => (γ ^ (k : ℕ) * a (j + 1)) • ((U : MatrixAlg D) ^ (j + 1))) +
          γ ^ (k : ℕ) • (1 : MatrixAlg D))
        = (↑m : ℂ)⁻¹ •
          (γ ^ (k : ℕ) •
            (Finset.sum (Finset.range (m - 1))
                (fun j => a (j + 1) • ((U : MatrixAlg D) ^ (j + 1))) +
              1)) := by
          rw [hfactor, smul_add]
          simp only [smul_smul, smul_add]
    _ = (↑m : ℂ)⁻¹ •
          (γ ^ (k : ℕ) •
            Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ j))) := by
          rw [hdecomp]
    _ = γ ^ (k : ℕ) •
          ((↑m : ℂ)⁻¹ •
            Finset.sum (Finset.range m) (fun j => a j • ((U : MatrixAlg D) ^ j))) := by
          simp only [smul_smul, mul_comm]

/-- Left multiplication by `U` diagonalizes on the cyclic projections. -/
private lemma left_mul_cyclicProjection_eq {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1) :
    ∀ k : Fin m,
      (U : MatrixAlg D) * cyclicProjection (m := m) (γ := γ) U k =
        γ ^ (k : ℕ) • cyclicProjection (m := m) (γ := γ) U k := by
  intro k
  calc
    (U : MatrixAlg D) * cyclicProjection (m := m) (γ := γ) U k =
        (↑m : ℂ)⁻¹ •
          (Finset.sum (Finset.range (m - 1))
              (fun j => (γ ^ (k : ℕ) *
                ((((star γ) ^ (k : ℕ)) ^ (j + 1) : ℂ))) •
                  ((U : MatrixAlg D) ^ (j + 1))) +
            γ ^ (k : ℕ) • (1 : MatrixAlg D)) := by
          exact cyclic_projection_step2_left_mul_shifted_sum (m := m) hγprim U hUm k
    _ = γ ^ (k : ℕ) • cyclicProjection (m := m) (γ := γ) U k := by
          exact cyclic_projection_step3_shifted_sum_eq_smul (m := m) (γ := γ) U k

omit [NeZero m] in
/-- Each cyclic projection commutes with the generating unitary. -/
private lemma commute_unitary_cyclicProjection {γ : ℂ}
    (U : Matrix.unitaryGroup (Fin D) ℂ) :
    ∀ k : Fin m, Commute (U : MatrixAlg D) (cyclicProjection (m := m) (γ := γ) U k) := by
  intro k
  dsimp [cyclicProjection]
  refine (Commute.sum_right (Finset.range m)
    (fun j : ℕ => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j))
    (U : MatrixAlg D) ?_).smul_right ((↑m : ℂ)⁻¹)
  intro j hj
  exact ((Commute.refl (U : MatrixAlg D)).pow_right j).smul_right _

/-- Right multiplication by `U` has the same eigenvalue on each cyclic projection. -/
private lemma right_mul_cyclicProjection_eq {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1) :
    ∀ k : Fin m,
      cyclicProjection (m := m) (γ := γ) U k * (U : MatrixAlg D) =
        γ ^ (k : ℕ) • cyclicProjection (m := m) (γ := γ) U k := by
  intro k
  rw [← (commute_unitary_cyclicProjection (m := m) (γ := γ) U k).eq]
  exact left_mul_cyclicProjection_eq (m := m) hγprim U hUm k

/-- The cyclic projections sum to the identity. -/
private lemma sum_cyclicProjection_eq_one {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) :
    ∑ k : Fin m, cyclicProjection (m := m) (γ := γ) U k = 1 := by
  dsimp [cyclicProjection]
  calc
    ∑ k : Fin m, (↑m : ℂ)⁻¹ •
        Finset.sum (Finset.range m)
          (fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j))
        = (↑m : ℂ)⁻¹ • ∑ k : Fin m,
            Finset.sum (Finset.range m)
              (fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)) := by
            symm
            rw [Finset.smul_sum]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j =>
            ∑ k : Fin m, ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)) := by
          refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
          rw [Finset.sum_comm]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j =>
            (∑ k : Fin m, ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) • ((U : MatrixAlg D) ^ j)) := by
          refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Finset.sum_smul]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j => (if j = 0 then (m : ℂ) else 0) • ((U : MatrixAlg D) ^ j)) := by
          refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
          apply Finset.sum_congr rfl
          intro j hj
          rw [coeff_sum_proj_of_primitiveRoot (m := m) hγprim j (Finset.mem_range.mp hj)]
    _ = (↑m : ℂ)⁻¹ • ((m : ℂ) • ((U : MatrixAlg D) ^ 0)) := by
          rw [Finset.sum_eq_single 0]
          · simp only [↓reduceIte, pow_zero]
          · intro j hj hj0
            simp only [hj0, ↓reduceIte, zero_smul]
          · intro hm
            exfalso
            have hm0 : m ≠ 0 := NeZero.ne m
            exact hm (by simp only [mem_range, Nat.pos_of_ne_zero hm0])
    _ = 1 := by
          simp only [
            pow_zero, ne_eq, Nat.cast_eq_zero, NeZero.ne m, not_false_eq_true,
            inv_smul_smul₀
          ]

/-- Summing the cyclic projections against their phases reconstructs `U`. -/
private lemma unitary_eq_sum_cyclicProjection {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1) :
    ∑ k : Fin m, γ ^ (k : ℕ) • cyclicProjection (m := m) (γ := γ) U k = (U : MatrixAlg D) := by
  have honeIdx_lt : cyclicOneIdx (m := m) < m := by
    simpa [cyclicOneIdx] using ((1 : Fin m).is_lt)
  have honeIdx_mem : cyclicOneIdx (m := m) ∈ Finset.range m := by
    exact Finset.mem_range.mpr honeIdx_lt
  dsimp [cyclicProjection]
  calc
    ∑ k : Fin m, γ ^ (k : ℕ) •
        ((↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)))
        = (↑m : ℂ)⁻¹ • ∑ k : Fin m,
            Finset.sum (Finset.range m)
              (fun j =>
                (γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) •
                  ((U : MatrixAlg D) ^ j)) := by
            calc
              ∑ k : Fin m, γ ^ (k : ℕ) •
                  ((↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
                    (fun j => ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)))
                  = ∑ k : Fin m, (↑m : ℂ)⁻¹ •
                      (γ ^ (k : ℕ) • Finset.sum (Finset.range m)
                        (fun j =>
                          ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j))) := by
                      apply Finset.sum_congr rfl
                      intro k hk
                      simp only [RCLike.star_def, smul_smul, mul_comm]
              _ = (↑m : ℂ)⁻¹ • ∑ k : Fin m,
                      γ ^ (k : ℕ) • Finset.sum (Finset.range m)
                        (fun j =>
                          ((((star γ) ^ (k : ℕ)) ^ j : ℂ)) • ((U : MatrixAlg D) ^ j)) := by
                      symm
                      rw [Finset.smul_sum]
              _ = (↑m : ℂ)⁻¹ • ∑ k : Fin m,
                      Finset.sum (Finset.range m)
                        (fun j =>
                          (γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) •
                            ((U : MatrixAlg D) ^ j)) := by
                      refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
                      apply Finset.sum_congr rfl
                      intro k hk
                      rw [Finset.smul_sum]
                      apply Finset.sum_congr rfl
                      intro j hj
                      rw [smul_smul]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j =>
            ∑ k : Fin m,
              (γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) • ((U : MatrixAlg D) ^ j)) := by
          refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
          rw [Finset.sum_comm]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j =>
            (∑ k : Fin m, γ ^ (k : ℕ) * ((((star γ) ^ (k : ℕ)) ^ j : ℂ))) •
              ((U : MatrixAlg D) ^ j)) := by
          refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Finset.sum_smul]
    _ = (↑m : ℂ)⁻¹ • Finset.sum (Finset.range m)
          (fun j => (if j = cyclicOneIdx (m := m) then (m : ℂ) else 0) •
            ((U : MatrixAlg D) ^ j)) := by
          refine congrArg (fun S => (↑m : ℂ)⁻¹ • S) ?_
          apply Finset.sum_congr rfl
          intro j hj
          rw [coeff_sum_spec_of_primitiveRoot (m := m) hγprim j (Finset.mem_range.mp hj)]
    _ = (↑m : ℂ)⁻¹ • ((m : ℂ) • ((U : MatrixAlg D) ^ cyclicOneIdx (m := m))) := by
          rw [Finset.sum_eq_single (cyclicOneIdx (m := m))]
          · simp only [Fin.coe_ofNat_eq_mod, ↓reduceIte]
          · intro j hj hj0
            have hif : (if j = cyclicOneIdx (m := m) then (m : ℂ) else 0) = 0 := by
              by_cases hjeq : j = cyclicOneIdx (m := m)
              · exact (hj0 hjeq).elim
              · exact if_neg hjeq
            rw [hif]
            simp only [zero_smul]
          · intro hnot
            exact False.elim (hnot honeIdx_mem)
    _ = (U : MatrixAlg D) := by
          rw [unitary_pow_oneIdx_of_pow_eq_one (m := m) U hUm]
          simp only [ne_eq, Nat.cast_eq_zero, NeZero.ne m, not_false_eq_true, inv_smul_smul₀]

omit [NeZero m] in
/-- Distinct exponents of a primitive root stay distinct on `Fin m`. -/
private lemma pow_inj_of_primitiveRoot {γ : ℂ} (hγprim : IsPrimitiveRoot γ m) :
    ∀ {a b : Fin m}, γ ^ (a : ℕ) = γ ^ (b : ℕ) → a = b := by
  intro a b hab
  apply Fin.ext
  exact hγprim.injOn_pow
    (by simp only [coe_range, Set.mem_Iio, a.is_lt])
    (by simp only [coe_range, Set.mem_Iio, b.is_lt])
    hab

/-- The product of two cyclic projections is simultaneously a left eigenvector in both indices. -/
private lemma cyclic_projection_step4_mul_projection_eigen_relations {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1)
    (k l : Fin m) :
    (U : MatrixAlg D) *
          (cyclicProjection (m := m) (γ := γ) U k *
            cyclicProjection (m := m) (γ := γ) U l) =
        γ ^ (k : ℕ) •
          (cyclicProjection (m := m) (γ := γ) U k *
            cyclicProjection (m := m) (γ := γ) U l) ∧
      (U : MatrixAlg D) *
          (cyclicProjection (m := m) (γ := γ) U k *
            cyclicProjection (m := m) (γ := γ) U l) =
        γ ^ (l : ℕ) •
          (cyclicProjection (m := m) (γ := γ) U k *
            cyclicProjection (m := m) (γ := γ) U l) := by
  constructor
  · calc
      (U : MatrixAlg D) *
          (cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U l) =
        ((U : MatrixAlg D) * cyclicProjection (m := m) (γ := γ) U k) *
          cyclicProjection (m := m) (γ := γ) U l := by
            simp only [Matrix.mul_assoc]
      _ = (γ ^ (k : ℕ) • cyclicProjection (m := m) (γ := γ) U k) *
            cyclicProjection (m := m) (γ := γ) U l := by
              rw [left_mul_cyclicProjection_eq (m := m) hγprim U hUm k]
      _ = γ ^ (k : ℕ) •
            (cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U l) := by
            simp only [Algebra.smul_mul_assoc]
  · calc
      (U : MatrixAlg D) *
          (cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U l) =
        ((U : MatrixAlg D) * cyclicProjection (m := m) (γ := γ) U k) *
          cyclicProjection (m := m) (γ := γ) U l := by
            simp only [Matrix.mul_assoc]
      _ = (cyclicProjection (m := m) (γ := γ) U k * (U : MatrixAlg D)) *
            cyclicProjection (m := m) (γ := γ) U l := by
              rw [(commute_unitary_cyclicProjection (m := m) (γ := γ) U k).eq]
      _ = cyclicProjection (m := m) (γ := γ) U k *
            ((U : MatrixAlg D) * cyclicProjection (m := m) (γ := γ) U l) := by
              simp only [Matrix.mul_assoc]
      _ = cyclicProjection (m := m) (γ := γ) U k *
            (γ ^ (l : ℕ) • cyclicProjection (m := m) (γ := γ) U l) := by
              rw [left_mul_cyclicProjection_eq (m := m) hγprim U hUm l]
      _ = γ ^ (l : ℕ) •
            (cyclicProjection (m := m) (γ := γ) U k *
              cyclicProjection (m := m) (γ := γ) U l) := by
            simp only [Algebra.mul_smul_comm]

/-- Distinct cyclic projections are orthogonal. -/
private lemma mul_cyclicProjection_eq_zero_of_ne {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1)
    {k l : Fin m} (hkl : k ≠ l) :
    cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U l = 0 := by
  obtain ⟨hkEig, hlEig⟩ :=
    cyclic_projection_step4_mul_projection_eigen_relations (m := m) hγprim U hUm k l
  have hsub :
      (γ ^ (k : ℕ) - γ ^ (l : ℕ)) •
          (cyclicProjection (m := m) (γ := γ) U k *
            cyclicProjection (m := m) (γ := γ) U l) = 0 := by
    calc
      (γ ^ (k : ℕ) - γ ^ (l : ℕ)) •
          (cyclicProjection (m := m) (γ := γ) U k *
            cyclicProjection (m := m) (γ := γ) U l)
          = γ ^ (k : ℕ) •
              (cyclicProjection (m := m) (γ := γ) U k *
                cyclicProjection (m := m) (γ := γ) U l) -
              γ ^ (l : ℕ) •
                (cyclicProjection (m := m) (γ := γ) U k *
                  cyclicProjection (m := m) (γ := γ) U l) := by
                  simp only [sub_smul]
      _ = 0 := by rw [← hkEig, ← hlEig]; simp only [sub_self]
  have hneq : γ ^ (k : ℕ) - γ ^ (l : ℕ) ≠ 0 := by
    refine sub_ne_zero.mpr ?_
    intro hpow
    exact hkl (pow_inj_of_primitiveRoot (m := m) hγprim hpow)
  exact (smul_eq_zero.mp hsub).resolve_left hneq

/-- Each cyclic projection is idempotent. -/
private lemma idem_cyclicProjection {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1) :
    ∀ k : Fin m,
      cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U k =
        cyclicProjection (m := m) (γ := γ) U k := by
  intro k
  have hsingle :
      ∑ l : Fin m,
          cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U l =
        cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U k := by
    exact Finset.sum_eq_single_of_mem k (Finset.mem_univ k) (by
      intro l hl hne
      simpa using mul_cyclicProjection_eq_zero_of_ne (m := m) hγprim U hUm hne.symm)
  have hEq :
      cyclicProjection (m := m) (γ := γ) U k =
        cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U k := by
    calc
      cyclicProjection (m := m) (γ := γ) U k =
          cyclicProjection (m := m) (γ := γ) U k * (1 : MatrixAlg D) := by simp only [mul_one]
      _ = cyclicProjection (m := m) (γ := γ) U k *
            (∑ l : Fin m, cyclicProjection (m := m) (γ := γ) U l) := by
              rw [sum_cyclicProjection_eq_one (m := m) hγprim U]
      _ = ∑ l : Fin m,
            cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U l := by
              simp only [mul_sum]
      _ = cyclicProjection (m := m) (γ := γ) U k * cyclicProjection (m := m) (γ := γ) U k := hsingle
  exact hEq.symm

/-- The adjoint of a cyclic projection has the same left eigenvalue under `U`. -/
private lemma unitary_mul_star_cyclicProjection_eq {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1) :
    ∀ k : Fin m,
      (U : MatrixAlg D) * (cyclicProjection (m := m) (γ := γ) U k)ᴴ =
        γ ^ (k : ℕ) • (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
  intro k
  have hstar :
      (U : MatrixAlg D)ᴴ * (cyclicProjection (m := m) (γ := γ) U k)ᴴ =
        star (γ ^ (k : ℕ)) • (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul] using
      congrArg Matrix.conjTranspose
        (right_mul_cyclicProjection_eq (m := m) hγprim U hUm k)
  have hU_mul_star : (U : MatrixAlg D) * (U : MatrixAlg D)ᴴ = 1 := by
    exact U.2.2
  have hpre :
      (cyclicProjection (m := m) (γ := γ) U k)ᴴ =
        star (γ ^ (k : ℕ)) • ((U : MatrixAlg D) * (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
    calc
      (cyclicProjection (m := m) (γ := γ) U k)ᴴ = (1 : MatrixAlg D) * (cyclicProjection
          (m := m) (γ := γ) U k)ᴴ := by simp only [one_mul]
      _ = ((U : MatrixAlg D) * (U : MatrixAlg D)ᴴ) *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by rw [hU_mul_star]
      _ = (U : MatrixAlg D) * ((U : MatrixAlg D)ᴴ *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
              simp only [Matrix.mul_assoc]
      _ = (U : MatrixAlg D) *
            (star (γ ^ (k : ℕ)) • (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
              rw [hstar]
      _ = star (γ ^ (k : ℕ)) • ((U : MatrixAlg D) *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
              rw [Matrix.mul_smul]
  have hunit : γ ^ (k : ℕ) * star (γ ^ (k : ℕ)) = 1 := by
    simpa using pow_mul_star_pow_of_primitiveRoot (m := m) hγprim (k : ℕ)
  have hmain :
      (U : MatrixAlg D) * (cyclicProjection (m := m) (γ := γ) U k)ᴴ =
        γ ^ (k : ℕ) • (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
    calc
      (U : MatrixAlg D) * (cyclicProjection (m := m) (γ := γ) U k)ᴴ =
          (1 : ℂ) • ((U : MatrixAlg D) * (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
            simp only [one_smul]
      _ = (γ ^ (k : ℕ) * star (γ ^ (k : ℕ))) •
            ((U : MatrixAlg D) * (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
              rw [← hunit]
      _ = γ ^ (k : ℕ) •
            (star (γ ^ (k : ℕ)) • ((U : MatrixAlg D) *
              (cyclicProjection (m := m) (γ := γ) U k)ᴴ)) := by
              rw [smul_smul]
      _ = γ ^ (k : ℕ) • (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by rw [← hpre]
  exact hmain

/-- Distinct cyclic projections are orthogonal to the adjoint of the others. -/
private lemma mul_star_cyclicProjection_eq_zero_of_ne {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1)
    {k l : Fin m} (hkl : k ≠ l) :
    cyclicProjection (m := m) (γ := γ) U l * (cyclicProjection (m := m) (γ := γ) U k)ᴴ = 0 := by
  have hlEig :
      (U : MatrixAlg D) *
          (cyclicProjection (m := m) (γ := γ) U l *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ) =
        γ ^ (l : ℕ) •
          (cyclicProjection (m := m) (γ := γ) U l *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
    calc
      (U : MatrixAlg D) *
          (cyclicProjection (m := m) (γ := γ) U l *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ) =
        ((U : MatrixAlg D) * cyclicProjection (m := m) (γ := γ) U l) *
          (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
            simp only [Matrix.mul_assoc]
      _ = (γ ^ (l : ℕ) • cyclicProjection (m := m) (γ := γ) U l) *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
              rw [left_mul_cyclicProjection_eq (m := m) hγprim U hUm l]
      _ = γ ^ (l : ℕ) •
            (cyclicProjection (m := m) (γ := γ) U l *
              (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
            simp only [Algebra.smul_mul_assoc]
  have hkEig :
      (U : MatrixAlg D) *
          (cyclicProjection (m := m) (γ := γ) U l *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ) =
        γ ^ (k : ℕ) •
          (cyclicProjection (m := m) (γ := γ) U l *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
    calc
      (U : MatrixAlg D) *
          (cyclicProjection (m := m) (γ := γ) U l *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ) =
        ((U : MatrixAlg D) * cyclicProjection (m := m) (γ := γ) U l) *
          (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
            simp only [Matrix.mul_assoc]
      _ = (cyclicProjection (m := m) (γ := γ) U l * (U : MatrixAlg D)) *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
              rw [(commute_unitary_cyclicProjection (m := m) (γ := γ) U l).eq]
      _ = cyclicProjection (m := m) (γ := γ) U l *
            ((U : MatrixAlg D) * (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
              simp only [Matrix.mul_assoc]
      _ = cyclicProjection (m := m) (γ := γ) U l *
            (γ ^ (k : ℕ) • (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
              rw [unitary_mul_star_cyclicProjection_eq (m := m) hγprim U hUm k]
      _ = γ ^ (k : ℕ) •
            (cyclicProjection (m := m) (γ := γ) U l *
              (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
            simp only [Algebra.mul_smul_comm]
  have hsub :
      (γ ^ (l : ℕ) - γ ^ (k : ℕ)) •
          (cyclicProjection (m := m) (γ := γ) U l *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ) = 0 := by
    calc
      (γ ^ (l : ℕ) - γ ^ (k : ℕ)) •
          (cyclicProjection (m := m) (γ := γ) U l *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ)
          = γ ^ (l : ℕ) •
              (cyclicProjection (m := m) (γ := γ) U l *
                (cyclicProjection (m := m) (γ := γ) U k)ᴴ) -
              γ ^ (k : ℕ) •
                (cyclicProjection (m := m) (γ := γ) U l *
                  (cyclicProjection (m := m) (γ := γ) U k)ᴴ) := by
                  simp only [sub_smul]
      _ = 0 := by rw [← hlEig, ← hkEig]; simp only [sub_self]
  have hneq : γ ^ (l : ℕ) - γ ^ (k : ℕ) ≠ 0 := by
    refine sub_ne_zero.mpr ?_
    intro hpow
    exact hkl.symm (pow_inj_of_primitiveRoot (m := m) hγprim hpow)
  exact (smul_eq_zero.mp hsub).resolve_left hneq

/-- Each cyclic projection is an orthogonal projection. -/
private lemma isOrthogonalProjection_cyclicProjection {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hUm : ((U : MatrixAlg D) ^ m) = 1) :
    ∀ k : Fin m, IsOrthogonalProjection (cyclicProjection (m := m) (γ := γ) U k) := by
  intro k
  have hstar_eq :
      (cyclicProjection (m := m) (γ := γ) U k)ᴴ =
        cyclicProjection (m := m) (γ := γ) U k *
          (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
    calc
      (cyclicProjection (m := m) (γ := γ) U k)ᴴ =
          (1 : MatrixAlg D) * (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by simp only [one_mul]
      _ = (∑ l : Fin m, cyclicProjection (m := m) (γ := γ) U l) *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
              rw [sum_cyclicProjection_eq_one (m := m) hγprim U]
      _ = ∑ l : Fin m,
            cyclicProjection (m := m) (γ := γ) U l *
              (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
              simp only [sum_mul]
      _ = cyclicProjection (m := m) (γ := γ) U k *
            (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
          exact Finset.sum_eq_single_of_mem k (Finset.mem_univ k) (by
            intro l hl hne
            simpa using mul_star_cyclicProjection_eq_zero_of_ne (m := m) hγprim U hUm hne.symm)
  have hself_aux :
      cyclicProjection (m := m) (γ := γ) U k =
        cyclicProjection (m := m) (γ := γ) U k *
          (cyclicProjection (m := m) (γ := γ) U k)ᴴ := by
    simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hstar_eq
  refine ⟨hstar_eq.trans hself_aux.symm, idem_cyclicProjection (m := m) hγprim U hUm k⟩

/-- Spectral projections of a finite-order peripheral unitary.

Here `γ` should be thought of as the canonical phase `exp(2π i / m)`, represented in Lean by
an abstract primitive root `hγprim : IsPrimitiveRoot γ m`. -/
theorem exists_cyclic_projections_of_peripheral_unitary
    (T : MatrixEnd D) {γ : ℂ}
    (hγprim : IsPrimitiveRoot γ m)
    (U : Matrix.unitaryGroup (Fin D) ℂ)
    (hUm : ((U : MatrixAlg D) ^ m) = 1)
    (hPow : ∀ k : ℕ, T ((U : MatrixAlg D) ^ k) = γ ^ k • ((U : MatrixAlg D) ^ k)) :
    ∃ P : Fin m → MatrixAlg D,
      (∀ k : Fin m, IsOrthogonalProjection (P k)) ∧
      (∑ k : Fin m, P k = 1) ∧
      ((U : MatrixAlg D) = ∑ k : Fin m, γ ^ (k : ℕ) • P k) ∧
      (∀ k : Fin m, T (P (k + 1)) = P k) := by
  classical
  let P : Fin m → MatrixAlg D := cyclicProjection (m := m) (γ := γ) U
  have hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k) := by
    simpa [P] using isOrthogonalProjection_cyclicProjection (m := m) hγprim U hUm
  have hPsum : ∑ k : Fin m, P k = 1 := by
    simpa [P] using sum_cyclicProjection_eq_one (m := m) hγprim U
  have hUspec_sum : ∑ k : Fin m, γ ^ (k : ℕ) • P k = (U : MatrixAlg D) := by
    simpa [P] using unitary_eq_sum_cyclicProjection (m := m) hγprim U hUm
  have hcyclic : ∀ k : Fin m, T (P (k + 1)) = P k := by
    simpa [P] using cyclic_action_of_cyclicProjection (m := m) (T := T) hγprim U hPow
  exact ⟨P, hPproj, hPsum, hUspec_sum.symm, hcyclic⟩

end CyclicProjections
