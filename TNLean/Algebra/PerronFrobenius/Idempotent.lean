/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PerronFrobenius.RankOne
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Primitive matrices with stationary powers

This module proves a finite-dimensional Perron--Frobenius lemma for a primitive
nonnegative real matrix whose second and third powers agree. Its square is a
strictly positive idempotent, and the fixed space of such an idempotent is
one-dimensional. Consequently the square has rank one.

The results support the rank-one trace factorization sought at
arXiv:1606.00608, Appendix C.2, line 1613.  In addition to the rank statement,
the square is factored as $a b^{\mathsf T}$ for real vectors satisfying
$a \mathbin{\cdot} b=1$.  These are source-independent matrix lemmas, not
statements asserted in that paper: applying them to the sector trace matrix
still requires a separate, non-circular proof of primitivity.
-/

open scoped BigOperators Matrix

namespace Matrix

variable {n : Type*} [Fintype n]

/-- A strictly positive idempotent real matrix on a nonempty finite index set
has rank one. -/
theorem rank_eq_one_of_pos_of_mul_self_eq_self [Nonempty n]
    {P : Matrix n n ℝ} (hP : ∀ i j, 0 < P i j) (hidem : P * P = P) :
    P.rank = 1 := by
  classical
  let f : (n → ℝ) →ₗ[ℝ] (n → ℝ) := Matrix.toLin' P
  let u : n → ℝ := f 1
  have hu_pos (i : n) : 0 < u i := by
    simp only [u, f, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.one_apply,
      mul_one]
    exact Finset.sum_pos (fun j _ ↦ hP i j) Finset.univ_nonempty
  have hf : f ∘ₗ f = f := by
    change Matrix.toLin' P ∘ₗ Matrix.toLin' P = Matrix.toLin' P
    rw [← Matrix.toLin'_mul, hidem]
  have hu_fix : f u = u := by
    simpa only [u, LinearMap.comp_apply] using LinearMap.congr_fun hf 1
  have hfixed (x : n → ℝ) (hx : f x = x) : ∃ c : ℝ, c • u = x := by
    obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ
      (fun i ↦ x i / u i) Finset.univ_nonempty
    let c : ℝ := x k / u k
    let y : n → ℝ := c • u - x
    have hy_nonneg (i : n) : 0 ≤ y i := by
      have hratio : x i / u i ≤ c := hk i (Finset.mem_univ i)
      have hxi : x i ≤ c * u i := (div_le_iff₀ (hu_pos i)).mp hratio
      exact sub_nonneg.mpr hxi
    have hyk : y k = 0 := by
      simp only [y, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, c]
      rw [div_mul_cancel₀ (x k) (ne_of_gt (hu_pos k)), sub_self]
    have hy_fix : f y = y := by
      simp only [y, map_sub, map_smul, hu_fix, hx]
    have hsum : ∑ j, P k j * y j = 0 := by
      have hky := congrFun hy_fix k
      rw [hyk] at hky
      simpa only [f, Matrix.toLin'_apply, Matrix.mulVec, dotProduct] using hky
    have hy_zero : y = 0 := by
      funext i
      have hterm : P k i * y i = 0 := congrFun
        ((Fintype.sum_eq_zero_iff_of_nonneg fun j ↦
          mul_nonneg (hP k j).le (hy_nonneg j)).mp hsum) i
      exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hP k i))
    refine ⟨c, sub_eq_zero.mp ?_⟩
    simpa only [y] using hy_zero
  have hu_mem : u ∈ LinearMap.range f := ⟨1, rfl⟩
  have hu_ne : u ≠ 0 := by
    intro hu
    have := hu_pos (Classical.choice inferInstance)
    rw [hu, Pi.zero_apply] at this
    exact lt_irrefl 0 this
  have hrank_le : Module.finrank ℝ (LinearMap.range f) ≤ 1 := by
    refine finrank_le_one ⟨u, hu_mem⟩ fun x ↦ ?_
    rcases x.property with ⟨z, hz⟩
    have hx : f x.1 = x.1 := by
      rw [← hz]
      exact LinearMap.congr_fun hf z
    obtain ⟨c, hc⟩ := hfixed x.1 hx
    refine ⟨c, Subtype.ext ?_⟩
    exact hc
  have hrank_pos : 0 < Module.finrank ℝ (LinearMap.range f) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨u, hu_mem⟩, ?_⟩
    intro hzero
    apply hu_ne
    exact congrArg Subtype.val hzero
  have hrange : Module.finrank ℝ (LinearMap.range f) = 1 := by omega
  rw [Matrix.rank_eq_finrank_range_toLin P (Pi.basisFun ℝ n) (Pi.basisFun ℝ n),
    Matrix.toLin_eq_toLin']
  simpa only [f] using hrange

/-- Multiplication by a positive scalar preserves primitivity. -/
theorem IsPrimitive.smul_of_pos [DecidableEq n]
    {T : Matrix n n ℝ} (hT : T.IsPrimitive)
    {c : ℝ} (hc : 0 < c) : (c • T).IsPrimitive := by
  obtain ⟨m, hm, hpos⟩ := hT.exists_pos_pow
  refine ⟨fun i j ↦ mul_nonneg hc.le (hT.nonneg i j), m, hm, ?_⟩
  intro i j
  rw [smul_pow, Matrix.smul_apply]
  exact mul_pos (pow_pos hc m) (hpos i j)

/-- If a primitive nonnegative real matrix has equal second and third powers,
then its square has rank one.

This is the finite-dimensional Perron-projection lemma supporting the proposed
argument at arXiv:1606.00608, Appendix C.2, line 1613; it is not itself a
claim of that source. Nonemptiness of the finite index type is necessary:
primitivity is vacuous for the empty matrix, whose square has rank zero. -/
theorem IsPrimitive.rank_pow_two_eq_one_of_pow_two_eq_pow_three
    [DecidableEq n] [Nonempty n] {T : Matrix n n ℝ}
    (hT : T.IsPrimitive) (h : T ^ 2 = T ^ 3) :
    (T ^ 2).rank = 1 := by
  obtain ⟨m, hm, hpos⟩ := hT.exists_pos_pow
  have htwom_pos (i j : n) : 0 < (T ^ (m + m)) i j := by
    rw [pow_add, Matrix.mul_apply]
    exact Finset.sum_pos (fun k _ ↦ mul_pos (hpos i k) (hpos k j))
      Finset.univ_nonempty
  have hsq_pos (i j : n) : 0 < (T ^ 2) i j := by
    rw [← pow_eq_pow_two_of_pow_two_eq_pow_three h (m + m) (by omega)]
    exact htwom_pos i j
  have hsq_idem : T ^ 2 * T ^ 2 = T ^ 2 := by
    rw [← pow_add]
    exact pow_eq_pow_two_of_pow_two_eq_pow_three h 4 (by omega)
  exact rank_eq_one_of_pos_of_mul_self_eq_self hsq_pos hsq_idem

/-- If a primitive nonnegative real matrix has equal second and third powers,
then its square has the form $a b^{\mathsf T}$ for real vectors satisfying
$a \mathbin{\cdot} b=1$.

This is the normalized factorization needed for the corrected two-step
coefficient in arXiv:1606.00608, Appendix C.2, Proposition 4to2, lines
1606--1616.  It factors `T ^ 2`, not the one-step matrix `T` printed at
line 1613. -/
theorem IsPrimitive.exists_pow_two_eq_vecMulVec_of_pow_two_eq_pow_three
    {N : ℕ} [NeZero N] {T : Matrix (Fin N) (Fin N) ℝ}
    (hT : T.IsPrimitive) (h : T ^ 2 = T ^ 3) :
    ∃ a b : Fin N → ℝ, T ^ 2 = Matrix.vecMulVec a b ∧ a ⬝ᵥ b = 1 := by
  have hsq_idem : T ^ 2 * T ^ 2 = T ^ 2 := by
    rw [← pow_add]
    exact pow_eq_pow_two_of_pow_two_eq_pow_three h 4 (by omega)
  have hrank := hT.rank_pow_two_eq_one_of_pow_two_eq_pow_three h
  let f : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) := Matrix.toLin' (T ^ 2)
  have hf : IsIdempotentElem f := by
    change Matrix.toLin' (T ^ 2) ∘ₗ Matrix.toLin' (T ^ 2) = Matrix.toLin' (T ^ 2)
    rw [← Matrix.toLin'_mul, hsq_idem]
  have hrange : Module.finrank ℝ (LinearMap.range f) = 1 := by
    rw [Matrix.rank_eq_finrank_range_toLin (T ^ 2)
      (Pi.basisFun ℝ (Fin N)) (Pi.basisFun ℝ (Fin N)), Matrix.toLin_eq_toLin'] at hrank
    exact hrank
  have htrace : Matrix.trace (T ^ 2) = 1 := by
    have hproj := (LinearMap.isProj_range_iff_isIdempotentElem f).2 hf |>.trace
    rw [Matrix.trace_toLin'_eq] at hproj
    rw [hrange] at hproj
    exact_mod_cast hproj
  obtain ⟨a, b, hab⟩ :=
    Matrix.hasRankOneFactorization_of_mul_self_eq_self hsq_idem htrace
  refine ⟨a, b, hab, ?_⟩
  rw [← Matrix.trace_vecMulVec, ← hab]
  exact htrace

end Matrix
