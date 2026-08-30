/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Trace
import QICLean.Algebra.ShiftedTracePowerSpectrum

/-!
# Semisimple Endomorphisms with Rank-One Trace Powers

This file isolates the finite-dimensional linear algebra used in the
Jordan--Chevalley step of arXiv:1706.07329v2, Proposition 20, lines 3839--3866.

A semisimple complex endomorphism has one-dimensional range when a nonzero
scalar multiple has trace one at every power above one. The proof applies
QICLean's shifted trace-power characteristic-polynomial theorem to a matrix in
an arbitrary basis. Semisimplicity identifies the generalized zero-eigenspace
with the kernel, and root multiplicity together with rank--nullity then gives
the range dimension.

A commuting nilpotent endomorphism preserves this one-dimensional range. Its
restriction is a scalar endomorphism, whose nilpotence forces that scalar to
vanish. Thus the nilpotent and semisimple parts annihilate one another in both
orders, and sufficiently high powers of their sum are powers of the
semisimple part alone.

No normality, Hermitianity, positivity, or chosen-basis hypothesis is used.

## Reference

* [Molnar--Ge--Schuch--Cirac 2018] arXiv:1706.07329v2, Proposition 20,
  lines 3839--3866
-/

open Polynomial

namespace Module.End

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- A semisimple complex endomorphism has one-dimensional range if a nonzero
scalar multiple has trace one at every power above one.

This is the root-multiplicity step in arXiv:1706.07329v2, Proposition 20,
lines 3839--3866. The scaling scalar is explicit and required to be nonzero. -/
theorem finrank_range_eq_one_of_isSemisimple_of_scaled_trace_pow_eq_one
    (S : Module.End ℂ V) (hS : S.IsSemisimple) (c : ℂ) (hc : c ≠ 0)
    (htrace : ∀ k : ℕ, 1 < k → LinearMap.trace ℂ V ((c • S) ^ k) = 1) :
    Module.finrank ℂ S.range = 1 := by
  classical
  let g := c • S
  let b := Module.Free.chooseBasis ℂ V
  let A := LinearMap.toMatrix b b g
  have hAtrace : ∀ k : ℕ, 1 < k → Matrix.trace (A ^ k) = 1 := by
    intro k hk
    change Matrix.trace ((LinearMap.toMatrix b b g) ^ k) = 1
    rw [LinearMap.toMatrix_pow, ← LinearMap.trace_eq_matrix_trace ℂ b]
    exact htrace k hk
  have hcharA :
      A.charpoly =
        X ^ (Fintype.card (Module.Free.ChooseBasisIndex ℂ V) - 1) * (X - 1) :=
    Matrix.charpoly_eq_X_pow_pred_mul_X_sub_one_of_forall_trace_pow_eq_one_of_one_lt
      A hAtrace
  have hdim :
      Fintype.card (Module.Free.ChooseBasisIndex ℂ V) = Module.finrank ℂ V := by
    simpa using (Module.finrank_eq_card_basis b).symm
  have hchar : g.charpoly = X ^ (Module.finrank ℂ V - 1) * (X - 1) := by
    rw [← LinearMap.charpoly_toMatrix g b, hcharA, hdim]
  have hgss : g.IsSemisimple := Module.End.IsSemisimple_smul c hS
  have hker : Module.finrank ℂ (LinearMap.ker g) = Module.finrank ℂ V - 1 := by
    calc
      Module.finrank ℂ (LinearMap.ker g) =
          Module.finrank ℂ (g.maxGenEigenspace 0) := by
            rw [hgss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
              Module.End.eigenspace_zero]
      _ = g.charpoly.rootMultiplicity 0 :=
        LinearMap.finrank_maxGenEigenspace_eq g 0
      _ = Module.finrank ℂ V - 1 := by
        rw [hchar, Polynomial.rootMultiplicity_eq_natTrailingDegree',
          Polynomial.natTrailingDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero)
            (by simpa using (Polynomial.X_sub_C_ne_zero (1 : ℂ)))]
        simp
  have hdimpos : 0 < Module.finrank ℂ V := by
    by_contra h
    have hdimzero : Module.finrank ℂ V = 0 := Nat.eq_zero_of_not_pos h
    have h := htrace 2 (by omega)
    rw [show (c • S) ^ 2 = 0 by
      have hs : Subsingleton V := Module.finrank_zero_iff.mp hdimzero
      apply LinearMap.ext
      intro x
      exact Subsingleton.elim _ _] at h
    simp at h
  have hrangeg : Module.finrank ℂ g.range = 1 := by
    have hnullity := g.finrank_range_add_finrank_ker
    rw [hker] at hnullity
    omega
  have hrange : g.range = S.range := LinearMap.range_smul S c hc
  rwa [← hrange]

/-- A nilpotent endomorphism commuting with an endomorphism of one-dimensional
range annihilates it in both orders.

The nilpotent map restricts to the range because of commutation. Every
endomorphism of that one-dimensional range is scalar, and a nilpotent scalar
over `ℂ` is zero. -/
theorem IsNilpotent.mul_eq_zero_and_mul_eq_zero_of_commute_of_finrank_range_eq_one
    {N : Module.End ℂ V} (hN : IsNilpotent N) (S : Module.End ℂ V)
    (hcomm : Commute N S) (hrank : Module.finrank ℂ S.range = 1) :
    N * S = 0 ∧ S * N = 0 := by
  have hmaps : Set.MapsTo N S.range S.range := by
    rintro _ ⟨x, rfl⟩
    refine ⟨N x, ?_⟩
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, hcomm.eq]
  let R : Module.End ℂ S.range := N.restrict hmaps
  have hRnil : IsNilpotent R := Module.End.isNilpotent.restrict hmaps hN
  obtain ⟨a, ha, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hrank R
  have htr : LinearMap.trace ℂ S.range R = 0 :=
    IsNilpotent.eq_zero (LinearMap.isNilpotent_trace_of_isNilpotent hRnil)
  have ha0 : a = 0 := by
    rw [ha, map_smul, LinearMap.trace_id, hrank, Nat.cast_one] at htr
    simpa using htr
  have hRzero : R = 0 := by rw [ha, ha0, zero_smul]
  have hNS : N * S = 0 := by
    ext x
    have hx :=
      LinearMap.congr_fun hRzero (⟨S x, LinearMap.mem_range_self S x⟩ : S.range)
    dsimp [R] at hx
    exact congrArg Subtype.val hx
  exact ⟨hNS, hcomm.eq ▸ hNS⟩

private lemma add_pow_eq_pow_add_pow_of_mul_eq_zero {R : Type*} [Semiring R]
    (x y : R) (hxy : x * y = 0) (hyx : y * x = 0) {k : ℕ} (hk : 0 < k) :
    (x + y) ^ k = x ^ k + y ^ k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih (by omega)]
      simp [add_mul, mul_add, mul_assoc, hxy, hyx, pow_succ]

omit [FiniteDimensional ℂ V] in
/-- If two endomorphisms annihilate one another and the first is nilpotent,
then sufficiently high powers of their sum are powers of the second alone. -/
theorem IsNilpotent.exists_add_pow_eq_right_of_mul_eq_zero
    {N : Module.End ℂ V} (hN : IsNilpotent N) (S : Module.End ℂ V)
    (hNS : N * S = 0) (hSN : S * N = 0) :
    ∃ J : ℕ, 0 < J ∧ ∀ k : ℕ, J ≤ k → (N + S) ^ k = S ^ k := by
  obtain ⟨j, hj⟩ := hN
  refine ⟨max 1 j, by omega, ?_⟩
  intro k hk
  rw [add_pow_eq_pow_add_pow_of_mul_eq_zero N S hNS hSN (by omega),
    pow_eq_zero_of_le (le_trans (Nat.le_max_right 1 j) hk) hj, zero_add]

/-- In a Jordan--Chevalley split, shifted scaled trace powers of the semisimple
part force the nilpotent and semisimple parts to annihilate one another; all
sufficiently high powers of their sum then equal powers of the semisimple part.

This packages the linear-algebra reduction in arXiv:1706.07329v2,
Proposition 20, lines 3839--3866. -/
theorem IsNilpotent.products_eq_zero_and_eventual_add_pow_eq_of_scaled_trace
    {N : Module.End ℂ V} (hN : IsNilpotent N) (S : Module.End ℂ V)
    (hcomm : Commute N S) (hS : S.IsSemisimple) (c : ℂ) (hc : c ≠ 0)
    (htrace : ∀ k : ℕ, 1 < k → LinearMap.trace ℂ V ((c • S) ^ k) = 1) :
    N * S = 0 ∧ S * N = 0 ∧
      ∃ J : ℕ, 0 < J ∧ ∀ k : ℕ, J ≤ k → (N + S) ^ k = S ^ k := by
  have hrank :=
    finrank_range_eq_one_of_isSemisimple_of_scaled_trace_pow_eq_one S hS c hc htrace
  obtain ⟨hNS, hSN⟩ :=
    IsNilpotent.mul_eq_zero_and_mul_eq_zero_of_commute_of_finrank_range_eq_one
      hN S hcomm hrank
  exact ⟨hNS, hSN,
    IsNilpotent.exists_add_pow_eq_right_of_mul_eq_zero hN S hNS hSN⟩

end Module.End
