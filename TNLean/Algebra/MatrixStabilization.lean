/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import TNLean.Algebra.PerronFrobenius.RankOne

/-!
# Stabilized rank-one matrix powers

This module gives a Cayley--Hamilton criterion for stabilization at a bounded
power and records the resulting normalized rank-one projector.

## Main definitions

* `Matrix.StabilizedRankOneData` records a positive stabilization exponent,
  its bound, normalized outer-product witnesses, and all later powers.

## Main results

* `Matrix.pow_card_eq_pow_pred_of_charpoly_eq_X_pow_pred_mul_X_sub_one` gives
  bounded stabilization from the characteristic polynomial.
* `Matrix.StabilizedRankOneData.power_eq_vec_mul_vec_of_fixed` identifies the
  stabilized projector using any normalized fixed pair.
-/

open scoped Matrix BigOperators
open Polynomial

namespace Matrix

/-! ### Cayley--Hamilton elimination and rank-one factorization -/

variable {ι : Type*} [Fintype ι]

/-- If the characteristic polynomial is `X^(n-1) * (X-1)`, Cayley--Hamilton
kills the zero-primary component after exponent `n-1`.

This is the generalized-eigenspace/Jordan-elimination step used at
arXiv:1703.09188, lines 397--409, expressed without choosing a Jordan basis. -/
theorem pow_card_eq_pow_pred_of_charpoly_eq_X_pow_pred_mul_X_sub_one
    [DecidableEq ι] [Nonempty ι] (E : Matrix ι ι ℂ)
    (hchar : E.charpoly = X ^ (Fintype.card ι - 1) * (X - 1)) :
    E ^ Fintype.card ι = E ^ (Fintype.card ι - 1) := by
  have hCH := E.aeval_self_charpoly
  rw [hchar, map_mul, map_pow, aeval_X, map_sub, aeval_X, map_one] at hCH
  have hn : Fintype.card ι - 1 + 1 = Fintype.card ι := by
    have : 0 < Fintype.card ι := Fintype.card_pos
    omega
  rw [mul_sub, mul_one, ← pow_succ, hn] at hCH
  exact sub_eq_zero.mp hCH

/-- A complex idempotent matrix of trace one is an outer product. -/
theorem exists_eq_vec_mul_vec_of_mul_self_eq_self_of_trace_eq_one
    {T : Matrix ι ι ℂ} (hTT : T * T = T) (hTrace : Matrix.trace T = 1) :
    ∃ a b : ι → ℂ, T = Matrix.vecMulVec a b := by
  change Matrix.HasRankOneFactorization T
  exact Matrix.hasRankOneFactorization_of_mul_self_eq_self hTT hTrace

/-! ### Reusable stabilized-transfer structure -/

/-- Data witnessing that a matrix stabilizes at a bounded positive power to a
normalized rank-one projector.

Here `right ⬝ᵥ left = 1` is the normalization `(Φ|ρ) = 1`, up to the harmless
commutation of complex scalars in the coordinate dot product. The equality
`power_eq` is the source formula `E^J = |ρ)(Φ|`.

Source: arXiv:1703.09188, lines 397--409. -/
structure StabilizedRankOneData [DecidableEq ι] (E : Matrix ι ι ℂ) (bound : ℕ) where
  /-- The blocking exponent that eliminates the zero-primary component. -/
  exponent : ℕ
  /-- The source blocking exponent is positive. -/
  exponent_pos : 0 < exponent
  /-- The exponent lies below the advertised ambient-dimensional bound. -/
  exponent_le : exponent ≤ bound
  /-- The normalized right fixed witness `ρ`. -/
  right : ι → ℂ
  /-- The normalized left fixed witness `Φ`. -/
  left : ι → ℂ
  /-- Normalization of the left/right pairing. -/
  pairing_eq_one : right ⬝ᵥ left = 1
  /-- The stabilized power is the outer product `|ρ)(Φ|`. -/
  power_eq : E ^ exponent = Matrix.vecMulVec right left
  /-- Every later power equals the stabilized projector. -/
  stable : ∀ k, exponent ≤ k → E ^ k = E ^ exponent

namespace StabilizedRankOneData

variable [DecidableEq ι] {E : Matrix ι ι ℂ} {bound : ℕ}

/-- The stabilized transfer matrix is idempotent. -/
theorem projector_idempotent (data : StabilizedRankOneData E bound) :
    E ^ data.exponent * E ^ data.exponent = E ^ data.exponent := by
  rw [← pow_add]
  exact data.stable _ (Nat.le_add_right _ _)

/-- The right witness is fixed by the original transfer matrix. -/
theorem right_fixed (data : StabilizedRankOneData E bound) :
    E *ᵥ data.right = data.right := by
  have hPright : E ^ data.exponent *ᵥ data.right = data.right := by
    rw [data.power_eq, Matrix.vecMulVec_mulVec, dotProduct_comm,
      data.pairing_eq_one]
    simp
  calc
    E *ᵥ data.right = E *ᵥ (E ^ data.exponent *ᵥ data.right) := by rw [hPright]
    _ = (E * E ^ data.exponent) *ᵥ data.right := by rw [Matrix.mulVec_mulVec]
    _ = E ^ (data.exponent + 1) *ᵥ data.right := by rw [← pow_succ']
    _ = E ^ data.exponent *ᵥ data.right := by
      rw [data.stable _ (Nat.le_succ data.exponent)]
    _ = data.right := hPright

/-- The left witness is fixed by the original transfer matrix. -/
theorem left_fixed (data : StabilizedRankOneData E bound) :
    Matrix.vecMul data.left E = data.left := by
  have hleftP : Matrix.vecMul data.left (E ^ data.exponent) = data.left := by
    rw [data.power_eq, Matrix.vecMul_vecMulVec, dotProduct_comm,
      data.pairing_eq_one, one_smul]
  calc
    Matrix.vecMul data.left E =
        Matrix.vecMul (Matrix.vecMul data.left (E ^ data.exponent)) E := by rw [hleftP]
    _ = Matrix.vecMul data.left (E ^ data.exponent * E) := by
      rw [Matrix.vecMul_vecMul]
    _ = Matrix.vecMul data.left (E ^ (data.exponent + 1)) := by rw [pow_succ]
    _ = Matrix.vecMul data.left (E ^ data.exponent) := by
      rw [data.stable _ (Nat.le_succ data.exponent)]
    _ = data.left := hleftP

/-- Any normalized pair of left and right fixed witnesses gives the same
outer-product factorization of the stabilized projector. -/
theorem power_eq_vec_mul_vec_of_fixed (data : StabilizedRankOneData E bound)
    (right' left' : ι → ℂ) (hpair : left' ⬝ᵥ right' = 1)
    (hright : E *ᵥ right' = right') (hleft : Matrix.vecMul left' E = left') :
    E ^ data.exponent = Matrix.vecMulVec right' left' := by
  have hright_pow : E ^ data.exponent *ᵥ right' = right' := by
    induction data.exponent with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hright]
  have hleft_pow : Matrix.vecMul left' (E ^ data.exponent) = left' := by
    induction data.exponent with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hleft]
  have hright' : (data.left ⬝ᵥ right') • data.right = right' := by
    rw [data.power_eq, Matrix.vecMulVec_mulVec] at hright_pow
    simpa [Algebra.smul_def, dotProduct_comm] using hright_pow
  have hleft' : (left' ⬝ᵥ data.right) • data.left = left' := by
    rw [data.power_eq, Matrix.vecMul_vecMulVec] at hleft_pow
    exact hleft_pow
  rw [data.power_eq]
  rw [← hright', ← hleft'] at hpair ⊢
  have hscalar :
      (data.left ⬝ᵥ right') * (left' ⬝ᵥ data.right) = 1 := by
    simpa [dotProduct_comm, mul_comm, mul_left_comm, mul_assoc,
      data.pairing_eq_one] using hpair
  ext i j
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  calc
    data.right i * data.left j =
        ((data.left ⬝ᵥ right') * (left' ⬝ᵥ data.right)) *
          (data.right i * data.left j) := by rw [hscalar, one_mul]
    _ = (data.left ⬝ᵥ right') * data.right i *
          ((left' ⬝ᵥ data.right) * data.left j) := by ring

/-- Construct stabilized rank-one data from one equality of consecutive powers
and the trace-one normalization at that power. -/
noncomputable def of_power_succ_eq [Nonempty ι]
    (J bound : ℕ) (hJpos : 0 < J) (hJle : J ≤ bound)
    (hstep : E ^ (J + 1) = E ^ J) (htrace : Matrix.trace (E ^ J) = 1) :
    StabilizedRankOneData E bound := by
  have hstable : ∀ k, J ≤ k → E ^ k = E ^ J := by
    intro k hk
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
    induction t with
    | zero => rfl
    | succ t iht =>
      rw [Nat.add_succ, pow_succ, iht (Nat.le_add_right _ _), ← pow_succ, hstep]
  have hidem : E ^ J * E ^ J = E ^ J := by
    rw [← pow_add]
    exact hstable _ (Nat.le_add_right _ _)
  let hex := Matrix.exists_eq_vec_mul_vec_of_mul_self_eq_self_of_trace_eq_one hidem htrace
  let right := Classical.choose hex
  let left := Classical.choose (Classical.choose_spec hex)
  have hfac : E ^ J = Matrix.vecMulVec right left :=
    Classical.choose_spec (Classical.choose_spec hex)
  refine ⟨J, hJpos, hJle, right, left, ?_, hfac, hstable⟩
  rw [← Matrix.trace_vecMulVec, ← hfac]
  exact htrace

end StabilizedRankOneData
end Matrix
