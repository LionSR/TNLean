/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.FiniteGroupDetectorSpatial
import QICLean.Channel.ComplementaryWeylTwirl

/-!
# Clock and shift instance of the spatial endpoint obstruction

This module instantiates the exact spatial calculation for the clock and shift
matrices already defined in QICLean. The permutation-matrix convention there
gives the conjugation phase `ζ`; using the inverse shift gives `ζ⁻¹` instead.
At even order both give the same total sign, namely `-1`.

The interval word and its ordering are those of the endpoint audit of
arXiv:2405.00439, Section V, `detectG`, lines 2108–2117. These results concern
that explicitly chosen interval family, not a canonical truncation assertion.
-/

open Matrix

namespace MPOTensor.FiniteGroupDetector

variable {m : ℕ} [NeZero m]

private theorem root_pow_val_add_one {ζ : ℂ} (hζ : ζ ^ m = 1) (i : ZMod m) :
    ζ ^ (i + 1).val = ζ * ζ ^ i.val := by
  have hcast : ((i.val + 1 : ℕ) : ZMod m) = i + 1 := by
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  rw [← hcast, ZMod.val_natCast, ← pow_eq_pow_mod (i.val + 1) hζ, pow_succ, mul_comm]

/-- The shift unitary supplied by the QICLean Weyl construction.
Source context: the cyclic clock/shift instance of the endpoint audit of
arXiv:2405.00439, `detectG`, lines 2108–2117. -/
noncomputable def detectorShift (m : ℕ) [NeZero m] :
    unitary (Matrix (ZMod m) (ZMod m) ℂ) :=
  ⟨weylShift, weylShift_mem_unitary⟩

/-- The clock unitary for a specified primitive root of unity.
Source context: the cyclic clock/shift instance of the endpoint audit of
arXiv:2405.00439, `detectG`, lines 2108–2117. -/
noncomputable def detectorClock {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) :
    unitary (Matrix (ZMod m) (ZMod m) ℂ) :=
  ⟨weylClock ζ, weylClock_mem_unitary hζ⟩

/-- The actual group commutator of the clock and shift; its scalar value is
derived below, so no scalar-unitary membership is supplied as an assumption.
Source context: the endpoint audit of arXiv:2405.00439, `detectG`. -/
noncomputable def detectorClockPhase {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) :
    unitary (Matrix (ZMod m) (ZMod m) ℂ) :=
  (detectorClock hζ)⁻¹ * detectorShift m * detectorClock hζ * (detectorShift m)⁻¹

private theorem weylShift_clock_conj {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (hm : 1 < m) :
    (weylShift : Matrix (ZMod m) (ZMod m) ℂ) * weylClock ζ * weylShiftᴴ =
      ζ • weylClock ζ := by
  letI : Fact (1 < m) := ⟨hm⟩
  have h := weylShift_pow_conj_diagonal (1 : ZMod m) (fun i ↦ ζ ^ i.val)
  simp only [ZMod.val_one, pow_one] at h
  rw [weylClock, h]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [root_pow_val_add_one hζ.pow_eq_one]
  · simp [diagonal_apply, hij]

/-- The clock commutator is the primitive scalar phase, proved from the
existing clock and shift matrices. Source context: the cyclic instance of
the endpoint audit of arXiv:2405.00439, `detectG`, lines 2108–2117. -/
theorem detectorClockPhase_coe {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (hm : 1 < m) :
    (detectorClockPhase hζ : Matrix (ZMod m) (ZMod m) ℂ) = ζ • 1 := by
  have hZ := Unitary.star_mul_self_of_mem (weylClock_mem_unitary hζ)
  change (weylClock ζ)ᴴ * weylShift * weylClock ζ * weylShiftᴴ = ζ • 1
  calc
    (weylClock ζ)ᴴ * weylShift * weylClock ζ * weylShiftᴴ =
        (weylClock ζ)ᴴ * (weylShift * weylClock ζ * weylShiftᴴ) := by
      simp only [mul_assoc]
    _ = (weylClock ζ)ᴴ * (ζ • weylClock ζ) := by rw [weylShift_clock_conj hζ hm]
    _ = ζ • 1 := by rw [Matrix.mul_smul, hZ]

/-- The scalar clock phase commutes with the bulk shift.
Source context: the endpoint audit of arXiv:2405.00439, `detectG`. -/
theorem detectorClockPhase_commute {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (hm : 1 < m) :
    Commute (detectorClockPhase hζ) (detectorShift m) := by
  apply Subtype.ext
  change (detectorClockPhase hζ : Matrix _ _ ℂ) * _ =
    _ * (detectorClockPhase hζ : Matrix _ _ ℂ)
  rw [detectorClockPhase_coe hζ hm, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]

/-- The needed local conjugation identity follows from the definition of the
clock commutator. Source context: the endpoint audit of
arXiv:2405.00439, `detectG`, lines 2108–2117. -/
theorem detectorClock_conjugation {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) :
    (detectorClock hζ)⁻¹ * detectorShift m * detectorClock hζ =
      detectorClockPhase hζ * detectorShift m := by
  simp [detectorClockPhase, mul_assoc]

/-- The bulk shift has the required cyclic period.
Source context: the finite cyclic instance of arXiv:2405.00439, `detectG`. -/
theorem detectorShift_pow_order : detectorShift m ^ m = 1 := by
  apply Subtype.ext
  change (weylShift : Matrix (ZMod m) (ZMod m) ℂ) ^ m = 1
  rw [weylShift_pow]
  simp

/-- The commutator phase has the cyclic period of the primitive root.
Source context: the endpoint audit of arXiv:2405.00439, `detectG`. -/
theorem detectorClockPhase_pow_order {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (hm : 1 < m) :
    detectorClockPhase hζ ^ m = 1 := by
  apply Subtype.ext
  change (detectorClockPhase hζ : Matrix _ _ ℂ) ^ m = 1
  rw [detectorClockPhase_coe hζ hm, smul_pow, one_pow, hζ.pow_eq_one, one_smul]

/-- For every positive even cyclic order, the complete spatial interval word
has total phase minus the identity in the clock/shift representation.
The intervals and every spatial factor are evaluated before the phases are
multiplied. Source context: the explicit counterexample family in the endpoint
audit of arXiv:2405.00439, `detectG`, lines 2108–2117. -/
theorem prod_spatialEndpointWord_clock_even {k : ℕ} [NeZero (2 * k)] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * k)) :
    (((List.range (2 * k)).map fun r ↦ spatialEndpointWord (detectorShift (2 * k))
      (detectorClock hζ) (2 * k) (r + 1)).prod : Matrix (ZMod (2 * k)) (ZMod (2 * k)) ℂ) =
        -1 := by
  have hk : k ≠ 0 := by
    intro h
    exact NeZero.ne (2 * k) (by simp [h])
  have hm : 1 < 2 * k := by omega
  rw [prod_spatialEndpointWord_even _ _ (detectorClockPhase hζ)
    (detectorClockPhase_commute hζ hm) (detectorClock_conjugation hζ) k
    (detectorClockPhase_pow_order hζ hm)]
  have hhalf : ζ ^ k = -1 := by
    have h := hζ.pow_of_dvd hk (dvd_mul_left k 2)
    have hdiv : 2 * k / k = 2 := Nat.mul_div_cancel 2 (Nat.pos_of_ne_zero hk)
    rw [hdiv] at h
    exact h.eq_neg_one_of_two_right
  change (detectorClockPhase hζ : Matrix _ _ ℂ) ^ k = -1
  rw [detectorClockPhase_coe hζ hm, smul_pow, one_pow, hhalf, neg_one_smul]

end MPOTensor.FiniteGroupDetector
