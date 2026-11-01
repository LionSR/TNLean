/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.WeylTwirl
import QICLean.Kraus.Word
import TNLean.MPS.Examples.ShortMomentum.Charges

/-!
# Fifth-root Weyl words with an exceptional central degree

The matrices in this module have charges (1,0), (0,1), and (-1,-1).
Their word products are nonzero scalar multiples of the corresponding
Weyl matrix. In particular every degree-seven word has zero trace.
This does not assert a Hamiltonian counterexample: classification of
all periodic local constraints remains a separate obligation.

Source context: SPWC10, arXiv:0909.5347, Theorem 5, main.tex lines 850--880.
See `docs/audits/2026-10-29_weyl_short_volume_candidate.md`.
-/

open Matrix
open scoped BigOperators

namespace MPSTensor.ShortMomentum

/-- The character of the additive group of residues modulo five. -/
noncomputable def rootCharacter (ζ : ℂ) (a : ZMod 5) : ℂ := ζ ^ a.val

@[simp] theorem rootCharacter_zero (ζ : ℂ) : rootCharacter ζ 0 = 1 := by
  simp [rootCharacter]

/-- Addition of residues becomes multiplication of complex phases. -/
theorem rootCharacter_add {ζ : ℂ} (hζ : ζ ^ 5 = 1) (a b : ZMod 5) :
    rootCharacter ζ (a + b) = rootCharacter ζ a * rootCharacter ζ b := by
  unfold rootCharacter
  rw [ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ hζ).symm

/-- Multiplication by a residue is a natural power of the character. -/
theorem rootCharacter_mul {ζ : ℂ} (hζ : ζ ^ 5 = 1) (a b : ZMod 5) :
    rootCharacter ζ (a * b) = rootCharacter ζ a ^ b.val := by
  unfold rootCharacter
  rw [ZMod.val_mul, ← pow_mul]
  exact (pow_eq_pow_mod _ hζ).symm

/-- Every character value is nonzero. -/
theorem rootCharacter_ne_zero {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (a : ZMod 5) :
    rootCharacter ζ a ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by decide))

/-- Primitivity makes the character faithful. -/
theorem rootCharacter_eq_one_iff {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (a : ZMod 5) :
    rootCharacter ζ a = 1 ↔ a = 0 := by
  constructor
  · intro h
    apply ZMod.val_injective 5
    exact hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt (0 : ZMod 5))
      (by simpa only [rootCharacter, ZMod.val_zero, pow_zero] using h)
  · rintro rfl
    exact rootCharacter_zero ζ

/-- The charged matrix: its nonzero entry in row i lies in column i-v. -/
noncomputable def chargedWeyl (ζ : ℂ) (u v : ZMod 5) :
    Matrix (ZMod 5) (ZMod 5) ℂ :=
  fun i j ↦ if j = i - v then rootCharacter ζ (u * i) else 0

@[simp] theorem chargedWeyl_zero (ζ : ℂ) : chargedWeyl ζ 0 0 = 1 := by
  ext i j
  simp [chargedWeyl, Matrix.one_apply, eq_comm]

/-- The exact scalar cocycle of charged matrix multiplication. -/
theorem chargedWeyl_mul {ζ : ℂ} (hζ : ζ ^ 5 = 1) (a b c d : ZMod 5) :
    chargedWeyl ζ a b * chargedWeyl ζ c d =
      rootCharacter ζ (-c * b) • chargedWeyl ζ (a + c) (b + d) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (i - b)]
  · simp only [chargedWeyl, Matrix.smul_apply, smul_eq_mul]
    rw [show i - b - d = i - (b + d) by ring]
    by_cases hj : j = i - (b + d)
    · simp only [hj, ite_true]
      rw [← rootCharacter_add hζ, ← rootCharacter_add hζ]
      congr 1
      ring
    · simp only [hj, ite_false, mul_zero]
  · intro k _ hk
    simp only [chargedWeyl, ite_eq_right hk, zero_mul]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The three physical letters carry the three cyclic Weyl charges. -/
def letterCharge : Fin 3 → ZMod 5 × ZMod 5 := ![(1, 0), (0, 1), (-1, -1)]

/-- The third generator is the inverse of the product of the first two. -/
def letterPhase : Fin 3 → ZMod 5 := ![0, 0, -1]

/-- The three-letter tensor on a five-dimensional virtual space. -/
noncomputable def threeLetterTensor (ζ : ℂ) : MPSTensor 3 5 :=
  fun i ↦ rootCharacter ζ (letterPhase i) •
    chargedWeyl ζ (letterCharge i).1 (letterCharge i).2

/-- Charge addition agrees with the letter counts. -/
theorem wordCharge_cons (i : Fin 3) (w : List (Fin 3)) :
    wordCharge (i :: w) = letterCharge i + wordCharge w := by
  fin_cases i <;> apply Prod.ext <;>
    simp [wordCharge, countCharge, letterCharge] <;> ring

/-- The exact scalar exponent produced by multiplying a word. -/
def wordPhase : List (Fin 3) → ZMod 5
  | [] => 0
  | i :: w => letterPhase i + wordPhase w - (wordCharge w).1 * (letterCharge i).2

/-- Every word is a scalar times its charged Weyl matrix. -/
theorem evalWord_threeLetterTensor {ζ : ℂ} (hζ : ζ ^ 5 = 1) (w : List (Fin 3)) :
    Kraus.evalWord (threeLetterTensor ζ) w =
      rootCharacter ζ (wordPhase w) •
        chargedWeyl ζ (wordCharge w).1 (wordCharge w).2 := by
  induction w with
  | nil =>
      change (1 : Matrix (ZMod 5) (ZMod 5) ℂ) =
        rootCharacter ζ (wordPhase []) • chargedWeyl ζ (wordCharge []).1 (wordCharge []).2
      simp [wordPhase, wordCharge, countCharge]
  | cons i w ih =>
      rw [Kraus.evalWord_cons, ih]
      change (rootCharacter ζ (letterPhase i) •
          chargedWeyl ζ (letterCharge i).1 (letterCharge i).2 :
            Matrix (ZMod 5) (ZMod 5) ℂ) *
          (rootCharacter ζ (wordPhase w) • chargedWeyl ζ (wordCharge w).1 (wordCharge w).2) =
        rootCharacter ζ (wordPhase (i :: w)) •
          chargedWeyl ζ (wordCharge (i :: w)).1 (wordCharge (i :: w)).2
      rw [smul_mul_smul_comm, chargedWeyl_mul hζ, smul_smul, wordCharge_cons, Prod.fst_add,
        Prod.snd_add, ← rootCharacter_add hζ, ← rootCharacter_add hζ]
      congr 2
      simp only [wordPhase]
      ring

/-- A noncentral charged matrix has zero trace. -/
theorem trace_chargedWeyl_eq_zero {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (u v : ZMod 5) (hne : (u, v) ≠ 0) : (chargedWeyl ζ u v).trace = 0 := by
  by_cases hv : v = 0
  · subst v
    have hu : rootCharacter ζ u ≠ 1 := fun h ↦ hne
      (Prod.ext ((rootCharacter_eq_one_iff hζ u).mp h) rfl)
    have hpow : rootCharacter ζ u ^ 5 = 1 := by
      unfold rootCharacter
      rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    simp only [Matrix.trace, Matrix.diag, chargedWeyl, sub_zero, ite_true]
    simp_rw [rootCharacter_mul hζ.pow_eq_one]
    rw [Matrix.sum_pow_val_eq_ite hpow, ite_eq_right hu]
  · apply Finset.sum_eq_zero
    intro i _
    change (if i = i - v then rootCharacter ζ (u * i) else 0) = 0
    apply ite_eq_right
    intro h
    exact hv (by linear_combination h)

/-- Every degree-seven word has zero trace. -/
theorem trace_evalWord_threeLetterTensor_seven {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (w : List (Fin 3)) (hw : w.length = 7) :
    (Kraus.evalWord (threeLetterTensor ζ) w).trace = 0 := by
  rw [evalWord_threeLetterTensor hζ.pow_eq_one]
  change (rootCharacter ζ (wordPhase w) • chargedWeyl ζ (wordCharge w).1 (wordCharge w).2 :
    Matrix (ZMod 5) (ZMod 5) ℂ).trace = 0
  rw [Matrix.trace_smul,
    trace_chargedWeyl_eq_zero hζ (wordCharge w).1 (wordCharge w).2
      (wordCharge_ne_zero_of_length_seven hw), smul_zero]

end MPSTensor.ShortMomentum
