/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Blocking
import TNLean.MPS.Examples.ShortMomentum.WeylWords

/-!
# Homogeneous relations of the fifth-root Weyl letters

The adjacent cyclic commutation and fifth-power transfer relations are
proved for the matrices, without a supplied algebra presentation.
Completeness of these relations for all periodic local constraints is
not asserted. Source context: the finite-prefix question for SPWC10,
arXiv:0909.5347, Theorem 5, main.tex lines 850--880; see
`docs/audits/2026-10-29_weyl_short_volume_candidate.md`.
-/

namespace MPSTensor.ShortMomentum

@[simp] theorem rootCharacter_one (ζ : ℂ) : rootCharacter ζ 1 = ζ := by
  rw [rootCharacter, show (1 : ZMod 5).val = 1 from rfl, pow_one]

/-- The commutator phase is the symplectic pairing of the charges. -/
theorem chargedWeyl_commute {ζ : ℂ} (hζ : ζ ^ 5 = 1) (a b c d : ZMod 5) :
    chargedWeyl ζ a b * chargedWeyl ζ c d =
      rootCharacter ζ (a * d - c * b) •
        (chargedWeyl ζ c d * chargedWeyl ζ a b) := by
  rw [chargedWeyl_mul hζ, chargedWeyl_mul hζ, smul_smul,
    ← rootCharacter_add hζ]
  rw [show a * d - c * b + -a * d = -c * b by ring,
    add_comm c a, add_comm d b]

/-- The site matrices obey the charged commutator relation. -/
theorem threeLetterTensor_commute {ζ : ℂ} (hζ : ζ ^ 5 = 1) (i j : Fin 3) :
    threeLetterTensor ζ i * threeLetterTensor ζ j =
      rootCharacter ζ ((letterCharge i).1 * (letterCharge j).2 -
        (letterCharge j).1 * (letterCharge i).2) •
      (threeLetterTensor ζ j * threeLetterTensor ζ i) := by
  change (rootCharacter ζ (letterPhase i) •
      chargedWeyl ζ (letterCharge i).1 (letterCharge i).2 : Matrix (ZMod 5) (ZMod 5) ℂ) *
      (rootCharacter ζ (letterPhase j) • chargedWeyl ζ (letterCharge j).1 (letterCharge j).2) =
    rootCharacter ζ ((letterCharge i).1 * (letterCharge j).2 -
        (letterCharge j).1 * (letterCharge i).2) •
      ((rootCharacter ζ (letterPhase j) •
          chargedWeyl ζ (letterCharge j).1 (letterCharge j).2 : Matrix (ZMod 5) (ZMod 5) ℂ) *
        (rootCharacter ζ (letterPhase i) • chargedWeyl ζ (letterCharge i).1 (letterCharge i).2))
  rw [smul_mul_smul_comm, smul_mul_smul_comm, chargedWeyl_commute hζ, smul_smul, smul_smul]
  congr 1
  ring

/-- The cyclically ordered physical letters q-commute. -/
theorem threeLetterTensor_cyclic_commute {ζ : ℂ} (hζ : ζ ^ 5 = 1) (i : Fin 3) :
    threeLetterTensor ζ i * threeLetterTensor ζ (i + 1) =
      ζ • (threeLetterTensor ζ (i + 1) * threeLetterTensor ζ i) := by
  have hdet : (letterCharge i).1 * (letterCharge (i + 1)).2 -
      (letterCharge (i + 1)).1 * (letterCharge i).2 = (1 : ZMod 5) := by
    fin_cases i <;> decide
  simpa only [hdet, rootCharacter_one] using threeLetterTensor_commute hζ i (i + 1)

/-- Each physical letter has fifth power equal to the identity. -/
theorem threeLetterTensor_pow_five {ζ : ℂ} (hζ : ζ ^ 5 = 1) (i : Fin 3) :
    threeLetterTensor ζ i ^ 5 = 1 := by
  have hcharge : wordCharge (List.replicate 5 i) = 0 := by
    fin_cases i <;> decide
  have hphase : wordPhase (List.replicate 5 i) = 0 := by
    fin_cases i <;> decide
  rw [← Kraus.evalWord_replicate, evalWord_threeLetterTensor hζ, hcharge, hphase]
  change (rootCharacter ζ 0 • chargedWeyl ζ (0 : ZMod 5 × ZMod 5).1 (0 : ZMod 5 × ZMod 5).2 :
    Matrix (ZMod 5) (ZMod 5) ℂ) = 1
  simp

/-- Replacing five equal physical letters by five copies of any other
letter preserves the matrix word in every left and right context. -/
theorem evalWord_five_letter_transfer {ζ : ℂ} (hζ : ζ ^ 5 = 1)
    (u v : List (Fin 3)) (i j : Fin 3) :
    Kraus.evalWord (threeLetterTensor ζ) (u ++ List.replicate 5 i ++ v) =
      Kraus.evalWord (threeLetterTensor ζ) (u ++ List.replicate 5 j ++ v) := by
  simp only [Kraus.evalWord_append, Kraus.evalWord_replicate,
    threeLetterTensor_pow_five hζ]

end MPSTensor.ShortMomentum
