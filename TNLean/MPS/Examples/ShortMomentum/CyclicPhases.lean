/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ListOfFn
import TNLean.MPS.Examples.ShortMomentum.LocalSpace

/-!
# Actual cyclic phase comparison for charged local spaces

The word exponent obeys the actual matrix cocycle under concatenation.
Moving the first letter to the end changes it by the symplectic pairing
of that letter with the total charge. This derives the charge comparison
for two actual local boundary vectors whose coefficients agree across
a cyclic cut. No all-volume intersection classification is assumed.

Source context: SPWC10, arXiv:0909.5347, Theorem 5, main.tex lines 850--880;
see `docs/audits/2026-10-29_weyl_short_volume_candidate.md`.
-/

namespace MPSTensor.ShortMomentum

/-- The symplectic pairing of a physical letter with a total virtual charge. -/
def letterPairing (i : Fin 3) (p : ZMod 5 × ZMod 5) : ZMod 5 :=
  (letterCharge i).1 * p.2 - p.1 * (letterCharge i).2

/-- The exact word exponent obeys the same cocycle as the actual matrices. -/
theorem wordPhase_append (u v : List (Fin 3)) :
    wordPhase (u ++ v) = wordPhase u + wordPhase v -
      (wordCharge v).1 * (wordCharge u).2 := by
  induction u with
  | nil => simp [wordPhase, wordCharge, countCharge]
  | cons i u ih =>
      simp only [List.cons_append, wordPhase, wordCharge_append, wordCharge_cons,
        Prod.fst_add, Prod.snd_add, ih]
      ring

@[simp] theorem wordCharge_singleton (i : Fin 3) : wordCharge [i] = letterCharge i := by
  rw [wordCharge_cons]
  simp [wordCharge, countCharge]

@[simp] theorem wordPhase_singleton (i : Fin 3) : wordPhase [i] = letterPhase i := by
  simp [wordPhase, wordCharge, countCharge]

/-- Moving the first physical letter to the end produces its actual cyclic phase. -/
theorem wordPhase_cons_sub_snoc (i : Fin 3) (w : List (Fin 3)) :
    wordPhase (i :: w) - wordPhase (w ++ [i]) =
      letterPairing i (wordCharge (i :: w)) := by
  rw [wordPhase_append, wordPhase_singleton, wordCharge_singleton, wordPhase,
    wordCharge_cons]
  simp only [letterPairing, Prod.fst_add, Prod.snd_add]
  ring

/-- The exact cyclic change of the actual scalar word phase. -/
theorem rootCharacter_wordPhase_cons {ζ : ℂ} (hζ : ζ ^ 5 = 1)
    (i : Fin 3) (w : List (Fin 3)) :
    rootCharacter ζ (wordPhase (i :: w)) =
      rootCharacter ζ (letterPairing i (wordCharge (i :: w))) *
        rootCharacter ζ (wordPhase (w ++ [i])) := by
  rw [← rootCharacter_add hζ]
  congr 1
  linear_combination wordPhase_cons_sub_snoc i w

/-- Two actual boundary vectors agreeing across a cyclic cut have charge
coefficients related by the actual cyclic phase, with no comparison premise
about those coefficients. -/
theorem exists_charge_comparison_of_cyclic_agreement {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) {n : ℕ} (f g : NSiteSpace 3 (n + 1))
    (hf : f ∈ groundSpace (threeLetterTensor ζ) (n + 1))
    (hg : g ∈ groundSpace (threeLetterTensor ζ) (n + 1))
    (hfg : ∀ (i : Fin 3) (σ : Cfg 3 n), f (Fin.cons i σ) = g (Fin.snoc σ i)) :
    ∃ F G : ZMod 5 × ZMod 5 → ℂ,
      (∀ σ, f σ = rootCharacter ζ (wordPhase (List.ofFn σ)) *
        F (wordCharge (List.ofFn σ))) ∧
      (∀ σ, g σ = rootCharacter ζ (wordPhase (List.ofFn σ)) *
        G (wordCharge (List.ofFn σ))) ∧
      ∀ (i : Fin 3) (σ : Cfg 3 n),
        G (wordCharge (i :: List.ofFn σ)) =
          rootCharacter ζ (letterPairing i (wordCharge (i :: List.ofFn σ))) *
            F (wordCharge (i :: List.ofFn σ)) := by
  obtain ⟨F, hF⟩ := (mem_groundSpace_threeLetterTensor_iff hζ (n + 1) f).mp hf
  obtain ⟨G, hG⟩ := (mem_groundSpace_threeLetterTensor_iff hζ (n + 1) g).mp hg
  refine ⟨F, G, hF, hG, ?_⟩
  intro i σ
  have h := hfg i σ
  rw [hF, hG, List.ofFn_cons, List.ofFn_snoc] at h
  have hc : wordCharge (List.ofFn σ ++ [i]) = wordCharge (i :: List.ofFn σ) := by
    rw [wordCharge_append, wordCharge_singleton, wordCharge_cons, add_comm]
  rw [hc, rootCharacter_wordPhase_cons hζ.pow_eq_one] at h
  have hphase := rootCharacter_ne_zero hζ (wordPhase (List.ofFn σ ++ [i]))
  apply (mul_left_cancel₀ hphase)
  calc
    rootCharacter ζ (wordPhase (List.ofFn σ ++ [i])) *
        G (wordCharge (i :: List.ofFn σ)) =
        (rootCharacter ζ (letterPairing i (wordCharge (i :: List.ofFn σ))) *
          rootCharacter ζ (wordPhase (List.ofFn σ ++ [i]))) *
          F (wordCharge (i :: List.ofFn σ)) := h.symm
    _ = _ := by ring

end MPSTensor.ShortMomentum
