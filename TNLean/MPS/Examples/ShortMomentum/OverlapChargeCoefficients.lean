/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.ShortMomentum.CyclicPhases
import TNLean.MPS.ParentHamiltonian.IntersectionProperty

/-!
# Actual charge coefficients for two overlapping boundary windows

The left and right boundary-space conditions on an actual physical
vector supply normalized charge functions for each fixed endpoint.
The normalization uses the actual full-word scalar phase. No endpoint
coefficient agreement or global boundary-space membership is assumed.

Source context: SPWC10, arXiv:0909.5347, Theorem 5, main.tex lines 850--880;
see `docs/audits/2026-10-29_weyl_short_volume_candidate.md`.
-/

namespace MPSTensor.ShortMomentum

/-- Actual left and right local boundary conditions give charge
coefficients normalized by the actual full-word phase. The functions may
be arbitrary on charges not reached with the fixed endpoint. -/
theorem exists_overlap_charge_coefficients {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    {n : ℕ} (ψ : NSiteSpace 3 (n + 2))
    (hLeft : InLeftGround (threeLetterTensor ζ) (n + 1) ψ)
    (hRight : InRightGround (threeLetterTensor ζ) (n + 1) ψ) :
    ∃ H K : Fin 3 → (ZMod 5 × ZMod 5) → ℂ,
      (∀ (j : Fin 3) (σ : Cfg 3 (n + 1)),
        ψ (Fin.snoc σ j) =
          rootCharacter ζ (wordPhase (List.ofFn (Fin.snoc σ j))) *
            H j (wordCharge (List.ofFn (Fin.snoc σ j)))) ∧
      (∀ (i : Fin 3) (σ : Cfg 3 (n + 1)),
        ψ (Fin.cons i σ) =
          rootCharacter ζ (wordPhase (List.ofFn (Fin.cons i σ))) *
            K i (wordCharge (List.ofFn (Fin.cons i σ)))) := by
  classical
  choose F hF using fun j ↦
    (mem_groundSpace_threeLetterTensor_iff hζ (n + 1) (restrictLast ψ j)).mp (hLeft j)
  choose G hG using fun i ↦
    (mem_groundSpace_threeLetterTensor_iff hζ (n + 1) (restrictFirst ψ i)).mp (hRight i)
  let H : Fin 3 → (ZMod 5 × ZMod 5) → ℂ := fun j q ↦
    rootCharacter ζ (-letterPhase j + (letterCharge j).1 * (q - letterCharge j).2) *
      F j (q - letterCharge j)
  let K : Fin 3 → (ZMod 5 × ZMod 5) → ℂ := fun i q ↦
    rootCharacter ζ (-letterPhase i + (q - letterCharge i).1 * (letterCharge i).2) *
      G i (q - letterCharge i)
  refine ⟨H, K, ?_, ?_⟩
  · intro j σ
    change ψ (Fin.snoc σ j) = _ *
      (rootCharacter ζ (-letterPhase j + (letterCharge j).1 *
        (wordCharge (List.ofFn (Fin.snoc σ j)) - letterCharge j).2) *
        F j (wordCharge (List.ofFn (Fin.snoc σ j)) - letterCharge j))
    have hcharge : wordCharge (List.ofFn (Fin.snoc σ j)) - letterCharge j =
        wordCharge (List.ofFn σ) := by
      rw [List.ofFn_snoc, wordCharge_append, wordCharge_singleton, add_sub_cancel_right]
    rw [hcharge, ← mul_assoc, ← rootCharacter_add hζ.pow_eq_one]
    have hphase : wordPhase (List.ofFn (Fin.snoc σ j)) +
        (-letterPhase j + (letterCharge j).1 * (wordCharge (List.ofFn σ)).2) =
        wordPhase (List.ofFn σ) := by
      rw [List.ofFn_snoc, wordPhase_append, wordPhase_singleton, wordCharge_singleton]
      ring
    rw [hphase]
    exact hF j σ
  · intro i σ
    change ψ (Fin.cons i σ) = _ *
      (rootCharacter ζ (-letterPhase i +
        (wordCharge (List.ofFn (Fin.cons i σ)) - letterCharge i).1 * (letterCharge i).2) *
        G i (wordCharge (List.ofFn (Fin.cons i σ)) - letterCharge i))
    have hcharge : wordCharge (List.ofFn (Fin.cons i σ)) - letterCharge i =
        wordCharge (List.ofFn σ) := by
      rw [List.ofFn_cons, wordCharge_cons, add_sub_cancel_left]
    rw [hcharge, ← mul_assoc, ← rootCharacter_add hζ.pow_eq_one]
    have hphase : wordPhase (List.ofFn (Fin.cons i σ)) +
        (-letterPhase i + (wordCharge (List.ofFn σ)).1 * (letterCharge i).2) =
        wordPhase (List.ofFn σ) := by
      rw [List.ofFn_cons, wordPhase]
      ring
    rw [hphase]
    exact hG i σ

end MPSTensor.ShortMomentum
