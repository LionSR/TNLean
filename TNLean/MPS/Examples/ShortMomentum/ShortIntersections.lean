/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.ShortMomentum.ShortOverlapBridges
import TNLean.MPS.Examples.ShortMomentum.OverlapChargeCoefficients

/-!
# The eight- and nine-site Weyl intersections

The actual left and right boundary restrictions supply endpoint charge
functions normalized by the full word phase. An actual middle word equates
the two endpoint functions at its total charge. The finite charge bridges
therefore assemble a single charge function for the full vector.

At eight sites, the isolated endpoint with zero complementary seven-site
charge cannot occur in an actual word. Only active endpoints are compared.
At nine sites every endpoint is compared. These prove the two exceptional
open-chain intersections without a supplied global-space or kernel premise.
Source context: SPWC10, arXiv:0909.5347, Theorem 5, lines 850--880.
-/

namespace MPSTensor.ShortMomentum

private theorem overlap_charge_edge {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    {n : ℕ} (ψ : NSiteSpace 3 (n + 2)) (H K : Fin 3 → (ZMod 5 × ZMod 5) → ℂ)
    (hH : ∀ j σ, ψ (Fin.snoc σ j) =
      rootCharacter ζ (wordPhase (List.ofFn (Fin.snoc σ j))) *
        H j (wordCharge (List.ofFn (Fin.snoc σ j))))
    (hK : ∀ i σ, ψ (Fin.cons i σ) =
      rootCharacter ζ (wordPhase (List.ofFn (Fin.cons i σ))) *
        K i (wordCharge (List.ofFn (Fin.cons i σ))))
    (p : ZMod 5 × ZMod 5) (i j : Fin 3) (σ : Cfg 3 n)
    (hσ : wordCharge (List.ofFn σ) = p - letterCharge i - letterCharge j) :
    H j p = K i p := by
  have hcharge : wordCharge (List.ofFn (Fin.snoc (Fin.cons i σ) j)) = p := by
    rw [List.ofFn_snoc, List.ofFn_cons, wordCharge_append, wordCharge_singleton,
      wordCharge_cons, hσ]
    abel
  have hL := hH j (Fin.cons i σ)
  have hR := hK i (Fin.snoc σ j)
  rw [Fin.cons_snoc_eq_snoc_cons] at hR
  rw [hcharge] at hL hR
  exact mul_left_cancel₀
    (rootCharacter_ne_zero hζ (wordPhase (List.ofFn (Fin.snoc (Fin.cons i σ) j))))
    (hL.symm.trans hR)

private theorem exists_active_endpoint (p : ZMod 5 × ZMod 5) :
    ∃ j : Fin 3, p ≠ letterCharge j := by
  by_cases h : p = letterCharge 0
  · refine ⟨1, ?_⟩
    rw [h]
    decide
  · exact ⟨0, h⟩

private theorem first_endpoint_active_eight (σ : Cfg 3 8) :
    wordCharge (List.ofFn σ) ≠ letterCharge (σ 0) := by
  intro h
  have hcharge := wordCharge_cons (σ 0) (List.ofFn (Fin.tail σ))
  rw [← List.ofFn_cons, Fin.cons_self_tail] at hcharge
  have hzero : wordCharge (List.ofFn (Fin.tail σ)) = 0 := by
    apply add_left_cancel (a := letterCharge (σ 0))
    simpa only [add_zero] using hcharge.symm.trans h
  exact wordCharge_ne_zero_of_length_seven (by simp) hzero

/-- The actual left and right seven-site boundary conditions reconstruct the
full eight-site boundary space. Only endpoint charges reached by actual words
are compared. Source: the short overlap in the SPWC10 finite-prefix investigation. -/
theorem groundSpace_intersection_threeLetterTensor_eight {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) {ψ : NSiteSpace 3 8}
    (hLeft : InLeftGround (threeLetterTensor ζ) 7 ψ)
    (hRight : InRightGround (threeLetterTensor ζ) 7 ψ) :
    ψ ∈ groundSpace (threeLetterTensor ζ) 8 := by
  classical
  obtain ⟨H, K, hH, hK⟩ := exists_overlap_charge_coefficients hζ ψ hLeft hRight
  have hedge (p : ZMod 5 × ZMod 5) (i j : Fin 3)
      (hij : p - letterCharge i - letterCharge j ∉
        ({(0, 4), (1, 1), (4, 0)} : Finset (ZMod 5 × ZMod 5))) : H j p = K i p := by
    have hbad : p - letterCharge i - letterCharge j ≠ (0, 4) ∧
        p - letterCharge i - letterCharge j ≠ (1, 1) ∧
        p - letterCharge i - letterCharge j ≠ (4, 0) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hij
    obtain ⟨σ, hσ⟩ := exists_six_config_of_charge _ _ hbad.1 hbad.2.1 hbad.2.2
    exact overlap_charge_edge hζ ψ H K hH hK p i j σ hσ
  choose pivot hpivot using exists_active_endpoint
  apply (mem_groundSpace_threeLetterTensor_iff hζ 8 ψ).mpr
  refine ⟨fun p ↦ H (pivot p) p, fun σ ↦ ?_⟩
  have h := hK (σ 0) (Fin.tail σ)
  rw [Fin.cons_self_tail] at h
  have hcmp := eq_of_six_overlap_charge_edges (wordCharge (List.ofFn σ))
    (fun j ↦ H j (wordCharge (List.ofFn σ)))
    (fun i ↦ K i (wordCharge (List.ofFn σ)))
    (hedge (wordCharge (List.ofFn σ))) (σ 0) (pivot (wordCharge (List.ofFn σ)))
    (first_endpoint_active_eight σ) (hpivot (wordCharge (List.ofFn σ)))
  exact h.trans (congrArg (fun z ↦ rootCharacter ζ (wordPhase (List.ofFn σ)) * z) hcmp.symm)

/-- The actual left and right eight-site boundary conditions reconstruct the
full nine-site boundary space. Its seven-site middle words realize every
noncentral charge. Source: the short overlap in the SPWC10 finite-prefix investigation. -/
theorem groundSpace_intersection_threeLetterTensor_nine {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) {ψ : NSiteSpace 3 9}
    (hLeft : InLeftGround (threeLetterTensor ζ) 8 ψ)
    (hRight : InRightGround (threeLetterTensor ζ) 8 ψ) :
    ψ ∈ groundSpace (threeLetterTensor ζ) 9 := by
  obtain ⟨H, K, hH, hK⟩ := exists_overlap_charge_coefficients hζ ψ hLeft hRight
  have hedge (p : ZMod 5 × ZMod 5) (i j : Fin 3)
      (hij : p - letterCharge i - letterCharge j ≠ 0) : H j p = K i p := by
    obtain ⟨w, hw, hcharge⟩ := exists_word_seven_of_charge _ _ hij
    obtain ⟨n, σ, rfl⟩ := List.exists_eq_ofFn w
    have hn : n = 7 := by simpa using hw
    subst n
    exact overlap_charge_edge hζ ψ H K hH hK p i j σ hcharge
  apply (mem_groundSpace_threeLetterTensor_iff hζ 9 ψ).mpr
  refine ⟨fun p ↦ H 0 p, fun σ ↦ ?_⟩
  have h := hK (σ 0) (Fin.tail σ)
  rw [Fin.cons_self_tail] at h
  have hcmp := eq_of_seven_overlap_charge_edges (wordCharge (List.ofFn σ))
    (fun j ↦ H j (wordCharge (List.ofFn σ)))
    (fun i ↦ K i (wordCharge (List.ofFn σ)))
    (hedge (wordCharge (List.ofFn σ))) (σ 0) 0
  exact h.trans (congrArg (fun z ↦ rootCharacter ζ (wordPhase (List.ofFn σ)) * z) hcmp.symm)

end MPSTensor.ShortMomentum
