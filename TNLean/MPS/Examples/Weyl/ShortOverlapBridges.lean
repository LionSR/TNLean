/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.Weyl.CyclicChargeDetection
import TNLean.MPS.Examples.Weyl.CyclicPhases

/-!
# Finite charge bridges for the two short overlaps

At degree six the three missing charges leave an isolated boundary letter
precisely when its complementary degree-seven charge is zero. Such a letter
cannot occur at that endpoint of an actual degree-eight word. Every pair of
active endpoint letters has a three-edge overlap bridge. At degree seven only
the zero charge is missing and every pair of endpoint letters has such a bridge.

The assertions are finite charge identities; the bridges themselves are
quantified witnesses, verified by finite case analysis over the twenty-five
charges. They do not assume or assert a Hamiltonian kernel or open-chain
intersection property.
Source context: SPWC10, arXiv:0909.5347, Theorem 5, lines 850--880.

It also contains the following results.

* `MPSTensor.ShortMomentum.groundSpace_intersection_threeLetterTensor_eight`,
  `MPSTensor.ShortMomentum.groundSpace_intersection_threeLetterTensor_nine`: the eight- and
  nine-site Weyl intersections.
-/

namespace MPSTensor.ShortMomentum

section ShortOverlapBridges

/-- Actual degree-six charge exclusions admit a three-edge bridge between
any two active endpoint letters. Inactive means that the complementary
seven-site charge is zero, which no seven-site word realizes.
Source: finite charge arithmetic for the SPWC10 finite-prefix investigation. -/
theorem exists_six_overlap_charge_bridge (p : ZMod 5 × ZMod 5) :
    ∀ i j : Fin 3, p ≠ letterCharge i → p ≠ letterCharge j →
      ∃ k l : Fin 3,
        (p - letterCharge i - letterCharge k ∉
          ({(0, 4), (1, 1), (4, 0)} : Finset (ZMod 5 × ZMod 5))) ∧
        (p - letterCharge l - letterCharge k ∉
          ({(0, 4), (1, 1), (4, 0)} : Finset (ZMod 5 × ZMod 5))) ∧
        (p - letterCharge l - letterCharge j ∉
          ({(0, 4), (1, 1), (4, 0)} : Finset (ZMod 5 × ZMod 5))) := by
  obtain ⟨u, v⟩ := p
  fin_cases u <;> fin_cases v <;> decide

/-- With only zero charge absent at degree seven, every pair of endpoint
letters admits a three-edge bridge.
Source: finite charge arithmetic for the SPWC10 finite-prefix investigation. -/
theorem exists_seven_overlap_charge_bridge (p : ZMod 5 × ZMod 5) :
    ∀ i j : Fin 3, ∃ k l : Fin 3,
      p - letterCharge i - letterCharge k ≠ 0 ∧
      p - letterCharge l - letterCharge k ≠ 0 ∧
      p - letterCharge l - letterCharge j ≠ 0 := by
  obtain ⟨u, v⟩ := p
  fin_cases u <;> fin_cases v <;> decide

/-- Equal endpoint coefficients along the actual degree-six overlap edges
therefore agree between every pair of active endpoints. No equality between
unrealized endpoint charges is required.
Source: the degree-six charge bridge in the SPWC10 finite-prefix investigation. -/
theorem eq_of_six_overlap_charge_edges (p : ZMod 5 × ZMod 5) (F G : Fin 3 → ℂ)
    (h : ∀ i j : Fin 3,
      p - letterCharge i - letterCharge j ∉
        ({(0, 4), (1, 1), (4, 0)} : Finset (ZMod 5 × ZMod 5)) → F j = G i)
    (i j : Fin 3) (hi : p ≠ letterCharge i) (hj : p ≠ letterCharge j) : F j = G i := by
  obtain ⟨k, l, hik, hlk, hlj⟩ := exists_six_overlap_charge_bridge p i j hi hj
  exact (h l j hlj).trans ((h l k hlk).symm.trans (h i k hik))

/-- Equal endpoint coefficients along the actual degree-seven overlap edges
agree between every pair of endpoints.
Source: the degree-seven charge bridge in the SPWC10 finite-prefix investigation. -/
theorem eq_of_seven_overlap_charge_edges (p : ZMod 5 × ZMod 5) (F G : Fin 3 → ℂ)
    (h : ∀ i j : Fin 3, p - letterCharge i - letterCharge j ≠ 0 → F j = G i)
    (i j : Fin 3) : F j = G i := by
  obtain ⟨k, l, hik, hlk, hlj⟩ := exists_seven_overlap_charge_bridge p i j
  exact (h l j hlj).trans ((h l k hlk).symm.trans (h i k hik))

end ShortOverlapBridges

section ShortIntersections

/-!
## The eight- and nine-site Weyl intersections

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

private theorem overlap_charge_edge {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    {n : ℕ} (ψ : NSiteSpace (Fin 3) (n + 2)) (H K : Fin 3 → (ZMod 5 × ZMod 5) → ℂ)
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
    (hζ : IsPrimitiveRoot ζ 5) {ψ : NSiteSpace (Fin 3) 8}
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
    (hζ : IsPrimitiveRoot ζ 5) {ψ : NSiteSpace (Fin 3) 9}
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

end ShortIntersections

end MPSTensor.ShortMomentum
