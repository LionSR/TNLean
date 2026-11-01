/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.ShortMomentum.CyclicChargeDetection

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
-/

namespace MPSTensor.ShortMomentum

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

end MPSTensor.ShortMomentum
