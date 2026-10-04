/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularChargeDetectorMatrix
import TNLean.PEPS.RegularSiteGram
import Mathlib.Logic.Equiv.Prod
import TNLean.Algebra.FinSumPermutation

/-!
# Actual shared-leg charge coordinates

Two arbitrary finite incident-leg sets are split at one shared leg each using
Mathlib's function-coordinate equivalence. Expanding the two local regular
averages identifies their literal shared-bond contraction with the translated
charge matrix, while retaining every remaining boundary label.

Source: SCP10, arXiv:1001.3807, charge detection, lines 2464–2486.
**Scope restriction (finite-leg identities):** This is the actual two-site
coefficient calculation, before a prescribed lattice block is chosen. The
source's original-spin detector is supplied by physical transport separately;
no six-spin creation or parent-Hamiltonian conclusion is asserted.
See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Split the two shared group labels from all other incident labels.
Source: SCP10, charge detection, lines 2464–2486. -/
def regularSharedLegEquiv (i : ι) (j : κ) :
    ((ι → G) × (κ → G)) ≃
      (G × G) × (({e : ι // e ≠ i} → G) × ({e : κ // e ≠ j} → G)) :=
  ((Equiv.funSplitAt i G).prodCongr (Equiv.funSplitAt j G)).trans
    (Equiv.prodProdProdComm _ _ _ _)

/-- The literal canonical two-site column with a character on the shared bond.
All other virtual labels are retained as boundary coordinates.
Source: SCP10, charge detection, lines 2464–2486. -/
def regularTwoSiteChargeColumn (i : ι) (j : κ) (χ : G → ℂ) (p : G)
    (θ : ({e : ι // e ≠ i} → G) × ({e : κ // e ≠ j} → G))
    (α : (ι → G) × (κ → G)) : ℂ :=
  ∑ k : G, χ (p * k) *
    regularLegProjector ι α.1 ((Equiv.funSplitAt i G).symm (k, θ.1)) *
    regularLegProjector κ α.2 ((Equiv.funSplitAt j G).symm (k, θ.2))

/-- The shared-label character matrix appears in each pair of independent local averages.
Source: SCP10, charge detection, lines 2470–2486. -/
theorem regularTwoSiteChargeColumn_apply (i : ι) (j : κ) (χ : G → ℂ) (p : G)
    (θ : ({e : ι // e ≠ i} → G) × ({e : κ // e ≠ j} → G))
    (α : (ι → G) × (κ → G)) :
    regularTwoSiteChargeColumn i j χ p θ α =
      (Fintype.card G : ℂ)⁻¹ ^ 2 * ∑ x : G, ∑ y : G,
        regularChargeMatrix χ p x y (α.1 i) (α.2 j) *
          (if (fun e : {e : ι // e ≠ i} => α.1 e) = x • θ.1 then 1 else 0) *
          (if (fun e : {e : κ // e ≠ j} => α.2 e) = y • θ.2 then 1 else 0) := by
  classical
  have hs (k x : G) :
      α.1 = x • (Equiv.funSplitAt i G).symm (k, θ.1) ↔
        α.1 i = x * k ∧ (fun e : {e : ι // e ≠ i} => α.1 e) = x • θ.1 := by
    constructor
    · intro h
      constructor
      · simpa using congrFun h i
      · funext e
        simpa [e.property] using congrFun h e
    · rintro ⟨h, hb⟩
      funext e
      by_cases he : e = i
      · subst e
        simpa using h
      · simpa [he] using congrFun hb ⟨e, he⟩
  have ht (k y : G) :
      α.2 = y • (Equiv.funSplitAt j G).symm (k, θ.2) ↔
        α.2 j = y * k ∧ (fun e : {e : κ // e ≠ j} => α.2 e) = y • θ.2 := by
    constructor
    · intro h
      constructor
      · simpa using congrFun h j
      · funext e
        simpa [e.property] using congrFun h e
    · rintro ⟨h, hb⟩
      funext e
      by_cases he : e = j
      · subst e
        simpa using h
      · simpa [he] using congrFun hb ⟨e, he⟩
  simp only [regularTwoSiteChargeColumn, regularLegProjector_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Fintype.sum_reverse_three]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [hs, ht, ite_and]
  have hrow (k : G) : α.1 i = x * k ↔ k = x⁻¹ * α.1 i := by
    constructor
    · intro h
      rw [h]
      group
    · rintro rfl
      group
  rw [Finset.sum_eq_single (x⁻¹ * α.1 i)]
  · simp only [hrow, ite_true, regularChargeMatrix, pow_two,
      mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
    split_ifs <;> (first | (solve | ring) | grind)
  · intro k _ hk
    simp [hrow, hk]
  · simp
end TNLean.PEPS
