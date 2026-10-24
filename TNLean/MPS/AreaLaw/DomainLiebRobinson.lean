/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ComponentReduction
import TNLean.Circuit.EntropySupport
import TNLean.Circuit.LiebRobinson.GraphPropagation

/-!
# Lieb–Robinson commutator estimate on finite integer domains

For a finite induced integer domain, finite-range interactions satisfy the
contiguous-chain commutator estimate with the same constants. The initial
support may meet several components. Its evolution commutes exactly with an
on-site observable at infinite distance from the support.

This extends the chain estimate of the TNLean one-dimensional note,
`part2a_mps_information.tex`, Lemma `lem:LR`, lines 267–309, to the finite
domains specified in `part0_preamble.tex`, lines 191–215. No ground-state or
spectral-gap assumption is used.
-/

open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The finite-domain commutator estimate, extending the chain estimate of the
TNLean one-dimensional note, `part2a_mps_information.tex`, Lemma `lem:LR`, lines 267–309,
to the induced integer domains of `part0_preamble.tex`, lines 191–215. -/
theorem norm_heisenberg_commutator_le_domainDistance
    {Λ : Finset ℤ} {q R : ℕ} {κ : Type*} [Fintype κ]
    (X : κ → DomainSupport Λ R)
    (h : κ → Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ)
    (hHerm : ∀ k, (h k).IsHermitian)
    (hSupport : ∀ k, Entropy.IsSupportedOn (n := fun _ ↦ q) (h k) (X k).1)
    (b₀ : ℝ)
    (hBudget : ∀ x : Fin Λ.card,
      ∑ k ∈ Finset.univ.filter (fun k ↦ x ∈ (X k).1), ‖h k‖ ≤ b₀)
    (S : Finset (Fin Λ.card))
    {A B : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ}
    (hA : Entropy.IsSupportedOn (n := fun _ ↦ q) A S) (y : Fin Λ.card)
    (hB : Entropy.IsSupportedOn (n := fun _ ↦ q) B {y}) (t : ℝ) :
    let δ : ℕ∞ := S.inf (fun x ↦ (domainGraph Λ).edist x y)
    ‖QuantumCircuit.heisenbergEvolution (∑ k, h k) t A * B -
        B * QuantumCircuit.heisenbergEvolution (∑ k, h k) t A‖ ≤
      (2 + 4 * |b₀| * Real.exp (2 * R)) * (S.card : ℝ) * ‖A‖ * ‖B‖ *
        Real.exp ((2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1) * |t|) *
        (if δ = ⊤ then 0 else Real.exp (-((δ.toNat : ℝ) / 2))) := by
  classical
  let a : κ → Fin Λ.card := fun k ↦ Classical.choose (X k).2.1
  have ha : ∀ k, a k ∈ (X k).1 := fun k ↦ Classical.choose_spec (X k).2.1
  have hBound (n : ℕ)
      (hn : ∀ x ∈ S, (n : ℕ∞) ≤ (domainGraph Λ).edist x y) :=
    QuantumCircuit.norm_heisenberg_commutator_le_graphDistance_finset
      (domainGraph Λ) (fun k ↦ (X k).1) a ha h hHerm
      (fun k ↦ QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hSupport k))
      R (fun k x hx z hz ↦ (X k).2.2 x hx z hz)
      (R + 1) (fun k ↦ (X k).2.isChainSupport.card_le) b₀ hBudget S
      (QuantumCircuit.mem_supportedOperators_of_isSupportedOn hA) y
      (by simpa only [Finset.coe_singleton] using
        QuantumCircuit.mem_supportedOperators_of_isSupportedOn hB)
      1 (by norm_num) n hn t
  dsimp only
  set δ := S.inf (fun x ↦ (domainGraph Λ).edist x y)
  by_cases hδ : δ = ⊤
  · have hComm := QuantumCircuit.heisenberg_commutator_eq_zero_of_forall_edist_eq_top
      (domainGraph Λ) (fun k ↦ (X k).1) h
      (fun k ↦ QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hSupport k))
      R (fun k x hx z hz ↦ (X k).2.2 x hx z hz) S
      (QuantumCircuit.mem_supportedOperators_of_isSupportedOn hA) y
      (by simpa only [Finset.coe_singleton] using
        QuantumCircuit.mem_supportedOperators_of_isSupportedOn hB)
      (fun x hx ↦ top_unique (hδ ▸
        (Finset.inf_le hx : δ ≤ (domainGraph Λ).edist x y))) t
    simp only [hComm, norm_zero, ite_eq_left hδ, mul_zero, le_refl]
  · have hGraph := hBound δ.toNat (fun x hx ↦
      (ENat.natCast_toNat_le_self δ).trans (Finset.inf_le hx))
    simp only [mul_one, one_mul, Nat.cast_add, Nat.cast_one, ite_eq_right hδ] at hGraph ⊢
    have hDecay :
        Real.exp ((2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1) * |t| - (δ.toNat : ℝ)) ≤
          Real.exp ((2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1) * |t|) *
            Real.exp (-((δ.toNat : ℝ) / 2)) := by
      simpa only [Real.exp_add] using Real.exp_le_exp.mpr
        (show (2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1) * |t| - (δ.toNat : ℝ) ≤
          (2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1) * |t| + -((δ.toNat : ℝ) / 2) by
          linarith [Nat.cast_nonneg (α := ℝ) δ.toNat])
    exact hGraph.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hDecay
        (show 0 ≤ (2 + 4 * |b₀| * Real.exp (2 * R)) * (S.card : ℝ) * ‖A‖ * ‖B‖ by
          positivity))

end TNLean.MPS.AreaLaw
