/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.UnblockedPowerSumCoefficients

/-!
# Signature and axiom checks for the unblocked power-sum theorem

These are permanent smoke tests for
`TNLean/MPS/FundamentalTheorem/SectorBNT/UnblockedPowerSumCoefficients.lean`: each
`example` re-states one main declaration's public signature (a drift check that fails
to compile if the signature changes unexpectedly), and each guarded `#print axioms` checks
that the proof rests only on the standard Lean axioms, with no `sorryAx` in its
transitive closure.
-/

open MPSTensor

variable {d : ℕ}

example {DB : ℕ} (B : MPSTensor d DB) :
    ∃ (g : ℕ) (dimRep : Fin g → ℕ) (A : (j : Fin g) → MPSTensor d (dimRep j))
      (per : Fin g → ℕ) (copies : Fin g → ℕ) (α : (j : Fin g) → Fin (copies j) → ℂ),
      (∀ j, 0 < dimRep j) ∧
      (∀ j, IsPeriodic (per j) (A j)) ∧
      (∀ j, 0 < copies j) ∧
      (∀ j q, α j q ≠ 0) ∧
      (∀ j k : Fin g, j ≠ k → ∀ h : dimRep j = dimRep k,
        ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (A k)) ∧
      (∀ L : ℕ, 0 < L → ∀ σ : Fin L → Fin d,
        mpv B σ = ∑ j : Fin g, (∑ q : Fin (copies j), (α j q) ^ L) * mpv (A j) σ) ∧
      ∑ j : Fin g, copies j * dimRep j ≤ DB :=
  exists_irreducible_expansion B

example {DB : ℕ} (B : MPSTensor d DB) {Γ : Type*} [Fintype Γ] {DM : Γ → ℕ}
    (M : ∀ γ, MPSTensor d (DM γ))
    (hM : ∀ γ, Kraus.IsNormal (M γ)) (hD : ∀ γ, 0 < DM γ)
    (hdistinct : ∀ γ δ : Γ, γ ≠ δ → ∀ h : DM γ = DM δ,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (M γ)) (M δ))
    (hspan : ∀ N : ℕ, 0 < N → ∃ c : Γ → ℂ, ∀ σ : Fin N → Fin d,
      mpv B σ = ∑ γ, c γ * mpv (M γ) σ)
    {g : ℕ} {dimRep : Fin g → ℕ} (A : (j : Fin g) → MPSTensor d (dimRep j))
    (per : Fin g → ℕ) (copies : Fin g → ℕ) (α : (j : Fin g) → Fin (copies j) → ℂ)
    (hPer : ∀ j, IsPeriodic (per j) (A j))
    (hCopiesPos : ∀ j, 0 < copies j)
    (hα : ∀ j q, α j q ≠ 0)
    (hRepDistinct : ∀ j k : Fin g, j ≠ k → ∀ h : dimRep j = dimRep k,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (A k))
    (hBeq : ∀ L : ℕ, 0 < L → ∀ σ : Fin L → Fin d,
      mpv B σ = ∑ j : Fin g, (∑ q : Fin (copies j), (α j q) ^ L) * mpv (A j) σ) :
    ∀ j : Fin g, ∃ γ : Γ, ∃ h : dimRep j = DM γ,
      GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (M γ) :=
  exists_matching_of_span B M hM hD hdistinct hspan A per copies α hPer hCopiesPos hα
    hRepDistinct hBeq

example {DB : ℕ} (B : MPSTensor d DB) {Γ : Type*} [Fintype Γ] {DM : Γ → ℕ}
    (M : ∀ γ, MPSTensor d (DM γ))
    (hM : ∀ γ, Kraus.IsNormal (M γ)) (hD : ∀ γ, 0 < DM γ)
    (hdistinct : ∀ γ δ : Γ, γ ≠ δ → ∀ h : DM γ = DM δ,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (M γ)) (M δ))
    (hspan : ∀ N : ℕ, 0 < N → ∃ c : Γ → ℂ, ∀ σ : Fin N → Fin d,
      mpv B σ = ∑ γ, c γ * mpv (M γ) σ) :
    ∃ (n : Γ → ℕ) (μ : ∀ γ, Fin (n γ) → ℂ),
      (∀ γ k, μ γ k ≠ 0) ∧
      (∀ L : ℕ, 0 < L → ∀ σ : Fin L → Fin d,
        mpv B σ = ∑ γ, (∑ k, (μ γ k) ^ L) * mpv (M γ) σ) ∧
      (∃ L₀ : ℕ, 0 < L₀ ∧ ∀ L, L₀ ≤ L → ∀ c : Γ → ℂ,
        (∀ σ : Fin L → Fin d, mpv B σ = ∑ γ, c γ * mpv (M γ) σ) →
        ∀ γ, c γ = ∑ k, (μ γ k) ^ L) ∧
      ∑ γ, n γ * DM γ ≤ DB :=
  exists_unblocked_powerSum_coeff B M hM hD hdistinct hspan

example {DB : ℕ} (B : MPSTensor d DB) {Γ : Type*} [Fintype Γ] {DM : Γ → ℕ}
    (M : ∀ γ, MPSTensor d (DM γ))
    (hM : ∀ γ, Kraus.IsNormal (M γ)) (hD : ∀ γ, 0 < DM γ)
    (hdistinct : ∀ γ δ : Γ, γ ≠ δ → ∀ h : DM γ = DM δ,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (M γ)) (M δ))
    (hspan : ∀ N : ℕ, 0 < N → ∃ c : Γ → ℂ, ∀ σ : Fin N → Fin d,
      mpv B σ = ∑ γ, c γ * mpv (M γ) σ) :
    ∃ (n : Γ → ℕ) (μ : ∀ γ, Fin (n γ) → ℂ),
      (∀ γ k, μ γ k ≠ 0) ∧
      (∀ L : ℕ, 0 < L → ∀ σ : Fin L → Fin d,
        mpv B σ = ∑ γ, (∑ k, (μ γ k) ^ L) * mpv (M γ) σ) ∧
      (∃ L₀ : ℕ, 0 < L₀ ∧ ∀ L, L₀ ≤ L → ∀ c : Γ → ℂ,
        (∀ σ : Fin L → Fin d, mpv B σ = ∑ γ, c γ * mpv (M γ) σ) →
        ∀ γ, c γ = ∑ k, (μ γ k) ^ L) ∧
      ∑ γ, n γ * DM γ ≤ DB ∧
      ∀ (n' : Γ → ℕ) (μ' : ∀ γ, Fin (n' γ) → ℂ), (∀ γ k, μ' γ k ≠ 0) →
        (∃ L₁ : ℕ, ∀ L, L₁ ≤ L → ∀ σ : Fin L → Fin d,
          mpv B σ = ∑ γ, (∑ k, (μ' γ k) ^ L) * mpv (M γ) σ) →
        ∀ γ, (↑(List.ofFn (μ' γ)) : Multiset ℂ) = ↑(List.ofFn (μ γ)) :=
  exists_unblocked_powerSum_coeff_unique B M hM hD hdistinct hspan

-- Axiom-report commands are intentional in this regression-test section.
section AxiomChecks
set_option linter.hashCommand false

/-- info: 'MPSTensor.dim_eq_of_mpvBlockPhaseEquiv_of_isPeriodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.dim_eq_of_mpvBlockPhaseEquiv_of_isPeriodic

/-- info: 'MPSTensor.exists_irreducible_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.exists_irreducible_expansion

/-- info: 'MPSTensor.exists_matching_of_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.exists_matching_of_span

/-- info: 'MPSTensor.exists_unblocked_powerSum_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.exists_unblocked_powerSum_coeff

/-- info: 'MPSTensor.exists_unblocked_powerSum_coeff_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.exists_unblocked_powerSum_coeff_unique

end AxiomChecks
