/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.SuccessiveStep
import TNLean.MPS.AreaLaw.ViableSet.Endpoints
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# The sweep

Starting with the scalar singleton at the empty cut, each family of the sweep `lvvSweep`
is the step `lvvSweepStep` applied to the previous one: extend by one site, take the
size-trimming selection of the extension, trim each selected vector independently through
its bonds, and apply the Gaussian filter factors. The sweep is a function of the chain
terms and the gap parameter alone, chosen before any ground energy or ground vector. For
every ground pair with the prescribed gap, all its families satisfy the required
viability bounds.

**Local fix (trimming radius):** The independent trimmings use the quadratic radius
recorded at <https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>.
The constant-cut bond and net-exponent scope is documented in
`docs/paper-gaps/lvv13_constant_bond.tex`; the use of Huang's Gaussian filters is
documented in `docs/paper-gaps/lvv13_runtime_ground_energy.tex`.

Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, the induction at lines 652--678,
using Huang, arXiv:1406.6355v6, Section 5.4, Lemmas 18--19 for error reduction.
-/

open ManyBody (interval)

open Matrix
open scoped ComplexOrder MatrixOrder

open ManyBody (IsGapped groundSpace)

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- **The sweep.** Starting from the scalar singleton at the empty cut, the family at the
cut after `i + 1` sites is the step `lvvSweepStep` applied to the family at the cut after
`i` sites, as long as `i + 1 ≤ L`; beyond the chain the families are empty. The sweep is a
function of the chain terms and the gap parameter alone. LVV13, `algo53.tex`,
lines 652--678, with Huang's Gaussian error reduction. -/
noncomputable def lvvSweep (hq : 2 ≤ q)
    (Φ : ManyBody.BondInteraction L q)
(h0 : ∀ j, 0 ≤ Φ.term j) (h1 : ∀ j, Φ.term j ≤ 1)
    (Delta : ℝ) : (i : ℕ) → Finset (LeftBlockVector L q i)
  | 0 => {emptyLeftVector L q}
  | i + 1 =>
    if hi : i + 1 ≤ L then lvvSweepStep hq Φ h0 Delta hi (lvvSweep hq Φ h0 h1 Delta i)
    else ∅

/-- The sweep starts from the scalar singleton. LVV13, `algo53.tex`, line 655. -/
theorem lvvSweep_zero (hq : 2 ≤ q)
    (Φ : ManyBody.BondInteraction L q)
(h0 : ∀ j, 0 ≤ Φ.term j) (h1 : ∀ j, Φ.term j ≤ 1) (Delta : ℝ) :
    lvvSweep hq Φ h0 h1 Delta 0 = {emptyLeftVector L q} := rfl

/-- Each family of the sweep is the step applied to the previous one.
LVV13, `algo53.tex`, lines 652--678. -/
theorem lvvSweep_succ (hq : 2 ≤ q)
    (Φ : ManyBody.BondInteraction L q)
(h0 : ∀ j, 0 ≤ Φ.term j) (h1 : ∀ j, Φ.term j ≤ 1) (Delta : ℝ)
    {i : ℕ} (hi : i + 1 ≤ L) :
    lvvSweep hq Φ h0 h1 Delta (i + 1) =
      lvvSweepStep hq Φ h0 Delta hi (lvvSweep hq Φ h0 h1 Delta i) := by
  simp only [lvvSweep, hi, ↓reduceDIte]

/-- **The sweep produces viable families of polynomial size and bond dimension.** Positive
cuts have uniform explicit size and bond budgets, the empty cut has its scalar singleton,
and for every ground pair with the prescribed gap every family of the sweep is viable.
LVV13, `algo53.tex`, lines 652--678, with the documented quadratic trimming correction and
Huang's Gaussian error reduction. -/
theorem lvvSweep_spec (hq : 2 ≤ q)
    (Φ : ManyBody.BondInteraction L q)
(h0 : ∀ j, 0 ≤ Φ.term j) (h1 : ∀ j, Φ.term j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) (i : ℕ) (hi : i ≤ L) :
    (lvvSweep hq Φ h0 h1 Delta i).card ≤
        (if i = 0 then 1 else lvvSuccessiveCardBound q Delta L) ∧
      (∀ v ∈ lvvSweep hq Φ h0 h1 Delta i, IsLeftOpenMPS
        (if i = 0 then 1 else lvvSuccessiveBondBound q Delta L) v) ∧
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
        ‖Γ‖ = 1 → IsGapped Φ.hamiltonian E₀ Delta →
        groundSpace Φ.hamiltonian E₀ = Submodule.span ℂ {Γ} →
        IsViable Γ (lvvSuccessiveError Delta / L)
          (lvvSweep hq Φ h0 h1 Delta i : Set (LeftBlockVector L q i)) := by
  induction i with
  | zero =>
    refine ⟨by simp [lvvSweep], ?_, ?_⟩
    · intro v hv
      simp only [lvvSweep, Finset.mem_singleton] at hv
      subst v
      exact isOpenMPS_of_internal_cutMatrix_rank_le
        (WithLp.toLp 2 fun x ↦ emptyLeftVector L q (leftConfigOfFin x))
        (fun k hk0 hkL ↦ by omega)
    · intro E₀ Γ hΩ hgap hspan
      obtain ⟨v, hv, hoverlap, hsupport⟩ :=
        (isViableMPS_emptyLeftVector hΩ).2.2
      refine ⟨v, hv, ?_, hsupport⟩
      have hδ : 0 ≤ lvvSuccessiveError Delta / (L : ℝ) :=
        div_nonneg (lvvSuccessiveError_pos hDelta).le (Nat.cast_nonneg L)
      linarith
  | succ i ih =>
    obtain ⟨-, -, hviable⟩ := ih (by omega)
    rw [lvvSweep_succ hq Φ h0 h1 Delta hi]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    exact ⟨card_lvvSweepStep_le hq Φ h0 h1 hDelta hi _,
      fun v hv ↦ isLeftOpenMPS_of_mem_lvvSweepStep hq Φ h0 h1 hDelta hi _ hv,
      fun E₀ Γ hΩ hgap hspan ↦ isViable_lvvSweepStep hq Φ h0 h1 hDelta hi _ E₀ Γ hΩ hgap hspan
        (hviable E₀ Γ hΩ hgap hspan)⟩

/-- The scalar singleton and the successive steps give one sequence of viable families
before every ground pair: the existence form of `lvvSweep_spec`. LVV13, `algo53.tex`,
lines 652--678, with the documented quadratic trimming correction and Huang's Gaussian
error reduction. -/
theorem exists_positive_chain_successive_viable_sets (hq : 2 ≤ q)
    (Φ : ManyBody.BondInteraction L q)
(h0 : ∀ j, 0 ≤ Φ.term j) (h1 : ∀ j, Φ.term j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) :
    ∃ S : (i : ℕ) → Finset (LeftBlockVector L q i),
      S 0 = {emptyLeftVector L q} ∧
      (∀ i : ℕ, (hi : i + 1 ≤ L) → S (i + 1) = lvvSweepStep hq Φ h0 Delta hi (S i)) ∧
      ∀ i : ℕ, i ≤ L →
        (S i).card ≤ (if i = 0 then 1 else lvvSuccessiveCardBound q Delta L) ∧
        (∀ v ∈ S i, IsLeftOpenMPS
          (if i = 0 then 1 else lvvSuccessiveBondBound q Delta L) v) ∧
        ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
          ‖Γ‖ = 1 → IsGapped Φ.hamiltonian E₀ Delta →
          groundSpace Φ.hamiltonian E₀ = Submodule.span ℂ {Γ} →
          IsViable Γ (lvvSuccessiveError Delta / L) (S i : Set (LeftBlockVector L q i)) :=
  ⟨lvvSweep hq Φ h0 h1 Delta, rfl, fun _ hi ↦ lvvSweep_succ hq Φ h0 h1 Delta hi,
    fun i hi ↦ lvvSweep_spec hq Φ h0 h1 hDelta i hi⟩

end TNLean.MPS.AreaLaw
