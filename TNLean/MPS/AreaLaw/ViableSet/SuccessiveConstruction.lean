/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.SuccessiveStep
import TNLean.MPS.AreaLaw.ViableSet.Endpoints

/-!
# The successive viable-set induction

Starting with the scalar singleton at the empty cut, each step extends by one site,
performs the actual size and independent bond trimmings, and applies the finite Gaussian
filter family. Every retained family is chosen before any ground energy or ground
vector. For every ground pair with the prescribed gap, all these same families satisfy
the required viability bounds.

**Local fix (trimming radius):** The independent trimmings use the quadratic radius
recorded at <https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>.
The constant-cut bond and net-exponent scope is documented in
`docs/paper-gaps/lvv13_constant_bond.tex`; the use of Huang's Gaussian filters is
documented in `docs/paper-gaps/lvv13_runtime_ground_energy.tex`.

Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, the induction at lines 652--678,
using Huang, arXiv:1406.6355v6, Section 5.4, Lemmas 18--19 for error reduction.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- The scalar singleton and the actual successive steps give one sequence of viable
families before every ground pair. Positive cuts have uniform explicit size and bond
budgets; the empty cut has its scalar singleton. LVV13, `algo53.tex`, lines 652--678,
with the documented quadratic trimming correction and Huang's Gaussian error reduction. -/
theorem exists_positive_chain_successive_viable_sets {L q : ℕ} (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) (hL : 1 ≤ L) :
    ∃ S : (i : ℕ) → Finset (LeftBlockVector L q i),
      S 0 = {emptyLeftVector L q} ∧
      ∀ i : ℕ, i ≤ L →
        (S i).card ≤ (if i = 0 then 1 else lvvSuccessiveCardBound q Delta L) ∧
        (∀ v ∈ S i, IsLeftOpenMPS
          (if i = 0 then 1 else lvvSuccessiveBondBound q Delta L) v) ∧
        ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
          IsGappedGroundState (∑ j, h j) E₀ Γ Delta →
          IsViable Γ (lvvSuccessiveError Delta / L) (S i : Set (LeftBlockVector L q i)) := by
  classical
  let P := fun (i : ℕ) (S : Finset (LeftBlockVector L q i)) ↦
    S.card ≤ (if i = 0 then 1 else lvvSuccessiveCardBound q Delta L) ∧
    (∀ v ∈ S, IsLeftOpenMPS (if i = 0 then 1 else lvvSuccessiveBondBound q Delta L) v) ∧
    ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
      IsGappedGroundState (∑ j, h j) E₀ Γ Delta →
      IsViable Γ (lvvSuccessiveError Delta / L) (S : Set (LeftBlockVector L q i))
  have hbase : P 0 {emptyLeftVector L q} := by
    refine ⟨by simp, ?_, ?_⟩
    · intro v hv
      simp only [Finset.mem_singleton] at hv
      subst v
      exact isOpenMPS_of_internal_cutMatrix_rank_le
        (WithLp.toLp 2 fun x ↦ emptyLeftVector L q (leftConfigOfFin x))
        (fun k hk0 hkL ↦ by omega)
    · intro E₀ Γ hgs
      obtain ⟨v, hv, hoverlap, hsupport⟩ :=
        (isViableMPS_emptyLeftVector hgs.1).2.2
      refine ⟨v, hv, ?_, hsupport⟩
      have hδ : 0 ≤ lvvSuccessiveError Delta / (L : ℝ) :=
        div_nonneg (lvvSuccessiveError_pos hDelta).le (Nat.cast_nonneg L)
      linarith
  let State := fun i : ℕ ↦
    {S : Finset (LeftBlockVector L q i) // i ≤ L → P i S}
  let initial : State 0 := ⟨{emptyLeftVector L q}, fun _ ↦ hbase⟩
  let advance : (i : ℕ) → State i → State (i + 1) := fun i previous ↦
    if hi : i + 1 ≤ L then
      let hprevious := previous.property (by omega)
      let step := exists_positive_chain_successive_step
        hq h hs h0 h1 hDelta hL (by omega) hi previous.val hprevious.2.1
      ⟨Classical.choose step, fun _ ↦ by
        obtain ⟨hcard, hMPS, hgood⟩ := Classical.choose_spec step
        refine ⟨hcard, hMPS, ?_⟩
        intro E₀ Γ hgs
        exact hgood E₀ Γ hgs (hprevious.2.2 E₀ Γ hgs)⟩
    else ⟨∅, fun hi' ↦ False.elim (hi hi')⟩
  let run : (i : ℕ) → State i := Nat.rec initial advance
  let S := fun i : ℕ ↦ (run i).val
  refine ⟨S, rfl, ?_⟩
  intro i hi
  exact (run i).property hi

end TNLean.MPS.AreaLaw
