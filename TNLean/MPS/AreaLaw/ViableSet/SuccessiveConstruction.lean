/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.SuccessiveStep
import TNLean.MPS.AreaLaw.ViableSet.Endpoints

/-!
# The successive viable-set induction

Starting with the scalar singleton at the empty cut, each family is the named step
`successiveStep` applied to the size-trimming selection of the extension of the previous
one: extend by one site, take the selection, trim each selected vector independently
through its bonds, and apply the finite Gaussian filter family. The filter factors are
chosen before every family, and every retained family is a function of the previous one,
chosen before any ground energy or ground vector. For every ground pair with the
prescribed gap, all these same families satisfy the required viability bounds.

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

/-- **The successive viable-set induction with each family obtained from the previous one.**
The Gaussian left filter factors `F i` at every cut are chosen from the chain and the gap
before every family and every ground pair. Starting from the scalar singleton, the family
at the cut after `i + 1` sites is the step `successiveStep _ m (F (i + 1)) id` applied to
the size-trimming selection of the extension of `S i` by one site: each family is a
function of the previous one. Positive cuts have uniform explicit size and bond budgets,
and for every ground pair with the prescribed gap all these same families are viable.
LVV13, `algo53.tex`, lines 652--678, with the documented quadratic trimming correction and
Huang's Gaussian error reduction. -/
theorem exists_positive_chain_successive_viable_sets {L q : ℕ} (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) (hL : 1 ≤ L) :
    let m := bondTrimmingRadius L (lvvReferenceBond q Delta L)
    let chain := ChainHamiltonian.ofNearestNeighborPositive h hs h0 h1
    ∃ F : (i : ℕ) → Finset (LeftBlockMatrix L q i),
      (∀ i : ℕ, i ≤ L →
        (F i).card ≤ huangEnergyCount (lvvSuccessiveError Delta) Delta L *
          huangFilterRankBound q (lvvSuccessiveError Delta) Delta L ∧
        ∀ A ∈ F i, ∀ k, 0 < k → k < i → operatorSchmidtRank
          (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
            (A.submatrix leftConfigOfFin leftConfigOfFin)) ≤
              huangFilterRankBound q (lvvSuccessiveError Delta) Delta L) ∧
      ∃ S : (i : ℕ) → Finset (LeftBlockVector L q i),
        S 0 = {emptyLeftVector L q} ∧
        (∀ i : ℕ, (hi : i + 1 ≤ L) →
          S (i + 1) = successiveStep hi m (F (i + 1)) id
            (chain.sizeTrimmingSelection hq Delta (AreaLaw.extend (i + 1) (S i)))) ∧
        ∀ i : ℕ, i ≤ L →
          (S i).card ≤ (if i = 0 then 1 else lvvSuccessiveCardBound q Delta L) ∧
          (∀ v ∈ S i, IsLeftOpenMPS
            (if i = 0 then 1 else lvvSuccessiveBondBound q Delta L) v) ∧
          ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
            IsGappedGroundState (∑ j, h j) E₀ Γ Delta →
            IsViable Γ (lvvSuccessiveError Delta / L) (S i : Set (LeftBlockVector L q i)) := by
  classical
  intro m chain
  have hF : ∀ i : ℕ, ∃ F : Finset (LeftBlockMatrix L q i),
      (F.card ≤ huangEnergyCount (lvvSuccessiveError Delta) Delta L *
          huangFilterRankBound q (lvvSuccessiveError Delta) Delta L ∧
        ∀ A ∈ F, ∀ k, 0 < k → k < i → operatorSchmidtRank
          (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
            (A.submatrix leftConfigOfFin leftConfigOfFin)) ≤
              huangFilterRankBound q (lvvSuccessiveError Delta) Delta L) ∧
      ∀ (hi0 : 0 < i) (hiL : i ≤ L) (S : Finset (LeftBlockVector L q (i - 1)))
        (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
        IsGappedGroundState (∑ j, h j) E₀ Γ Delta →
        IsViable Γ (lvvSuccessiveError Delta / L) (S : Set (LeftBlockVector L q (i - 1))) →
        IsViable Γ (lvvSuccessiveError Delta / L)
          (successiveStep hiL m F id
            (chain.sizeTrimmingSelection hq Delta (AreaLaw.extend i S)) :
              Set (LeftBlockVector L q i)) := by
    intro i
    by_cases hi : 0 < i ∧ i ≤ L
    · obtain ⟨F, hcard, hrank, hstep⟩ :=
        exists_positive_chain_successive_step_factors hq h hs h0 h1 hDelta hL hi.1 hi.2
      exact ⟨F, ⟨hcard, hrank⟩, fun _ _ ↦ hstep⟩
    · exact ⟨∅, ⟨Nat.zero_le _, fun A hA ↦ absurd hA (Finset.notMem_empty A)⟩,
        fun hi0 hiL ↦ absurd ⟨hi0, hiL⟩ hi⟩
  choose F hFbounds hFstep using hF
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
  let step := fun (i : ℕ) (hi : i + 1 ≤ L) (S : Finset (LeftBlockVector L q i)) ↦
    successiveStep hi m (F (i + 1)) id
      (chain.sizeTrimmingSelection hq Delta (AreaLaw.extend (i + 1) S))
  have hstepP : ∀ (i : ℕ) (hi : i + 1 ≤ L) (S : Finset (LeftBlockVector L q i)),
      (i ≤ L → P i S) → P (i + 1) (step i hi S) := by
    intro i hi S hS
    refine ⟨?_, ?_, ?_⟩
    · simp only [Nat.succ_ne_zero, ↓reduceIte]
      calc
        _ ≤ (F (i + 1)).card *
              (chain.sizeTrimmingSelection hq Delta (AreaLaw.extend (i + 1) S)).card :=
          card_successiveStep_le hi m (F (i + 1)) id _
        _ ≤ (huangEnergyCount (lvvSuccessiveError Delta) Delta L *
              huangFilterRankBound q (lvvSuccessiveError Delta) Delta L) *
            (lvvSizeTrimmingCoefficient q Delta * L ^ lvvSizeTrimmingDegree q Delta) :=
          Nat.mul_le_mul (hFbounds (i + 1)).1
            (chain.card_sizeTrimmingSelection_le_polynomial (by omega) hq hDelta _)
        _ = lvvSuccessiveCardBound q Delta L := by
          dsimp only [lvvSuccessiveCardBound]
          ring
    · intro v hv
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      exact isLeftOpenMPS_of_mem_successiveStep hi (hFbounds (i + 1)).2 _ hv
    · intro E₀ Γ hgs
      exact hFstep (i + 1) (by omega) hi S E₀ Γ hgs ((hS (by omega)).2.2 E₀ Γ hgs)
  let State := fun i : ℕ ↦ {S : Finset (LeftBlockVector L q i) // i ≤ L → P i S}
  let initial : State 0 := ⟨{emptyLeftVector L q}, fun _ ↦ hbase⟩
  let advance : (i : ℕ) → State i → State (i + 1) := fun i previous ↦
    if hi : i + 1 ≤ L then
      ⟨step i hi previous.val, fun _ ↦ hstepP i hi previous.val previous.property⟩
    else ⟨∅, fun hi' ↦ False.elim (hi hi')⟩
  let run : (i : ℕ) → State i := Nat.rec initial advance
  refine ⟨F, fun i _ ↦ hFbounds i, fun i ↦ (run i).val, rfl, ?_,
    fun i hi ↦ (run i).property hi⟩
  intro i hi
  have hrun : run (i + 1) = advance i (run i) := rfl
  simp only [hrun, advance, hi, ↓reduceDIte, step]

end TNLean.MPS.AreaLaw
