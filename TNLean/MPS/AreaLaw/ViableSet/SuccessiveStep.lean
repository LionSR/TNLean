/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.SuccessiveBudgets
import TNLean.MPS.AreaLaw.Huang.PositiveChainHamiltonian
import TNLean.MPS.AreaLaw.Huang.ViableFilter

/-!
# One complete step of the successive viable-set construction

Extend the input by one physical site, take the size-trimming selection of the extension,
trim each selected vector independently through its internal bonds, and apply the finite
family of Gaussian left filter factors. The step is the named family
`successiveStep hi m F id T₀ = {A (trim_m u) : A ∈ F, u ∈ T₀}` applied to the selection
`T₀ = sizeTrimmingSelection (S ⊗ {|1⟩, …, |q⟩})`: the filter factors `F` are chosen before
the input family, and the output is a function of the input family. Both the size and the
individual bond bounds of the output are reset to length-dependent budgets that do not
depend on the preceding family size.

**Local fix (trimming radius):** The independent trimmings use the quadratic radius
recorded at <https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>.
The library constant-cut bound and corrected net exponent are documented in
`docs/paper-gaps/lvv13_constant_bond.tex`. Error reduction uses Huang's Gaussian
construction, with the quantitative scope recorded in
`docs/paper-gaps/lvv13_runtime_ground_energy.tex`.

Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, algorithm steps 1--4 and Claims
`c:ext`, `c:2`, `c:trim`, `c:errorreduction`, lines 379--592; Huang,
arXiv:1406.6355v6, Section 5.4, Lemmas 18--19.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

variable {L q i : ℕ} {ι : Type*}

/-- **One step of the sweep at the cut after `i` sites**, after the size-trimming selection
`T₀` has been made: independently trim every member of `T₀` through its internal bonds at
the radius `m`, then apply every left factor `A j`, `j ∈ J`, of the error-reduction
operator. The output is the family `{A j (trim_m u) : j ∈ J, u ∈ T₀}`. In the algorithm
`T₀` is the size-trimming selection: the left columns, read on the first `i` sites, of
the leading vectors of the convex programs over the net of boundary contractions, drawn
from the span of the extension `S ⊗ {|1⟩, …, |q⟩}` of the previous family; the factors are
those of the Gaussian filters, indexed by themselves, or those of the sampled projector.
LVV13, `algo53.tex`, algorithm steps 2--4, lines 379--592. -/
noncomputable def successiveStep (hi : i ≤ L) (m : ℕ) (J : Finset ι)
    (A : ι → LeftBlockMatrix L q i) (T₀ : Finset (LeftBlockVector L q i)) :
    Finset (LeftBlockVector L q i) :=
  errorReductionSet J A (bondTrimSet hi m T₀)

/-- The output of one step has at most `|J| |T₀|` members.
LVV13, `algo53.tex`, Claims `c:trim` and `c:errorreduction`, lines 549--592. -/
theorem card_successiveStep_le (hi : i ≤ L) (m : ℕ) (J : Finset ι)
    (A : ι → LeftBlockMatrix L q i) (T₀ : Finset (LeftBlockVector L q i)) :
    (successiveStep hi m J A T₀).card ≤ J.card * T₀.card :=
  (card_errorReductionSet_le J A _).trans
    (Nat.mul_le_mul_left _ (card_bondTrimSet_le hi m T₀))

/-- Every member of the output of one step is a matrix product state of bond dimension at
most `D * max 1 m` when every factor `A j`, `j ∈ J`, has operator-Schmidt rank at most `D`
at every internal left cut. LVV13, `algo53.tex`, Claims `c:trim` and `c:errorreduction`,
lines 549--592. -/
theorem isLeftOpenMPS_of_mem_successiveStep (hi : i ≤ L) {m D : ℕ} {J : Finset ι}
    {A : ι → LeftBlockMatrix L q i}
    (hA : ∀ j ∈ J, ∀ k, 0 < k → k < i → operatorSchmidtRank
      (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
        ((A j).submatrix leftConfigOfFin leftConfigOfFin)) ≤ D)
    (T₀ : Finset (LeftBlockVector L q i)) {v : LeftBlockVector L q i}
    (hv : v ∈ successiveStep hi m J A T₀) : IsLeftOpenMPS (D * max 1 m) v :=
  isLeftOpenMPS_of_mem_errorReductionSet hi hA
    (fun _ hu ↦ isLeftOpenMPS_of_mem_bondTrimSet hi m T₀ hu) hv

/-- **The complete step with its selections named.** The Gaussian left filter factors `F`
at the cut after `i` sites are chosen from the chain, the gap and the cut, before every
input family and every ground pair, with explicit cardinality and rank budgets. For every
input family `S` at the cut after `i - 1` sites, the step applied to the size-trimming
selection of the extension `S ⊗ {|1⟩, …, |q⟩}` is `c_Δ / L`-viable for every ground pair
for which `S` is. LVV13, `algo53.tex`, algorithm steps 1--4, lines 379--592, using Huang,
Section 5.4, Lemmas 18--19 for the error-reduction operator. -/
theorem exists_positive_chain_successive_step_factors (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) (hL : 1 ≤ L) (hi0 : 0 < i) (hiL : i ≤ L) :
    let m := bondTrimmingRadius L (lvvReferenceBond q Delta L)
    ∃ F : Finset (LeftBlockMatrix L q i),
      F.card ≤ huangEnergyCount (lvvSuccessiveError Delta) Delta L *
        huangFilterRankBound q (lvvSuccessiveError Delta) Delta L ∧
      (∀ A ∈ F, ∀ k, 0 < k → k < i → operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
          (A.submatrix leftConfigOfFin leftConfigOfFin)) ≤
            huangFilterRankBound q (lvvSuccessiveError Delta) Delta L) ∧
      ∀ (S : Finset (LeftBlockVector L q (i - 1))) (E₀ : ℝ)
        (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
        IsGappedGroundState (∑ j, h j) E₀ Γ Delta →
        IsViable Γ (lvvSuccessiveError Delta / L) (S : Set (LeftBlockVector L q (i - 1))) →
        IsViable Γ (lvvSuccessiveError Delta / L)
          (successiveStep hiL m F id
            ((ChainHamiltonian.ofNearestNeighborPositive h hs h0 h1).sizeTrimmingSelection hq
              Delta (AreaLaw.extend i S)) : Set (LeftBlockVector L q i)) := by
  classical
  intro m
  obtain ⟨F, hFcard, hFrank, hFgood⟩ := exists_positive_chain_error_reduction_factors
    (by omega) h hs h0 h1 (lvvSuccessiveError_pos hDelta) hDelta hL hiL
  refine ⟨F, hFcard, hFrank, ?_⟩
  intro S E₀ Γ hgs hviable
  let chain := ChainHamiltonian.ofNearestNeighborPositive h hs h0 h1
  have hpos (X) : (chain.term X).PosSemidef :=
    (ChainHamiltonian.ofNearestNeighborPositive_term_nonneg h hs h0 h1 X).posSemidef
  have hgsChain : IsGappedGroundState chain.operator E₀ Γ Delta := by
    simpa only [chain, ChainHamiltonian.ofNearestNeighborPositive_operator] using hgs
  obtain ⟨hΓ, hEig, hgap⟩ := isGappedGroundState_iff.mp hgs
  exact hFgood E₀ Γ hΓ hEig hgap _
    (chain.isViable_bondTrimSet_sizeTrimmingSelection hpos (by omega) hq hiL hDelta
      (AreaLaw.extend i S) E₀ Γ hgsChain (hviable.extend hi0 hiL))

/-- The actual extension, size trimming, independent bond trimming and Gaussian error
reduction at one cut: the existence form of
`exists_positive_chain_successive_step_factors`, with the output left unnamed. The family
is selected before every ground pair, with explicit size and bond budgets. LVV13,
`algo53.tex`, algorithm steps 1--4, lines 379--592, using Huang, Section 5.4,
Lemmas 18--19 for the error-reduction operator. -/
theorem exists_positive_chain_successive_step (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) (hL : 1 ≤ L) (hi0 : 0 < i) (hiL : i ≤ L)
    (S : Finset (LeftBlockVector L q (i - 1))) :
    ∃ T : Finset (LeftBlockVector L q i),
      T.card ≤ lvvSuccessiveCardBound q Delta L ∧
      (∀ v ∈ T, IsLeftOpenMPS (lvvSuccessiveBondBound q Delta L) v) ∧
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
        IsGappedGroundState (∑ j, h j) E₀ Γ Delta →
        IsViable Γ (lvvSuccessiveError Delta / L)
          (S : Set (LeftBlockVector L q (i - 1))) →
        IsViable Γ (lvvSuccessiveError Delta / L) (T : Set (LeftBlockVector L q i)) := by
  obtain ⟨F, hFcard, hFrank, hstep⟩ :=
    exists_positive_chain_successive_step_factors hq h hs h0 h1 hDelta hL hi0 hiL
  refine ⟨successiveStep hiL _ F id _, ?_,
    fun v hv ↦ isLeftOpenMPS_of_mem_successiveStep hiL hFrank _ hv, hstep S⟩
  calc
    _ ≤ F.card * ((ChainHamiltonian.ofNearestNeighborPositive h hs h0 h1).sizeTrimmingSelection
          hq Delta (AreaLaw.extend i S)).card := card_successiveStep_le hiL _ F id _
    _ ≤ (huangEnergyCount (lvvSuccessiveError Delta) Delta L *
          huangFilterRankBound q (lvvSuccessiveError Delta) Delta L) *
        (lvvSizeTrimmingCoefficient q Delta * L ^ lvvSizeTrimmingDegree q Delta) :=
      Nat.mul_le_mul hFcard (ChainHamiltonian.card_sizeTrimmingSelection_le_polynomial
        (ChainHamiltonian.ofNearestNeighborPositive h hs h0 h1) (by omega) hq hDelta _)
    _ = lvvSuccessiveCardBound q Delta L := by
      dsimp only [lvvSuccessiveCardBound]
      ring

end TNLean.MPS.AreaLaw
