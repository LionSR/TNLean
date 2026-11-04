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
family of Gaussian left filter factors. The generic step is the named family
`successiveStep hi m F id T₀ = {A (trim_m u) : A ∈ F, u ∈ T₀}`; the step of the sweep,
`lvvSweepStep`, applies it with the Gaussian filter factors `gaussianFilterFactors` to the
selection `sizeTrimmingSelection (S ⊗ {|1⟩, …, |q⟩})`, so that the output is a function
of the input family. Both the size and the individual bond bounds of the output are reset
to length-dependent budgets that do not depend on the preceding family size.

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

/-- **One step of the sweep as a function of the previous family.** Extend the family at
the cut after `i` sites by one site, take the size-trimming selection of the extension,
trim each selected vector independently at the corrected radius, and apply every Gaussian
filter factor at the cut after `i + 1` sites. LVV13, `algo53.tex`, algorithm steps 1--4,
lines 379--592, with Huang, Section 5.4, Lemmas 18--19 for the error-reduction operator. -/
noncomputable def lvvSweepStep (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    (Delta : ℝ) (hi : i + 1 ≤ L) (S : Finset (LeftBlockVector L q i)) :
    Finset (LeftBlockVector L q (i + 1)) :=
  successiveStep hi (bondTrimmingRadius L (lvvReferenceBond q Delta L))
    (gaussianFilterFactors (Nat.le_of_lt hq) h h0 (lvvSuccessiveError Delta) Delta (i + 1)) id
    ((ChainHamiltonian.ofNearestNeighborPositive h hs h0 h1).sizeTrimmingSelection hq Delta
      (AreaLaw.extend (i + 1) S))

/-- The output of one step of the sweep has at most `s_L` members.
LVV13, `algo53.tex`, Claims `c:2` and `c:errorreduction`, lines 520--592. -/
theorem card_lvvSweepStep_le (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) (hi : i + 1 ≤ L) (S : Finset (LeftBlockVector L q i)) :
    (lvvSweepStep hq h hs h0 h1 Delta hi S).card ≤ lvvSuccessiveCardBound q Delta L := by
  calc
    _ ≤ (gaussianFilterFactors (Nat.le_of_lt hq) h h0 (lvvSuccessiveError Delta) Delta
          (i + 1)).card *
        ((ChainHamiltonian.ofNearestNeighborPositive h hs h0 h1).sizeTrimmingSelection hq Delta
          (AreaLaw.extend (i + 1) S)).card := card_successiveStep_le hi _ _ id _
    _ ≤ (huangEnergyCount (lvvSuccessiveError Delta) Delta L *
          huangFilterRankBound q (lvvSuccessiveError Delta) Delta L) *
        (lvvSizeTrimmingCoefficient q Delta * L ^ lvvSizeTrimmingDegree q Delta) :=
      Nat.mul_le_mul
        (card_gaussianFilterFactors_le (Nat.le_of_lt hq) h hs h0 h1
          (lvvSuccessiveError_pos hDelta) hDelta)
        (ChainHamiltonian.card_sizeTrimmingSelection_le_polynomial
          (ChainHamiltonian.ofNearestNeighborPositive h hs h0 h1) (by omega) hq hDelta _)
    _ = lvvSuccessiveCardBound q Delta L := by
      dsimp only [lvvSuccessiveCardBound]
      ring

/-- Every member of the output of one step of the sweep is a matrix product state of bond
dimension at most `b_L`. LVV13, `algo53.tex`, Claims `c:trim` and `c:errorreduction`,
lines 549--592. -/
theorem isLeftOpenMPS_of_mem_lvvSweepStep (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) (hi : i + 1 ≤ L) (S : Finset (LeftBlockVector L q i))
    {v : LeftBlockVector L q (i + 1)} (hv : v ∈ lvvSweepStep hq h hs h0 h1 Delta hi S) :
    IsLeftOpenMPS (lvvSuccessiveBondBound q Delta L) v :=
  isLeftOpenMPS_of_mem_successiveStep hi
    (fun _ hA k _ hki ↦ operatorSchmidtRank_of_mem_gaussianFilterFactors (Nat.le_of_lt hq) h hs
      h0 h1 (lvvSuccessiveError_pos hDelta) hDelta hi hA k hki) _ hv

/-- **One step of the sweep preserves viability.** For every ground pair with the
prescribed gap, `c_Δ / L`-viability of the family at the cut after `i` sites implies
`c_Δ / L`-viability of the step at the cut after `i + 1` sites. LVV13, `algo53.tex`,
algorithm steps 1--4, lines 379--592, using Huang, Section 5.4, Lemmas 18--19 for the
error-reduction operator. -/
theorem isViable_lvvSweepStep (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) (hi : i + 1 ≤ L) (S : Finset (LeftBlockVector L q i))
    (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q))
    (hgs : IsGappedGroundState (∑ j, h j) E₀ Γ Delta)
    (hviable : IsViable Γ (lvvSuccessiveError Delta / L) (S : Set (LeftBlockVector L q i))) :
    IsViable Γ (lvvSuccessiveError Delta / L)
      (lvvSweepStep hq h hs h0 h1 Delta hi S : Set (LeftBlockVector L q (i + 1))) := by
  classical
  let chain := ChainHamiltonian.ofNearestNeighborPositive h hs h0 h1
  have hpos (X) : (chain.term X).PosSemidef :=
    (ChainHamiltonian.ofNearestNeighborPositive_term_nonneg h hs h0 h1 X).posSemidef
  have hgsChain : IsGappedGroundState chain.operator E₀ Γ Delta := by
    simpa only [chain, ChainHamiltonian.ofNearestNeighborPositive_operator] using hgs
  obtain ⟨hΓ, hEig, hgap⟩ := isGappedGroundState_iff.mp hgs
  exact isViable_errorReductionSet_gaussianFilterFactors (Nat.le_of_lt hq) h hs h0 h1
    (lvvSuccessiveError_pos hDelta) hDelta (by omega) E₀ Γ hΓ hEig hgap _
    (chain.isViable_bondTrimSet_sizeTrimmingSelection hpos (by omega) hq hi hDelta
      (AreaLaw.extend (i + 1) S) E₀ Γ hgsChain (hviable.extend (by omega) hi))

/-- The actual extension, size trimming, independent bond trimming and Gaussian error
reduction at one cut: the existence form of the step `lvvSweepStep`, with the output
left unnamed. The family is selected before every ground pair, with explicit size and
bond budgets. LVV13, `algo53.tex`, algorithm steps 1--4, lines 379--592, using Huang,
Section 5.4, Lemmas 18--19 for the error-reduction operator. -/
theorem exists_positive_chain_successive_step (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) (hi : i + 1 ≤ L)
    (S : Finset (LeftBlockVector L q i)) :
    ∃ T : Finset (LeftBlockVector L q (i + 1)),
      T.card ≤ lvvSuccessiveCardBound q Delta L ∧
      (∀ v ∈ T, IsLeftOpenMPS (lvvSuccessiveBondBound q Delta L) v) ∧
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
        IsGappedGroundState (∑ j, h j) E₀ Γ Delta →
        IsViable Γ (lvvSuccessiveError Delta / L) (S : Set (LeftBlockVector L q i)) →
        IsViable Γ (lvvSuccessiveError Delta / L) (T : Set (LeftBlockVector L q (i + 1))) :=
  ⟨lvvSweepStep hq h hs h0 h1 Delta hi S, card_lvvSweepStep_le hq h hs h0 h1 hDelta hi S,
    fun _ hv ↦ isLeftOpenMPS_of_mem_lvvSweepStep hq h hs h0 h1 hDelta hi S hv,
    fun E₀ Γ hgs hviable ↦ isViable_lvvSweepStep hq h hs h0 h1 hDelta hi S E₀ Γ hgs hviable⟩

end TNLean.MPS.AreaLaw
