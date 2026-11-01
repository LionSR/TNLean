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

Extend the input by one physical site, construct the actual size-trimming family, trim
each retained vector independently through its internal bonds, and apply the finite
family of Gaussian filters. The output is chosen before the ground energy or vector.
Both its size and individual bond bounds are reset to length-dependent budgets that do
not depend on the preceding family size.

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

/-- The actual extension, size trimming, independent bond trimming and Gaussian error
reduction at one cut. The family is selected before every ground pair, with explicit
size and bond budgets. LVV13, `algo53.tex`, algorithm steps 1--4, lines 379--592,
using Huang, Section 5.4, Lemmas 18--19 for the error-reduction operator. -/
theorem exists_positive_chain_successive_step {L q i b : ℕ} (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) (hL : 1 ≤ L) (hi0 : 0 < i) (hiL : i ≤ L)
    (S : Finset (LeftBlockVector L q (i - 1))) (hS : ∀ v ∈ S, IsLeftOpenMPS b v) :
    ∃ T : Finset (LeftBlockVector L q i),
      T.card ≤ lvvSuccessiveCardBound q Delta L ∧
      (∀ v ∈ T, IsLeftOpenMPS (lvvSuccessiveBondBound q Delta L) v) ∧
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
        IsGappedGroundState (∑ j, h j) E₀ Γ Delta →
        IsViable Γ (lvvSuccessiveError Delta / L)
          (S : Set (LeftBlockVector L q (i - 1))) →
        IsViable Γ (lvvSuccessiveError Delta / L) (T : Set (LeftBlockVector L q i)) := by
  classical
  let chain := ChainHamiltonian.ofNearestNeighborPositive h hs h0 h1
  have hpos (X) : (chain.term X).PosSemidef :=
    (ChainHamiltonian.ofNearestNeighborPositive_term_nonneg h hs h0 h1 X).posSemidef
  have hExt : ∀ v ∈ AreaLaw.extend i S, IsLeftOpenMPS b v := by
    intro v hv
    unfold AreaLaw.extend at hv
    obtain ⟨u, hu, k, -, rfl⟩ := Finset.mem_image₂.mp hv
    exact (hS u hu).extendSite hi0 hiL k
  obtain ⟨S₀, hcard, hMPS, hhalf⟩ := chain.exists_size_bond_trimmed_family_polynomial
    hpos (by omega) hq hiL hDelta (AreaLaw.extend i S) b hExt
  change S₀.card ≤ lvvSizeTrimmingCoefficient q Delta * L ^ lvvSizeTrimmingDegree q Delta
    at hcard
  obtain ⟨T, hTcard, hTMPS, hgood⟩ := exists_positive_chain_error_reduced_set
    (by omega) h hs h0 h1 (lvvSuccessiveError_pos hDelta) hDelta hL hiL S₀ hcard hMPS
  refine ⟨T, ?_, hTMPS, ?_⟩
  · convert hTcard using 1
    dsimp only [lvvSuccessiveCardBound]
    ring
  · intro E₀ Γ hgs hviable
    have hgsChain : IsGappedGroundState chain.operator E₀ Γ Delta := by
      simpa only [chain, ChainHamiltonian.ofNearestNeighborPositive_operator] using hgs
    obtain ⟨hΓ, hEig, hgap⟩ := isGappedGroundState_iff.mp hgs
    exact hgood E₀ Γ hΓ hEig hgap
      (hhalf E₀ Γ hgsChain (hviable.extend hi0 hiL))

end TNLean.MPS.AreaLaw
