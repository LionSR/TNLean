/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.SuccessiveStep
import TNLean.MPS.AreaLaw.ViableSet.Endpoints
import QICLean.ManyBody.Hamiltonian.GroundSpace
import TNLean.MPS.AreaLaw.ViableSet.FinalMPS
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.BoundaryState.ChainPaddingGroundState
import TNLean.MPS.AreaLaw.ViableSet.PrefixColumn
import QICLean.Analysis.Projection.PhaseError

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

## Uniform polynomial successive viable sets and final-span MPS approximation

For fixed local dimension and positive gap, the natural polynomial coefficient and
degree are chosen before the length and physical interaction. The Gaussian filter factors
and the sweep are functions of that interaction, chosen before any ground pair. Every
such ground pair has a normalized approximation in the span of the final family of the
sweep.

**Local fix (trimming radius):** The independent trimmings use the quadratic radius
recorded at <https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>.
The library constant-cut bound and corrected net exponent are documented in
`docs/paper-gaps/lvv13_constant_bond.tex`; the conservative Gaussian error-reduction
scope is documented in `docs/paper-gaps/lvv13_runtime_ground_energy.tex`.

Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, final induction, lines 652--678,
using Huang, arXiv:1406.6355v6, Section 5.4, Lemmas 18--19. The conclusion concerns
the mathematical construction and its cardinality and bond bounds; no computational
running-time statement is asserted.

## Arbitrary accuracy with a uniform polynomial degree

Fix the local dimension and a positive lower bound for the original gap.
Product-state padding caps that lower bound at one and increases the chain
length from `L` to `L + 2 R²`. Apply the same successive viable-set construction
to this actual interaction, before choosing any ground pair. A normalized
column of its stage-`L` witness, with its phase chosen, remains in the actual
retained stage-`L` span and has squared error at most `R⁻²`.

The natural polynomial coefficient and degree are chosen before both `L` and
`R`. No independent MPS existence theorem or computational running-time bound
is used.

This product-ancilla argument is a consequence of the proved LVV13
construction (arXiv:1307.5143v1, `algo53.tex`, final successive induction,
lines 652--678), rather than a claim that padding appears in the source.
The underlying construction retains the trimming corrections and Gaussian
error-reduction scope documented in `SuccessiveApproximation`.

It also contains the following results.

* `TNLean.MPS.AreaLaw.IsViable.exists_prefix_mps_of_paddedGroundVector`: an MPS in the actual
  retained prefix span.
-/

section PrefixMPS

/-!
## An MPS in the actual retained prefix span

A viable family for a target with fixed right configuration contains a
normalized prefix vector with the same overlap. Choosing its phase gives
the corresponding squared vector error. Its MPS bound follows from the
actual finite retained family, without a separate approximation theorem.

Source: product-ancilla use of LVV13, arXiv:1307.5143v1, final successive
induction, lines 652--678.
-/

open scoped InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- A phase-aligned MPS is obtained in the actual retained prefix span.
The coefficient two converts overlap loss to squared vector distance. -/
theorem IsViable.exists_prefix_mps_of_paddedGroundVector {L N q b : ℕ}
    (hi : L ≤ N) (z : Fin q) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hΓ : ‖Γ‖ = 1) {delta : ℝ} (hdelta : delta < 1)
    {S : Finset (LeftBlockVector N q L)}
    (hS : ∀ v ∈ S, IsLeftOpenMPS b v)
    (hv : IsViable (paddedGroundVector hi z Γ) delta (S : Set (LeftBlockVector N q L))) :
    ∃ w ∈ Submodule.span ℂ (S : Set (LeftBlockVector N q L)), ‖w‖ = 1 ∧
      ‖(LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (leftConfigOfFinEquiv hi)).symm w - Γ‖ ^ 2 ≤
        2 * delta ∧
      IsOpenMPS L q (S.card * max 1 b) (fun x ↦ w (leftConfigOfFin x)) := by
  classical
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (leftConfigOfFinEquiv (q := q) hi)
  obtain ⟨w, hw, hwnorm, hoverlap⟩ := hv.exists_prefix_of_rightBasisExtension hdelta
  obtain ⟨θ, _, hθ⟩ := exists_isMinOn_norm_sub_exp_smul (e Γ) w
  let w' := Complex.exp ((θ : ℂ) * Complex.I) • w
  have hw' : w' ∈ Submodule.span ℂ (S : Set (LeftBlockVector N q L)) :=
    Submodule.smul_mem _ _ hw
  refine ⟨w', hw', ?_, ?_, isOpenMPS_leftChain_of_mem_span S hS hw'⟩
  · simp only [w', norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul, hwnorm]
  · have hinner : ‖⟪e Γ, w⟫_ℂ‖ = ‖⟪w, e Γ⟫_ℂ‖ := norm_inner_symm _ _
    have hdist : ‖e.symm w' - Γ‖ = ‖w' - e Γ‖ := by
      rw [← e.norm_map (e.symm w' - Γ), map_sub, e.apply_symm_apply]
    change ‖e.symm w' - Γ‖ ^ 2 ≤ _
    rw [hdist, norm_sub_rev]
    change ‖e Γ - Complex.exp ((θ : ℂ) * Complex.I) • w‖ ^ 2 ≤ _
    rw [hθ, e.norm_map, hΓ, hwnorm, hinner]
    linarith

end TNLean.MPS.AreaLaw

end PrefixMPS

section SuccessiveConstruction

section

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

end

section

open ManyBody (interval)

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder

open ManyBody (IsGapped groundSpace)

namespace TNLean.MPS.AreaLaw

/-- **Uniform polynomial budgets for the sweep and the final-span approximation.** Natural
polynomial budgets chosen before length bound every family of the sweep, every family of
Gaussian filter factors and the normalized MPS extracted from the final span. The sweep is
a function of the interaction, chosen before ground data. LVV13, `algo53.tex`, final
induction, lines 652--678, with the documented quadratic trimming correction and Huang's
Gaussian error reduction. -/
theorem exists_uniform_positive_chain_successive_approximation {q : ℕ} (hq : 2 ≤ q)
    {Delta : ℝ} (hDelta : 0 < Delta) :
    ∃ P d : ℕ, 1 ≤ P ∧ ∀ L : ℕ, 1 ≤ L →
      ∀ (Φ : ManyBody.BondInteraction L q)
        (h0 : ∀ j, 0 ≤ Φ.term j) (h1 : ∀ j, Φ.term j ≤ 1),
      (∀ i : ℕ, i ≤ L →
        (gaussianFilterFactors Φ h0 (lvvSuccessiveError Delta) Delta i).card ≤
          P * (L + 1) ^ d ∧
        ∀ A ∈ gaussianFilterFactors Φ h0 (lvvSuccessiveError Delta) Delta i,
          ∀ k, k < i → operatorSchmidtRank
            (ManyBody.cutOperator (X := fun _ ↦ Fin q) (leftBlock i k)
              (A.submatrix leftConfigOfFin leftConfigOfFin)) ≤ P * (L + 1) ^ d) ∧
      (∀ i : ℕ, i ≤ L → (lvvSweep hq Φ h0 h1 Delta i).card ≤ P * (L + 1) ^ d ∧
        (∀ v ∈ lvvSweep hq Φ h0 h1 Delta i, IsLeftOpenMPS (P * (L + 1) ^ d) v) ∧
        ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
          ‖Γ‖ = 1 → IsGapped Φ.hamiltonian E₀ Delta →
          groundSpace Φ.hamiltonian E₀ = Submodule.span ℂ {Γ} →
          IsViable Γ (lvvSuccessiveError Delta / L)
            (lvvSweep hq Φ h0 h1 Delta i : Set (LeftBlockVector L q i))) ∧
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
        ‖Γ‖ = 1 → IsGapped Φ.hamiltonian E₀ Delta →
        groundSpace Φ.hamiltonian E₀ = Submodule.span ℂ {Γ} →
        ∃ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 ∧
          1 - lvvSuccessiveError Delta / L ≤ ‖⟪ψ, Γ⟫_ℂ‖ ∧
          IsOpenMPS L q (P * (L + 1) ^ d) (fun x ↦ ψ x) ∧
          fullLeftEquiv L q ψ ∈
            Submodule.span ℂ (lvvSweep hq Φ h0 h1 Delta L : Set (LeftBlockVector L q L)) := by
  classical
  obtain ⟨P, d, hP, hbudgets⟩ := exists_lvvSuccessive_uniform_polynomial (q := q) (by omega) hDelta
  refine ⟨P, d, hP, ?_⟩
  intro L hL Φ h0 h1
  obtain ⟨hcardBudget, hbondBudget, hspanBudget, hfactorBudget, hrankBudget⟩ :=
    hbudgets L hL
  have hS := lvvSweep_spec hq Φ h0 h1 hDelta
  refine ⟨fun i hi ↦ ⟨(card_gaussianFilterFactors_le (Nat.le_of_lt hq) Φ h0 h1
      (lvvSuccessiveError_pos hDelta) hDelta).trans hfactorBudget,
    fun A hA k hki ↦ (operatorSchmidtRank_of_mem_gaussianFilterFactors (Nat.le_of_lt hq) Φ h0
      h1 (lvvSuccessiveError_pos hDelta) hDelta hi hA k hki).trans hrankBudget⟩, ?_, ?_⟩
  · intro i hi
    obtain ⟨hcard, hMPS, hviable⟩ := hS i hi
    have hsize : (if i = 0 then 1 else lvvSuccessiveCardBound q Delta L) ≤
        P * (L + 1) ^ d := by
      split_ifs
      · exact (le_max_left 1 _).trans hcardBudget
      · exact (le_max_right 1 _).trans hcardBudget
    have hbond : (if i = 0 then 1 else lvvSuccessiveBondBound q Delta L) ≤
        P * (L + 1) ^ d := by
      split_ifs
      · exact (le_max_left 1 _).trans hbondBudget
      · exact (le_max_right 1 _).trans hbondBudget
    refine ⟨hcard.trans hsize, ?_, hviable⟩
    intro v hv
    exact (hMPS v hv).mono (max_le_max le_rfl hbond)
  · intro E₀ Γ hΩ hgap hspan
    obtain ⟨hcard, hMPS, hviable⟩ := hS L le_rfl
    have hLne : L ≠ 0 := by omega
    simp only [hLne, ite_false] at hcard hMPS
    obtain ⟨v, hvspan, hvnorm, hoverlap⟩ := (hviable E₀ Γ hΩ hgap hspan).exists_fullLeftVector
    let ψ := (fullLeftEquiv L q).symm v
    have hψimage : fullLeftEquiv L q ψ = v := (fullLeftEquiv L q).apply_symm_apply v
    have hinner : ⟪ψ, Γ⟫_ℂ = ⟪v, fullLeftEquiv L q Γ⟫_ℂ := by
      rw [← (fullLeftEquiv L q).inner_map_map ψ Γ, hψimage]
    refine ⟨ψ, ?_, ?_, ?_, ?_⟩
    · simpa only [ψ, LinearIsometryEquiv.norm_map] using hvnorm
    · rwa [hinner]
    · have hspan := isOpenMPS_leftChain_of_mem_span _ hMPS hvspan
      exact hspan.mono ((Nat.mul_le_mul_right _ hcard).trans hspanBudget)
    · rwa [hψimage]

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder

open ManyBody (IsGapped groundSpace)

namespace TNLean.MPS.AreaLaw

/-- The capped-gap successive error is strictly below one. -/
theorem lvvSuccessiveError_min_lt_one {Delta : ℝ} (hDelta : 0 < Delta) :
    lvvSuccessiveError (min Delta 1) < 1 := by
  have hpos : 0 ≤ min Delta 1 := le_min hDelta.le zero_le_one
  have hle : min Delta 1 ≤ 1 := min_le_right _ _
  unfold lvvSuccessiveError
  nlinarith [mul_nonneg hpos (sub_nonneg.mpr hle)]

/-- A single uniform natural polynomial bounds a padded successive run and an
arbitrarily accurate original-chain MPS in its actual retained prefix span.
The families are selected before the original ground energy and vector. -/
theorem exists_uniform_positive_chain_successive_accuracy {q : ℕ} (hq : 2 ≤ q)
    {Delta : ℝ} (hDelta : 0 < Delta) :
    ∃ P d : ℕ, 1 ≤ P ∧ ∀ L : ℕ, 1 ≤ L → ∀ R : ℕ, 1 ≤ R →
      ∀ (Φ : ManyBody.BondInteraction L q) (h0 : ∀ j, 0 ≤ Φ.term j) (_h1 : ∀ j, Φ.term j ≤ 1),
      let N := L + 2 * R ^ 2
      let hi : L ≤ N := Nat.le_add_right _ _
      let z : Fin q := ⟨0, by omega⟩
      ∃ S : (i : ℕ) → Finset (LeftBlockVector N q i),
        S 0 = {emptyLeftVector N q} ∧
        (∀ i : ℕ, i ≤ N → (S i).card ≤ P * (N + 1) ^ d ∧
          (∀ v ∈ S i, IsLeftOpenMPS (P * (N + 1) ^ d) v) ∧
          ∀ (E : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
            ‖Γ‖ = 1 → IsGapped Φ.hamiltonian E Delta →
            groundSpace Φ.hamiltonian E = Submodule.span ℂ {Γ} →
            IsViable (paddedGroundVector hi z Γ)
              (lvvSuccessiveError (min Delta 1) / N) (S i : Set (LeftBlockVector N q i))) ∧
        ∀ (E : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
          ‖Γ‖ = 1 → IsGapped Φ.hamiltonian E Delta →
          groundSpace Φ.hamiltonian E = Submodule.span ℂ {Γ} →
          ∃ w ∈ Submodule.span ℂ (S L : Set (LeftBlockVector N q L)), ‖w‖ = 1 ∧
            ‖(LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (leftConfigOfFinEquiv hi)).symm w - Γ‖ ^ 2 ≤
              1 / (R : ℝ) ^ 2 ∧
            IsOpenMPS L q (P * (N + 1) ^ d) (fun x ↦ w (leftConfigOfFin x)) := by
  classical
  have hg : 0 < min Delta 1 := lt_min hDelta zero_lt_one
  obtain ⟨P, d, hP, hrun⟩ := exists_uniform_positive_chain_successive_approximation hq hg
  refine ⟨P ^ 2, 2 * d, by nlinarith, ?_⟩
  intro L hL R hR Φ h0 h1
  dsimp only
  let N := L + 2 * R ^ 2
  have hi : L ≤ N := Nat.le_add_right _ _
  have hN : 1 ≤ N := hL.trans hi
  let z : Fin q := ⟨0, by omega⟩
  let Ψ : ManyBody.BondInteraction N q :=
    Φ.padded hi (fun _ ↦ ManyBody.siteBasisPenalty z)
  obtain ⟨_, hS, _⟩ := hrun N hN Ψ
    (ManyBody.BondInteraction.padded_term_nonneg (hi := hi) h0
      fun _ ↦ (ManyBody.siteBasisPenalty_posSemidef z).nonneg)
    (ManyBody.BondInteraction.padded_term_le_one (hi := hi) h1
      fun _ ↦ ManyBody.siteBasisPenalty_le_one z)
  let S := lvvSweep hq Ψ
    (ManyBody.BondInteraction.padded_term_nonneg (hi := hi) h0
      fun _ ↦ (ManyBody.siteBasisPenalty_posSemidef z).nonneg)
    (ManyBody.BondInteraction.padded_term_le_one (hi := hi) h1
      fun _ ↦ ManyBody.siteBasisPenalty_le_one z) (min Delta 1)
  have hS0 : S 0 = {emptyLeftVector N q} := rfl
  let B := P * (N + 1) ^ d
  have hB : 1 ≤ B := by
    simpa only [one_mul] using Nat.mul_le_mul hP (Nat.one_le_pow' d N)
  have hbudget : P ^ 2 * (N + 1) ^ (2 * d) = B ^ 2 := by
    simp only [B, mul_pow, pow_mul, mul_comm 2 d]
  have hBB : B ≤ B ^ 2 := by nlinarith
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hδ : lvvSuccessiveError (min Delta 1) / N < 1 := by
    apply (div_lt_one hNreal).mpr
    exact (lvvSuccessiveError_min_lt_one hDelta).trans_le (by exact_mod_cast hN)
  refine ⟨S, hS0, ?_, ?_⟩
  · intro i hiN
    obtain ⟨hcard, hmps, hviable⟩ := hS i hiN
    refine ⟨hcard.trans (hBB.trans_eq hbudget.symm), ?_, ?_⟩
    · intro v hv
      exact (hmps v hv).mono (max_le_max le_rfl (hBB.trans_eq hbudget.symm))
    · intro E Γ hΩ hgap hspan
      obtain ⟨hpn, hpg, hps⟩ := isGapped_paddedInteraction hL hi z Φ
        (Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun j _ ↦ h0 j)).isHermitian hΩ hgap
        hspan hDelta
      exact hviable E _ hpn hpg hps
  · intro E Γ hΩ hgap hspan
    obtain ⟨hcard, hmps, hviable⟩ := hS L hi
    obtain ⟨hpn, hpg, hps⟩ := isGapped_paddedInteraction hL hi z Φ
      (Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun j _ ↦ h0 j)).isHermitian hΩ hgap
      hspan hDelta
    obtain ⟨w, hw, hwnorm, herror, hmpsw⟩ :=
      (hviable E _ hpn hpg hps).exists_prefix_mps_of_paddedGroundVector hi z hΩ hδ hmps
    refine ⟨w, hw, hwnorm, ?_, hmpsw.mono ?_⟩
    · have hRreal : 0 < (R : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast (show 0 < R by omega))
      have hNR : 2 * (R : ℝ) ^ 2 ≤ N := by
        exact_mod_cast (show 2 * R ^ 2 ≤ N from Nat.le_add_left _ _)
      have hsmall : 2 * (lvvSuccessiveError (min Delta 1) / N) ≤ 1 / (R : ℝ) ^ 2 := by
        rw [← mul_div_assoc]
        apply (div_le_div_iff₀ hNreal hRreal).mpr
        have hc := mul_le_mul_of_nonneg_right (lvvSuccessiveError_min_lt_one hDelta).le
          hRreal.le
        nlinarith
      exact herror.trans hsmall
    · rw [hbudget, max_eq_right hB]
      exact (Nat.mul_le_mul_right B hcard).trans_eq (pow_two B).symm

end TNLean.MPS.AreaLaw

end

end SuccessiveConstruction
