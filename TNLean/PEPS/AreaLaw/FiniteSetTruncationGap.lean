/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.CrossingBudget
import TNLean.PEPS.AreaLaw.TruncationRadius
import QICLean.Analysis.PositiveGapUniqueness

/-!
# The truncated Hamiltonian keeps a unique gapped ground vector

Truncating the positive constraints near a finite set `S₀` with base radius
`r₀ = ⌈C₁ (log n)²⌉` changes their sum by at most `ε_n = min {n^{-1000}, g/4}`. The
truncated sum is again a sum of positive contractions, and by the gap-stability statement
its ground vector is unique, its ground energy lies in `[0, ε_n]`, its gap is at least
`g/2`, and its ground vector is `2 √(ε_n/g)`-close to `Ω` after a choice of phase, with
trace distance at most `√(2 ε_n / g)`.

## Main results

* `TNLean.PEPS.AreaLaw.exists_finiteSetTruncation`: Proposition 4.5, first part, for any
  family of constraints with the conclusions of Proposition 4.3 at `p = 1`.

The gap inequality `H' - e₀ I ≥ (g/2) (I - |Ω₀⟩⟨Ω₀|)` in the conclusion makes `Ω₀` the unique
ground vector up to a scalar: `Matrix.PosSemidef.eq_inner_smul_of_gap` shows that every vector
`ψ` with `H' ψ = e₀ ψ` equals `⟪Ω₀, ψ⟫ Ω₀`, and `Matrix.PosSemidef.eigenspace_eq_span_of_gap`
identifies the eigenspace of `H'` at `e₀` with the line spanned by `Ω₀`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 4.5 (`prop:truncation`), section file `03-quasilocal.tex`, lines 405–433 and
  457–505. Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
  Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

open QuantumCircuit

/-- Each truncated constraint is a positive contraction (`03-quasilocal.tex`, line 426). -/
theorem truncatedConstraint_mem_Icc {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (S₀ : Finset ι) (r₀ : ℕ) (a : ι)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) :
    0 ≤ truncatedConstraint q G S₀ r₀ a k ∧ truncatedConstraint q G S₀ r₀ a k ≤ 1 := by
  unfold truncatedConstraint
  split_ifs
  · exact ⟨hk₀, hk₁⟩
  · exact ⟨siteExpectation_nonneg _ hk₀, siteExpectation_le_one _ hk₁⟩

/-- **Truncation near a finite set** (Proposition 4.5, `prop:truncation`, first part,
`03-quasilocal.tex`, lines 405–433), for constraints with the conclusions of Proposition 4.3
at `p = 1`: `0 ≤ kᵢ ≤ I`, `kᵢ Ω = 0`, `∑ᵢ kᵢ ≥ g (I - |Ω⟩⟨Ω|)`, and ball tails
`C e^{-c √l}`, on a graph whose balls of radius `d` have at most `K_b (d + 1)²` sites and
whose sites anchor at most `μ` labels. There is `C₁ > 0`, depending only on
`C, c, g, μ, K_b, C₀`, such that for every real `n ≥ 2` and every `S₀` with
`|S₀| ≤ C₀ n²`, with `r₀ = ⌈C₁ (log n)²⌉` and `ε_n = min {n^{-1000}, g/4}`: the truncated
constraints are positive contractions, `‖H' - H_F‖ ≤ ε_n` for their sum `H'`, and `H'` has
a unit ground vector `Ω₀` with ground energy `e₀ ∈ [0, ε_n]`,
`H' - e₀ I ≥ (g/2) (I - |Ω₀⟩⟨Ω₀|)`, `‖Ω₀ - e^{iθ} Ω‖ ≤ 2 √(ε_n / g)` for some phase, and
trace distance at most `√(2 ε_n / g)` (`eq:quasilocal-truncation-error`,
`eq:quasilocal-ground-distance`). -/
theorem exists_finiteSetTruncation {C c g μ Kb C₀ : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hg : 0 < g)
    (hμ : 0 ≤ μ) (hKb : 0 ≤ Kb) (hC₀ : 0 ≤ C₀) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
        (G : SimpleGraph ι) (a : κ → ι) (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
        (Ω : EuclideanSpace ℂ (ι → Fin q)), ‖Ω‖ = 1 →
        (∀ i, 0 ≤ k i ∧ k i ≤ 1 ∧ k i *ᵥ WithLp.ofLp Ω = 0) →
        ((∑ i, k i) - (g : ℂ) •
          (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
        (∀ i (l : ℕ), ‖k i - siteExpectation q (graphBall G (a i) l) (k i)‖ ≤
          C * Real.exp (-(c * (l : ℝ) ^ (1 / 2 : ℝ)))) →
        (∀ x (d : ℕ), ((graphBall G x d).card : ℝ) ≤ Kb * ((d : ℝ) + 1) ^ 2) →
        (∀ x, ((Finset.univ.filter fun i => a i = x).card : ℝ) ≤ μ) →
        ∀ n : ℝ, 2 ≤ n → ∀ S₀ : Finset ι, (S₀.card : ℝ) ≤ C₀ * n ^ 2 →
        let r₀ := ⌈C₁ * Real.log n ^ 2⌉₊
        let ε := min (n ^ (-1000 : ℝ)) (g / 4)
        let Ht := ∑ i, truncatedConstraint q G S₀ r₀ (a i) (k i)
        (∀ i, 0 ≤ truncatedConstraint q G S₀ r₀ (a i) (k i) ∧
          truncatedConstraint q G S₀ r₀ (a i) (k i) ≤ 1) ∧
        ‖Ht - ∑ i, k i‖ ≤ ε ∧
        ∃ (e : ℝ) (Ω₀ : EuclideanSpace ℂ (ι → Fin q)), ‖Ω₀‖ = 1 ∧
          Ht *ᵥ WithLp.ofLp Ω₀ = (e : ℂ) • WithLp.ofLp Ω₀ ∧ 0 ≤ e ∧ e ≤ ε ∧
          (Ht - (e : ℂ) • 1 - ((g / 2 : ℝ) : ℂ) •
            (1 - Matrix.vecMulVec (WithLp.ofLp Ω₀) (star (WithLp.ofLp Ω₀)))).PosSemidef ∧
          (∃ θ : ℝ, ‖Ω₀ - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * Real.sqrt (ε / g)) ∧
          Matrix.traceDistance (Matrix.vecMulVec (WithLp.ofLp Ω₀) (star (WithLp.ofLp Ω₀)))
              (Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
            Real.sqrt (2 * ε / g) := by
  obtain ⟨A, hA0, hA⟩ := exists_sum_shell_le hc (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨C₁, hC₁, hrad⟩ := exists_truncationConstant (B := C * μ * Kb * A) (C₀ := C₀)
    (by positivity) hC₀ hc hg
  refine ⟨C₁, hC₁, ?_⟩
  intro q _ ι _ _ κ _ G a k Ω hΩ hk hgap htail hBall hMult n hn S₀ hS₀ r₀ ε Ht
  have hHt := truncatedConstraint_mem_Icc (q := q) G S₀ r₀
  have herr : ‖Ht - ∑ i, k i‖ ≤ ε := by
    refine (norm_sum_truncatedConstraint_sub_le G S₀ a k hC hKb hμ htail hBall hMult hA r₀).trans
      ?_
    have := hrad n hn S₀.card (Nat.cast_nonneg _) hS₀
    calc C * μ * Kb * S₀.card * A * Real.exp (-(c / 2 * (r₀ : ℝ) ^ (1 / 2 : ℝ)))
        = C * μ * Kb * A * S₀.card * Real.exp (-(c / 2 * (r₀ : ℝ) ^ (1 / 2 : ℝ))) := by ring
      _ ≤ ε := this
  refine ⟨fun i => hHt (a i) (hk i).1 (hk i).2.1, herr, ?_⟩
  have hHtpsd : Ht.PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    exact Finset.sum_nonneg fun i _ => (hHt (a i) (hk i).1 (hk i).2.1).1
  have hHFΩ : (∑ i, k i) *ᵥ WithLp.ofLp Ω = 0 := by
    rw [Matrix.sum_mulVec]; exact Finset.sum_eq_zero fun i _ => (hk i).2.2
  have hε : ε ≤ g / 4 := min_le_right _ _
  exact Matrix.exists_posSemidef_gap_of_norm_sub_le hΩ hg hε hgap hHFΩ hHtpsd herr

theorem kernelExponent_one : SpectralFilter.kernelExponent 1 = 1 / 2 := by
  norm_num [SpectralFilter.kernelExponent]

/-- **Truncation near a finite set, from the global gap** (Proposition 4.5, first part,
`03-quasilocal.tex`, lines 405–433): Proposition 4.3 with `p = 1` followed by
`exists_finiteSetTruncation`. The graph carries the hypotheses of Proposition 4.3 and the
ball and anchor-multiplicity counts `K_b (d + 1)²`, `μ` of the source's Section 2. The
constant `C₁` depends only on `R, v_R, b₀, K_g, k_g, J, Δ, K_b, μ, C₀`. In addition, each
truncated term acts on its designated support (the ball `N_{rᵢ}(aᵢ)`, or the component of
`aᵢ` when `d_Λ(aᵢ, S₀) = ∞`), so the crossing counts of `CrossingBudget.lean` bound the actual
supports of the terms of `H'`. -/
theorem exists_finiteSetTruncation_of_gap (R vR : ℕ) (b₀ Kg : ℝ) (kg : ℕ) {J Δ Kb μ C₀ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hKb : 0 ≤ Kb) (hμ : 0 ≤ μ) (hC₀ : 0 ≤ C₀) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
        (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι), (∀ k, a k ∈ X k) →
        ∀ (h : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ), (∀ k, (h k).IsHermitian) →
        (∀ k, h k ∈ supportedOperators q (X k : Set ι)) →
        (∀ k, ∀ x ∈ X k, ∀ z ∈ X k, G.edist x z ≤ R) →
        (∀ k, (X k).card ≤ vR) →
        (∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ X j), ‖h j‖ ≤ b₀) →
        (∀ x (d : ℕ),
          ((Finset.univ.filter fun y => G.edist x y = d).card : ℝ) ≤ Kg * ((d : ℝ) + 1) ^ kg) →
        (∀ x (d : ℕ), ((graphBall G x d).card : ℝ) ≤ Kb * ((d : ℝ) + 1) ^ 2) →
        (∀ x, ((Finset.univ.filter fun i => a i = x).card : ℝ) ≤ μ) →
        (∀ k, ‖h k‖ ≤ J) →
        ∀ (E₀ : ℝ) (Ω : EuclideanSpace ℂ (ι → Fin q)), ‖Ω‖ = 1 →
        (∑ k, h k) *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω →
        ((∑ k, h k) - (E₀ : ℂ) • 1 -
          (Δ : ℂ) • (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
        ∀ n : ℝ, 2 ≤ n → ∀ S₀ : Finset ι, (S₀.card : ℝ) ≤ C₀ * n ^ 2 →
        let cs := SpectralFilter.positiveNormalization 1 (Δ / 2) J
        let g := Δ / cs
        let k := fun i =>
          SpectralFilter.positiveConstraint cs
            (SpectralFilter.centeredFilter 1 (Δ / 2) (∑ j, h j) Ω (h i))
        let r₀ := ⌈C₁ * Real.log n ^ 2⌉₊
        let ε := min (n ^ (-1000 : ℝ)) (g / 4)
        let Ht := ∑ i, truncatedConstraint q G S₀ r₀ (a i) (k i)
        (∀ i, truncatedConstraint q G S₀ r₀ (a i) (k i) ∈
          supportedOperators q (designatedSupport G S₀ r₀ (a i) : Set ι)) ∧
        (∀ i, 0 ≤ truncatedConstraint q G S₀ r₀ (a i) (k i) ∧
          truncatedConstraint q G S₀ r₀ (a i) (k i) ≤ 1) ∧
        ‖Ht - ∑ i, k i‖ ≤ ε ∧
        ∃ (e : ℝ) (Ω₀ : EuclideanSpace ℂ (ι → Fin q)), ‖Ω₀‖ = 1 ∧
          Ht *ᵥ WithLp.ofLp Ω₀ = (e : ℂ) • WithLp.ofLp Ω₀ ∧ 0 ≤ e ∧ e ≤ ε ∧
          (Ht - (e : ℂ) • 1 - ((g / 2 : ℝ) : ℂ) •
            (1 - Matrix.vecMulVec (WithLp.ofLp Ω₀) (star (WithLp.ofLp Ω₀)))).PosSemidef ∧
          (∃ θ : ℝ, ‖Ω₀ - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * Real.sqrt (ε / g)) ∧
          Matrix.traceDistance (Matrix.vecMulVec (WithLp.ofLp Ω₀) (star (WithLp.ofLp Ω₀)))
              (Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
            Real.sqrt (2 * ε / g) := by
  obtain ⟨C, c, hC, hc, hpos⟩ :=
    exists_positiveQuasilocalConstraints (le_refl 1) R vR b₀ Kg kg hJ hΔ
  set cs := SpectralFilter.positiveNormalization 1 (Δ / 2) J
  have hcs : 0 < cs := SpectralFilter.positiveNormalization_pos 1 (Δ / 2) J
  obtain ⟨C₁, hC₁, htr⟩ := exists_finiteSetTruncation hC hc (div_pos hΔ hcs) hμ hKb hC₀
  refine ⟨C₁, hC₁, ?_⟩
  intro q _ ι _ _ κ _ G X a ha h hHerm hSupport hDiam hCard hBudget hGrowth hBall hMult hJh
    E₀ Ω hΩ hHΩ hgap n hn S₀ hS₀n
  obtain ⟨hk, hsum, hgapk, htail, hcomp⟩ := hpos G X a ha h hHerm hSupport hDiam hCard hBudget
    hGrowth hJh E₀ Ω hΩ hHΩ hgap
  have hgapF : ((∑ i, SpectralFilter.positiveConstraint cs
      (SpectralFilter.centeredFilter 1 (Δ / 2) (∑ j, h j) Ω (h i))) -
        ((Δ / cs : ℝ) : ℂ) •
          (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef := by
    rw [← Matrix.le_iff]; exact hgapk.trans hsum
  have htail' : ∀ i (l : ℕ), ‖SpectralFilter.positiveConstraint cs
      (SpectralFilter.centeredFilter 1 (Δ / 2) (∑ j, h j) Ω (h i)) -
        siteExpectation q (graphBall G (a i) l) (SpectralFilter.positiveConstraint cs
          (SpectralFilter.centeredFilter 1 (Δ / 2) (∑ j, h j) Ω (h i)))‖ ≤
        C * Real.exp (-(c * (l : ℝ) ^ (1 / 2 : ℝ))) := by
    intro i l
    have := (htail i l).2.2
    rwa [kernelExponent_one] at this
  exact ⟨fun i => truncatedConstraint_mem_supportedOperators G S₀ _ (a i) (hcomp i),
    htr G a _ Ω hΩ hk hgapF htail' hBall hMult n hn S₀ hS₀n⟩

end TNLean.PEPS.AreaLaw
