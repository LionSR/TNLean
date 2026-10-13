/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.StatusMarginalBudget
import TNLean.PEPS.AreaLaw.Scan.ActualMarginalTails

/-!
# Common marginal moment input at every physical status

The same truncated ground vector has the five comparator moment bounds on
one real interval, with a common budget of order nD(log n)^12. The geometric
coefficient is selected before every scanner, and the truncation radius
coefficient is selected before the local dimension. The energy, phase and
trace-distance conclusions are retained for that very same vector.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 32–58 and 400–414; `07-comparators.tex`, lines 70–85,
at `openai/math@adc7f124`.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

/-- Increasing a positive budget only shortens the allowed real moment interval. -/
theorem tailRadius_antitone_budget {ϑ B B' : ℝ} (hϑ : 0 ≤ ϑ)
    (hB : 0 < B) (hBB' : B ≤ B') :
    Entropy.tailRadius ϑ B' ≤ Entropy.tailRadius ϑ B := by
  unfold Entropy.tailRadius
  apply one_div_le_one_div_of_le
  · positivity
  · gcongr

/-- The moment radius has the comparator's separated constant and budget form. -/
theorem tailRadius_eq_div_sqrt {ϑ B : ℝ} (hϑ : 0 ≤ ϑ) :
    Entropy.tailRadius ϑ B = (1 / (32 * Real.sqrt (1 + ϑ))) / Real.sqrt B := by
  simp only [Entropy.tailRadius, Real.sqrt_mul (by linarith : 0 ≤ 1 + ϑ),
    div_div, mul_assoc]

namespace CollarScan

open SpectralFilter

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ} [NeZero q]
    (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
    (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q)

/-- A common upper bound for the geometric budget gives the comparator's exact
real-u interval, without changing the truncated physical ground vector. -/
theorem log_surprisalMoment_truncated_reducedState_le_common
    (hgraph : S.graph = domainGraph Λ) (hanchor : ∀ i, S.anchor i ∈ i.val)
    (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1) (L : ℕ) {e B : ℝ} {Ωt : StateSpace Λ q}
    (hgs : IsGappedGroundState Λ q (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e Ωt
      ((Δ / positiveNormalization 1 (Δ / 2) J) / 2))
    (Q : Finset (Site Λ))
    (hB : cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor Q ≤ B) {u : ℝ}
    (hu : |u| ≤ (1 / (32 * Real.sqrt
      (1 + 2 / (Δ / positiveNormalization 1 (Δ / 2) J)))) / Real.sqrt B) :
    Real.log (Entropy.surprisalMoment (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
      u * regionalEntropy Λ q Ωt Q +
        512 * Real.exp 1 * (2 / (Δ / positiveNormalization 1 (Δ / 2) J)) * B * u ^ 2 := by
  have hg : 0 < Δ / positiveNormalization 1 (Δ / 2) J :=
    div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  have hϑ : 0 ≤ 2 / (Δ / positiveNormalization 1 (Δ / 2) J) := by positivity
  have hr := tailRadius_antitone_budget hϑ
    (lt_of_lt_of_le zero_lt_one
      (one_le_cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor Q)) hB
  have hu' : |u| ≤ Entropy.tailRadius
      (2 / (Δ / positiveNormalization 1 (Δ / 2) J)) B := by
    rw [tailRadius_eq_div_sqrt hϑ]
    exact hu
  refine (S.log_surprisalMoment_truncated_reducedState_le h Ω hgraph hanchor hΔ hΩ L
    hgs Q (hu'.trans hr)).trans ?_
  gcongr

/-- One truncation and one budget give all five marginal-MGF inputs at every
completed and pre-charge status. Both coefficients precede the scanner; the
truncation coefficient also precedes the local dimension. The quantitative
energy, phase and trace bounds concern the same existential pair as the moment
bounds. Literal scale separation, rows and clearance are the geometric inputs;
no moment, cut-budget or truncated spectral hypothesis is supplied.

Source: `08-scanner.tex`, lines 32–58 and 400–414, and the marginal moment input
of `07-comparators.tex`, lines 70–85. -/
theorem exists_truncated_statusMarginal_moment_bounds
    (R : ℕ) {J Δ Ccard : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hCcard : 0 ≤ Ccard) :
    ∃ Ctr : ℝ, 0 < Ctr ∧ ∀ (q : ℕ) [NeZero q],
      ∃ CB : ℝ, 0 < CB ∧
        ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)] (hT : T.Nonempty)
          (h : LocalHamiltonian Λ q R J)
          (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
          (E₀ : ℝ) (Ω : StateSpace Λ q),
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          S.graph = domainGraph Λ →
          S.depth = (fun x ↦ ambientDepth T hT x.val) →
          (∀ i, S.anchor i ∈ i.val) →
          ∀ L : ℕ, 2 ≤ S.n →
          S.r₀ = ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ →
          ((S.truncationSet L).card : ℝ) ≤ Ccard * (S.n : ℝ) ^ 2 →
          S.r₀ ≤ S.D → 1 ≤ S.D → 4 * S.D ≤ S.m → 8 * S.K * S.m ≤ L →
          (∀ d : ℕ, 1 ≤ d → d ≤ L →
            (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
          (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
            ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
          let g := Δ / positiveNormalization 1 (Δ / 2) J
          let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
          let C₀ := 512 * Real.exp 1 * (2 / g)
          let c₀ := 1 / (32 * Real.sqrt (1 + 2 / g))
          0 < C₀ ∧ 0 < c₀ ∧
          ∃ (e : ℝ) (Ωt : StateSpace Λ q) (B : ℝ),
            1 ≤ B ∧ B ≤ CB * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12) ∧
            IsGappedGroundState Λ q (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e Ωt (g / 2) ∧
            0 ≤ e ∧ e ≤ ε ∧
            (∃ θ : ℝ, ‖Ωt - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * Real.sqrt (ε / g)) ∧
            Matrix.traceDistance
                (Matrix.vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)))
                (Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
              Real.sqrt (2 * ε / g) ∧
            ∀ (k : ℕ) (hist : History S.K S.m S.M k) (band : Fin S.K),
              (k ≤ S.n * S.m →
                ∀ Q ∈ statusMarginalRegions S.depth (S.state hist band),
                  ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
                    Real.log (Entropy.surprisalMoment
                      (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
                      u * regionalEntropy Λ q Ωt Q + C₀ * B * u ^ 2) ∧
              (k + 1 ≤ S.n * S.m →
                ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist band),
                  ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
                    Real.log (Entropy.surprisalMoment
                      (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
                      u * regionalEntropy Λ q Ωt Q + C₀ * B * u ^ 2) := by
  classical
  obtain ⟨Ctr, hCtr, htr⟩ := exists_truncated_reducedState_moment_tail_bounds R hJ hΔ hCcard
  refine ⟨Ctr, hCtr, ?_⟩
  intro q _
  obtain ⟨CB, hCB, hbudget⟩ := exists_statusMarginal_cutBudget_le_log
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) R hCtr.le
  refine ⟨CB, hCB, ?_⟩
  intro Λ T _ hT h S E₀ Ω hgs hgraph hdepth hanchor L hn hradius hcard
    hr hDpos hD hL hrows hclear
  dsimp only
  have hg : 0 < Δ / positiveNormalization 1 (Δ / 2) J :=
    div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  refine ⟨by positivity, by positivity, ?_⟩
  obtain ⟨e, Ωt, htrgs, he0, he, hphase, htrace, _, _⟩ :=
    htr Λ h S E₀ Ω hgs hgraph hanchor L hn hradius hcard
  obtain ⟨hB, hb⟩ := hbudget Λ T hT S hgraph hdepth hanchor L hn hradius
    hr hDpos hD hL hrows hclear
  refine ⟨e, Ωt, CB * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12),
    hB, le_rfl, htrgs, he0, he, hphase, htrace, ?_⟩
  intro k hist band
  constructor
  · intro hk Q hQ u hu
    exact S.log_surprisalMoment_truncated_reducedState_le_common h Ω hgraph hanchor hΔ
      hgs.1 L htrgs Q ((hb k hist band).1 hk Q hQ) hu
  · intro hk Q hQ u hu
    exact S.log_surprisalMoment_truncated_reducedState_le_common h Ω hgraph hanchor hΔ
      hgs.1 L htrgs Q ((hb k hist band).2 hk Q hQ) hu

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
