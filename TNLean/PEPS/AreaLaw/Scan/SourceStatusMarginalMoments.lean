/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.StatusMarginalMoments
import TNLean.PEPS.AreaLaw.Scan.StatusScaleSeparation
import TNLean.PEPS.AreaLaw.Scan.CompactCollarCounting
import TNLean.PEPS.AreaLaw.Scan.BadChargeRatioBound

/-!
# Physical status moments at the literal source scales

The actual target-size and ambient-layer bounds give the quadratic volume
needed by truncation. The rounded source powers supply every scale inequality
used by the five physical cuts, including a positive integer band count.
The threshold depends on the fixed exponents and truncation coefficient, and
is chosen before the local dimension and every physical scanner.

The resulting ground vector is the same vector in the spectral, energy,
phase, trace-distance and all completed/pre-charge marginal moment estimates.
No compact-volume bound, status boundary bound or moment bound is assumed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 21–58 and 400–414; `07-comparators.tex`, lines 70–85,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter Matrix
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter

/-- The source geometry and rounded scales give a single quantitative truncated
vector and a common marginal moment budget at every physical status. The radius
coefficient and integer threshold precede the local dimension. The budget
coefficient may depend on that dimension, but precedes every physical instance.
The threshold is allowed to depend on the fixed exponent gaps.

Source: `08-scanner.tex`, lines 21–58 and 400–414. -/
theorem exists_source_statusMarginal_moment_bounds
    (R : ℕ) {J Δ Ct ell kappa mu : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hCt : 0 ≤ Ct) (hell : 0 < ell)
    (hkappa : 0 < kappa) (hkm : kappa < mu) (hmuL : mu < 1 - ell) :
    ∃ Ctr : ℝ, 0 < Ctr ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ (q : ℕ) [NeZero q],
      ∃ CB : ℝ, 0 < CB ∧
        ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)] (hT : T.Nonempty)
          (h : LocalHamiltonian Λ q R J)
          (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
          (E₀ : ℝ) (Ω : StateSpace Λ q),
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          S.graph = domainGraph Λ →
          S.depth = (fun x ↦ ambientDepth T hT x.val) →
          (∀ i, S.anchor i ∈ i.val) →
          ∀ L : ℕ, N ≤ S.n →
          L = ⌊(S.n : ℝ) ^ (1 - ell)⌋₊ →
          S.m = ⌊(S.n : ℝ) ^ mu⌋₊ →
          S.D = ⌈(S.n : ℝ) ^ kappa⌉₊ →
          S.K = L / (8 * S.m) →
          S.r₀ = ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ →
          (T.card : ℝ) ≤ Ct * (S.n : ℝ) ^ 2 →
          (∀ d : ℕ, 1 ≤ d → d ≤ L →
            (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
          (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
            ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
          1 ≤ S.K ∧
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
  obtain ⟨Ctr, hCtr, hstatus⟩ := exists_truncated_statusMarginal_moment_bounds R hJ hΔ
    (show 0 ≤ Ct + 1 by linarith)
  have hscales := (eventually_status_scale_separation (ell := ell) hCtr.le hkappa hkm).and
    (eventually_one_le_source_bandCount (hkappa.trans hkm) hmuL)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hscales
  refine ⟨Ctr, hCtr, max N 2, le_max_right _ _, ?_⟩
  intro q _
  obtain ⟨CB, hCB, hstatusq⟩ := hstatus q
  refine ⟨CB, hCB, ?_⟩
  intro Λ T _ hT h S E₀ Ω hgs hgraph hdepth hanchor L hn hL hm hD hK hradius
    hsize hrows hclear
  obtain ⟨hscales, hKpos⟩ := hN S.n ((le_max_left N 2).trans hn)
  dsimp only [roundedLogRadius] at hscales
  rw [← hL, ← hm, ← hD, ← hK, ← hradius] at hscales
  rw [← hL, ← hm, ← hK] at hKpos
  obtain ⟨hn2, hr, hDpos, hDm, hKL⟩ := hscales
  have hLn : L ≤ S.n := by
    rw [hL]
    exact (source_lengths_le (n := S.n) (mu := mu) (by omega) hell.le (by linarith)).1
  have hcard : ((S.truncationSet L).card : ℝ) ≤ (Ct + 1) * (S.n : ℝ) ^ 2 := by
    simpa only [truncationSet, hdepth] using
      card_compact_collar_le_quadratic hT S.A hLn hsize hrows
  exact ⟨hKpos, hstatusq Λ T hT h S E₀ Ω hgs hgraph hdepth hanchor L hn2 hradius
    hcard hr hDpos hDm hKL hrows hclear⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan
