/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scanner.Statuses.StatusMarginalBudget
import TNLean.PEPS.AreaLaw.Scanner.Statuses.ActualMarginalTails
import QICLean.ManyBody.Hamiltonian.GroundSpace
import TNLean.PEPS.AreaLaw.Collar.Scales.StatusScaleSeparation
import QICLean.ManyBody.Sites.Lattice.SupDistance
import TNLean.PEPS.AreaLaw.Collar.PhysicalPartition
import TNLean.PEPS.AreaLaw.Scanner.Histories.BadHistoryAsymptotics

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

## Physical status moments at the literal source scales

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

## Common status moments for a supplied truncated ground vector

The geometric coefficient is chosen before the physical system. The moment
estimates then apply to any supplied ground vector of the same truncated
Hamiltonian, at every completed and pre-charge status. Thus the vector chosen
by physical charge selection need not be chosen again.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Proposition 9.2, lines 386–391 and 400–414, and
`07-comparators.tex`, lines 70–85, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open ManyBody (designatedSupport)

section

open Matrix

open ManyBody (IsGapped groundSpace PlaneInteraction ambientDepth supDist)
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

open ManyBody (AdmissibleSupport ambientDilation planeDomainGraph)

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
    (S : CollarScan ↥Λ (AdmissibleSupport Λ R))
    (h : PlaneInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
        (Ω : EuclideanSpace ℂ (↥Λ → Fin q))

include hh hhJ in
/-- A common upper bound for the geometric budget gives the comparator's exact
real-u interval, without changing the truncated physical ground vector. -/
theorem log_surprisalMoment_truncated_regionState_le_common
    (hgraph : S.graph = planeDomainGraph Λ) (hanchor : ∀ i, S.anchor i ∈ i.val)
    (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1) (L : ℕ) {e B : ℝ} {Ωt : EuclideanSpace ℂ (↥Λ → Fin q)}
    (hΩt : ‖Ωt‖ = 1)
    (hgapt : IsGapped (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e
      ((Δ / positiveNormalization 1 (Δ / 2) J) / 2))
    (hspant : groundSpace (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e = Submodule.span ℂ {Ωt})
    (Q : Finset ↥Λ)
    (hB : ManyBody.cutLogBudget
      (fun i ↦ designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)) (fun _ ↦ q) Q ≤ B)
    {u : ℝ}
    (hu : |u| ≤ (1 / (32 * Real.sqrt
      (1 + 2 / (Δ / positiveNormalization 1 (Δ / 2) J)))) / Real.sqrt B) :
    Real.log (Entropy.surprisalMoment (ManyBody.regionState_isHermitian Q Ωt).eigenvalues u) ≤
      u * ManyBody.regionEntropy Ωt Q +
        512 * Real.exp 1 * (2 / (Δ / positiveNormalization 1 (Δ / 2) J)) * B * u ^ 2 := by
  have hg : 0 < Δ / positiveNormalization 1 (Δ / 2) J :=
    div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  have hϑ : 0 ≤ 2 / (Δ / positiveNormalization 1 (Δ / 2) J) := by positivity
  have hr := tailRadius_antitone_budget hϑ
    (lt_of_lt_of_le zero_lt_one (Entropy.one_le_cutLogBudget _ _)) hB
  have hu' : |u| ≤ Entropy.tailRadius
      (2 / (Δ / positiveNormalization 1 (Δ / 2) J)) B := by
    rw [tailRadius_eq_div_sqrt hϑ]
    exact hu
  refine (S.log_surprisalMoment_truncated_regionState_le h hh hhJ Ω hgraph hanchor hΔ hΩ L
    hΩt hgapt hspant Q (hu'.trans hr)).trans ?_
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
          (h : PlaneInteraction Λ q R) (_ : ∀ X, (h.term X).IsHermitian) (_ : ∀ X, ‖h.term X‖ ≤ J)
          (S : CollarScan ↥Λ (AdmissibleSupport Λ R))
          (E₀ : ℝ) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)),
          ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
          groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
          S.graph = planeDomainGraph Λ →
          S.depth = (fun x ↦ ambientDepth T hT x.val) →
          (∀ i, S.anchor i ∈ i.val) →
          ∀ L : ℕ, 2 ≤ S.n →
          S.r₀ = ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ →
          ((S.truncationSet L).card : ℝ) ≤ Ccard * (S.n : ℝ) ^ 2 →
          S.r₀ ≤ S.D → 1 ≤ S.D → 4 * S.D ≤ S.m → 8 * S.K * S.m ≤ L →
          (∀ d : ℕ, 1 ≤ d → d ≤ L →
            (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
          (∀ t ∈ T, ∀ z ∈ ManyBody.boundaryEndpoints Λ S.A,
            ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < (supDist t z : ℤ)) →
          let g := Δ / positiveNormalization 1 (Δ / 2) J
          let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
          let C₀ := 512 * Real.exp 1 * (2 / g)
          let c₀ := 1 / (32 * Real.sqrt (1 + 2 / g))
          0 < C₀ ∧ 0 < c₀ ∧
          ∃ (e : ℝ) (Ωt : EuclideanSpace ℂ (↥Λ → Fin q)) (B : ℝ),
            1 ≤ B ∧ B ≤ CB * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12) ∧
            (‖Ωt‖ = 1 ∧ IsGapped (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e (g / 2) ∧
              groundSpace (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e = Submodule.span ℂ {Ωt}) ∧
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
                      (ManyBody.regionState_isHermitian Q Ωt).eigenvalues u) ≤
                      u * ManyBody.regionEntropy Ωt Q + C₀ * B * u ^ 2) ∧
              (k + 1 ≤ S.n * S.m →
                ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist band),
                  ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
                    Real.log (Entropy.surprisalMoment
                      (ManyBody.regionState_isHermitian Q Ωt).eigenvalues u) ≤
                      u * ManyBody.regionEntropy Ωt Q + C₀ * B * u ^ 2) := by
  classical
  obtain ⟨Ctr, hCtr, htr⟩ := exists_truncated_regionState_moment_tail_bounds R hJ hΔ hCcard
  refine ⟨Ctr, hCtr, ?_⟩
  intro q _
  obtain ⟨CB, hCB, hbudget⟩ := exists_statusMarginal_cutLogBudget_le_log
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) R hCtr.le
  refine ⟨CB, hCB, ?_⟩
  intro Λ T _ hT h hh hhJ S E₀ Ω hΩ hgap hspan hgraph hdepth hanchor L hn hradius hcard
    hr hDpos hD hL hrows hclear
  dsimp only
  have hg : 0 < Δ / positiveNormalization 1 (Δ / 2) J :=
    div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  refine ⟨by positivity, by positivity, ?_⟩
  obtain ⟨e, Ωt, htrgs, he0, he, hphase, htrace, _, _⟩ :=
    htr Λ h hh hhJ S E₀ Ω hΩ hgap hspan hgraph hanchor L hn hradius hcard
  obtain ⟨hB, hb⟩ := hbudget Λ T hT S hgraph hdepth hanchor L hn hradius
    hr hDpos hD hL hrows hclear
  refine ⟨e, Ωt, CB * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12),
    hB, le_rfl, htrgs, he0, he, hphase, htrace, ?_⟩
  intro k hist band
  constructor
  · intro hk Q hQ u hu
    exact S.log_surprisalMoment_truncated_regionState_le_common h hh hhJ Ω hgraph hanchor hΔ
      hΩ L htrgs.1 htrgs.2.1 htrgs.2.2 Q ((hb k hist band).1 hk Q hQ) hu
  · intro hk Q hQ u hu
    exact S.log_surprisalMoment_truncated_regionState_le_common h hh hhJ Ω hgraph hanchor hΔ
      hΩ L htrgs.1 htrgs.2.1 htrgs.2.2 Q ((hb k hist band).2 hk Q hQ) hu

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
end

end

section

open Filter Matrix

open ManyBody (IsGapped groundSpace PlaneInteraction ambientDepth
  card_filter_ambientDepth_le_quadratic supDist)
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

open ManyBody (AdmissibleSupport ambientDilation planeDomainGraph)

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
          (h : PlaneInteraction Λ q R) (_ : ∀ X, (h.term X).IsHermitian) (_ : ∀ X, ‖h.term X‖ ≤ J)
          (S : CollarScan ↥Λ (AdmissibleSupport Λ R))
          (E₀ : ℝ) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)),
          ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
          groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
          S.graph = planeDomainGraph Λ →
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
          (∀ t ∈ T, ∀ z ∈ ManyBody.boundaryEndpoints Λ S.A,
            ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < (supDist t z : ℤ)) →
          1 ≤ S.K ∧
          let g := Δ / positiveNormalization 1 (Δ / 2) J
          let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
          let C₀ := 512 * Real.exp 1 * (2 / g)
          let c₀ := 1 / (32 * Real.sqrt (1 + 2 / g))
          0 < C₀ ∧ 0 < c₀ ∧
          ∃ (e : ℝ) (Ωt : EuclideanSpace ℂ (↥Λ → Fin q)) (B : ℝ),
            1 ≤ B ∧ B ≤ CB * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12) ∧
            (‖Ωt‖ = 1 ∧ IsGapped (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e (g / 2) ∧
              groundSpace (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e = Submodule.span ℂ {Ωt}) ∧
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
                      (ManyBody.regionState_isHermitian Q Ωt).eigenvalues u) ≤
                      u * ManyBody.regionEntropy Ωt Q + C₀ * B * u ^ 2) ∧
              (k + 1 ≤ S.n * S.m →
                ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist band),
                  ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
                    Real.log (Entropy.surprisalMoment
                      (ManyBody.regionState_isHermitian Q Ωt).eigenvalues u) ≤
                      u * ManyBody.regionEntropy Ωt Q + C₀ * B * u ^ 2) := by
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
  intro Λ T _ hT h hh hhJ S E₀ Ω hΩ hgap hspan hgraph hdepth hanchor L hn hL hm hD hK hradius
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
      card_filter_ambientDepth_le_quadratic hT S.A hLn hsize hrows
  exact ⟨hKpos, hstatusq Λ T hT h hh hhJ S E₀ Ω hΩ hgap hspan hgraph hdepth hanchor L hn2 hradius
    hcard hr hDpos hDm hKL hrows hclear⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan
end

end

section

noncomputable section

open Matrix Filter

open ManyBody (IsGapped groundSpace PlaneInteraction ambientDepth supDist)
open scoped BigOperators Matrix.Norms.L2Operator

open ManyBody (AdmissibleSupport ambientDilation planeDomainGraph)

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter

/-- The actual geometric budgets give all sharp marginal moment estimates
for the supplied truncated ground vector. The geometric scale conditions
are explicit here and follow from the rounded scales in the scanner theorem.
Source: Proposition 9.2, `08-scanner.tex`, lines 386–391 and 400–414. -/
theorem exists_suppliedTarget_statusMarginal_moment_bounds
    {q : ℕ} [NeZero q] (hq : 1 ≤ q) (R : ℕ) {Cr : ℝ} (hCr : 0 ≤ Cr) :
    ∃ CB : ℝ, 0 < CB ∧
      ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)]
        (hT : T.Nonempty) (S : CollarScan ↥Λ (AdmissibleSupport Λ R)),
        S.graph = planeDomainGraph Λ →
        S.depth = (fun x ↦ ambientDepth T hT x.val) →
        (∀ i, S.anchor i ∈ i.val) →
        ∀ L : ℕ, 2 ≤ S.n →
        S.r₀ = ⌈Cr * Real.log (S.n : ℝ) ^ 2⌉₊ →
        S.r₀ ≤ S.D → 1 ≤ S.D → 4 * S.D ≤ S.m → 8 * S.K * S.m ≤ L →
        (∀ d : ℕ, 1 ≤ d → d ≤ L →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ t ∈ T, ∀ z ∈ ManyBody.boundaryEndpoints Λ S.A,
          ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < (supDist t z : ℤ)) →
        let B := CB * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12)
        1 ≤ B ∧
          ∀ {J Δ : ℝ} (h : PlaneInteraction Λ q R) (_ : ∀ X, (h.term X).IsHermitian)
              (_ : ∀ X, ‖h.term X‖ ≤ J) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)),
            0 < Δ → ‖Ω‖ = 1 →
            ∀ (e : ℝ) (Ωt : EuclideanSpace ℂ (↥Λ → Fin q)),
              ‖Ωt‖ = 1 →
              IsGapped (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e
                ((Δ / positiveNormalization 1 (Δ / 2) J) / 2) →
              groundSpace (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e = Submodule.span ℂ {Ωt} →
              let g := Δ / positiveNormalization 1 (Δ / 2) J
              let C₀ := 512 * Real.exp 1 * (2 / g)
              let c₀ := 1 / (32 * Real.sqrt (1 + 2 / g))
              0 < C₀ ∧ 0 < c₀ ∧
                ∀ (s : ℕ) (hist : History S.K S.m S.M s) (band : Fin S.K),
                  (s ≤ S.n * S.m →
                    ∀ Q ∈ statusMarginalRegions S.depth (S.state hist band),
                      ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
                        Real.log (Entropy.surprisalMoment
                          (ManyBody.regionState_isHermitian Q Ωt).eigenvalues u) ≤
                          u * ManyBody.regionEntropy Ωt Q + (C₀ * B) * u ^ 2) ∧
                  (s + 1 ≤ S.n * S.m →
                    ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist band),
                      ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
                        Real.log (Entropy.surprisalMoment
                          (ManyBody.regionState_isHermitian Q Ωt).eigenvalues u) ≤
                          u * ManyBody.regionEntropy Ωt Q + (C₀ * B) * u ^ 2) := by
  obtain ⟨CB, hCB, hbudget⟩ := exists_statusMarginal_cutLogBudget_le_log hq R hCr
  refine ⟨CB, hCB, ?_⟩
  intro Λ T _ hT S hgraph hdepth hanchor L hn hradius hr hDpos hD hL hrows hclear
  obtain ⟨hB, hcut⟩ := hbudget Λ T hT S hgraph hdepth hanchor L hn hradius
    hr hDpos hD hL hrows hclear
  refine ⟨hB, ?_⟩
  intro J Δ h hh hhJ Ω hΔ hΩ e Ωt hΩt hgapt hspant
  have hg : 0 < Δ / positiveNormalization 1 (Δ / 2) J :=
    div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  refine ⟨by positivity, by positivity, ?_⟩
  intro s hist band
  exact ⟨fun hs Q hQ u hu ↦
    S.log_surprisalMoment_truncated_regionState_le_common h hh hhJ Ω hgraph hanchor hΔ hΩ
      L hΩt hgapt hspant Q ((hcut s hist band).1 hs Q hQ) hu,
    fun hs Q hQ u hu ↦
      S.log_surprisalMoment_truncated_regionState_le_common h hh hhJ Ω hgraph hanchor hΔ hΩ
        L hΩt hgapt hspant Q ((hcut s hist band).2 hs Q hQ) hu⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan
end

end
