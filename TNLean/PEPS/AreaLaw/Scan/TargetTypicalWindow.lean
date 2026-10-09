/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualMarginalTails
import TNLean.PEPS.AreaLaw.Scan.TargetGeometry
import TNLean.PEPS.AreaLaw.ZeroBoundary
import QICLean.Analysis.TypicalTailScales
import QICLean.Entropy.TypicalStateFromTail

/-!
# The target typical window of the actual truncated ground vector

Fixed physical parameters and a target-size coefficient determine the truncation
constant, target-budget constant and threshold before the scale, domain,
Hamiltonian, cut or scanner is chosen. Source ambient rows and clearance give
the compact volume bound and the target's `4n` boundary. The labelled lattice
budget is then at most `C_B * n * (log n)^12`.

One actual truncated physical ground vector retains its quantitative energy,
phase distance, trace distance and every-cut marginal bounds. Its target marginal
has failure mass at most `n^(-100)` at width `n^(3/5)`, hence positive canonical
typical mass and the source exponential eigenvalue window. Original `Ω` centers
the Hamiltonian terms; the entropy of `Ωt` centers this spectral window.
No auxiliary ground-state assertion or comparator construction is made.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 400–414, and `07-comparators.tex`, lines 37–53, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter

/-- A regional tail gives a nonempty positive-eigenvalue typical set with
positive mass and the exponential window, including singular marginals.
Source: `07-comparators.tex`, lines 37–53. -/
theorem target_typicalSet_bounds {Λ : Finset (ℤ × ℤ)} {q : ℕ}
    (Ωt : StateSpace Λ q) (hΩt : ‖Ωt‖ = 1) (X : Finset (Site Λ)) {w δ : ℝ}
    (htail : Entropy.surprisalTail (reducedState_isHermitian Λ q Ωt X).eigenvalues
      (regionalEntropy Λ q Ωt X) w ≤ δ) (hδ : δ < 1) :
    let p := (reducedState_isHermitian Λ q Ωt X).eigenvalues
    let E := Entropy.typicalSet p (regionalEntropy Λ q Ωt X) w
    let z := (reducedState_isHermitian Λ q Ωt X).spectralRestrictionMass E
    0 < 1 - δ ∧ 1 - δ ≤ z ∧ 0 < z ∧ z ≤ 1 ∧ E.Nonempty ∧
      ∀ i ∈ E, 0 < p i ∧
        Real.exp (-regionalEntropy Λ q Ωt X - w) ≤ p i ∧
        p i ≤ Real.exp (-regionalEntropy Λ q Ωt X + w) := by
  classical
  obtain ⟨hzδ, hz, hz1, _⟩ :=
    (reducedState_posSemidef Λ q Ωt X).typicalSet_normalizedSpectralRestriction_bounds
      w δ (trace_reducedState Ωt hΩt X) htail hδ
  refine ⟨sub_pos.mpr hδ, hzδ, hz, hz1, ?_, ?_⟩
  · apply Finset.nonempty_iff_ne_empty.mpr
    intro hE
    simpa only [hE, Matrix.IsHermitian.spectralRestrictionMass, Finset.sum_empty,
      lt_self_iff_false] using hz
  · intro i hi
    exact ⟨(Entropy.mem_typicalSet.mp hi).1, Entropy.exp_le_of_mem_typicalSet hi⟩

/-- The source target window belongs to the same quantitative actual truncated
ground vector as every-cut moment and tail estimates. The constants and threshold
are independent of all physical and scanner data quantified afterward. The budget
uses the original admissible labels, even for repeated anchors and zero terms.
Only the target's `4n` boundary permits setting the lattice-budget factor to one;
no growing scanner parameter is absorbed into a constant.

Source: `08-scanner.tex`, lines 400–414, and `07-comparators.tex`, lines 37–53.
The floor scale is used literally; neither collar volume, target boundary,
cut budget nor target tail is assumed. -/
theorem exists_truncated_target_typical_window {q : ℕ} [NeZero q]
    (hq : 1 ≤ q) (R : ℕ) {J Δ C_T : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) :
    ∃ Ctr C_B : ℝ, 0 < Ctr ∧ 0 < C_B ∧ ∃ N : ℕ, 2 ≤ N ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
        (E₀ : ℝ) (Ω : StateSpace Λ q) (F : ScannerExponents)
        (T : Finset (ℤ × ℤ)) (hT : T.Nonempty),
        IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        S.graph = domainGraph Λ → (∀ i, S.anchor i ∈ i.val) → N ≤ S.n →
        S.r₀ = ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ →
        (T.card : ℝ) ≤ C_T * (S.n : ℝ) ^ 2 →
        S.depth = (fun x ↦ ambientDepth T hT x.val) →
        (∀ d : ℕ, 1 ≤ d → d ≤ F.L S.n →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
          ((2 * F.L S.n + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        let L := F.L S.n
        let X := S.A.filter fun x ↦ x.val ∈ T
        let g := Δ / positiveNormalization 1 (Δ / 2) J
        let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
        let w := (S.n : ℝ) ^ ((3 : ℝ) / 5)
        let δ := (S.n : ℝ) ^ (-100 : ℝ)
        let B : Finset (Site Λ) → ℝ :=
          fun Y => cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor Y
        ((S.truncationSet L).card : ℝ) ≤ (C_T + 1) * (S.n : ℝ) ^ 2 ∧
        X ⊆ S.truncationSet L ∧ (edgeBoundary Λ X).card ≤ 4 * S.n ∧
        ∃ (e : ℝ) (Ωt : StateSpace Λ q),
          IsGappedGroundState Λ q (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e Ωt (g / 2) ∧
          0 ≤ e ∧ e ≤ ε ∧
          (∃ θ : ℝ, ‖Ωt - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * Real.sqrt (ε / g)) ∧
          Matrix.traceDistance (Matrix.vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)))
              (Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
            Real.sqrt (2 * ε / g) ∧
          (∀ (Y : Finset (Site Λ)) (u : ℝ),
            |u| ≤ Entropy.tailRadius (2 / g) (B Y) →
            Real.log (Entropy.surprisalMoment
              (reducedState_isHermitian Λ q Ωt Y).eigenvalues u) ≤
              u * regionalEntropy Λ q Ωt Y +
                512 * Real.exp 1 * (2 / g) * B Y * u ^ 2) ∧
          (∀ (Y : Finset (Site Λ)) (v : ℝ),
            Entropy.surprisalTail (reducedState_isHermitian Λ q Ωt Y).eigenvalues
              (regionalEntropy Λ q Ωt Y) v ≤
              min 1 (2 * Real.exp (Real.exp 1 / 2) *
                Real.exp (-(v / (32 * Real.sqrt ((1 + 2 / g) * B Y)))))) ∧
          B X ≤ C_B * (S.n : ℝ) * Real.log (S.n : ℝ) ^ 12 ∧
          Entropy.surprisalTail (reducedState_isHermitian Λ q Ωt X).eigenvalues
            (regionalEntropy Λ q Ωt X) w ≤ δ ∧
          let p := (reducedState_isHermitian Λ q Ωt X).eigenvalues
          let E := Entropy.typicalSet p (regionalEntropy Λ q Ωt X) w
          let z := (reducedState_isHermitian Λ q Ωt X).spectralRestrictionMass E
          0 < 1 - δ ∧ 1 - δ ≤ z ∧ 0 < z ∧ z ≤ 1 ∧ E.Nonempty ∧
            ∀ i ∈ E, 0 < p i ∧
              Real.exp (-regionalEntropy Λ q Ωt X - w) ≤ p i ∧
              p i ≤ Real.exp (-regionalEntropy Λ q Ωt X + w) := by
  classical
  obtain ⟨Ctr, hCtr, htr⟩ := exists_truncated_reducedState_moment_tail_bounds R hJ hΔ
    (show 0 ≤ C_T + 1 by positivity)
  obtain ⟨C, _, hbudget⟩ := exists_latticeCutBudget_le_log hq R hCtr.le
    (show (0 : ℝ) ≤ 4 by norm_num)
  have hCB : 0 < max 1 C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hg : 0 < Δ / positiveNormalization 1 (Δ / 2) J :=
    div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  obtain ⟨N, hN, hscalar⟩ := Entropy.exists_typical_tail_bound_of_log_pow_twelve_budget
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hg.le) hCB
  refine ⟨Ctr, max 1 C, hCtr, hCB, N, hN, ?_⟩
  intro Λ h S E₀ Ω F T hT hgs hgraph hanchor hn hr hsize hdepth hrows hclear
  have hn2 : 2 ≤ S.n := hN.trans hn
  obtain ⟨hcard, hX, hboundary⟩ := S.source_target_geometry F T hT
    (by omega) hsize hdepth hrows hclear
  refine ⟨hcard, hX, hboundary, ?_⟩
  obtain ⟨e, Ωt, htrgs, he0, he, hphase, htrace, hmoment, htail⟩ :=
    htr Λ h S E₀ Ω hgs hgraph hanchor (F.L S.n) hn2 hr hcard
  let X := S.A.filter fun x ↦ x.val ∈ T
  let B := cutBudget q S.graph (S.truncationSet (F.L S.n)) S.r₀ S.anchor X
  have hboundaryR : ((edgeBoundary Λ X).card : ℝ) ≤ 4 * (S.n : ℝ) := by
    exact_mod_cast hboundary
  have hB : B ≤ max 1 C * (S.n : ℝ) * Real.log (S.n : ℝ) ^ 12 := by
    have hb := hbudget Λ S.anchor hanchor (S.truncationSet (F.L S.n)) X hX
      (S.n : ℝ) 1 (by exact_mod_cast hn2) le_rfl
      (by simpa only [mul_one] using hboundaryR)
    dsimp [B]
    rw [hgraph, hr]
    calc
      _ ≤ C * ((S.n : ℝ) * Real.log (S.n : ℝ) ^ 12) := by
        simpa only [mul_one] using hb
      _ ≤ max 1 C * ((S.n : ℝ) * Real.log (S.n : ℝ) ^ 12) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ = _ := by ring
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one
    (one_le_cutBudget q S.graph (S.truncationSet (F.L S.n)) S.r₀ S.anchor X)
  have htypical : Entropy.surprisalTail (reducedState_isHermitian Λ q Ωt X).eigenvalues
      (regionalEntropy Λ q Ωt X) ((S.n : ℝ) ^ ((3 : ℝ) / 5)) ≤
        (S.n : ℝ) ^ (-100 : ℝ) :=
    (htail X _).trans ((min_le_right _ _).trans (hscalar S.n hn B hBpos hB))
  have hδ : (S.n : ℝ) ^ (-100 : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (show 1 < S.n by omega))
      (by norm_num)
  exact ⟨e, Ωt, htrgs, he0, he, hphase, htrace, hmoment, htail, hB, htypical,
    target_typicalSet_bounds Ωt htrgs.1 X htypical hδ⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan
