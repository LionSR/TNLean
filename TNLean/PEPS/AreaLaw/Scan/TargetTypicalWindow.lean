/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ExplicitThresholds
import TNLean.PEPS.AreaLaw.Scan.ActualMarginalTails
import TNLean.PEPS.AreaLaw.Scan.TargetGeometry
import TNLean.PEPS.AreaLaw.ZeroBoundary
import QICLean.Analysis.TypicalTailScales
import QICLean.Entropy.TypicalStateFromTail

/-!
# The target typical window of the actual truncated ground vector

The interaction range, interaction bound, spectral gap and target-size coefficient
determine the truncation constant before the local dimension is chosen. For each
local dimension, the target-budget constant and threshold are then fixed before
the scale, domain, Hamiltonian, cut or scanner is chosen. Source ambient rows and clearance give
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
    change 0 < (reducedState_isHermitian Λ q Ωt X).spectralRestrictionMass
      (Entropy.typicalSet (reducedState_isHermitian Λ q Ωt X).eigenvalues
        (regionalEntropy Λ q Ωt X) w) at hz
    rw [hE] at hz
    simp only [Matrix.IsHermitian.spectralRestrictionMass, Finset.sum_empty,
      lt_self_iff_false] at hz
  · intro i hi
    exact ⟨(Entropy.mem_typicalSet.mp hi).1, Entropy.exp_le_of_mem_typicalSet hi⟩

/-- The explicit threshold of the typical-tail bound at width `n^(3/5)`: with
`c = (32 √((1 + θ) C))⁻¹`, the thresholds for `2 e^(e/2) exp (-c n^(1/20)) ≤ n^(-100)` and
`(log n)^6 ≤ n^(1/20)`, and `2` (`08-scanner.tex`, lines 405–414). -/
noncomputable def typicalTailThreshold (θ C : ℝ) : ℕ :=
  max 2 (max ⌈Real.stretchedExpThreshold (2 * Real.exp (Real.exp 1 / 2))
    (32 * Real.sqrt ((1 + θ) * C))⁻¹ (1 / 20) 100⌉₊ ⌈Real.logPowThreshold 1 1 (1 / 20) 6⌉₊)

/-- At width `n^(3/5)`, the marginal-tail expression is at most `n^(-100)` at every `n` from
the explicit threshold `typicalTailThreshold θ C` on, uniformly over
`0 < B ≤ C n (log n)^12`. Source: `08-scanner.tex`, lines 405–414. -/
theorem typical_tail_bound_of_typicalTailThreshold_le {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 0 < C)
    {n : ℕ} (hn : typicalTailThreshold θ C ≤ n) (B : ℝ) (hB : 0 < B)
    (hBn : B ≤ C * (n : ℝ) * (Real.log (n : ℝ)) ^ 12) :
    2 * Real.exp (Real.exp 1 / 2) *
        Real.exp (-((n : ℝ) ^ ((3 : ℝ) / 5) / (32 * Real.sqrt ((1 + θ) * B)))) ≤
      (n : ℝ) ^ (-100 : ℝ) := by
  set c := (32 * Real.sqrt ((1 + θ) * C))⁻¹
  have hnr : 1 < (n : ℝ) := by exact_mod_cast (le_max_left _ _).trans hn
  have hn0 : 0 < (n : ℝ) := one_pos.trans hnr
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnr
  have htail := Real.mul_exp_neg_le_rpow_neg_of_ceil_stretchedExpThreshold_le
    (by positivity) (by positivity : 0 < c) (by norm_num : (0 : ℝ) < 1 / 20)
    ((le_max_left _ _).trans ((le_max_right _ _).trans hn))
  have hlogpow : Real.log (n : ℝ) ^ 6 ≤ (n : ℝ) ^ ((1 : ℝ) / 20) := by
    simpa only [one_mul] using Real.mul_log_pow_le_mul_rpow_of_ceil_logPowThreshold_le
      zero_le_one one_pos (by norm_num) ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hpoly : c * (n : ℝ) ^ ((1 : ℝ) / 20) ≤
      c * (n : ℝ) ^ ((1 : ℝ) / 10) / (Real.log (n : ℝ)) ^ 6 := by
    rw [le_div_iff₀ (pow_pos hlog 6), mul_assoc, show (n : ℝ) ^ ((1 : ℝ) / 10) =
      (n : ℝ) ^ ((1 : ℝ) / 20) * (n : ℝ) ^ ((1 : ℝ) / 20) by
        rw [← Real.rpow_add hn0]; norm_num]
    gcongr
  have hcoef := hpoly.trans
    (Entropy.typicalWidth_div_sqrt_log_pow_twelve_budget_ge hθ hC hB hnr hBn)
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hcoef))
    (by positivity)).trans htail

/-- The explicit target-budget coefficient `max 1 (latticeCutBudgetConstant q R Ctr 4)`
(`08-scanner.tex`, lines 400–414, and `03-quasilocal.tex`, lines 452–455). -/
noncomputable def targetBudgetConstant (q R : ℕ) (Ctr : ℝ) : ℝ :=
  max 1 (latticeCutBudgetConstant q R Ctr 4)

/-- The explicit threshold of the target typical window: the typical-tail threshold at
`θ = 2 / g` and the target-budget coefficient (`08-scanner.tex`, lines 400–414). -/
noncomputable def targetTypicalWindowThreshold (q R : ℕ) (Ctr g : ℝ) : ℕ :=
  typicalTailThreshold (2 / g) (targetBudgetConstant q R Ctr)

/-- The source target window holds at every `S.n` from the explicit threshold
`targetTypicalWindowThreshold q R Ctr g` on, with the explicit target-budget coefficient
`targetBudgetConstant q R Ctr`. Only the truncation constant `Ctr` is chosen, before the local
dimension. Source: `08-scanner.tex`, lines 400–414, and `07-comparators.tex`, lines 37–53. -/
theorem exists_truncated_target_typical_window_of_targetTypicalWindowThreshold_le (R : ℕ)
    {J Δ C_T : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hC_T : 0 ≤ C_T) :
    ∃ Ctr : ℝ, 0 < Ctr ∧ ∀ (q : ℕ) [NeZero q], 1 ≤ q →
      ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
        (E₀ : ℝ) (Ω : StateSpace Λ q) (F : ScannerExponents)
        (T : Finset (ℤ × ℤ)) (hT : T.Nonempty),
        IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        S.graph = domainGraph Λ → (∀ i, S.anchor i ∈ i.val) →
        targetTypicalWindowThreshold q R Ctr (Δ / positiveNormalization 1 (Δ / 2) J) ≤ S.n →
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
          B X ≤ targetBudgetConstant q R Ctr * (S.n : ℝ) * Real.log (S.n : ℝ) ^ 12 ∧
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
  refine ⟨Ctr, hCtr, fun q _ hq ↦ ?_⟩
  have hbudget := latticeCutBudget_le_log hq R hCtr.le (show (0 : ℝ) ≤ 4 by norm_num)
  set C := latticeCutBudgetConstant q R Ctr 4
  have hCB : 0 < max 1 C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hg : 0 < Δ / positiveNormalization 1 (Δ / 2) J :=
    div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  have hscalar := fun n (hn : typicalTailThreshold (2 / (Δ / positiveNormalization 1 (Δ / 2) J))
    (max 1 C) ≤ n) => typical_tail_bound_of_typicalTailThreshold_le
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hg.le) hCB hn
  intro Λ h S E₀ Ω F T hT hgs hgraph hanchor hn hr hsize hdepth hrows hclear
  have hn2 : 2 ≤ S.n := (le_max_left _ _).trans hn
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
      (n := (S.n : ℝ)) (D := 1) (by exact_mod_cast hn2) le_rfl
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

/-- The source target window belongs to the same quantitative actual truncated
ground vector as every-cut moment and tail estimates. The constants and threshold
are independent of all physical and scanner data quantified afterward. The budget
uses the original admissible labels, even for repeated anchors and zero terms.
Only the target's `4n` boundary permits setting the lattice-budget factor to one;
no growing scanner parameter is absorbed into a constant.

The truncation coefficient is uniform in the local dimension; the target-budget
coefficient and threshold may depend on it. This is a proved strengthening of the
printed truncation proposition: `03-quasilocal.tex`, lines 406–410, permits its
coefficient to depend on `q`. The scanner uses that radius in `08-scanner.tex`,
lines 49–59, without asserting uniformity in `q`. Here
`exists_truncated_reducedState_moment_tail_bounds` supplies `Ctr` before `q`.
For the target window, see `08-scanner.tex`, lines 400–414, and
`07-comparators.tex`, lines 37–53, at the revision pinned above. The floor scale
is used literally; neither collar volume, target boundary, cut budget nor target
tail is assumed. -/
theorem exists_truncated_target_typical_window_uniform_in_q (R : ℕ)
    {J Δ C_T : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hC_T : 0 ≤ C_T) :
    ∃ Ctr : ℝ, 0 < Ctr ∧ ∀ (q : ℕ) [NeZero q], 1 ≤ q →
      ∃ C_B : ℝ, 0 < C_B ∧ ∃ N : ℕ, 2 ≤ N ∧
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
  obtain ⟨Ctr, hCtr, hall⟩ :=
    exists_truncated_target_typical_window_of_targetTypicalWindowThreshold_le R hJ hΔ hC_T
  exact ⟨Ctr, hCtr, fun q _ hq => ⟨_, one_pos.trans_le (le_max_left _ _), _, le_max_left _ _,
    hall q hq⟩⟩

/-- The target typical window at a fixed local dimension. This specialization is used
by the rough and sharp selection estimates. Source: `08-scanner.tex`, lines 400–414,
and `07-comparators.tex`, lines 37–53. -/
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
  obtain ⟨Ctr, hCtr, hall⟩ :=
    exists_truncated_target_typical_window_uniform_in_q R hJ hΔ hC_T
  obtain ⟨C_B, hC_B, N, hN, hwindow⟩ := hall q hq
  exact ⟨Ctr, C_B, hCtr, hC_B, N, hN, hwindow⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan
