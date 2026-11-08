/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyCommutator
import TNLean.Lattice.GaussianFilteredMetricTruncation
import TNLean.Lattice.GaussianFilteredTruncationWeighted
import TNLean.Lattice.GaussianTruncationDecayBound

/-!
# Low-energy commutators in an arbitrary finite metric space

The numerical finite-support Lieb–Robinson bound, Gaussian filtering, and the
original spectral gap give exponential decay of ground-space commutators.
The argument retains the support cardinality and needs no sphere-growth bound.
Physical metric separation is converted to an integer interaction-graph distance;
the observables themselves need not lie in bounded graph balls.

For interaction radius `R > 0`, term norm bound `J`, and at most `S` sites in
any interaction ball, put `v = 4(S+1)|SJ|exp(4)+1` and
`λ = min(1/4, Δ/(8v))/R`. For observables supported in metric balls of radius
`ρ` about `i,j`, the bound is
`(4 |ball(j,ρ)|+4) ‖W‖ ‖B‖ exp(2λρ) exp(-λ dist(i,j))`.
The same estimate applies directly to the actual truncated Gaussian terms, with
`‖W‖ ‖B‖` replaced by `J²`. Their initial filter parameter is unrestricted;
the second Gaussian filter under the original Hamiltonian is chosen separately.

The cardinality is the source's explicit support factor `N_M`. No uniform bound
on the sum over all sites is asserted here; the corresponding general-metric
claim has the separate correction documented in
`docs/paper-gaps/hastings05_geometric_growth_scope.tex`.

Source: Hastings, *Solving Gapped Hamiltonians Locally*,
arXiv:cond-mat/0508554v3, `proj3new.tex`, eqs. `lc` and `blecm`, lines 1548–1601.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.Lattice

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Exponential low-energy commutator decay needs no growth assumption.
Hastings, arXiv:cond-mat/0508554v3, lines 1548–1601. -/
theorem norm_groundCompression_commutator_le_graphSeparation
    (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι) (ha : ∀ k, a k ∈ X k)
    (h : κ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ k, (h k).IsHermitian)
    (hSupport : ∀ k, h k ∈ supportedOperators d (X k : Set ι))
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ X k, ∀ y ∈ X k, G.edist x y ≤ R)
    (vR : ℕ) (hvR : 1 ≤ vR) (hCard : ∀ k, (X k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ X j), ‖h j‖ ≤ b₀)
    {Δ : ℝ} (hΔ : 0 < Δ) (hH : (∑ k, h k).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + Δ ≤ hH.eigenvalues k)
    (S Y : Finset ι) {W B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hW : W ∈ supportedOperators d (S : Set ι))
    (hB : B ∈ supportedOperators d (Y : Set ι)) (m : ℕ)
    (hm : ∀ x ∈ S, ∀ y ∈ Y, (m : ℕ∞) ≤ G.edist x y) :
    let v := 4 * vR * |b₀| * Real.exp (2 * (R : ℝ)) + 1
    let γ := min (1 / 4) (Δ / (8 * v))
    ‖groundCompression (∑ k, h k) E₀ W * groundCompression (∑ k, h k) E₀ B -
        groundCompression (∑ k, h k) E₀ B * groundCompression (∑ k, h k) E₀ W‖ ≤
      (4 * (S.card : ℝ) + 4) * ‖W‖ * ‖B‖ * Real.exp (-(γ * m)) := by
  intro v γ
  have hv : 0 < v := by dsimp [v]; positivity
  let T : ℝ := m / (4 * v)
  let q := T * Δ
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb := commutator_time_window_exp_bounds hv hΔ (Nat.cast_nonneg m)
  change Real.exp (v * T - m / 2) ≤ Real.exp (-(γ * m)) ∧
    Real.exp (-(T * Δ) ^ 2 / (2 * q)) ≤ Real.exp (-(γ * m)) ∧
    Real.exp (-q / 2) ≤ Real.exp (-(γ * m)) at hb
  obtain ⟨e1, e2, e3⟩ := hb
  have hloc (t : ℝ) (ht : t ∈ Set.Icc (-T) T) :
      ‖hermitianUnitaryPath (∑ k, h k) t * W * hermitianUnitaryPath (∑ k, h k) (-t) * B -
        B *
          (hermitianUnitaryPath (∑ k, h k) t * W * hermitianUnitaryPath (∑ k, h k) (-t))‖ ≤
      4 * (S.card : ℝ) * ‖W‖ * ‖B‖ * Real.exp (-(γ * m)) := by
    have hn := norm_heisenberg_commutator_le_graphDistance_finsets_numeric G X a ha h hHerm
      hSupport R hDiam vR hvR hCard b₀ hBudget S hW Y hB 1 (by norm_num) m hm t
    refine hn.trans (mul_le_mul_of_nonneg_left (le_trans ?_ e1) (by positivity))
    apply Real.exp_le_exp.mpr
    have htT : |t| ≤ T := abs_le.mpr ht
    have hvel : 0 ≤ 4 * vR * |b₀| * Real.exp (2 * (R : ℝ)) := by positivity
    have hx := mul_le_mul_of_nonneg_left htT hvel
    change 4 * vR * |b₀| * Real.exp (2 * 1 * R) * |t| - 1 * m ≤ v * T - m / 2
    simp only [mul_one, one_mul]
    dsimp [v] at *
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hfilter := norm_commutator_gaussianFilteredTerm_le (ΔE := Δ) hq hH W B hT
    (show 0 ≤ 4 * (S.card : ℝ) * ‖W‖ * ‖B‖ * Real.exp (-(γ * m)) by positivity) hloc
  have hfiltered : ‖gaussianFilteredTerm q Δ (∑ k, h k) W * B -
      B * gaussianFilteredTerm q Δ (∑ k, h k) W‖ ≤
      (4 * (S.card : ℝ) + 2) * ‖W‖ * ‖B‖ * Real.exp (-(γ * m)) := by
    refine hfilter.trans ?_
    have := mul_le_mul_of_nonneg_left e2 (show 0 ≤ 2 * ‖W‖ * ‖B‖ by positivity)
    nlinarith
  refine (norm_groundCompression_commutator_le hq hΔ hH hgap W B).trans ?_
  have := mul_le_mul_of_nonneg_left e3 (show 0 ≤ 2 * ‖W‖ * ‖B‖ by positivity)
  nlinarith


/-- Physical support separation gives exponential low-energy decay in an arbitrary
finite metric space with the source's local range and cardinality bounds.
Hastings, arXiv:cond-mat/0508554v3, lines 1548–1601. -/
theorem norm_groundCompression_commutator_le_metricSeparation
    [PseudoMetricSpace ι] {R J Δ : ℝ} (hR : 0 < R) (S : ℕ) (hJ : 0 ≤ J)
    (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ i, (h i).IsHermitian)
    (hSupport : ∀ i, h i ∈ supportedOperators d (Metric.closedBall i R))
    (hNorm : ∀ i, ‖h i‖ ≤ J) (hCard : ∀ i : ι, (metricRangeBall R i).card ≤ S)
    (hΔ : 0 < Δ) (hH : (∑ i, h i).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + Δ ≤ hH.eigenvalues k)
    (X Y : Finset ι) {W B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hW : W ∈ supportedOperators d (X : Set ι))
    (hB : B ∈ supportedOperators d (Y : Set ι)) (ℓ : ℝ)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, ℓ ≤ dist x y) :
    let vR := S + 1
    let v := 4 * vR * |(S : ℝ) * J| * Real.exp (2 * (2 : ℝ)) + 1
    let γ := min (1 / 4) (Δ / (8 * v))
    ‖groundCompression (∑ i, h i) E₀ W * groundCompression (∑ i, h i) E₀ B -
        groundCompression (∑ i, h i) E₀ B * groundCompression (∑ i, h i) E₀ W‖ ≤
      (4 * (X.card : ℝ) + 4) * ‖W‖ * ‖B‖ * Real.exp (-((γ / R) * ℓ)) := by
  classical
  intro vR v γ
  have hgen (i : ι) : h i ∈ supportedOperators d (metricRangeBall R i : Set ι) := by
    simpa only [coe_metricRangeBall] using hSupport i
  have hdist (x : ι) (hx : x ∈ X) (y : ι) (hy : y ∈ Y) :
      (Nat.ceil (ℓ / R) : ℕ∞) ≤ (metricRangeGraph R).edist x y := by
    apply metricRangeGraph_edist_lower_ceil hR
    have heq : R * (ℓ / R) = ℓ := by field_simp
    rw [heq]
    exact hsep x hx y hy
  have hg := norm_groundCompression_commutator_le_graphSeparation
    (metricRangeGraph R) (metricRangeBall R) id (fun i ↦ self_mem_metricRangeBall hR.le i)
    h hHerm hgen 2 (metricRangeBall_graph_diameter_le_two R)
    vR (by dsimp [vR]; omega)
    (fun i ↦ (hCard i).trans (by dsimp [vR]; omega)) ((S : ℝ) * J)
    (metricRangeBall_norm_budget_le hCard hJ h hNorm) hΔ hH hgap X Y hW hB
    (Nat.ceil (ℓ / R)) hdist
  change ‖groundCompression (∑ i, h i) E₀ W * groundCompression (∑ i, h i) E₀ B -
      groundCompression (∑ i, h i) E₀ B * groundCompression (∑ i, h i) E₀ W‖ ≤
      (4 * (X.card : ℝ) + 4) * ‖W‖ * ‖B‖ *
        Real.exp (-(γ * (Nat.ceil (ℓ / R) : ℝ))) at hg
  have hv : 0 < v := by dsimp [v]; positivity
  have hγ : 0 < γ := lt_min (by norm_num) (div_pos hΔ (by positivity))
  refine hg.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (Nat.le_ceil (ℓ / R)) hγ.le
  convert neg_le_neg hh using 1
  ring


/-- The source's low-energy estimate for finite-radius observables, with the
second observable's support cardinality explicit and without graph growth.
Hastings, arXiv:cond-mat/0508554v3, lines 1548–1601. -/
theorem norm_groundCompression_commutator_le_metricBalls
    [PseudoMetricSpace ι] {R J Δ : ℝ} (hR : 0 < R) (S : ℕ) (hJ : 0 ≤ J)
    (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ i, (h i).IsHermitian)
    (hSupport : ∀ i, h i ∈ supportedOperators d (Metric.closedBall i R))
    (hNorm : ∀ i, ‖h i‖ ≤ J) (hCard : ∀ i : ι, (metricRangeBall R i).card ≤ S)
    (hΔ : 0 < Δ) (hH : (∑ i, h i).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + Δ ≤ hH.eigenvalues k)
    (ρ : ℝ) (i j : ι) {W B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hW : W ∈ supportedOperators d (Metric.closedBall i ρ))
    (hB : B ∈ supportedOperators d (Metric.closedBall j ρ)) :
    let vR := S + 1
    let v := 4 * vR * |(S : ℝ) * J| * Real.exp (2 * (2 : ℝ)) + 1
    let γ := min (1 / 4) (Δ / (8 * v))
    ‖groundCompression (∑ k, h k) E₀ W * groundCompression (∑ k, h k) E₀ B -
        groundCompression (∑ k, h k) E₀ B * groundCompression (∑ k, h k) E₀ W‖ ≤
      (4 * ((metricRangeBall ρ j).card : ℝ) + 4) * ‖W‖ * ‖B‖ *
        Real.exp (2 * (γ / R) * ρ) * Real.exp (-((γ / R) * dist i j)) := by
  intro vR v γ
  have hW' : W ∈ supportedOperators d (metricRangeBall ρ i : Set ι) := by
    simpa only [coe_metricRangeBall] using hW
  have hB' : B ∈ supportedOperators d (metricRangeBall ρ j : Set ι) := by
    simpa only [coe_metricRangeBall] using hB
  have hsep (x : ι) (hx : x ∈ metricRangeBall ρ j) (y : ι)
      (hy : y ∈ metricRangeBall ρ i) : dist i j - 2 * ρ ≤ dist x y := by
    have hx' : dist x j ≤ ρ := by simpa only [dist_comm] using mem_metricRangeBall.mp hx
    have hy' : dist i y ≤ ρ := mem_metricRangeBall.mp hy
    have h1 := dist_triangle i y j
    have h2 := dist_triangle y x j
    rw [dist_comm y x] at h2
    linarith
  have hg := norm_groundCompression_commutator_le_metricSeparation hR S hJ h hHerm
    hSupport hNorm hCard hΔ hH hgap (metricRangeBall ρ j) (metricRangeBall ρ i)
    hB' hW' (dist i j - 2 * ρ) hsep
  change ‖groundCompression (∑ k, h k) E₀ B * groundCompression (∑ k, h k) E₀ W -
      groundCompression (∑ k, h k) E₀ W * groundCompression (∑ k, h k) E₀ B‖ ≤
      (4 * ((metricRangeBall ρ j).card : ℝ) + 4) * ‖B‖ * ‖W‖ *
        Real.exp (-((γ / R) * (dist i j - 2 * ρ))) at hg
  rw [norm_sub_rev] at hg
  refine hg.trans_eq ?_
  rw [show -((γ / R) * (dist i j - 2 * ρ)) =
    2 * (γ / R) * ρ + -((γ / R) * dist i j) by ring, Real.exp_add]
  ring

/-- The source's actual truncated operators satisfy the growth-free low-energy
commutator bound; the second Gaussian filter is independent of their first filter.
Hastings, arXiv:cond-mat/0508554v3, lines 1548–1601. -/
theorem norm_groundCompression_metric_truncated_commutator_le
    [PseudoMetricSpace ι] {R J Δ : ℝ} (hR : 0 < R) (S : ℕ) (hJ : 0 ≤ J)
    (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ i, (h i).IsHermitian)
    (hSupport : ∀ i, h i ∈ supportedOperators d (Metric.closedBall i R))
    (hNorm : ∀ i, ‖h i‖ ≤ J) (hCard : ∀ i : ι, (metricRangeBall R i).card ≤ S)
    (hΔ : 0 < Δ) (hH : (∑ i, h i).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + Δ ≤ hH.eigenvalues k)
    (q ρ : ℝ) (hρ : R ≤ ρ) (i j : ι) :
    let vR := S + 1
    let v := 4 * vR * |(S : ℝ) * J| * Real.exp (2 * (2 : ℝ)) + 1
    let γ := min (1 / 4) (Δ / (8 * v))
    let Mi := gaussianFilteredTerm q Δ (∑ k ∈ metricRangeBall (ρ - R) i, h k) (h i)
    let Mj := gaussianFilteredTerm q Δ (∑ k ∈ metricRangeBall (ρ - R) j, h k) (h j)
    ‖groundCompression (∑ k, h k) E₀ Mi * groundCompression (∑ k, h k) E₀ Mj -
        groundCompression (∑ k, h k) E₀ Mj * groundCompression (∑ k, h k) E₀ Mi‖ ≤
      (4 * ((metricRangeBall ρ j).card : ℝ) + 4) * J ^ 2 *
        Real.exp (2 * (γ / R) * ρ) * Real.exp (-((γ / R) * dist i j)) := by
  intro vR v γ Mi Mj
  obtain ⟨hMi, -, hnMi⟩ := metric_truncated_filter_properties hρ h hHerm hSupport hNorm q Δ i
  obtain ⟨hMj, -, hnMj⟩ := metric_truncated_filter_properties hρ h hHerm hSupport hNorm q Δ j
  have hg := norm_groundCompression_commutator_le_metricBalls hR S hJ h hHerm hSupport
    hNorm hCard hΔ hH hgap ρ i j hMi hMj
  refine hg.trans ?_
  calc (4 * ((metricRangeBall ρ j).card : ℝ) + 4) * ‖Mi‖ * ‖Mj‖ *
      Real.exp (2 * (γ / R) * ρ) * Real.exp (-((γ / R) * dist i j))
      ≤ (4 * ((metricRangeBall ρ j).card : ℝ) + 4) * J * J *
        Real.exp (2 * (γ / R) * ρ) * Real.exp (-((γ / R) * dist i j)) := by gcongr
    _ = _ := by ring

end TNLean.Lattice
