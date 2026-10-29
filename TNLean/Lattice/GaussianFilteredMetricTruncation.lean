/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.MetricInteractionGraph
import TNLean.Lattice.GaussianFilteredTruncationWeighted
import TNLean.Lattice.GaussianFilteredTruncationGround
import TNLean.Lattice.GaussianTruncationDecayBound

/-!
# Gaussian truncation in a finite metric space

Let each interaction term be supported in the metric ball of radius `R` about its
index, with norm at most `J`, and suppose each such ball has at most `S` sites.
For positive `R` and gap `Δ`, constants independent of the metric space and the
Hamiltonian give exponential bounds for the actual truncated Gaussian filter
`Mᵢ`, obtained by retaining the terms centred within distance `ℓ - R` of `i`.
The conclusions include its support, Hermiticity and norm, its difference from
the full filter, and its action on ground vectors.

No polynomial growth assumption is needed. The graph joining sites at distance
at most `R` has degree at most `S`; a sufficiently strong Lieb–Robinson weight
makes its weighted tails summable even when its balls grow exponentially.
The time window is `c₁ ℓ` and the Gaussian parameter is `q = c₁ ℓ Δ`.
Constants are chosen before the finite site set and Hamiltonian. The assumption
`R ≤ ℓ` expresses the large-radius range of the exponential estimate and ensures
that the initial term is supported in the truncation ball. The zero-range case
is treated separately in `GaussianZeroRange`.

**Local fix (factorization length):** after eq. `facld`, the source prints the minimum
of two decay lengths; adding the decays requires the maximum of their lengths,
equivalently the minimum of their rates. The explicit rate below uses the latter rule.
See `docs/paper-gaps/hastings05_truncated_dynamics.tex`.

## References

Hastings, *Solving Gapped Hamiltonians Locally*, arXiv:cond-mat/0508554v3,
lines 169–190, 285–349, 343–374 and 1469–1533. The distinction between the earlier
polynomial-shell argument and this metric-space result is documented in
`docs/paper-gaps/hastings05_geometric_growth_scope.tex`.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.Lattice

private theorem exp_neg_mul_ceil_metric_le {R β : ℝ} (hR : 0 < R) (hβ : 0 ≤ β) (ℓ : ℝ) :
    Real.exp (-(β * (Nat.ceil ((ℓ - R) / R) : ℝ))) ≤
      Real.exp β * Real.exp (-((β / R) * ℓ)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (Nat.le_ceil ((ℓ - R) / R)) hβ
  have he : β + -((β / R) * ℓ) = -(β * ((ℓ - R) / R)) := by field_simp; ring
  rw [he]
  exact neg_le_neg hh

/-- Uniform source constants control the sum of spectral leakage and actual physical-ball
truncation error. Hastings, arXiv:cond-mat/0508554v3, lines 169–190, 285–349 and 1469–1533. -/
theorem exists_metric_truncated_filter_budget {R J Δ : ℝ} (hR : 0 < R)
    (S : ℕ) (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ c₁ η C : ℝ, 0 < c₁ ∧ 0 < η ∧ 0 ≤ C ∧
      ∀ {ι : Type*} [PseudoMetricSpace ι] [Fintype ι] [DecidableEq ι] {d : ℕ},
        ∀ (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
          (_hHerm : ∀ i, (h i).IsHermitian)
          (_hSupport : ∀ i, h i ∈ supportedOperators d (Metric.closedBall i R))
          (_hNorm : ∀ i, ‖h i‖ ≤ J)
          (_hCard : ∀ i : ι, (metricRangeBall R i).card ≤ S)
          (ℓ : ℝ), R ≤ ℓ → ∀ i : ι,
          let q := c₁ * ℓ * Δ
          ‖h i‖ * Real.exp (-q / 2) +
            ‖gaussianFilteredTerm q Δ (∑ j, h j) (h i) -
              gaussianFilteredTerm q Δ (∑ j ∈ metricRangeBall (ℓ - R) i, h j) (h i)‖ ≤
            ‖h i‖ * C * Real.exp (-(η * ℓ)) := by
  let μ : ℝ := Real.log ((S : ℝ) + 1) + 1
  let v : ℝ := 4 * (S : ℝ) * |(S : ℝ) * J| * Real.exp (2 * μ * 2)
  have hv : 0 ≤ v := by dsimp [v]; positivity
  let c₁ : ℝ := (1 / 2) / (2 * R * (v + 1))
  have hc₁ : 0 < c₁ := div_pos (by norm_num) (by positivity)
  have hc : 2 * R * (v + 1) * c₁ = (1 / 2 : ℝ) := by
    dsimp [c₁]
    field_simp
  let γ : ℝ := (1 / 2) / R - v * c₁
  have hγ : 0 < γ := by
    have hr : 0 < R * c₁ := mul_pos hR hc₁
    have hvc : v * c₁ * R < (1 / 2 : ℝ) := by nlinarith only [hc, hr]
    have := (lt_div_iff₀ hR).mpr hvc
    dsimp [γ]
    linarith only [this]
  let δ : ℝ := min (c₁ * Δ) γ
  have hδ : 0 < δ := lt_min (mul_pos hc₁ hΔ) hγ
  have hden : 0 < 1 - Real.exp (-(1 / 2 : ℝ)) := by
    have := Real.exp_lt_one_iff.mpr (by norm_num : -(1 / 2 : ℝ) < 0)
    linarith
  let A : ℝ := 4 * ((S : ℝ) + 1) * Real.exp (μ * (2 * 2 + 1)) * J * c₁ *
    Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let C : ℝ := 3 + A / (Real.exp 1 * (δ / 2))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨c₁, δ / 2, C, hc₁, half_pos hδ, hC, ?_⟩
  intro ι _ _ _ d h hHerm hSupport hNorm hCard ℓ hℓ i q
  have hℓ0 : 0 ≤ ℓ := hR.le.trans hℓ
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hS : 1 ≤ S := (Finset.one_le_card.mpr ⟨i, self_mem_metricRangeBall hR.le i⟩).trans
    (hCard i)
  have hSupp (j : ι) : h j ∈ supportedOperators d (metricRangeBall R j : Set ι) := by
    rw [coe_metricRangeBall]
    exact hSupport j
  have hDegree (x : ι) : (metricRangeGraph R).degree x ≤ S := by
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
      metricRangeGraph_neighbor_card_le hCard x
  have hrad (x : ι) (hx : x ∈ metricRangeBall R i) :
      (metricRangeGraph R).edist i x ≤ (2 : ℕ∞) :=
    (metricRangeGraph_edist_le_one (mem_metricRangeBall.mp hx)).trans (by norm_num)
  have hAnchor (x : ι) :
      ∑ j ∈ Finset.univ.filter (fun j : ι ↦ id j = x), ‖h j‖ ≤ J := by
    rw [show Finset.univ.filter (fun j : ι ↦ id j = x) = {x} by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, id_eq, Finset.mem_singleton]]
    simpa only [Finset.sum_singleton] using hNorm x
  have hμ : Real.log ((S : ℝ) + 1) < μ := by dsimp [μ]; linarith
  have hβ : (μ - Real.log ((S : ℝ) + 1)) / 2 = (1 / 2 : ℝ) := by dsimp [μ]; ring
  have hf := norm_gaussianFilteredTerm_sub_truncated_le_degree_tail
    (ΔE := Δ) (q := q) (T := c₁ * ℓ)
    (metricRangeGraph R) S hDegree (metricRangeBall R) id
    (self_mem_metricRangeBall hR.le) h hHerm hSupp 2
    (metricRangeBall_graph_diameter_le_two R) S hS hCard ((S : ℝ) * J)
    (metricRangeBall_norm_budget_le hCard hJ h hNorm) J hJ hAnchor
    (metricRangeBall (ℓ - R) i) i (metricRangeBall R i) hrad (hSupp i)
    (Nat.ceil ((ℓ - R) / R))
    (fun j hj ↦ metricRangeGraph_omitted_threshold hR hj) hq hμ (mul_nonneg hc₁.le hℓ0)
  simp only [hβ] at hf
  have htime : q / Δ = c₁ * ℓ := by dsimp [q]; field_simp
  have hgauss := exp_neg_sq_div_eq_of_time_eq (q := q) hΔ.ne'
  rw [htime] at hgauss
  rw [hgauss] at hf
  have htail := exp_neg_mul_ceil_metric_le hR (by norm_num : (0 : ℝ) ≤ 1 / 2) ℓ
  have hexp : Real.exp (v * (c₁ * ℓ)) * Real.exp (-(((1 / 2 : ℝ) / R) * ℓ)) =
      Real.exp (-(γ * ℓ)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [γ]
    ring
  have hspatial :
      4 * (((metricRangeBall R i).card : ℝ) + 1) * Real.exp (μ * (2 * 2 + 1)) *
        ‖h i‖ * (c₁ * ℓ) * Real.exp (v * (c₁ * ℓ)) *
        (J * Real.exp (-((1 / 2 : ℝ) * (Nat.ceil ((ℓ - R) / R) : ℝ))) /
          (1 - Real.exp (-(1 / 2 : ℝ)))) ≤
      A * ‖h i‖ * ℓ * Real.exp (-(γ * ℓ)) := by
    calc
      _ ≤ 4 * ((S : ℝ) + 1) * Real.exp (μ * (2 * 2 + 1)) * ‖h i‖ * (c₁ * ℓ) *
          Real.exp (v * (c₁ * ℓ)) *
          (J * (Real.exp (1 / 2) * Real.exp (-(((1 / 2 : ℝ) / R) * ℓ))) /
            (1 - Real.exp (-(1 / 2 : ℝ)))) := by
        gcongr
        · exact_mod_cast hCard i
      _ = A * ‖h i‖ * ℓ *
          (Real.exp (v * (c₁ * ℓ)) * Real.exp (-(((1 / 2 : ℝ) / R) * ℓ))) := by
        dsimp [A]
        ring
      _ = _ := by rw [hexp]
  have herr :
      ‖gaussianFilteredTerm q Δ (∑ j, h j) (h i) -
        gaussianFilteredTerm q Δ (∑ j ∈ metricRangeBall (ℓ - R) i, h j) (h i)‖ ≤
      A * ‖h i‖ * ℓ * Real.exp (-(γ * ℓ)) + 2 * ‖h i‖ * Real.exp (-q / 2) :=
    hf.trans (add_le_add hspatial le_rfl)
  have hscalar := gaussian_truncation_bound_le_exp (mul_pos hc₁ hΔ) hγ hA (norm_nonneg (h i)) hℓ0
  calc _ ≤ ‖h i‖ * Real.exp (-q / 2) +
        (A * ‖h i‖ * ℓ * Real.exp (-(γ * ℓ)) + 2 * ‖h i‖ * Real.exp (-q / 2)) :=
      add_le_add le_rfl herr
    _ = 3 * ‖h i‖ * Real.exp (-((c₁ * Δ) * ℓ) / 2) +
        A * ‖h i‖ * ℓ * Real.exp (-(γ * ℓ)) := by
      rw [show -q / 2 = -((c₁ * Δ) * ℓ) / 2 by dsimp [q]; ring]
      ring
    _ ≤ ‖h i‖ * C * Real.exp (-(δ / 2 * ℓ)) := by
      simpa only [C, δ, neg_mul] using hscalar


/-- The actual physical-ball truncated filter has the support, Hermiticity and norm
asserted in Hastings, arXiv:cond-mat/0508554v3, lines 322–349 and 1469–1505. -/
theorem metric_truncated_filter_properties {ι : Type*} [PseudoMetricSpace ι]
    [Fintype ι] [DecidableEq ι] {d : ℕ} {R ℓ J : ℝ} (hℓ : R ≤ ℓ)
    (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hHerm : ∀ i, (h i).IsHermitian)
    (hSupport : ∀ i, h i ∈ supportedOperators d (Metric.closedBall i R))
    (hNorm : ∀ i, ‖h i‖ ≤ J) (q Δ : ℝ) (i : ι) :
    let M := gaussianFilteredTerm q Δ (∑ j ∈ metricRangeBall (ℓ - R) i, h j) (h i)
    M ∈ supportedOperators d (Metric.closedBall i ℓ) ∧ M.IsHermitian ∧ ‖M‖ ≤ J := by
  intro M
  have hsupp (j : ι) : h j ∈ supportedOperators d (metricRangeBall R j : Set ι) := by
    simpa only [coe_metricRangeBall] using hSupport j
  have hHs : (∑ j ∈ metricRangeBall (ℓ - R) i, h j).IsHermitian :=
    Matrix.isHermitian_sum _ fun j _ ↦ hHerm j
  have hHsSupp : (∑ j ∈ metricRangeBall (ℓ - R) i, h j) ∈
      supportedOperators d (metricRangeBall ℓ i : Set ι) :=
    Submodule.sum_mem _ fun j hj ↦ supportedOperators_mono
      (Finset.coe_subset.mpr (metricRangeBall_retained_support hj)) (hsupp j)
  have hWi := supportedOperators_mono
    (Finset.coe_subset.mpr (metricRangeBall_initial_support hℓ i)) (hsupp i)
  refine ⟨?_, isHermitian_gaussianFilteredTerm q Δ hHs (hHerm i),
    (norm_gaussianFilteredTerm_le q Δ hHs (h i)).trans (hNorm i)⟩
  simpa only [coe_metricRangeBall] using
    gaussianFilteredTerm_mem_supportedOperators q Δ hHsSupp hWi


/-- Source-faithful exponential localization for the actual physical-ball truncated
operators. Constants depend only on the range, local cardinality bound, interaction norm
bound and gap, and are uniform in the finite metric space and Hamiltonian. Hastings,
arXiv:cond-mat/0508554v3, eqs. `mid` and `facld`, lines 285–349. -/
theorem exists_metric_truncated_filter_localization {R J Δ : ℝ} (hR : 0 < R)
    (S : ℕ) (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ c₁ η C : ℝ, 0 < c₁ ∧ 0 < η ∧ 0 ≤ C ∧
      ∀ {ι : Type*} [PseudoMetricSpace ι] [Fintype ι] [DecidableEq ι] {d : ℕ},
        ∀ (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
          (_hHerm : ∀ i, (h i).IsHermitian)
          (_hSupport : ∀ i, h i ∈ supportedOperators d (Metric.closedBall i R))
          (_hNorm : ∀ i, ‖h i‖ ≤ J)
          (_hCard : ∀ i : ι, (metricRangeBall R i).card ≤ S)
          (ℓ : ℝ), R ≤ ℓ → ∀ i : ι,
          let q := c₁ * ℓ * Δ
          let M := gaussianFilteredTerm q Δ (∑ j ∈ metricRangeBall (ℓ - R) i, h j) (h i)
          M ∈ supportedOperators d (Metric.closedBall i ℓ) ∧ M.IsHermitian ∧ ‖M‖ ≤ J ∧
            ‖gaussianFilteredTerm q Δ (∑ j, h j) (h i) - M‖ ≤ J * C * Real.exp (-(η * ℓ)) ∧
            (∀ (hH : (∑ j, h j).IsHermitian) {E₀ : ℝ}
              (_hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + Δ ≤ hH.eigenvalues k)
              {ψ : EuclideanSpace ℂ (ι → Fin d)}, ψ ∈ groundEigenspace (∑ j, h j) E₀ →
              ‖toEuclideanLin M ψ - (groundEigenspace (∑ j, h j) E₀).starProjection
                (toEuclideanLin M ψ)‖ ≤ J * C * Real.exp (-(η * ℓ)) * ‖ψ‖) ∧
            (∀ {E₀ : ℝ} {Ω : EuclideanSpace ℂ (ι → Fin d)},
              Matrix.IsGappedGroundState (∑ j, h j) E₀ Ω Δ →
              ‖toEuclideanLin M Ω - ⟪Ω, toEuclideanLin M Ω⟫_ℂ • Ω‖ ≤
                J * C * Real.exp (-(η * ℓ))) := by
  obtain ⟨c₁, η, C, hc₁, hη, hC, hb⟩ := exists_metric_truncated_filter_budget hR S hJ hΔ
  refine ⟨c₁, η, C, hc₁, hη, hC, ?_⟩
  intro ι _ _ _ d h hHerm hSupport hNorm hCard ℓ hℓ i q M
  have hq : 0 ≤ q := mul_nonneg (mul_nonneg hc₁.le (hR.le.trans hℓ)) hΔ.le
  have hbudget := hb h hHerm hSupport hNorm hCard ℓ hℓ i
  have hbound : ‖h i‖ * C * Real.exp (-(η * ℓ)) ≤ J * C * Real.exp (-(η * ℓ)) := by
    gcongr
    exact hNorm i
  have htotal : ‖h i‖ * Real.exp (-q / 2) +
      ‖gaussianFilteredTerm q Δ (∑ j, h j) (h i) - M‖ ≤ J * C * Real.exp (-(η * ℓ)) :=
    hbudget.trans hbound
  obtain ⟨hMsupp, hMHerm, hMnorm⟩ :=
    metric_truncated_filter_properties hℓ h hHerm hSupport hNorm q Δ i
  refine ⟨hMsupp, hMHerm, hMnorm, ?_, ?_, ?_⟩
  · exact (le_add_of_nonneg_left (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)).trans htotal
  · intro hH E₀ hgap ψ hψ
    exact (norm_sub_starProjection_apply_le_of_gaussianFilteredTerm hq hΔ hH hgap (h i) M hψ).trans
      (mul_le_mul_of_nonneg_right htotal (norm_nonneg ψ))
  · intro E₀ Ω hgs
    exact (norm_apply_sub_inner_smul_le_of_gaussianFilteredTerm hq hΔ hgs (h i) M).trans htotal


/-- The sum of the actual physical-ball truncated operators approximates the Hamiltonian
with the number of sites times the uniform exponential error. Hastings,
arXiv:cond-mat/0508554v3, lines 343–374. -/
theorem exists_metric_truncated_filter_sum_bound {R J Δ : ℝ} (hR : 0 < R)
    (S : ℕ) (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ c₁ η C : ℝ, 0 < c₁ ∧ 0 < η ∧ 0 ≤ C ∧
      ∀ {ι : Type*} [PseudoMetricSpace ι] [Fintype ι] [DecidableEq ι] {d : ℕ},
        ∀ (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
          (_hHerm : ∀ i, (h i).IsHermitian)
          (_hSupport : ∀ i, h i ∈ supportedOperators d (Metric.closedBall i R))
          (_hNorm : ∀ i, ‖h i‖ ≤ J)
          (_hCard : ∀ i : ι, (metricRangeBall R i).card ≤ S)
          (ℓ : ℝ), R ≤ ℓ →
          ‖∑ i, gaussianFilteredTerm (c₁ * ℓ * Δ) Δ
              (∑ j ∈ metricRangeBall (ℓ - R) i, h j) (h i) - ∑ j, h j‖ ≤
            Fintype.card ι * (J * C * Real.exp (-(η * ℓ))) := by
  obtain ⟨c₁, η, C, hc₁, hη, hC, hb⟩ := exists_metric_truncated_filter_localization hR S hJ hΔ
  refine ⟨c₁, η, C, hc₁, hη, hC, ?_⟩
  intro ι _ _ _ d h hHerm hSupport hNorm hCard ℓ hℓ
  have hH : (∑ j, h j).IsHermitian := Matrix.isHermitian_sum _ fun j _ ↦ hHerm j
  refine (norm_sum_sub_le_of_sum_eq Finset.univ (c₁ * ℓ * Δ) Δ hH (W := h)
    (by simp)).trans ?_
  calc
    _ ≤ ∑ _i : ι, J * C * Real.exp (-(η * ℓ)) :=
      Finset.sum_le_sum fun i _ ↦ (hb h hHerm hSupport hNorm hCard ℓ hℓ i).2.2.2.1
    _ = _ := by simp

end TNLean.Lattice
