/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.PeriodicPhysicalMetric
import TNLean.MPS.AreaLaw.LocalSolution.RoundedPeriodicApproximation
import TNLean.Lattice.GaussianFilteredMetricTruncation
import TNLean.Lattice.GaussianZeroRange

/-!
# The physical periodic hierarchy at quadratic logarithmic range

The original local Hamiltonian determines the actual truncated Gaussian terms,
their pair operators, and every spectral window. The cyclic metric and its local
ball count give localization constants uniform in chain length. Their full-filter
errors are derived; they are not hypotheses of the final physical theorem.

With `Jb=max(J,J*C)`, choose the physical radius as the maximum of `ceil(R)` and
the explicit integer quadratic logarithmic radius with effective coupling `8Jb/η`.
The source's local residual condition (low) then constructs a nearby unit vector
retained at every node, and the original physical gap bounds every orthonormal
family retained by the final projection. No separate pair-norm, length, total-error
or approximating-gap assumption is made. The zero-range case uses exact commuting
filters; the positive-range case uses the proved metric localization estimate.

**Local fix (periodic hierarchy):** the norm deficiency uses the corrected recurrence
and the closing edge has one further spectral window. See
`docs/paper-gaps/hastings05_hierarchical_projection.tex` and
`docs/paper-gaps/hastings05_hierarchical_energy.tex`.

Source: Hastings, arXiv:cond-mat/0508554v3, lines 169–190, 285–374 and 609–743.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

/-- The chosen physical radius also contains the original interaction range.
Hastings, arXiv:cond-mat/0508554v3, lines 169–190 and 609–743. -/
noncomputable def physicalPeriodicProjectionRadius (R : ℝ) (M : ℕ) (J η Δ : ℝ) : ℕ :=
  max (Nat.ceil R) (roundedPeriodicProjectionRadius M J η Δ)

/-- The physical radius is positive and is at least the interaction range.
Hastings, arXiv:cond-mat/0508554v3, lines 169–190 and 609–743. -/
theorem physicalPeriodicProjectionRadius_spec (R : ℝ) (M : ℕ) (J Δ : ℝ) {η : ℝ}
    (hη : 0 < η) :
    0 < physicalPeriodicProjectionRadius R M J η Δ ∧
      R ≤ (physicalPeriodicProjectionRadius R M J η Δ : ℝ) := by
  constructor
  · exact (roundedPeriodicProjectionRadius_pos M J Δ hη).trans_le (le_max_right _ _)
  · exact (Nat.le_ceil R).trans (by exact_mod_cast (le_max_left (Nat.ceil R)
      (roundedPeriodicProjectionRadius M J η Δ)))

/-- The enlarged physical radius satisfies the length inequality for its own block count.
Hastings, arXiv:cond-mat/0508554v3, lines 169–190 and 609–743. -/
theorem hierarchyProjectionLength_le_physicalPeriodicProjectionRadius {M : ℕ} (hM : 0 < M)
    (R J Δ : ℝ) {η : ℝ} (hη : 0 < η) :
    let ℓ := physicalPeriodicProjectionRadius R M J η Δ
    hierarchyProjectionLength (finiteHierarchyDepth (roundedPeriodicBlockCount M ℓ))
      (8 * J / η) Δ ≤ η * (ℓ : ℝ) := by
  let ℓ := physicalPeriodicProjectionRadius R M J η Δ
  have hbase := hierarchyProjectionLength_roundedPeriodic_le hM ℓ J η Δ
  have hceil := Nat.le_ceil
    (hierarchyProjectionLength (Nat.clog 2 M + 2) (8 * J / η) Δ / η)
  have hscale : hierarchyProjectionLength (Nat.clog 2 M + 2) (8 * J / η) Δ ≤
      η * (roundedPeriodicProjectionRadius M J η Δ : ℝ) := by
    simpa only [roundedPeriodicProjectionRadius, mul_comm] using (div_le_iff₀ hη).mp hceil
  have hscale' : hierarchyProjectionLength (Nat.clog 2 M + 2) (8 * J / η) Δ ≤ η * (ℓ : ℝ) :=
    hscale.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast (le_max_right
      (Nat.ceil R) (roundedPeriodicProjectionRadius M J η Δ))) hη.le)
  exact hbase.trans (by
    simpa only [hierarchyProjectionLength, Nat.cast_add, Nat.cast_ofNat] using hscale')

/-- The physical radius differs from an explicit quadratic logarithm by at most the
rounded interaction range and one.
Hastings, arXiv:cond-mat/0508554v3, lines 169–190 and 609–743. -/
theorem physicalPeriodicProjectionRadius_lt (R : ℝ) (M : ℕ) (J Δ : ℝ) {η : ℝ}
    (hη : 0 < η) :
    (physicalPeriodicProjectionRadius R M J η Δ : ℝ) < (Nat.ceil R : ℝ) +
      512 * ((Nat.clog 2 M : ℝ) + 2) ^ 2 *
        (1 + max 0 (Real.log ((8 * J / η) / Δ))) / η + 1 := by
  have hmax : physicalPeriodicProjectionRadius R M J η Δ ≤
      Nat.ceil R + roundedPeriodicProjectionRadius M J η Δ := by
    unfold physicalPeriodicProjectionRadius
    omega
  have hcast : (physicalPeriodicProjectionRadius R M J η Δ : ℝ) ≤
      (Nat.ceil R : ℝ) + (roundedPeriodicProjectionRadius M J η Δ : ℝ) := by
    exact_mod_cast hmax
  linarith [roundedPeriodicProjectionRadius_lt M J Δ hη]

/-- The actual physical-ball truncated Gaussian term on the original periodic chain.
Hastings, arXiv:cond-mat/0508554v3, eq. `mid`, lines 285–303. -/
noncomputable def periodicPhysicalTruncatedTerm {M d : ℕ} (c₁ R Δ : ℝ) (ℓ : ℕ)
    (g : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ) (i : Fin M) :
    Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ :=
  TNLean.Lattice.gaussianFilteredTerm (c₁ * (ℓ : ℝ) * Δ) Δ
    (∑ j with (roundedPeriodicDistance i j : ℝ) ≤ (ℓ : ℝ) - R, g j) (g i)

/-- Uniform physical localization constants for the actual periodic truncated terms.
Hastings, arXiv:cond-mat/0508554v3, eqs. `mid`, `apb`, `facld`, lines 285–349. -/
theorem exists_periodicPhysicalTruncatedTerm_localization {R J Δ : ℝ}
    (hR : 0 ≤ R) (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ c₁ η C : ℝ, 0 < c₁ ∧ 0 < η ∧ 0 ≤ C ∧
      ∀ {M d : ℕ}, 0 < M →
        ∀ (g : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ),
          (∀ i, (g i).IsHermitian) →
          (∀ i, g i ∈ supportedOperators d {v | (roundedPeriodicDistance i v : ℝ) ≤ R}) →
          (∀ i, ‖g i‖ ≤ J) → ∀ (ℓ : ℕ), R ≤ (ℓ : ℝ) → ∀ i,
          let a := periodicPhysicalTruncatedTerm c₁ R Δ ℓ g i
          a ∈ supportedOperators d {v | roundedPeriodicDistance i v ≤ ℓ} ∧
            a.IsHermitian ∧ ‖a‖ ≤ J ∧
            ‖TNLean.Lattice.gaussianFilteredTerm (c₁ * (ℓ : ℝ) * Δ) Δ (∑ j, g j) (g i) - a‖ ≤
              J * C * Real.exp (-(η * (ℓ : ℝ))) := by
  by_cases hRzero : R = 0
  · subst R
    refine ⟨1, 1, 0, by norm_num, by norm_num, by norm_num, ?_⟩
    intro M d hM g hg hsupp hnorm ℓ hℓ i a
    let _ : NeZero M := ⟨by omega⟩
    let _ := periodicPhysicalMetricSpace M
    have hsupp' : ∀ j, g j ∈ supportedOperators d (Metric.closedBall j 0) := by
      intro j
      apply supportedOperators_mono _ (hsupp j)
      intro v hv
      change (roundedPeriodicDistance j v : ℝ) ≤ 0 at hv
      change dist v j ≤ 0
      change (roundedPeriodicDistance v j : ℝ) ≤ 0
      simpa only [roundedPeriodicDistance, Nat.dist_comm] using hv
    have hfilters := TNLean.Lattice.gaussianFilteredTerm_full_and_sum_eq_of_zero_range
      g hsupp' (TNLean.Lattice.metricRangeBall (ℓ : ℝ) i) ((ℓ : ℝ) * Δ) Δ i
    have ha : a = g i := by
      have heq : a = TNLean.Lattice.gaussianFilteredTerm (1 * (ℓ : ℝ) * Δ) Δ
          (∑ j ∈ TNLean.Lattice.metricRangeBall ((ℓ : ℝ) - 0) i, g j) (g i) := rfl
      rw [heq, one_mul, sub_zero]
      exact hfilters.2
    rw [ha]
    refine ⟨supportedOperators_mono (fun v hv ↦ ?_) (hsupp i), hg i, hnorm i, ?_⟩
    · change (roundedPeriodicDistance i v : ℝ) ≤ 0 at hv
      change roundedPeriodicDistance i v ≤ ℓ
      have hd : roundedPeriodicDistance i v = 0 := by
        exact_mod_cast (le_antisymm hv (by positivity))
      rw [hd]
      omega
    · rw [one_mul, hfilters.1, sub_self, norm_zero, mul_zero, zero_mul]
  · have hRp : 0 < R := lt_of_le_of_ne hR (Ne.symm hRzero)
    obtain ⟨c₁, η, C, hc₁, hη, hC, hloc⟩ :=
      TNLean.Lattice.exists_metric_truncated_filter_localization hRp (2 * Nat.ceil R + 1) hJ hΔ
    refine ⟨c₁, η, C, hc₁, hη, hC, ?_⟩
    intro M d hM g hg hsupp hnorm ℓ hℓ i a
    let _ : NeZero M := ⟨by omega⟩
    let _ := periodicPhysicalMetricSpace M
    have hsupp' : ∀ j, g j ∈ supportedOperators d (Metric.closedBall j R) := by
      intro j
      apply supportedOperators_mono _ (hsupp j)
      intro v hv
      change (roundedPeriodicDistance j v : ℝ) ≤ R at hv
      change dist v j ≤ R
      change (roundedPeriodicDistance v j : ℝ) ≤ R
      simpa only [roundedPeriodicDistance, Nat.dist_comm] using hv
    have ha := hloc g hg hsupp' hnorm (card_periodicPhysical_metricRangeBall_le R) (ℓ : ℝ) hℓ i
    have heq : TNLean.Lattice.gaussianFilteredTerm (c₁ * (ℓ : ℝ) * Δ) Δ
        (∑ j ∈ TNLean.Lattice.metricRangeBall ((ℓ : ℝ) - R) i, g j) (g i) = a := by
      rfl
    dsimp only at ha
    rw [heq] at ha
    refine ⟨supportedOperators_mono (fun v hv ↦ ?_) ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1⟩
    · change (roundedPeriodicDistance v i : ℝ) ≤ (ℓ : ℝ) at hv
      change roundedPeriodicDistance i v ≤ ℓ
      have hd : (roundedPeriodicDistance v i : ℝ) ≤ (ℓ : ℝ) := hv
      have hsym : roundedPeriodicDistance v i = roundedPeriodicDistance i v := by
        simp only [roundedPeriodicDistance, Nat.dist_comm]
      rw [hsym] at hd
      exact_mod_cast hd

/-- Physical local interactions determine a corrected periodic hierarchy at explicit
quadratic logarithmic radius. The only ground-vector estimate assumed is source (low).
Hastings, arXiv:cond-mat/0508554v3, lines 169–190 and 609–743. -/
theorem exists_periodicPhysicalHierarchy {R J Δ : ℝ} (hR : 0 ≤ R) (hJ : 0 < J) (hΔ : 0 < Δ) :
    ∃ c₁ η C : ℝ, 0 < c₁ ∧ 0 < η ∧ 0 ≤ C ∧
      ∀ {M d : ℕ}, 0 < M →
        ∀ (g : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ),
          (∀ i, (g i).IsHermitian) →
          (∀ i, g i ∈ supportedOperators d {v | (roundedPeriodicDistance i v : ℝ) ≤ R}) →
          (∀ i, ‖g i‖ ≤ J) →
          ∀ (ψ : EuclideanSpace ℂ (Fin M → Fin d)), ‖ψ‖ = 1 →
          ∀ (P₀ : Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ), IsStarProjection P₀ →
          ∀ E₀ : ℝ,
          (∀ v : EuclideanSpace ℂ (Fin M → Fin d),
            Δ * (‖v‖ ^ 2 - (⟪v, toEuclideanLin P₀ v⟫_ℂ).re) ≤
              (⟪v, toEuclideanLin (∑ i, g i) v⟫_ℂ).re - E₀ * ‖v‖ ^ 2) →
          (⟪ψ, toEuclideanLin (∑ i, g i) ψ⟫_ℂ).re = E₀ →
          let Jb := max J (J * C)
          let ℓ := physicalPeriodicProjectionRadius R M Jb η Δ
          let r := η * (ℓ : ℝ)
          let a := periodicPhysicalTruncatedTerm c₁ R Δ ℓ g
          let P := roundedPeriodicProjection ℓ a ψ Jb r
          let b := roundedPeriodicOperator ℓ a
          let h := finiteHierarchyDepth (roundedPeriodicBlockCount M ℓ)
          let K := 8 * (ℓ : ℝ) * Jb
          (∀ i, ‖toEuclideanLin
            (a i - ((⟪ψ, toEuclideanLin (a i) ψ⟫_ℂ).re : ℂ) • 1) ψ‖ ≤
            Jb * Real.exp (-r)) →
          ∃ φ : EuclideanSpace ℂ (Fin M → Fin d), ‖φ‖ = 1 ∧
            toEuclideanLin P φ = φ ∧
            ‖φ - ψ‖ ≤ 2 * (((3 : ℝ) ^ (h + 1) - 1) * Real.exp (-r / 8)) ∧
            IsRetainedHierarchy
              (hierarchyProjection (hierarchyEdge (extendFiniteEdges b))
                (fun m k ↦
                  (⟪ψ, toEuclideanLin (hierarchyEdge (extendFiniteEdges b) m k) ψ⟫_ℂ).re)
                (hierarchyWindowRadius K r h)) h 0 φ ∧
            ∀ {n : ℕ} (Φ : Fin n → EuclideanSpace ℂ (Fin M → Fin d)), Orthonormal ℂ Φ →
              (∀ j, toEuclideanLin P (Φ j) = Φ j) → (n : ℝ) ≤ 2 * (trace P₀).re := by
  obtain ⟨c₁, η, C, hc₁, hη, hC, hloc⟩ :=
    exists_periodicPhysicalTruncatedTerm_localization hR hJ.le hΔ
  refine ⟨c₁, η, C, hc₁, hη, hC, ?_⟩
  intro M d hM g hg hsupp hnorm ψ hψ P₀ hP₀ E₀ hgap hE₀ Jb ℓ r a P b h K hlow
  have hJb : 0 < Jb := hJ.trans_le (le_max_left _ _)
  obtain ⟨hℓ, hℓR⟩ := physicalPeriodicProjectionRadius_spec R M Jb Δ hη
  have hr := hierarchyProjectionLength_le_physicalPeriodicProjectionRadius hM R Jb Δ hη
  have haloc (i : Fin M) := hloc hM g hg hsupp hnorm ℓ hℓR i
  have haSupp (i : Fin M) : a i ∈ supportedOperators d {v | roundedPeriodicDistance i v ≤ ℓ} :=
    (haloc i).1
  have haHerm (i : Fin M) : (a i).IsHermitian := (haloc i).2.1
  have haNorm (i : Fin M) : ‖a i‖ ≤ Jb := ((haloc i).2.2.1).trans (le_max_left _ _)
  have haError (i : Fin M) :
      ‖TNLean.Lattice.gaussianFilteredTerm (c₁ * (ℓ : ℝ) * Δ) Δ (∑ j, g j) (g i) - a i‖ ≤
        Jb * Real.exp (-r) := by
    exact ((haloc i).2.2.2).trans
      (mul_le_mul_of_nonneg_right (le_max_right J (J * C)) (Real.exp_pos _).le)
  obtain ⟨φ, hφ, hkeep, hnear, htree⟩ := exists_unit_mem_roundedPeriodicProjection hℓ a
    haSupp haHerm hψ hJb hr hlow haNorm
  refine ⟨φ, hφ, hkeep, hnear, htree, ?_⟩
  intro n Φ hΦ hfix
  have hc := card_le_two_mul_re_trace_of_roundedPeriodicProjection hℓ a g haSupp haHerm hg hψ
    hJb hη hΔ rfl hr haError hP₀ hgap hE₀ hΦ Finset.univ (fun j _ ↦ hfix j)
  simpa using hc

end TNLean.MPS.AreaLaw.LocalSolution
