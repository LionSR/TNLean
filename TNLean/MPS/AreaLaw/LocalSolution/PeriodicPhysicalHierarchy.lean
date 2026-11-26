/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.RoundedPeriodicApproximation
import QICLean.ManyBody.Hamiltonian.GaussianFilterMetric
import QICLean.ManyBody.Hamiltonian.GaussianFilterLocality
import QICLean.ManyBody.Hamiltonian.GroundSpace

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

It also contains the following results.

* `TNLean.MPS.AreaLaw.LocalSolution.exists_periodicPhysicalHierarchy_of_isGapped`: the periodic
  hierarchy from a unique gapped ground state.
-/

section PeriodicPhysicalHierarchy

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
    hierarchyProjectionLength (finiteHierarchyDepth (ManyBody.roundedPeriodicBlockCount M ℓ))
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
  ManyBody.gaussianFilteredTerm (c₁ * (ℓ : ℝ) * Δ) Δ
    (∑ j with (ManyBody.roundedPeriodicDistance i j : ℝ) ≤ (ℓ : ℝ) - R, g j) (g i)

/-- Uniform physical localization constants for the actual periodic truncated terms.
Hastings, arXiv:cond-mat/0508554v3, eqs. `mid`, `apb`, `facld`, lines 285–349. -/
theorem exists_periodicPhysicalTruncatedTerm_localization {R J Δ : ℝ}
    (hR : 0 ≤ R) (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ c₁ η C : ℝ, 0 < c₁ ∧ 0 < η ∧ 0 ≤ C ∧
      ∀ {M d : ℕ}, 0 < M →
        ∀ (g : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ),
          (∀ i, (g i).IsHermitian) →
          (∀ i, g i ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
              (Finset.univ.filter fun v ↦ (ManyBody.roundedPeriodicDistance i v : ℝ) ≤ R)) →
          (∀ i, ‖g i‖ ≤ J) → ∀ (ℓ : ℕ), R ≤ (ℓ : ℝ) → ∀ i,
          let a := periodicPhysicalTruncatedTerm c₁ R Δ ℓ g i
          a ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
              (Finset.univ.filter fun v ↦ ManyBody.roundedPeriodicDistance i v ≤ ℓ) ∧
            a.IsHermitian ∧ ‖a‖ ≤ J ∧
            ‖ManyBody.gaussianFilteredTerm (c₁ * (ℓ : ℝ) * Δ) Δ (∑ j, g j) (g i) - a‖ ≤
              J * C * Real.exp (-(η * (ℓ : ℝ))) := by
  by_cases hRzero : R = 0
  · subst R
    refine ⟨1, 1, 0, by norm_num, by norm_num, by norm_num, ?_⟩
    intro M d hM g hg hsupp hnorm ℓ hℓ i a
    let _ : NeZero M := ⟨by omega⟩
    let _ := ManyBody.cyclicMetricSpace M
    have hsupp' : ∀ j,
        g j ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (ManyBody.metricRangeBall 0 j) := by
      intro j
      apply ManyBody.supportedOperators_mono _ (hsupp j)
      intro v hv
      rw [ManyBody.mem_metricRangeBall]
      exact (Finset.mem_filter.mp hv).2
    have hfilters := ManyBody.gaussianFilteredTerm_full_and_sum_eq_of_zero_range
      (⟨g, hsupp'⟩ : ManyBody.Interaction (fun _ ↦ Fin d) (ManyBody.metricRangeBall 0))
      (ManyBody.metricRangeBall (ℓ : ℝ) i) ((ℓ : ℝ) * Δ) Δ i
    have ha : a = g i := by
      have heq : a = ManyBody.gaussianFilteredTerm (1 * (ℓ : ℝ) * Δ) Δ
          (∑ j ∈ ManyBody.metricRangeBall ((ℓ : ℝ) - 0) i, g j) (g i) := rfl
      rw [heq, one_mul, sub_zero]
      exact hfilters.2
    rw [ha]
    refine ⟨ManyBody.supportedOperators_mono (fun v hv ↦ ?_) (hsupp i), hg i, hnorm i, ?_⟩
    · have hv : (ManyBody.roundedPeriodicDistance i v : ℝ) ≤ 0 := (Finset.mem_filter.mp hv).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hd : ManyBody.roundedPeriodicDistance i v = 0 := by
        exact_mod_cast (le_antisymm hv (by positivity))
      rw [hd]
      omega
    · have h1 : ManyBody.gaussianFilteredTerm ((ℓ : ℝ) * Δ) Δ (∑ j, g j) (g i) = g i :=
        hfilters.1
      rw [one_mul, h1, sub_self, norm_zero, mul_zero, zero_mul]
  · have hRp : 0 < R := lt_of_le_of_ne hR (Ne.symm hRzero)
    obtain ⟨c₁, η, C, hc₁, hη, hC, hloc⟩ :=
      ManyBody.exists_metric_truncated_filter_localization hRp (2 * Nat.ceil R + 1) hJ hΔ
    refine ⟨c₁, η, C, hc₁, hη, hC, ?_⟩
    intro M d hM g hg hsupp hnorm ℓ hℓ i a
    let _ : NeZero M := ⟨by omega⟩
    let _ := ManyBody.cyclicMetricSpace M
    have hsupp' : ∀ j,
        g j ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (ManyBody.metricRangeBall R j) := by
      intro j
      apply ManyBody.supportedOperators_mono _ (hsupp j)
      intro v hv
      rw [ManyBody.mem_metricRangeBall]
      exact (Finset.mem_filter.mp hv).2
    have ha := hloc
      (⟨g, hsupp'⟩ : ManyBody.Interaction (fun _ ↦ Fin d) (ManyBody.metricRangeBall R))
      hg hnorm (ManyBody.card_metricRangeBall_cyclicMetricSpace_le R) (ℓ : ℝ) hℓ i
    have heq : ManyBody.gaussianFilteredTerm (c₁ * (ℓ : ℝ) * Δ) Δ
        (∑ j ∈ ManyBody.metricRangeBall ((ℓ : ℝ) - R) i, g j) (g i) = a := by
      rfl
    dsimp only at ha
    rw [heq] at ha
    refine ⟨ManyBody.supportedOperators_mono (fun v hv ↦ ?_) ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1⟩
    · rw [ManyBody.mem_metricRangeBall] at hv
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hd : (ManyBody.roundedPeriodicDistance i v : ℝ) ≤ (ℓ : ℝ) := hv
      exact_mod_cast hd

/-- Physical local interactions determine a corrected periodic hierarchy at explicit
quadratic logarithmic radius. The only ground-vector estimate assumed is source (low).
Hastings, arXiv:cond-mat/0508554v3, lines 169–190 and 609–743. -/
theorem exists_periodicPhysicalHierarchy {R J Δ : ℝ} (hR : 0 ≤ R) (hJ : 0 < J) (hΔ : 0 < Δ) :
    ∃ c₁ η C : ℝ, 0 < c₁ ∧ 0 < η ∧ 0 ≤ C ∧
      ∀ {M d : ℕ}, 0 < M →
        ∀ (g : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ),
          (∀ i, (g i).IsHermitian) →
          (∀ i, g i ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
              (Finset.univ.filter fun v ↦ (ManyBody.roundedPeriodicDistance i v : ℝ) ≤ R)) →
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
          let h := finiteHierarchyDepth (ManyBody.roundedPeriodicBlockCount M ℓ)
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
  have haSupp (i : Fin M) : a i ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
      (Finset.univ.filter fun v ↦ ManyBody.roundedPeriodicDistance i v ≤ ℓ) :=
    (haloc i).1
  have haHerm (i : Fin M) : (a i).IsHermitian := (haloc i).2.1
  have haNorm (i : Fin M) : ‖a i‖ ≤ Jb := ((haloc i).2.2.1).trans (le_max_left _ _)
  have haError (i : Fin M) :
      ‖ManyBody.gaussianFilteredTerm (c₁ * (ℓ : ℝ) * Δ) Δ (∑ j, g j) (g i) - a i‖ ≤
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

end PeriodicPhysicalHierarchy

section GappedPeriodicHierarchy

/-!
## The periodic hierarchy from a unique gapped ground state

The local ground-vector estimate is derived from the actual Gaussian
filters and the original projector gap. The filter parameter, decay rate
and norm allowance are chosen before the chain and its ground data.
The filters and pair assignment depend on the local operators and these
parameters; the spectral-window centres use expectations in the specified
ground vector. No ground-vector-free algorithm or running time is asserted.
This supplies the one-ground-state case of Hastings,
arXiv:cond-mat/0508554v3, lines 375–387 and 609–743.

**Scope restriction (unique ground state):** The degenerate-ground-space
basis construction is separate; see
https://sirui-lu.com/QICLean/paper-gaps/hastings05_two_dim_ground_basis.pdf.

**Local fix (periodic hierarchy):** the norm deficiency is measured against
the original ground vector, and a further window controls the closing edge.
See `docs/paper-gaps/hastings05_hierarchical_projection.tex` and
`docs/paper-gaps/hastings05_hierarchical_energy.tex`.
-/

open Matrix QuantumCircuit ManyBody GaussianFilter
open scoped Matrix.Norms.L2Operator InnerProductSpace

open ManyBody (IsGapped groundSpace)

namespace TNLean.MPS.AreaLaw.LocalSolution

/-- The actual truncated filters satisfy the local ground-vector estimate
with one common exponential rate. Hastings, arXiv:cond-mat/0508554v3,
eq. `low`, and the hierarchy construction in Section III. -/
private theorem exists_periodic_gapped_truncation_data {R J Δ : ℝ}
    (hR : 0 ≤ R) (hJ : 0 < J) (hΔ : 0 < Δ) :
    ∃ c₁ η C : ℝ, 0 < c₁ ∧ 0 < η ∧ 0 ≤ C ∧
      ∀ {M d : ℕ}, 0 < M →
        ∀ (g : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ),
          (∀ i, (g i).IsHermitian) →
          (∀ i, g i ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
              (Finset.univ.filter fun v ↦ (ManyBody.roundedPeriodicDistance i v : ℝ) ≤ R)) →
          (∀ i, ‖g i‖ ≤ J) →
          ∀ (Ω : EuclideanSpace ℂ (Fin M → Fin d)) (E₀ : ℝ),
            ‖Ω‖ = 1 → IsGapped (∑ i, g i) E₀ Δ →
            groundSpace (∑ i, g i) E₀ = Submodule.span ℂ {Ω} →
            ∀ (ℓ : ℕ), R ≤ (ℓ : ℝ) → ∀ i,
              let a := periodicPhysicalTruncatedTerm c₁ R Δ ℓ g i
              let Jb := 2 * max J (J * C)
              a ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
                  (Finset.univ.filter fun v ↦ ManyBody.roundedPeriodicDistance i v ≤ ℓ) ∧
                a.IsHermitian ∧ ‖a‖ ≤ Jb ∧
                ‖gaussianFilteredTerm (c₁ * (ℓ : ℝ) * Δ) Δ (∑ j, g j) (g i) - a‖ ≤
                  Jb * Real.exp (-(η * (ℓ : ℝ))) ∧
                ‖toEuclideanLin
                  (a - ((⟪Ω, toEuclideanLin a Ω⟫_ℂ).re : ℂ) • 1) Ω‖ ≤
                  Jb * Real.exp (-(η * (ℓ : ℝ))) := by
  obtain ⟨c₁, ηloc, C, hc₁, hηloc, hC, hloc⟩ :=
    exists_periodicPhysicalTruncatedTerm_localization hR hJ.le hΔ
  refine ⟨c₁, min ηloc (c₁ * Δ / 2), C, hc₁,
    lt_min hηloc (half_pos (mul_pos hc₁ hΔ)), hC, ?_⟩
  intro M d hM g hg hsupp hnorm Ω E₀ hΩ hgap hspan ℓ hℓR i a Jb
  obtain ⟨haS, haH, haN, haE⟩ := hloc hM g hg hsupp hnorm ℓ hℓR i
  have hJb : J ≤ Jb := by
    dsimp only [Jb]
    linarith only [le_max_left J (J * C), hJ]
  have hlow := norm_apply_sub_inner_smul_le_of_gaussianFilteredTerm
    (by positivity : 0 ≤ c₁ * (ℓ : ℝ) * Δ) hΔ (Matrix.isHermitian_sum _ fun i _ ↦ hg i) hΩ hgap
      hspan (g i) a
  have hExpLoc : Real.exp (-(ηloc * (ℓ : ℝ))) ≤
      Real.exp (-(min ηloc (c₁ * Δ / 2) * (ℓ : ℝ))) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right
      (min_le_left ηloc (c₁ * Δ / 2)) (Nat.cast_nonneg ℓ)))
  have hExpGap : Real.exp (-(c₁ * (ℓ : ℝ) * Δ) / 2) ≤
      Real.exp (-(min ηloc (c₁ * Δ / 2) * (ℓ : ℝ))) := by
    rw [show -(c₁ * (ℓ : ℝ) * Δ) / 2 = -(c₁ * Δ / 2 * (ℓ : ℝ)) by ring]
    gcongr
    exact min_le_right _ _
  have hError : ‖gaussianFilteredTerm (c₁ * (ℓ : ℝ) * Δ) Δ (∑ j, g j) (g i) - a‖ ≤
      J * C * Real.exp (-(min ηloc (c₁ * Δ / 2) * (ℓ : ℝ))) :=
    haE.trans (mul_le_mul_of_nonneg_left hExpLoc (mul_nonneg hJ.le hC))
  have hbudget : J + J * C ≤ Jb := by
    dsimp only [Jb]
    linarith only [le_max_left J (J * C), le_max_right J (J * C)]
  have hJC : J * C ≤ Jb := (le_add_of_nonneg_left hJ.le).trans hbudget
  refine ⟨haS, haH, haN.trans hJb,
    hError.trans (mul_le_mul_of_nonneg_right hJC (Real.exp_pos _).le), ?_⟩
  have hreal : ((⟪Ω, toEuclideanLin a Ω⟫_ℂ).re : ℂ) =
      ⟪Ω, toEuclideanLin a Ω⟫_ℂ :=
    (isSymmetric_toEuclideanLin_iff.mpr haH).coe_re_inner_self_apply Ω
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    toLpLin_one, LinearMap.id_apply, hreal]
  calc _ ≤ ‖g i‖ * Real.exp (-(c₁ * (ℓ : ℝ) * Δ) / 2) +
        ‖gaussianFilteredTerm (c₁ * (ℓ : ℝ) * Δ) Δ (∑ j, g j) (g i) - a‖ := hlow
    _ ≤ J * Real.exp (-(min ηloc (c₁ * Δ / 2) * (ℓ : ℝ))) +
        J * C * Real.exp (-(min ηloc (c₁ * Δ / 2) * (ℓ : ℝ))) := by
      exact add_le_add (mul_le_mul (hnorm i) hExpGap (Real.exp_pos _).le hJ.le) hError
    _ = (J + J * C) * Real.exp (-(min ηloc (c₁ * Δ / 2) * (ℓ : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (Real.exp_pos _).le

/-- Original Hermitian local interactions and a specified unique gapped ground state
give an actual periodic hierarchy, with no supplied local residual or pair family. The
constants are chosen before the chain, the Hamiltonian and its ground data.
Hastings, arXiv:cond-mat/0508554v3, eq. `low`, lines 375–387 and 609–743, with the
corrected deficiency recurrence and closing window documented in
`docs/paper-gaps/hastings05_hierarchical_projection.tex` and
`docs/paper-gaps/hastings05_hierarchical_energy.tex`. -/
theorem exists_periodicPhysicalHierarchy_of_isGapped {R J Δ : ℝ}
    (hR : 0 ≤ R) (hJ : 0 < J) (hΔ : 0 < Δ) :
    ∃ c₁ η C : ℝ, 0 < c₁ ∧ 0 < η ∧ 0 ≤ C ∧
      ∀ {M d : ℕ}, 0 < M →
        ∀ (g : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ),
          (∀ i, (g i).IsHermitian) →
          (∀ i, g i ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
              (Finset.univ.filter fun v ↦ (ManyBody.roundedPeriodicDistance i v : ℝ) ≤ R)) →
          (∀ i, ‖g i‖ ≤ J) →
          ∀ (Ω : EuclideanSpace ℂ (Fin M → Fin d)) (E₀ : ℝ),
            ‖Ω‖ = 1 → IsGapped (∑ i, g i) E₀ Δ →
            groundSpace (∑ i, g i) E₀ = Submodule.span ℂ {Ω} →
            let Jb := 2 * max J (J * C)
            let ℓ := physicalPeriodicProjectionRadius R M Jb η Δ
            let r := η * (ℓ : ℝ)
            let a := periodicPhysicalTruncatedTerm c₁ R Δ ℓ g
            let P := roundedPeriodicProjection ℓ a Ω Jb r
            let b := roundedPeriodicOperator ℓ a
            let h := finiteHierarchyDepth (ManyBody.roundedPeriodicBlockCount M ℓ)
            let K := 8 * (ℓ : ℝ) * Jb
            ∃ φ : EuclideanSpace ℂ (Fin M → Fin d), ‖φ‖ = 1 ∧
              toEuclideanLin P φ = φ ∧
              ‖φ - Ω‖ ≤ 2 * (((3 : ℝ) ^ (h + 1) - 1) * Real.exp (-r / 8)) ∧
              IsRetainedHierarchy
                (hierarchyProjection (hierarchyEdge (extendFiniteEdges b))
                  (fun m k ↦
                    (⟪Ω, toEuclideanLin (hierarchyEdge (extendFiniteEdges b) m k) Ω⟫_ℂ).re)
                  (hierarchyWindowRadius K r h)) h 0 φ ∧
              ∀ {n : ℕ} (Φ : Fin n → EuclideanSpace ℂ (Fin M → Fin d)), Orthonormal ℂ Φ →
                (∀ j, toEuclideanLin P (Φ j) = Φ j) → n ≤ 2 := by
  obtain ⟨c₁, η, C, hc₁, hη, hC, hdata⟩ :=
    exists_periodic_gapped_truncation_data hR hJ hΔ
  refine ⟨c₁, η, C, hc₁, hη, hC, ?_⟩
  intro M d hM g hg hsupp hnorm Ω E₀ hΩ hgap hspan Jb ℓ r a P b h K
  have hJb : 0 < Jb := mul_pos (by norm_num) (hJ.trans_le (le_max_left _ _))
  obtain ⟨hℓ, hℓR⟩ := physicalPeriodicProjectionRadius_spec R M Jb Δ hη
  have hr := hierarchyProjectionLength_le_physicalPeriodicProjectionRadius hM R Jb Δ hη
  have ha (i : Fin M) := hdata hM g hg hsupp hnorm Ω E₀ hΩ hgap hspan ℓ hℓR i
  have haSupp (i : Fin M) :
      a i ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
      (Finset.univ.filter fun v ↦ ManyBody.roundedPeriodicDistance i v ≤ ℓ) :=
    (ha i).1
  have haHerm (i : Fin M) : (a i).IsHermitian := (ha i).2.1
  have haNorm (i : Fin M) : ‖a i‖ ≤ Jb := (ha i).2.2.1
  have haError (i : Fin M) :
      ‖gaussianFilteredTerm (c₁ * (ℓ : ℝ) * Δ) Δ (∑ j, g j) (g i) - a i‖ ≤
        Jb * Real.exp (-r) := (ha i).2.2.2.1
  obtain ⟨φ, hφ, hkeep, hnear, htree⟩ := exists_unit_mem_roundedPeriodicProjection hℓ a
    haSupp haHerm hΩ hJb hr (fun i ↦ (ha i).2.2.2.2) haNorm
  refine ⟨φ, hφ, hkeep, hnear, htree, ?_⟩
  let P₀ := vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))
  have hP₀ : IsStarProjection P₀ := by
    have heq : Matrix.toEuclideanCLM (n := Fin M → Fin d) (𝕜 := ℂ) P₀ =
        InnerProductSpace.rankOne ℂ Ω Ω := by
      apply ContinuousLinearMap.ext
      intro v
      change toEuclideanLin P₀ v = ⟪Ω, v⟫_ℂ • Ω
      exact toEuclideanLin_vecMulVec_star_self_apply Ω v
    have h := (InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) hΩ).map
      (Matrix.toEuclideanCLM (n := Fin M → Fin d) (𝕜 := ℂ)).symm.toStarAlgHom
    rw [← heq] at h
    change IsStarProjection ((Matrix.toEuclideanCLM (n := Fin M → Fin d) (𝕜 := ℂ)).symm
      (Matrix.toEuclideanCLM (n := Fin M → Fin d) (𝕜 := ℂ) P₀)) at h
    simpa only [StarAlgEquiv.symm_apply_apply] using h
  have hgap (v : EuclideanSpace ℂ (Fin M → Fin d)) :
      Δ * (‖v‖ ^ 2 - (⟪v, toEuclideanLin P₀ v⟫_ℂ).re) ≤
        (⟪v, toEuclideanLin (∑ i, g i) v⟫_ℂ).re - E₀ * ‖v‖ ^ 2 := by
    have hinner : (⟪v, toEuclideanLin P₀ v⟫_ℂ).re = ‖⟪Ω, v⟫_ℂ‖ ^ 2 := by
      change (⟪v, toEuclideanLin
        (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) v⟫_ℂ).re = _
      rw [toEuclideanLin_vecMulVec_star_self_apply, inner_smul_right,
        ← inner_conj_symm v Ω, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    simpa only [hinner] using (hgap.posSemidef_sub_smul_one
        (Matrix.isHermitian_sum _ fun i _ ↦ hg i) hΩ hspan).gap_le v
  have hE₀ : (⟪Ω, toEuclideanLin (∑ i, g i) Ω⟫_ℂ).re = E₀ := by
    have heigen : toEuclideanLin (∑ i, g i) Ω = (E₀ : ℂ) • Ω :=
      ManyBody.mem_groundSpace_iff.mp (hspan ▸ Submodule.mem_span_singleton_self _)
    rw [heigen, inner_smul_right, inner_self_eq_norm_sq_to_K, hΩ]
    simp
  have htrace : (trace P₀).re = 1 := by
    change (trace (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).re = 1
    rw [trace_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct]
    rw [inner_self_eq_norm_sq_to_K, hΩ]
    norm_num
  intro n Φ hΦ hfix
  have hc := card_le_two_mul_re_trace_of_roundedPeriodicProjection hℓ a g haSupp haHerm hg hΩ
    hJb hη hΔ rfl hr haError hP₀ hgap hE₀ hΦ Finset.univ (fun j _ ↦ hfix j)
  have hc' : (n : ℝ) ≤ 2 := by simpa [htrace] using hc
  exact_mod_cast hc'

end TNLean.MPS.AreaLaw.LocalSolution

end GappedPeriodicHierarchy
