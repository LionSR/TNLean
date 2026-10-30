/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.GappedGroundState
import TNLean.Lattice.GaussianFilteredMetricTruncation
import QICLean.Analysis.GapPerturbation

/-!
# Ground-state overlap for the actual truncated Gaussian Hamiltonian

Let a Hermitian approximation `M` satisfy `‖H-M‖ ≤ ε`. A unit vector minimizing
its Rayleigh quotient is an actual eigenvector of `M`, and its excess energy
under `H` is at most `2ε`. The original spectral gap therefore controls its
projection onto the full original ground eigenspace. For a unique unit ground
vector `Ω`, the overlap defect is at most `2ε/Δ` and the attained minimum
squared distance after phase choice is at most `4ε/Δ`.

No gap or positivity assumption on `M` is needed. The degenerate statement
uses the canonical ground eigenspace, and the quadratic gap above it is
derived from the original eigenvalue gap by spectral expansion and Parseval.

For the actual sum of physical metric-ball truncated filters, the norm error
is bounded by `N J C exp(-βℓ)`. For every accuracy `η > 0`, the explicit radius
`max R (log(4 max(N J C,1)/(Δ min(η,1)))/β)` gives a ground vector of nonzero
original-ground-space projection. Its projection defect is at most `η`;
in the unique-ground-state case the squared phase error is at most `η`.
The constants are chosen before the finite metric space and its Hamiltonian.
The physical metric estimates use positive `R`; for zero range the filters
are exact by `GaussianZeroRange`, and the norm-comparison results apply with
`ε=0`.

Source: Hastings, *Solving Gapped Hamiltonians Locally*,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 359–367, with the truncation
estimate at lines 343–357.
-/

open Matrix Complex
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.Lattice

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem unit_energy_error_le {H M : Matrix n n ℂ} {ε : ℝ}
    (hHM : ‖H - M‖ ≤ ε) {v : EuclideanSpace ℂ n} (hv : ‖v‖ = 1) :
    |(⟪v, toEuclideanLin H v⟫_ℂ).re - (⟪v, toEuclideanLin M v⟫_ℂ).re| ≤ ε := by
  have hq := ((toEuclideanCLM (𝕜 := ℂ) (n := n) (H - M)).rayleighQuotient_le_norm v).trans hHM
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    hv, one_pow, div_one] at hq
  change |(⟪toEuclideanLin (H - M) v, v⟫_ℂ).re| ≤ ε at hq
  rw [← inner_conj_symm (toEuclideanLin (H - M) v) v, Complex.conj_re] at hq
  simpa only [map_sub, LinearMap.sub_apply, inner_sub_right, Complex.sub_re] using hq

/-- The eigenvalue gap is the quadratic-form gap above the canonical ground eigenspace.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem groundEigenspace_gap_le_of_eigenvalues {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {E₀ Δ : ℝ} (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + Δ ≤ hH.eigenvalues k)
    (ψ : EuclideanSpace ℂ n) :
    Δ * (‖ψ‖ ^ 2 - ‖(groundEigenspace H E₀).starProjection ψ‖ ^ 2) ≤
      (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re - E₀ * ‖ψ‖ ^ 2 := by
  let K := groundEigenspace H E₀
  let b := hH.eigenvectorBasis
  let y := ψ - K.starProjection ψ
  have hb (k : n) : H *ᵥ WithLp.ofLp (b k) = (hH.eigenvalues k : ℂ) • WithLp.ofLp (b k) :=
    SpectralFilter.mulVec_eigenvectorBasis_complex hH k
  have hcoef (k : n) : ⟪b k, toEuclideanLin H ψ⟫_ℂ =
      (hH.eigenvalues k : ℂ) * ⟪b k, ψ⟫_ℂ := by
    have hs := isSymmetric_toEuclideanLin_iff.mpr hH
    have heig : toEuclideanLin H (b k) = (hH.eigenvalues k : ℂ) • b k := by
      exact (WithLp.ofLp_injective 2) (hb k)
    rw [← hs, heig, inner_smul_left, Complex.conj_ofReal]
  have henergy : (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re =
      ∑ k, hH.eigenvalues k * ‖⟪b k, ψ⟫_ℂ‖ ^ 2 := by
    rw [← b.sum_inner_mul_inner ψ (toEuclideanLin H ψ)]
    change Complex.reAddGroupHom (∑ k, ⟪ψ, b k⟫_ℂ * ⟪b k, toEuclideanLin H ψ⟫_ℂ) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hcoef, ← inner_conj_symm ψ (b k)]
    have heq : (starRingEnd ℂ) ⟪b k, ψ⟫_ℂ *
        ((hH.eigenvalues k : ℂ) * ⟪b k, ψ⟫_ℂ) =
        ((hH.eigenvalues k * ‖⟪b k, ψ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      calc _ = (hH.eigenvalues k : ℂ) *
          ((starRingEnd ℂ) ⟪b k, ψ⟫_ℂ * ⟪b k, ψ⟫_ℂ) := by ring
        _ = _ := by rw [Complex.conj_mul']; push_cast; rfl
    rw [heq]
    rfl
  have henergySub : (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re - E₀ * ‖ψ‖ ^ 2 =
      ∑ k, (hH.eigenvalues k - E₀) * ‖⟪b k, ψ⟫_ℂ‖ ^ 2 := by
    rw [henergy, ← b.sum_sq_norm_inner_right ψ, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  have hres : ‖ψ‖ ^ 2 - ‖K.starProjection ψ‖ ^ 2 = ‖y‖ ^ 2 := by
    have hp := Submodule.norm_sq_eq_add_norm_sq_starProjection ψ K
    rw [K.starProjection_orthogonal_val ψ] at hp
    dsimp [y]
    linarith
  change Δ * (‖ψ‖ ^ 2 - ‖K.starProjection ψ‖ ^ 2) ≤ _
  rw [hres, ← b.sum_sq_norm_inner_right y, Finset.mul_sum, henergySub]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : hH.eigenvalues k = E₀
  · have hmem : b k ∈ K := mem_groundEigenspace_iff.mpr (by simpa only [hk] using hb k)
    have hzero : ⟪b k, y⟫_ℂ = 0 := by
      rw [inner_eq_zero_symm]
      exact K.starProjection_inner_eq_zero ψ (b k) hmem
    simp [hzero, hk]
  · have hzero : ⟪b k, K.starProjection ψ⟫_ℂ = 0 :=
      inner_eq_zero_of_mem_groundEigenspace hH hk (hb k) (K.starProjection_apply_mem ψ)
    have hge := (hgap k).resolve_left hk
    simp only [y, inner_sub_right, hzero, sub_zero]
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

/-- A unit eigenvector of a Hermitian approximation minimizes its quadratic form
and has excess original energy at most twice the operator-norm error.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exists_groundVector_energy_le_of_norm_sub_le {H M : Matrix n n ℂ}
    {E₀ ε : ℝ} {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1)
    (hHΩ : toEuclideanCLM (𝕜 := ℂ) (n := n) H Ω = (E₀ : ℂ) • Ω)
    (hM : M.IsHermitian) (hHM : ‖H - M‖ ≤ ε) :
    ∃ (e : ℝ) (φ : EuclideanSpace ℂ n), ‖φ‖ = 1 ∧
      toEuclideanCLM (𝕜 := ℂ) (n := n) M φ = (e : ℂ) • φ ∧
      (∀ ψ : EuclideanSpace ℂ n,
        e * ‖ψ‖ ^ 2 ≤ (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re) ∧
      (⟪φ, toEuclideanLin H φ⟫_ℂ).re - E₀ ≤ 2 * ε := by
  have : Nontrivial (EuclideanSpace ℂ n) :=
    ⟨⟨Ω, 0, fun h ↦ by simp [h] at hΩ⟩⟩
  have hMsym : (toEuclideanCLM (𝕜 := ℂ) (n := n) M :
      EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.mpr hM
  obtain ⟨φ, hφ, heig, hmin⟩ := exists_unit_eigenvector_re_inner_le hMsym
  have hE₀ : (⟪Ω, toEuclideanLin H Ω⟫_ℂ).re = E₀ := by
    change (⟪Ω, toEuclideanCLM (𝕜 := ℂ) (n := n) H Ω⟫_ℂ).re = E₀
    rw [hHΩ, inner_smul_right, inner_self_eq_norm_sq_to_K, hΩ]
    simp
  have hminΩ := hmin Ω
  have hdiffΩ := unit_energy_error_le hHM hΩ
  have hdiffφ := unit_energy_error_le hHM hφ
  have henergy : (⟪φ, toEuclideanLin H φ⟫_ℂ).re - E₀ ≤ 2 * ε := by
    rw [hΩ, one_pow, mul_one] at hminΩ
    change (⟪φ, toEuclideanLin M φ⟫_ℂ).re ≤
      (⟪Ω, toEuclideanLin M Ω⟫_ℂ).re at hminΩ
    linarith [(abs_le.mp hdiffΩ).1, (abs_le.mp hdiffφ).2]
  exact ⟨_, φ, hφ, heig, hmin, henergy⟩

/-- An actual ground vector of a Hermitian approximation has large overlap with the
unique gapped ground vector of the original Hamiltonian.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exists_groundVector_overlap_of_norm_sub_le {H M : Matrix n n ℂ}
    {E₀ Δ ε : ℝ} {Ω : EuclideanSpace ℂ n}
    (hgs : Matrix.IsGappedGroundState H E₀ Ω Δ) (hΔ : 0 < Δ)
    (hM : M.IsHermitian) (hHM : ‖H - M‖ ≤ ε) :
    ∃ (e : ℝ) (φ : EuclideanSpace ℂ n), ‖φ‖ = 1 ∧
      toEuclideanCLM (𝕜 := ℂ) (n := n) M φ = (e : ℂ) • φ ∧
      (∀ ψ : EuclideanSpace ℂ n,
        e * ‖ψ‖ ^ 2 ≤ (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re) ∧
      Δ * (1 - ‖⟪Ω, φ⟫_ℂ‖ ^ 2) ≤ 2 * ε ∧
      ∃ θ : ℝ, IsMinOn
        (fun α : ℝ ↦ ‖φ - Complex.exp (α * Complex.I) • Ω‖) Set.univ θ ∧
        ‖φ - Complex.exp (θ * Complex.I) • Ω‖ ^ 2 ≤ 4 * ε / Δ := by
  obtain ⟨e, φ, hφ, heig, hmin, henergy⟩ :=
    exists_groundVector_energy_le_of_norm_sub_le hgs.1 hgs.2.1 hM hHM
  have hgap : Δ * (1 - ‖⟪Ω, φ⟫_ℂ‖ ^ 2) ≤ 2 * ε := by
    have hg := hgs.2.2.gap_le φ
    rw [hφ, one_pow, mul_one] at hg
    exact hg.trans henergy
  obtain ⟨θ, hminθ, hθ⟩ := exists_isMinOn_sq_norm_sub_exp_smul_le_of_gap hΔ hφ hgs.1 hgap
  refine ⟨_, φ, hφ, heig, hmin, hgap, θ, hminθ, ?_⟩
  simpa only [show (2 : ℝ) * (2 * ε) = 4 * ε by ring] using hθ

/-- The same energy comparison controls mass outside the canonical ground eigenspace,
without a simplicity assumption on the original ground energy.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exists_groundVector_projected_mass_of_norm_sub_le {H M : Matrix n n ℂ}
    {E₀ Δ ε : ℝ} {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1)
    (hHΩ : toEuclideanCLM (𝕜 := ℂ) (n := n) H Ω = (E₀ : ℂ) • Ω)
    (hgap : ∀ ψ : EuclideanSpace ℂ n,
      Δ * (‖ψ‖ ^ 2 - ‖(groundEigenspace H E₀).starProjection ψ‖ ^ 2) ≤
        (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re - E₀ * ‖ψ‖ ^ 2)
    (hM : M.IsHermitian) (hHM : ‖H - M‖ ≤ ε) :
    ∃ (e : ℝ) (φ : EuclideanSpace ℂ n), ‖φ‖ = 1 ∧
      toEuclideanCLM (𝕜 := ℂ) (n := n) M φ = (e : ℂ) • φ ∧
      (∀ ψ : EuclideanSpace ℂ n,
        e * ‖ψ‖ ^ 2 ≤ (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re) ∧
      Δ * (1 - ‖(groundEigenspace H E₀).starProjection φ‖ ^ 2) ≤ 2 * ε ∧
      (2 * ε < Δ → (groundEigenspace H E₀).starProjection φ ≠ 0) := by
  obtain ⟨e, φ, hφ, heig, hmin, henergy⟩ :=
    exists_groundVector_energy_le_of_norm_sub_le hΩ hHΩ hM hHM
  have hmass : Δ * (1 - ‖(groundEigenspace H E₀).starProjection φ‖ ^ 2) ≤ 2 * ε := by
    have hg := hgap φ
    rw [hφ, one_pow, mul_one] at hg
    exact hg.trans henergy
  refine ⟨e, φ, hφ, heig, hmin, hmass, ?_⟩
  intro hsmall hz
  rw [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, mul_one] at hmass
  linarith

/-- A logarithmic radius makes an exponential approximation error smaller than
one quarter of the gap times a prescribed accuracy.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exp_error_le_of_log_radius {B β Δ τ ℓ : ℝ} (hβ : 0 < β) (hΔ : 0 < Δ)
    (hτ : 0 < τ) (hℓ : Real.log (4 * max B 1 / (Δ * τ)) / β ≤ ℓ) :
    B * Real.exp (-(β * ℓ)) ≤ Δ * τ / 4 := by
  let Q := max B 1
  have hQ : 0 < Q := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hr : 0 < 4 * Q / (Δ * τ) := by positivity
  have hlog : Real.log (4 * Q / (Δ * τ)) ≤ ℓ * β := (div_le_iff₀ hβ).mp hℓ
  have he : Real.exp (-(β * ℓ)) ≤ Δ * τ / (4 * Q) := by
    calc Real.exp (-(β * ℓ)) ≤ Real.exp (-Real.log (4 * Q / (Δ * τ))) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log hr, inv_div]
  calc B * Real.exp (-(β * ℓ)) ≤ Q * Real.exp (-(β * ℓ)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ Q * (Δ * τ / (4 * Q)) := mul_le_mul_of_nonneg_left he hQ.le
    _ = _ := by field_simp

/-- An exponential norm approximation gives a ground vector of nonzero overlap
and arbitrary phase-minimized accuracy at an explicit logarithmic radius.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exists_groundVector_overlap_of_exp_norm_bound {H M : Matrix n n ℂ}
    {E₀ Δ B β ℓ η : ℝ} {Ω : EuclideanSpace ℂ n}
    (hgs : Matrix.IsGappedGroundState H E₀ Ω Δ) (hΔ : 0 < Δ)
    (hM : M.IsHermitian) (hβ : 0 < β) (hη : 0 < η)
    (hHM : ‖H - M‖ ≤ B * Real.exp (-(β * ℓ)))
    (hℓ : Real.log (4 * max B 1 / (Δ * min η 1)) / β ≤ ℓ) :
    ∃ (e : ℝ) (φ : EuclideanSpace ℂ n), ‖φ‖ = 1 ∧
      toEuclideanCLM (𝕜 := ℂ) (n := n) M φ = (e : ℂ) • φ ∧
      (∀ ψ : EuclideanSpace ℂ n,
        e * ‖ψ‖ ^ 2 ≤ (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re) ∧
      ⟪Ω, φ⟫_ℂ ≠ 0 ∧
      ∃ θ : ℝ, IsMinOn
        (fun α : ℝ ↦ ‖φ - Complex.exp (α * Complex.I) • Ω‖) Set.univ θ ∧
        ‖φ - Complex.exp (θ * Complex.I) • Ω‖ ^ 2 ≤ η := by
  have herr := exp_error_le_of_log_radius hβ hΔ (lt_min hη zero_lt_one) hℓ
  obtain ⟨e, φ, hφ, heig, hmin, hgap, θ, hminθ, hphase⟩ :=
    exists_groundVector_overlap_of_norm_sub_le hgs hΔ hM hHM
  have hsmall : 2 * (B * Real.exp (-(β * ℓ))) ≤ Δ / 2 := by
    nlinarith [min_le_right η 1]
  have hnonzero : ⟪Ω, φ⟫_ℂ ≠ 0 := by
    intro hz
    rw [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, mul_one] at hgap
    linarith
  refine ⟨e, φ, hφ, heig, hmin, hnonzero, θ, hminθ, hphase.trans ?_⟩
  apply le_trans _ (min_le_left η 1)
  apply (div_le_iff₀ hΔ).mpr
  nlinarith


/-- An exponential approximation gives a ground vector with nonzero projection onto
the full original ground eigenspace at a logarithmic radius.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exists_groundVector_projection_of_exp_norm_bound {H M : Matrix n n ℂ}
    {E₀ Δ B β ℓ η : ℝ} {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1)
    (hHΩ : toEuclideanCLM (𝕜 := ℂ) (n := n) H Ω = (E₀ : ℂ) • Ω)
    (hgap : ∀ ψ : EuclideanSpace ℂ n,
      Δ * (‖ψ‖ ^ 2 - ‖(groundEigenspace H E₀).starProjection ψ‖ ^ 2) ≤
        (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re - E₀ * ‖ψ‖ ^ 2)
    (hΔ : 0 < Δ) (hM : M.IsHermitian) (hβ : 0 < β) (hη : 0 < η)
    (hHM : ‖H - M‖ ≤ B * Real.exp (-(β * ℓ)))
    (hℓ : Real.log (4 * max B 1 / (Δ * min η 1)) / β ≤ ℓ) :
    ∃ (e : ℝ) (φ : EuclideanSpace ℂ n), ‖φ‖ = 1 ∧
      toEuclideanCLM (𝕜 := ℂ) (n := n) M φ = (e : ℂ) • φ ∧
      (∀ ψ : EuclideanSpace ℂ n,
        e * ‖ψ‖ ^ 2 ≤ (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re) ∧
      (groundEigenspace H E₀).starProjection φ ≠ 0 ∧
      1 - ‖(groundEigenspace H E₀).starProjection φ‖ ^ 2 ≤ η := by
  have herr := exp_error_le_of_log_radius hβ hΔ (lt_min hη zero_lt_one) hℓ
  obtain ⟨e, φ, hφ, heig, hmin, hmass, hnonzero⟩ :=
    exists_groundVector_projected_mass_of_norm_sub_le hΩ hHΩ hgap hM hHM
  have hsmall : 2 * (B * Real.exp (-(β * ℓ))) < Δ := by
    nlinarith [min_le_right η 1]
  refine ⟨e, φ, hφ, heig, hmin, hnonzero hsmall, ?_⟩
  apply (mul_le_mul_iff_right₀ hΔ).mp
  nlinarith [min_le_left η 1]

open QuantumCircuit

/-- The actual metric-ball truncated Hamiltonian has a ground vector with nonzero
projection onto the full original ground eigenspace at a logarithmic radius.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exists_metric_truncated_groundVector_projection {R J Δ : ℝ} (hR : 0 < R)
    (S : ℕ) (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ c₁ β C : ℝ, 0 < c₁ ∧ 0 < β ∧ 0 ≤ C ∧
      ∀ {ι : Type*} [PseudoMetricSpace ι] [Fintype ι] [DecidableEq ι] {d : ℕ},
        ∀ (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
          (_hHerm : ∀ i, (h i).IsHermitian)
          (_hSupport : ∀ i, h i ∈ supportedOperators d (Metric.closedBall i R))
          (_hNorm : ∀ i, ‖h i‖ ≤ J)
          (_hCard : ∀ i : ι, (metricRangeBall R i).card ≤ S)
          (hH : (∑ i, h i).IsHermitian) {E₀ : ℝ} {Ω : EuclideanSpace ℂ (ι → Fin d)},
          ‖Ω‖ = 1 →
          toEuclideanCLM (𝕜 := ℂ) (n := ι → Fin d) (∑ i, h i) Ω = (E₀ : ℂ) • Ω →
          (∀ k, hH.eigenvalues k = E₀ ∨ E₀ + Δ ≤ hH.eigenvalues k) →
          ∀ {η : ℝ}, 0 < η → ∀ ℓ : ℝ,
          max R (Real.log (4 * max ((Fintype.card ι : ℝ) * (J * C)) 1 /
            (Δ * min η 1)) / β) ≤ ℓ →
          let M := ∑ i, gaussianFilteredTerm (c₁ * ℓ * Δ) Δ
            (∑ j ∈ metricRangeBall (ℓ - R) i, h j) (h i)
          ∃ (e : ℝ) (φ : EuclideanSpace ℂ (ι → Fin d)), ‖φ‖ = 1 ∧
            toEuclideanCLM (𝕜 := ℂ) (n := ι → Fin d) M φ = (e : ℂ) • φ ∧
            (∀ ψ : EuclideanSpace ℂ (ι → Fin d),
              e * ‖ψ‖ ^ 2 ≤ (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re) ∧
            (groundEigenspace (∑ i, h i) E₀).starProjection φ ≠ 0 ∧
            1 - ‖(groundEigenspace (∑ i, h i) E₀).starProjection φ‖ ^ 2 ≤ η := by
  obtain ⟨c₁, β, C, hc₁, hβ, hC, hbound⟩ :=
    exists_metric_truncated_filter_sum_bound hR S hJ hΔ
  refine ⟨c₁, β, C, hc₁, hβ, hC, ?_⟩
  intro ι _ _ _ d h hHerm hSupport hNorm hCard hH E₀ Ω hΩ hHΩ hgapSpec η hη ℓ hℓ M
  have hℓR : R ≤ ℓ := (le_max_left _ _).trans hℓ
  have hℓlog := (le_max_right _ _).trans hℓ
  have hM : M.IsHermitian := by
    apply Matrix.isHermitian_sum
    intro i _
    exact isHermitian_gaussianFilteredTerm _ _
      (Matrix.isHermitian_sum _ fun j _ ↦ hHerm j) (hHerm i)
  have hgap := groundEigenspace_gap_le_of_eigenvalues hH hgapSpec
  apply exists_groundVector_projection_of_exp_norm_bound hΩ hHΩ hgap hΔ hM hβ hη _ hℓlog
  have hb := hbound h hHerm hSupport hNorm hCard ℓ hℓR
  rw [norm_sub_rev] at hb
  simpa only [M, mul_assoc] using hb

/-- The actual metric-ball truncated Hamiltonian has a ground vector with nonzero
original-ground-state overlap and arbitrary accuracy at a logarithmic radius.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exists_metric_truncated_groundVector_overlap {R J Δ : ℝ} (hR : 0 < R)
    (S : ℕ) (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ c₁ β C : ℝ, 0 < c₁ ∧ 0 < β ∧ 0 ≤ C ∧
      ∀ {ι : Type*} [PseudoMetricSpace ι] [Fintype ι] [DecidableEq ι] {d : ℕ},
        ∀ (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
          (_hHerm : ∀ i, (h i).IsHermitian)
          (_hSupport : ∀ i, h i ∈ supportedOperators d (Metric.closedBall i R))
          (_hNorm : ∀ i, ‖h i‖ ≤ J)
          (_hCard : ∀ i : ι, (metricRangeBall R i).card ≤ S)
          {E₀ : ℝ} {Ω : EuclideanSpace ℂ (ι → Fin d)},
          Matrix.IsGappedGroundState (∑ i, h i) E₀ Ω Δ →
          ∀ {η : ℝ}, 0 < η → ∀ ℓ : ℝ,
          max R (Real.log (4 * max ((Fintype.card ι : ℝ) * (J * C)) 1 /
            (Δ * min η 1)) / β) ≤ ℓ →
          let M := ∑ i, gaussianFilteredTerm (c₁ * ℓ * Δ) Δ
            (∑ j ∈ metricRangeBall (ℓ - R) i, h j) (h i)
          ∃ (e : ℝ) (φ : EuclideanSpace ℂ (ι → Fin d)), ‖φ‖ = 1 ∧
            toEuclideanCLM (𝕜 := ℂ) (n := ι → Fin d) M φ = (e : ℂ) • φ ∧
            (∀ ψ : EuclideanSpace ℂ (ι → Fin d),
              e * ‖ψ‖ ^ 2 ≤ (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re) ∧
            ⟪Ω, φ⟫_ℂ ≠ 0 ∧
            ∃ θ : ℝ, IsMinOn
              (fun α : ℝ ↦ ‖φ - Complex.exp (α * Complex.I) • Ω‖) Set.univ θ ∧
              ‖φ - Complex.exp (θ * Complex.I) • Ω‖ ^ 2 ≤ η := by
  obtain ⟨c₁, β, C, hc₁, hβ, hC, hbound⟩ :=
    exists_metric_truncated_filter_sum_bound hR S hJ hΔ
  refine ⟨c₁, β, C, hc₁, hβ, hC, ?_⟩
  intro ι _ _ _ d h hHerm hSupport hNorm hCard E₀ Ω hgs η hη ℓ hℓ M
  have hℓR : R ≤ ℓ := (le_max_left _ _).trans hℓ
  have hℓlog := (le_max_right _ _).trans hℓ
  have hM : M.IsHermitian := by
    apply Matrix.isHermitian_sum
    intro i _
    exact isHermitian_gaussianFilteredTerm _ _
      (Matrix.isHermitian_sum _ fun j _ ↦ hHerm j) (hHerm i)
  apply exists_groundVector_overlap_of_exp_norm_bound hgs hΔ hM hβ hη _ hℓlog
  have hb := hbound h hHerm hSupport hNorm hCard ℓ hℓR
  rw [norm_sub_rev] at hb
  simpa only [M, mul_assoc] using hb

end TNLean.Lattice
