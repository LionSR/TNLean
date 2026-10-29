/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GaussianNegativeFrequencyOperator
import TNLean.Lattice.GaussianFilteredGround

/-!
# Actual Gaussian frequency separation at a unique ground line

The regularized operator and its adjoint have actual vector limits on a
ground eigenvector. Their energy coefficients are obtained from the actual
Gaussian--Cauchy integral, rather than supplied as spectral hypotheses.
Centering removes the entire ground component when the ground eigenspace
is a line. The Gaussian tails and Parseval's identity give dimension-free
errors. Cauchy--Schwarz then compares the limiting regularized commutator
with the ordinary ground correlation.

No locality or correlation-decay estimate is assumed. Only the first
observable needs centering. The ground vector need not be normalized.

Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
equations (3.1)–(3.14) and Lemma 3.1.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Matrix Filter
open scoped Matrix.Norms.L2Operator InnerProductSpace NNReal Topology

namespace TNLean.Lattice

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "L" => Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)

private theorem inner_adjoint_matrix (A : Matrix n n ℂ)
    (x y : EuclideanSpace ℂ n) :
    ⟪x, L Aᴴ y⟫_ℂ = star ⟪y, L A x⟫_ℂ := by
  rw [← Matrix.star_eq_conjTranspose, map_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm (L A x) y).symm

private theorem star_inner_matrix (A : Matrix n n ℂ)
    (x y : EuclideanSpace ℂ n) :
    star ⟪x, L A y⟫_ℂ = ⟪y, L Aᴴ x⟫_ℂ :=
  (inner_adjoint_matrix A y x).symm

private theorem actual_inner_cutoff_limit
    {q Δ : ℝ} (hq : 0 < q) (hΔ : 0 < Δ)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (A : Matrix n n ℂ)
    {v w : EuclideanSpace ℂ n} {E E' : ℝ}
    (hv : H *ᵥ WithLp.ofLp v = (E : ℂ) • WithLp.ofLp v)
    (hw : H *ᵥ WithLp.ofLp w = (E' : ℂ) • WithLp.ofLp w) :
    Tendsto (fun ε : ℝ ↦
      ⟪v, L (gaussianNegativeFrequencyOperator (q / Δ ^ 2).toNNReal ε H A) w⟫_ℂ)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 ((gaussianNegativeFrequencyCutoff q Δ (E - E') : ℂ) * ⟪v, L A w⟫_ℂ)) := by
  apply ((tendsto_normalized_gaussianCauchyTransform_cutoff hq hΔ (E - E')).mul_const
    ⟪v, L A w⟫_ℂ).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (inner_gaussianNegativeFrequencyOperator _ hH A hε hv hw).symm

private theorem exists_vector_limit_of_inner_limits
    {α : Type*} {l : Filter α} [l.NeBot]
    (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n))
    (f : α → EuclideanSpace ℂ n) (c : n → ℂ)
    (hc : ∀ i, Tendsto (fun t ↦ ⟪b i, f t⟫_ℂ) l (𝓝 (c i))) :
    ∃ ξ : EuclideanSpace ℂ n, Tendsto f l (𝓝 ξ) ∧ ∀ i, ⟪b i, ξ⟫_ℂ = c i := by
  let ξ := ∑ i, c i • b i
  have hsum := tendsto_finsetSum Finset.univ fun i _ ↦ (hc i).smul_const (b i)
  have hf : Tendsto f l (𝓝 ξ) := by
    apply hsum.congr'
    exact Eventually.of_forall fun t ↦ b.sum_repr' (f t)
  refine ⟨ξ, hf, fun i ↦ ?_⟩
  exact tendsto_nhds_unique (tendsto_const_nhds.inner hf) (hc i)

private theorem norm_le_of_inner_coefficients_le
    (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n))
    (x y : EuclideanSpace ℂ n) {r : ℝ} (hr : 0 ≤ r)
    (hcoef : ∀ i, ‖⟪b i, x⟫_ℂ‖ ≤ r * ‖⟪b i, y⟫_ℂ‖) :
    ‖x‖ ≤ r * ‖y‖ := by
  have hsq : ‖x‖ ^ 2 ≤ (r * ‖y‖) ^ 2 := by
    rw [← b.sum_sq_norm_inner_right x, mul_pow, ← b.sum_sq_norm_inner_right y,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hcoef i) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))
    two_ne_zero).mp hsq

private theorem centered_ground_line_inner_eq_zero
    {H : Matrix n n ℂ} {E₀ : ℝ} {ψ : EuclideanSpace ℂ n}
    (hline : groundEigenspace H E₀ = Submodule.span ℂ {ψ})
    (A : Matrix n n ℂ) (hcenter : ⟪ψ, L A ψ⟫_ℂ = 0)
    {φ : EuclideanSpace ℂ n} (hφ : φ ∈ groundEigenspace H E₀) :
    ⟪φ, L A ψ⟫_ℂ = 0 := by
  rw [hline, Submodule.mem_span_singleton] at hφ
  obtain ⟨c, rfl⟩ := hφ
  rw [inner_smul_left, hcenter, mul_zero]

/-- Actual regularized operators and their adjoints have ground-vector
limits with the two Gaussian separation bounds. Neither the limits nor
their spectral coefficients are hypotheses. Source: Hastings–Koma,
arXiv:math-ph/0507008, Section 3, equations (3.1)–(3.14), Lemma 3.1. -/
theorem exists_gaussianNegativeFrequency_ground_limits
    {q Δ : ℝ} (hq : 0 < q) (hΔ : 0 < Δ)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hgap : ∀ i, hH.eigenvalues i = E₀ ∨ E₀ + Δ ≤ hH.eigenvalues i)
    {ψ : EuclideanSpace ℂ n} (hψ : ψ ∈ groundEigenspace H E₀)
    (hline : groundEigenspace H E₀ = Submodule.span ℂ {ψ})
    (A : Matrix n n ℂ) (hcenter : ⟪ψ, L A ψ⟫_ℂ = 0) :
    ∃ ξ η : EuclideanSpace ℂ n,
      Tendsto (fun ε : ℝ ↦
        L (gaussianNegativeFrequencyOperator (q / Δ ^ 2).toNNReal ε H A) ψ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 ξ) ∧
      Tendsto (fun ε : ℝ ↦
        L (gaussianNegativeFrequencyOperator (q / Δ ^ 2).toNNReal ε H A)ᴴ ψ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 η) ∧
      ‖ξ‖ ≤ Real.exp (-q / 2) * ‖L A ψ‖ ∧
      ‖L Aᴴ ψ - η‖ ≤ Real.exp (-q / 2) * ‖L Aᴴ ψ‖ := by
  classical
  let b := hH.eigenvectorBasis
  let F := fun ε : ℝ ↦ gaussianNegativeFrequencyOperator (q / Δ ^ 2).toNNReal ε H A
  have hb (i : n) :
      H *ᵥ WithLp.ofLp (b i) = (hH.eigenvalues i : ℂ) • WithLp.ofLp (b i) :=
    SpectralFilter.mulVec_eigenvectorBasis_complex hH i
  have hψ' := mem_groundEigenspace_iff.mp hψ
  have hplus (i : n) := actual_inner_cutoff_limit hq hΔ hH A (hb i) hψ'
  have hminus (i : n) :
      Tendsto (fun ε : ℝ ↦ ⟪b i, L (F ε)ᴴ ψ⟫_ℂ)
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 ((gaussianNegativeFrequencyCutoff q Δ (E₀ - hH.eigenvalues i) : ℂ) *
          ⟪b i, L Aᴴ ψ⟫_ℂ)) := by
    have h := (actual_inner_cutoff_limit hq hΔ hH A hψ' (hb i)).star
    simpa only [star_mul', star_inner_matrix, Complex.star_def, Complex.conj_ofReal,
      mul_comm] using h
  obtain ⟨ξ, hξ, hξcoef⟩ := exists_vector_limit_of_inner_limits b
    (fun ε ↦ L (F ε) ψ) _ hplus
  obtain ⟨η, hη, hηcoef⟩ := exists_vector_limit_of_inner_limits b
    (fun ε ↦ L (F ε)ᴴ ψ) _ hminus
  have hcenterAdj : ⟪ψ, L Aᴴ ψ⟫_ℂ = 0 := by
    rw [inner_adjoint_matrix, hcenter, star_zero]
  have hground (i : n) (hi : hH.eigenvalues i = E₀) : b i ∈ groundEigenspace H E₀ :=
    mem_groundEigenspace_iff.mpr (by simpa only [hi] using hb i)
  refine ⟨ξ, η, hξ, hη, ?_, ?_⟩
  · apply norm_le_of_inner_coefficients_le b ξ (L A ψ) (Real.exp_pos _).le
    intro i
    by_cases hi : hH.eigenvalues i = E₀
    · have hz := centered_ground_line_inner_eq_zero hline A hcenter (hground i hi)
      rw [hξcoef, hz, mul_zero, norm_zero]
      positivity
    · have hω : Δ ≤ hH.eigenvalues i - E₀ := by
        have := (hgap i).resolve_left hi
        linarith
      rw [hξcoef, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (gaussianNegativeFrequencyCutoff_nonneg _ _ _)]
      exact mul_le_mul_of_nonneg_right
        (gaussianNegativeFrequencyCutoff_le_exp_of_gap hq hΔ hω) (norm_nonneg _)
  · apply norm_le_of_inner_coefficients_le b (L Aᴴ ψ - η) (L Aᴴ ψ) (Real.exp_pos _).le
    intro i
    by_cases hi : hH.eigenvalues i = E₀
    · have hz := centered_ground_line_inner_eq_zero hline Aᴴ hcenterAdj (hground i hi)
      have hzero : ⟪b i, L Aᴴ ψ - η⟫_ℂ = 0 := by
        simp only [inner_sub_right, hηcoef, hz, mul_zero, sub_zero]
      rw [hzero, norm_zero]
      positivity
    · have hω : E₀ - hH.eigenvalues i ≤ -Δ := by
        have := (hgap i).resolve_left hi
        linarith
      have hcoef : ⟪b i, L Aᴴ ψ - η⟫_ℂ =
          ((1 - gaussianNegativeFrequencyCutoff q Δ (E₀ - hH.eigenvalues i) : ℝ) : ℂ) *
            ⟪b i, L Aᴴ ψ⟫_ℂ := by
        rw [inner_sub_right, hηcoef]
        push_cast
        ring
      rw [hcoef, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (abs_one_sub_gaussianNegativeFrequencyCutoff_le_exp_of_gap hq hΔ hω) (norm_nonneg _)

/-- The actual regularized scalar commutator has a limit approximating the
ordinary ground correlation, with the Gaussian separation error. Only the
first observable is centered, and the ground vector is not required to have
unit norm. Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
equations (3.1)–(3.14), before using the Lieb–Robinson bound. -/
theorem exists_gaussianNegativeFrequency_ground_commutator_limit
    {q Δ : ℝ} (hq : 0 < q) (hΔ : 0 < Δ)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hgap : ∀ i, hH.eigenvalues i = E₀ ∨ E₀ + Δ ≤ hH.eigenvalues i)
    {ψ : EuclideanSpace ℂ n} (hψ : ψ ∈ groundEigenspace H E₀)
    (hline : groundEigenspace H E₀ = Submodule.span ℂ {ψ})
    (A B : Matrix n n ℂ) (hcenter : ⟪ψ, L A ψ⟫_ℂ = 0) :
    ∃ z : ℂ,
      Tendsto (fun ε : ℝ ↦
        let F := gaussianNegativeFrequencyOperator (q / Δ ^ 2).toNNReal ε H A
        ⟪ψ, L (F * B - B * F) ψ⟫_ℂ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 z) ∧
      ‖⟪ψ, L (A * B) ψ⟫_ℂ - z‖ ≤
        2 * Real.exp (-q / 2) * ‖A‖ * ‖B‖ * ‖ψ‖ ^ 2 := by
  obtain ⟨ξ, η, hξ, hη, hsmall, herror⟩ :=
    exists_gaussianNegativeFrequency_ground_limits hq hΔ hH hgap hψ hline A hcenter
  let z := ⟪η, L B ψ⟫_ℂ - ⟪L Bᴴ ψ, ξ⟫_ℂ
  have hmove (M : Matrix n n ℂ) (x y : EuclideanSpace ℂ n) :
      ⟪L Mᴴ x, y⟫_ℂ = ⟪x, L M y⟫_ℂ := by
    rw [← Matrix.star_eq_conjTranspose, map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  refine ⟨z, ?_, ?_⟩
  · have h := (hη.inner tendsto_const_nhds).sub (tendsto_const_nhds.inner hξ)
    apply h.congr'
    exact Eventually.of_forall fun ε ↦ by
      dsimp only
      simp only [map_sub, map_mul, ContinuousLinearMap.sub_apply, inner_sub_right,
        ContinuousLinearMap.mul_apply, hmove]
  · have hnorm (M : Matrix n n ℂ) : ‖L M ψ‖ ≤ ‖M‖ * ‖ψ‖ := by
      simpa only [← Matrix.cstar_norm_def] using (L M).le_opNorm ψ
    have hnormAdj (M : Matrix n n ℂ) : ‖L Mᴴ ψ‖ ≤ ‖M‖ * ‖ψ‖ := by
      simpa only [Matrix.l2_opNorm_conjTranspose] using hnorm Mᴴ
    have hid : ⟪ψ, L (A * B) ψ⟫_ℂ - z =
        ⟪L Aᴴ ψ - η, L B ψ⟫_ℂ + ⟪L Bᴴ ψ, ξ⟫_ℂ := by
      rw [map_mul, ContinuousLinearMap.mul_apply, ← hmove A ψ (L B ψ), inner_sub_left]
      dsimp only [z]
      ring
    rw [hid]
    calc
      _ ≤ ‖⟪L Aᴴ ψ - η, L B ψ⟫_ℂ‖ + ‖⟪L Bᴴ ψ, ξ⟫_ℂ‖ := norm_add_le _ _
      _ ≤ ‖L Aᴴ ψ - η‖ * ‖L B ψ‖ + ‖L Bᴴ ψ‖ * ‖ξ‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ (Real.exp (-q / 2) * ‖L Aᴴ ψ‖) * ‖L B ψ‖ +
          ‖L Bᴴ ψ‖ * (Real.exp (-q / 2) * ‖L A ψ‖) :=
        add_le_add (mul_le_mul_of_nonneg_right herror (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hsmall (norm_nonneg _))
      _ ≤ (Real.exp (-q / 2) * (‖A‖ * ‖ψ‖)) * (‖B‖ * ‖ψ‖) +
          (‖B‖ * ‖ψ‖) * (Real.exp (-q / 2) * (‖A‖ * ‖ψ‖)) := by
        gcongr <;> first | exact hnormAdj _ | exact hnorm _
      _ = _ := by ring

end TNLean.Lattice
