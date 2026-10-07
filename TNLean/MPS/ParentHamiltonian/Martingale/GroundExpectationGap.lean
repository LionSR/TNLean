/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.FiniteIntervalGapComparison
import Mathlib.Topology.Order.Basic

/-!
# Ground-space subtraction in the commutator gap estimate

For a positive finite-volume Hamiltonian \(H\) with gap \(\gamma\), a
zero-energy vector \(\psi\), and a local observable \(X\), the excitation
energy bounds
\(\gamma(\|X\psi\|^2-\|P_{\ker H}X\psi\|^2)\).
For a sequence of expanding volumes, convergence of the expectations and
vanishing of the full ground-space projection give the limiting gap bound.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947,
and the final finite-volume argument in Section 6, lines 2649--2675.

**Scope restriction (infinite-volume consequence):** The limit theorem
assumes decay of the full finite-volume ground projection. It does not yet
derive that decay from purity of a GVBS ground state, and is therefore an
intermediate assertion rather than the infinite-volume conclusion of
Theorem 1.2. The remaining argument is recorded in
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.
-/

open Filter
open scoped InnerProductSpace Topology ComplexOrder

namespace FrustrationFree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- A finite-volume gap bounds the excitation energy after subtracting
its full ground-space component. Source: Nachtergaele,
arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem energy_gap_sub_ground_projection (H : E →ₗ[ℂ] E) (hH : H.IsPositive)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hGap : ∀ v ∈ (LinearMap.ker H)ᗮ, γ * ‖v‖ ≤ ‖H v‖) (v : E) :
    γ * (‖v‖ ^ 2 - ‖(LinearMap.ker H).starProjection v‖ ^ 2) ≤
      (⟪H v, v⟫_ℂ).re := by
  have hOrder := hH.smul_orthogonal_ker_projection_le_of_norm_gap hγ hGap
  have hEnergy : γ * ‖(LinearMap.ker H)ᗮ.starProjection v‖ ^ 2 ≤
      (⟪H v, v⟫_ℂ).re := by
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      inner_sub_left, inner_smul_left, Complex.conj_ofReal, RCLike.re_eq_complex_re,
      Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, sub_nonneg,
      (show (⟪(LinearMap.ker H)ᗮ.starProjection v, v⟫_ℂ).re =
        ‖(LinearMap.ker H)ᗮ.starProjection v‖ ^ 2 from
        (LinearMap.ker H)ᗮ.re_inner_starProjection_eq_normSq v)] using
      hOrder.re_inner_nonneg_left v
  simpa only [(LinearMap.ker H).norm_sq_eq_add_norm_sq_starProjection v,
    add_sub_cancel_left] using hEnergy

/-- On a zero-energy vector, the expectation of \(X^*[H,X]\) is the
energy of \(X\psi\). Source: Nachtergaele, arXiv:cond-mat/9410110,
Section 6, lines 2657--2675. -/
theorem commutator_ground_expectation (H X : E →ₗ[ℂ] E) (ψ : E)
    (hψ : ψ ∈ LinearMap.ker H) :
    ⟪(X.adjoint.comp (H.comp X - X.comp H)) ψ, ψ⟫_ℂ =
      ⟪H (X ψ), X ψ⟫_ℂ := by
  simp only [LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.mem_ker.mp hψ, map_zero, sub_zero, LinearMap.adjoint_inner_left]

/-- The commutator excitation energy dominates \(\gamma\) times the
squared norm remaining after full ground-space projection.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem commutator_ground_gap (H X : E →ₗ[ℂ] E) (hH : H.IsPositive)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hGap : ∀ v ∈ (LinearMap.ker H)ᗮ, γ * ‖v‖ ≤ ‖H v‖)
    (ψ : E) (hψ : ψ ∈ LinearMap.ker H) :
    γ * (‖X ψ‖ ^ 2 - ‖(LinearMap.ker H).starProjection (X ψ)‖ ^ 2) ≤
      (⟪(X.adjoint.comp (H.comp X - X.comp H)) ψ, ψ⟫_ℂ).re := by
  simpa only [commutator_ground_expectation H X ψ hψ] using
    energy_gap_sub_ground_projection H hH hγ hGap (X ψ)

/-- A uniform finite-volume gap passes to the limiting commutator
expectation when the observable's full ground-space component vanishes.
The Hilbert spaces may vary with the volume. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947, and Section 6,
lines 2649--2675; the pure-GVBS projection-decay step remains separate. -/
theorem commutator_gap_of_tendsto_ground_projection_zero
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)]
    [∀ n, InnerProductSpace ℂ (F n)] [∀ n, FiniteDimensional ℂ (F n)]
    (H X : (n : ℕ) → F n →ₗ[ℂ] F n) (ψ : (n : ℕ) → F n)
    {γ e a : ℝ} (hγ : 0 ≤ γ)
    (hPos : ∀ᶠ n in atTop, (H n).IsPositive)
    (hGap : ∀ᶠ n in atTop, ∀ v ∈ (LinearMap.ker (H n))ᗮ,
      γ * ‖v‖ ≤ ‖H n v‖)
    (hGround : ∀ᶠ n in atTop, ψ n ∈ LinearMap.ker (H n))
    (hNorm : Tendsto (fun n => ‖X n (ψ n)‖ ^ 2) atTop (𝓝 a))
    (hProjection : Tendsto (fun n =>
      ‖(LinearMap.ker (H n)).starProjection (X n (ψ n))‖ ^ 2) atTop (𝓝 0))
    (hEnergy : Tendsto (fun n =>
      (⟪((X n).adjoint.comp ((H n).comp (X n) - (X n).comp (H n))) (ψ n),
        ψ n⟫_ℂ).re) atTop (𝓝 e)) : γ * a ≤ e := by
  have hLeft := (tendsto_const_nhds (x := γ) (f := (atTop : Filter ℕ))).mul
    (hNorm.sub hProjection)
  have hBound : ∀ᶠ n in atTop, γ * (‖X n (ψ n)‖ ^ 2 -
      ‖(LinearMap.ker (H n)).starProjection (X n (ψ n))‖ ^ 2) ≤
      (⟪((X n).adjoint.comp ((H n).comp (X n) - (X n).comp (H n))) (ψ n),
        ψ n⟫_ℂ).re := by
    filter_upwards [hPos, hGap, hGround] with n hnPos hnGap hnGround using
      commutator_ground_gap (H n) (X n) hnPos hγ hnGap (ψ n) hnGround
  simpa only [sub_zero] using le_of_tendsto_of_tendsto hLeft hEnergy hBound

/-- For a one-dimensional ground space generated by a unit vector, the
ground-space subtraction is the squared scalar expectation. This is the
rank-one specialization of Nachtergaele, arXiv:cond-mat/9410110, Section 6,
lines 2649--2675. -/
theorem commutator_ground_gap_of_ker_eq_span (H X : E →ₗ[ℂ] E) (hH : H.IsPositive)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hGap : ∀ v ∈ (LinearMap.ker H)ᗮ, γ * ‖v‖ ≤ ‖H v‖)
    (ψ : E) (hψ : ‖ψ‖ = 1) (hker : LinearMap.ker H = ℂ ∙ ψ) :
    γ * (‖X ψ‖ ^ 2 - ‖⟪ψ, X ψ⟫_ℂ‖ ^ 2) ≤
      (⟪(X.adjoint.comp (H.comp X - X.comp H)) ψ, ψ⟫_ℂ).re := by
  simpa only [hker, Submodule.starProjection_unit_singleton ℂ hψ, norm_smul, hψ, mul_one] using
    commutator_ground_gap H X hH hγ hGap ψ
      (by simpa only [hker] using (Submodule.mem_span_singleton_self ψ : ψ ∈ ℂ ∙ ψ))

/-- A uniform gap passes to limiting expectations when each sufficiently
large volume has a one-dimensional ground space and the observable mean
tends to zero. This is an intermediate rank-one consequence of Nachtergaele,
arXiv:cond-mat/9410110, Section 6, lines 2649--2675; finite-volume uniqueness
is an explicit hypothesis, rather than a consequence of infinite-volume purity. -/
theorem commutator_gap_of_tendsto_mean_zero_of_ker_eq_span
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)]
    [∀ n, InnerProductSpace ℂ (F n)] [∀ n, FiniteDimensional ℂ (F n)]
    (H X : (n : ℕ) → F n →ₗ[ℂ] F n) (ψ : (n : ℕ) → F n)
    {γ e a : ℝ} (hγ : 0 ≤ γ)
    (hPos : ∀ᶠ n in atTop, (H n).IsPositive)
    (hGap : ∀ᶠ n in atTop, ∀ v ∈ (LinearMap.ker (H n))ᗮ,
      γ * ‖v‖ ≤ ‖H n v‖)
    (hUnit : ∀ᶠ n in atTop, ‖ψ n‖ = 1)
    (hKernel : ∀ᶠ n in atTop, LinearMap.ker (H n) = ℂ ∙ ψ n)
    (hNorm : Tendsto (fun n => ‖X n (ψ n)‖ ^ 2) atTop (𝓝 a))
    (hMean : Tendsto (fun n => ⟪ψ n, X n (ψ n)⟫_ℂ) atTop (𝓝 0))
    (hEnergy : Tendsto (fun n =>
      (⟪((X n).adjoint.comp ((H n).comp (X n) - (X n).comp (H n))) (ψ n),
        ψ n⟫_ℂ).re) atTop (𝓝 e)) : γ * a ≤ e := by
  have hMeanNorm : Tendsto (fun n => ‖⟪ψ n, X n (ψ n)⟫_ℂ‖ ^ 2) atTop (𝓝 0) := by
    simpa only [norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using hMean.norm.pow 2
  have hLeft := (tendsto_const_nhds (x := γ) (f := (atTop : Filter ℕ))).mul
    (hNorm.sub hMeanNorm)
  have hBound : ∀ᶠ n in atTop, γ * (‖X n (ψ n)‖ ^ 2 -
      ‖⟪ψ n, X n (ψ n)⟫_ℂ‖ ^ 2) ≤
      (⟪((X n).adjoint.comp ((H n).comp (X n) - (X n).comp (H n))) (ψ n),
        ψ n⟫_ℂ).re := by
    filter_upwards [hPos, hGap, hUnit, hKernel] with n hnPos hnGap hnUnit hnKernel using
      commutator_ground_gap_of_ker_eq_span (H n) (X n) hnPos hγ hnGap (ψ n) hnUnit hnKernel
  simpa only [sub_zero] using le_of_tendsto_of_tendsto hLeft hEnergy hBound


end FrustrationFree
