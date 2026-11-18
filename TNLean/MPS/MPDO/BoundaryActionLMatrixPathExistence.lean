/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryActionLMatrixPath
import QICLean.Analysis.MatrixEvolution

/-!
# Constructing gauges for L-symbol invariance

For globally bounded continuously differentiable span generators, the
matrix ODE existence theorem constructs fundamental solutions. These
implement the L-symbol gauge law on any closed interval satisfying the
first-order symmetric-path hypotheses.

This is a scope restriction of GLM23, arXiv:2203.12563v3, Section 5.2,
line 1551: the source does not state boundedness or continuous
differentiability of the generators.
-/

open Filter Topology
open scoped Matrix BigOperators NNReal Matrix.Norms.L2Operator

namespace MPOTensor

variable {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}

variable
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  {O : ∀ a, MPOTensor d (χ a)} {A : ℝ → ∀ x, MPSTensor d (D x)}
  {VA : ℝ → ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ}
  {WA : ℝ → ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ}

/-- **Scope restriction (bounded continuously differentiable generators):**
The L-symbol gauge class is constant, with the fundamental gauges
constructed rather than assumed. All generators are defined on the real
line, continuously differentiable, and uniformly bounded (with a bound
allowed to depend on the multiplicity space). The tensor-path assumptions
are needed only near the chosen closed interval.

This supplies an existence-based version of the integration of GLM23,
`REsubmission.tex`, lines 1387--1551. The additional regularity and
boundedness assumptions are absent from the source; see
`docs/paper-gaps/glm23_mpo_symmetric_mps_scope.tex`. -/
theorem exists_actionLMatrix_gaugeEquiv_of_contDiff
    (hF : ∀ a b,
      MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
        (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
    {α β γ₀ : ℝ} (hγ₀ : γ₀ ∈ Set.Icc α β)
    (hA : ∀ t ∈ Set.Icc α β, ∀ᶠ γ in 𝓝 t, ∀ a x,
      MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A γ x))
        (fun q : (y : Fin s) × Fin (M a x y) ↦ A γ q.1)
        (fun q ↦ VA γ a x q.1 q.2) (fun q ↦ WA γ a x q.1 q.2))
    (hInj : ∀ t ∈ Set.Icc α β, ∀ᶠ γ in 𝓝 t, ∀ x, Kraus.IsInjective (A γ x))
    (hne : ∀ t ∈ Set.Icc α β, ∀ᶠ γ in 𝓝 t, MPSTensor.BlocksNotGaugePhaseEquiv (A γ))
    (hD : ∀ x, 0 < D x)
    (X : ℝ → ∀ a x y, Matrix (Fin (M a x y)) (Fin (M a x y)) ℂ)
    (hX : ∀ a x y, ContDiff ℝ 1 (fun t ↦ X t a x y))
    (hbound : ∀ a x y, ∃ C : ℝ≥0, ∀ t, ‖X t a x y‖ ≤ C)
    (hdV : ∀ t ∈ Set.Icc α β, ∀ a x y i u v,
      HasDerivAt (fun γ ↦ VA γ a x y i u v)
        ((∑ i', X t a x y i i' • VA t a x y i') u v) t) :
    ∃ g : ℝ → ∀ a x y, Matrix (Fin (M a x y)) (Fin (M a x y)) ℂ,
      (∀ a x y, g γ₀ a x y = 1) ∧
      (∀ t a x y, HasDerivAt (fun u ↦ g u a x y) (X t a x y * g t a x y) t) ∧
      ∀ t ∈ Set.Icc α β,
        (∀ a x y, IsUnit (g t a x y)) ∧
          ∀ (a b c : Fin r) (x y z : Fin s) (i : Fin (M a z y)) (j : Fin (M b x z))
            (k : Fin (M c x y)) (μ : Fin (N a b c)),
            actionLMatrix WF (VA t) (WA t) a b x y ⟨z, i, j⟩ ⟨c, k, μ⟩ =
              ∑ i', ∑ j', ∑ k', g t a z y i i' * g t b x z j j' * (g t c x y)⁻¹ k' k *
                actionLMatrix WF (VA γ₀) (WA γ₀) a b x y ⟨z, i', j'⟩ ⟨c, k', μ⟩ := by
  have hex (a : Fin r) (x y : Fin s) :
      ∃ U : ℝ → Matrix (Fin (M a x y)) (Fin (M a x y)) ℂ,
        U 0 = 1 ∧ ∀ t, HasDerivAt U (X (γ₀ + t) a x y * U t) t := by
    obtain ⟨C, hC⟩ := hbound a x y
    exact MatrixEvolution.exists_solution (fun t ↦ X (γ₀ + t) a x y)
      ((hX a x y).comp (contDiff_const.add contDiff_id)) C (fun t ↦ hC (γ₀ + t)) 1
  choose U hU₀ hU using hex
  let g : ℝ → ∀ a x y, Matrix (Fin (M a x y)) (Fin (M a x y)) ℂ :=
    fun t a x y ↦ U a x y (t - γ₀)
  have hg₀ (a : Fin r) (x y : Fin s) : g γ₀ a x y = 1 := by
    simp only [g, sub_self, hU₀]
  have hg (t : ℝ) (a : Fin r) (x y : Fin s) :
      HasDerivAt (fun u ↦ g u a x y) (X t a x y * g t a x y) t := by
    have hshift : γ₀ + (t - γ₀) = t := by ring
    simpa only [g, Function.comp_def, id_eq, hshift, one_smul] using
      (hU a x y (t - γ₀)).scomp t ((hasDerivAt_id t).sub_const γ₀)
  refine ⟨g, hg₀, hg, fun t ht ↦ ?_⟩
  exact actionLMatrix_gaugeEquiv_of_continuous VF WF hF hγ₀ hA hInj hne hD X g
    (fun a x y ↦ (hX a x y).continuous.continuousOn) hdV hg₀
    (fun u _ a x y i j ↦ hasDerivAt_pi.mp (hasDerivAt_pi.mp (hg u a x y) i) j) ht

end MPOTensor
