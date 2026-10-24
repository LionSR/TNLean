/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GaussianFilteredTermLocalization
import TNLean.Lattice.GaussianFilteredTruncation

/-!
# Ground states and the truncated approximation `M_i`

Hastings approximates the Gaussian-filtered term `H_tilde_i⁰` by the truncated filter
`M_i = gaussianFilteredTerm q ΔE H_loc H_i`. This file combines the truncation error of eq.
`apb` with the excited-component bound for the filtered term. The time window is chosen as
`T = q / ΔE`, the source's choice `T = c₁ l_proj` for `q = c₁ l_proj ΔE`, which turns the
Gaussian tail `e^{-(TΔE)²/(2q)}` into `e^{-q/2}`.

* `norm_sub_starProjection_truncated_apply_le`: eq. `facld`. For a ground vector `ψ`, the
  component of `M_i ψ` orthogonal to the ground eigenspace has norm at most
  `(3 ‖W‖ e^{-q/2} + C (q/ΔE) e^{v q/ΔE - μ m}) ‖ψ‖`.
* `norm_truncated_apply_sub_inner_smul_le`: for a unique gapped ground state `Ω`,
  `‖M_i Ω - ⟨Ω, M_i Ω⟩ Ω‖` has the same bound (lines 375–387).

The constants `C` and `v` are those of `norm_gaussianFilteredTerm_sub_truncated_le`, and the
module inherits its **Local fix (the truncated approximation `M_i`, eqs. `mid`, `apb`,
`truncb`):** the shell is the set of omitted terms meeting `K`, the time integral of the
Lieb–Robinson function is bounded by `T` times its value at `T`, and the constants are explicit
rather than the source's `g` and `c₁`. Documented in
`docs/paper-gaps/hastings05_truncated_dynamics.tex`.

Remark (not formalized): take `μ > 0` fixed, `m = l_proj - 3R` and `q = c₁ l_proj ΔE` for a
constant `0 < c₁ < μ / v`, and suppose the number `N` of omitted terms meeting `K` grows
subexponentially in `l_proj` (polynomially, for instance, when spheres have polynomial size).
Then both terms decay exponentially in `l_proj`, which is the form `J O(e^{-l_proj / l_fac})`
of eq. `facld`.

## References

Hastings, *Solving Gapped Hamiltonians Locally*, arXiv:cond-mat/0508554v3, `proj3new.tex`:
eq. `facld` and the choice of `q` (lines 322–348), and the unique ground state (lines 375–387).
-/

open GaussianFilter Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.Lattice

/-- At the time window `T = q / ΔE`, the Gaussian tail `e^{-(TΔE)²/(2q)}` is `e^{-q/2}`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, the choice `q = c₁ l_proj ΔE` at
lines 337–341, where `T = c₁ l_proj`. -/
theorem exp_neg_sq_div_eq_of_time_eq {q ΔE : ℝ} (hΔE : ΔE ≠ 0) :
    Real.exp (-(q / ΔE * ΔE) ^ 2 / (2 * q)) = Real.exp (-q / 2) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · congr 1
    rw [div_mul_cancel₀ q hΔE]
    field_simp
    ring

section Graph

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι) (ha : ∀ k, a k ∈ X k)
  (h : κ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ k, (h k).IsHermitian)
  (hSupport : ∀ k, h k ∈ supportedOperators d (X k : Set ι))
  (R : ℕ) (hDiam : ∀ k, ∀ x ∈ X k, ∀ z ∈ X k, G.edist x z ≤ R)
  (vR : ℕ) (hCard : ∀ k, (X k).card ≤ vR)
  (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ X j), ‖h j‖ ≤ b₀)

include ha hHerm hSupport hDiam hCard hBudget

/-- **The truncation error at the time window `T = q / ΔE`.** The bound of
`norm_gaussianFilteredTerm_sub_truncated_le` at `T = q / ΔE`, where the Gaussian tail is
`2 ‖W‖ e^{-q/2}`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, the bound on
`‖H_tilde_i⁰ - M_i‖` after the choice of `q` (lines 343–349). -/
theorem norm_gaussianFilteredTerm_sub_truncated_le_of_time [NeZero d] [DecidableEq κ]
    {q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE) (s : Finset κ) (K : Finset ι)
    (hsK : ∀ k ∈ s, X k ⊆ K) (S : Finset ι) (hSK : S ⊆ K)
    {W : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hW : W ∈ supportedOperators d (S : Set ι)) (J : ℝ)
    (hJ : ∀ k, ‖h k‖ ≤ J) (μ : ℝ) (hμ : 0 ≤ μ) (m : ℕ)
    (hm : ∀ k ∉ s, ¬Disjoint (X k) K → ∀ x ∈ S, ∀ y ∈ X k, (m : ℕ∞) ≤ G.edist x y) :
    ‖gaussianFilteredTerm q ΔE (∑ k, h k) W - gaussianFilteredTerm q ΔE (∑ k ∈ s, h k) W‖ ≤
      2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ * J *
          ((sᶜ.filter (fun k => ¬Disjoint (X k) K)).card : ℝ) * (q / ΔE) *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * (q / ΔE) - μ * m) +
        2 * ‖W‖ * Real.exp (-q / 2) := by
  have hb := norm_gaussianFilteredTerm_sub_truncated_le G X a ha h hHerm hSupport R hDiam vR hCard
    b₀ hBudget hq s K hsK S hSK hW J hJ μ hμ m hm (div_nonneg hq hΔE.le)
  rwa [exp_neg_sq_div_eq_of_time_eq hΔE.ne'] at hb

/-- **Eq. `facld` for the truncated approximation.** Let every eigenvalue of `H = ∑ₖ hₖ` equal
`E₀` or be at least `E₀ + ΔE`, and let `ψ` be a ground vector. For the truncated filter
`M = W_tilde_s` of `W` under `H_s = ∑_{k ∈ s} hₖ`, the component of `M ψ` orthogonal to the
ground eigenspace has norm at most `(3 ‖W‖ e^{-q/2} + C (q/ΔE) e^{v q/ΔE - μ m}) ‖ψ‖`, with the
constants of `norm_gaussianFilteredTerm_sub_truncated_le`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, eq. `facld` (lines 322–348), with `q` free and `T = q / ΔE`. -/
theorem norm_sub_starProjection_truncated_apply_le [NeZero d] [DecidableEq κ] {q ΔE : ℝ}
    (hq : 0 ≤ q) (hΔE : 0 < ΔE) (hH : (∑ k, h k).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ j, hH.eigenvalues j = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues j) (s : Finset κ)
    (K : Finset ι) (hsK : ∀ k ∈ s, X k ⊆ K) (S : Finset ι) (hSK : S ⊆ K)
    {W : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hW : W ∈ supportedOperators d (S : Set ι)) (J : ℝ)
    (hJ : ∀ k, ‖h k‖ ≤ J) (μ : ℝ) (hμ : 0 ≤ μ) (m : ℕ)
    (hm : ∀ k ∉ s, ¬Disjoint (X k) K → ∀ x ∈ S, ∀ y ∈ X k, (m : ℕ∞) ≤ G.edist x y)
    {ψ : EuclideanSpace ℂ (ι → Fin d)} (hψ : ψ ∈ groundEigenspace (∑ k, h k) E₀) :
    ‖toEuclideanLin (gaussianFilteredTerm q ΔE (∑ k ∈ s, h k) W) ψ -
        (groundEigenspace (∑ k, h k) E₀).starProjection
          (toEuclideanLin (gaussianFilteredTerm q ΔE (∑ k ∈ s, h k) W) ψ)‖ ≤
      (3 * ‖W‖ * Real.exp (-q / 2) +
        2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ * J *
          ((sᶜ.filter (fun k => ¬Disjoint (X k) K)).card : ℝ) * (q / ΔE) *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * (q / ΔE) - μ * m)) * ‖ψ‖ := by
  refine (norm_sub_starProjection_apply_le_of_gaussianFilteredTerm hq hΔE hH hgap W _ hψ).trans
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg ψ))
  have hb := norm_gaussianFilteredTerm_sub_truncated_le_of_time G X a ha h hHerm hSupport R hDiam
    vR hCard b₀ hBudget hq hΔE s K hsK S hSK hW J hJ μ hμ m hm
  linarith

/-- **A unique gapped ground state is nearly an eigenvector of `M_i`.** If `Ω` is a unique
ground state of `H = ∑ₖ hₖ` with gap `ΔE > 0`, then the truncated filter `M = W_tilde_s`
satisfies `‖M Ω - ⟨Ω, M Ω⟩ Ω‖ ≤ 3 ‖W‖ e^{-q/2} + C (q/ΔE) e^{v q/ΔE - μ m}`, with the constants
of `norm_gaussianFilteredTerm_sub_truncated_le`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, the case of one ground state (lines 375–387), with `q` free and
`T = q / ΔE`. -/
theorem norm_truncated_apply_sub_inner_smul_le [NeZero d] [DecidableEq κ] {q ΔE : ℝ}
    (hq : 0 ≤ q) (hΔE : 0 < ΔE) {E₀ : ℝ} {Ω : EuclideanSpace ℂ (ι → Fin d)}
    (hgs : IsGappedGroundState (∑ k, h k) E₀ Ω ΔE) (s : Finset κ) (K : Finset ι)
    (hsK : ∀ k ∈ s, X k ⊆ K) (S : Finset ι) (hSK : S ⊆ K)
    {W : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hW : W ∈ supportedOperators d (S : Set ι)) (J : ℝ)
    (hJ : ∀ k, ‖h k‖ ≤ J) (μ : ℝ) (hμ : 0 ≤ μ) (m : ℕ)
    (hm : ∀ k ∉ s, ¬Disjoint (X k) K → ∀ x ∈ S, ∀ y ∈ X k, (m : ℕ∞) ≤ G.edist x y) :
    ‖toEuclideanLin (gaussianFilteredTerm q ΔE (∑ k ∈ s, h k) W) Ω -
        ⟪Ω, toEuclideanLin (gaussianFilteredTerm q ΔE (∑ k ∈ s, h k) W) Ω⟫_ℂ • Ω‖ ≤
      3 * ‖W‖ * Real.exp (-q / 2) +
        2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ * J *
          ((sᶜ.filter (fun k => ¬Disjoint (X k) K)).card : ℝ) * (q / ΔE) *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * (q / ΔE) - μ * m) := by
  refine (norm_apply_sub_inner_smul_le_of_gaussianFilteredTerm hq hΔE hgs W _).trans ?_
  have hb := norm_gaussianFilteredTerm_sub_truncated_le_of_time G X a ha h hHerm hSupport R hDiam
    vR hCard b₀ hBudget hq hΔE s K hsK S hSK hW J hJ μ hμ m hm
  linarith

end Graph

end TNLean.Lattice
