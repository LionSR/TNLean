/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PowerExponential
import TNLean.Lattice.GaussianFilteredTruncationGround

/-!
# Exponential decay in the projection radius for the truncated approximation `M_i`

`TNLean.Lattice.GaussianFilteredTruncationGround` bounds the excited component of `M_i ψ`, for a
ground vector `ψ`, by `3 ‖W‖ e^{-q/2} + A N (q/ΔE) e^{v q/ΔE - μ m}` with `q` and `m` free. This
file makes the choices of the source and obtains the single exponential of eq. `facld`: fix
`μ > 0` and a constant `c₁ > 0` with `c₁ v < μ`, and at projection radius `l` take
`q = c₁ l ΔE` and `m = l - 3R`. If the number `N l` of omitted terms meeting the projection
region grows at most polynomially, `N l ≤ K_g (l + 1)^k`, then the excited component is at most
`‖W‖ (3 + C' J) e^{-l / l_fac}` times `‖ψ‖`, with `l_fac = 2 / min (c₁ ΔE) (μ - c₁ v)`.

* `exists_norm_sub_starProjection_truncated_apply_le_exp`: eq. `facld` for a ground vector.
* `exists_norm_truncated_apply_sub_inner_smul_le_exp`: the same for a unique gapped ground
  state (lines 375–387).

The module inherits the **Local fix (the truncated approximation `M_i`, eqs. `mid`, `apb`,
`truncb`):** the shell is the set of omitted terms meeting `K`, the time integral of the
Lieb–Robinson function is bounded by `T` times its value at `T`, and the constants are explicit
rather than the source's `g` and `c₁`. Documented in
`docs/paper-gaps/hastings05_truncated_dynamics.tex`.

**Scope restriction (shell growth):** the source states eq. `facld` only to order of magnitude,
with the size `N(l_proj)` of the shell implicitly subexponential on a finite-dimensional
lattice. Here the polynomial growth `N l ≤ K_g (l + 1)^k` of the number of omitted terms meeting
the projection region is an explicit hypothesis. Documented in
`docs/paper-gaps/hastings05_truncated_dynamics.tex`.

**Local fix (nonnegative interaction bound):** both theorems assume `0 ≤ J`. The source's `J`
bounds the norms of the terms, so it is nonnegative; the hypothesis matters only when there
are no terms, where `‖h k‖ ≤ J` is vacuous. Documented in
`docs/paper-gaps/hastings05_truncated_dynamics.tex`.

## References

Hastings, *Solving Gapped Hamiltonians Locally*, arXiv:cond-mat/0508554v3, `proj3new.tex`:
eq. `facld` (lines 322–348), the choice of `q` (lines 337–349), and the unique ground state
(lines 375–387).
-/

open GaussianFilter Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace Nat

namespace TNLean.Lattice

/-- The two terms of eq. `facld` at `q = c₁ l ΔE` and `m = l - 3R` decay as `e^{-δ l / 2}`,
`δ = min (c₁ ΔE) (μ - c₁ v)`, once the shell count `N` is at most `K_g (l + 1)^k`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `facld` and the choice of `q`
(lines 322–349). -/
private theorem facld_bound_le_exp {ΔE c₁ μ v B w J N Kg : ℝ} (kg l R : ℕ) (hΔE : 0 < ΔE)
    (hc₁ : 0 < c₁) (hμ : 0 ≤ μ) (hc₁v : c₁ * v < μ) (hB : 0 ≤ B) (hw : 0 ≤ w) (hJ : 0 ≤ J)
    (hN0 : 0 ≤ N) (hKg : 0 ≤ Kg) (hN : N ≤ Kg * (l + 1) ^ kg) :
    3 * w * Real.exp (-(c₁ * l * ΔE) / 2) +
        B * w * J * N * (c₁ * l * ΔE / ΔE) *
          Real.exp (v * (c₁ * l * ΔE / ΔE) - μ * (l - 3 * R : ℕ)) ≤
      w * (3 + B * Kg * c₁ * Real.exp (3 * μ * R) *
          ((kg + 1)! * Real.exp (min (c₁ * ΔE) (μ - c₁ * v) / 2) /
            (min (c₁ * ΔE) (μ - c₁ * v) / 2) ^ (kg + 1)) * J) *
        Real.exp (-(min (c₁ * ΔE) (μ - c₁ * v) / 2) * l) := by
  have hm : (l : ℝ) - 3 * R ≤ ((l - 3 * R : ℕ) : ℝ) := by
    have : l ≤ l - 3 * R + 3 * R := le_tsub_add
    rw [sub_le_iff_le_add]; exact_mod_cast this
  have hL : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  set L : ℝ := (l : ℝ)
  set m : ℝ := ((l - 3 * R : ℕ) : ℝ)
  set δ := min (c₁ * ΔE) (μ - c₁ * v) with hδdef
  have hδ : 0 < δ := lt_min (mul_pos hc₁ hΔE) (by linarith)
  set P := (kg + 1)! * Real.exp (δ / 2) / (δ / 2) ^ (kg + 1)
  have hqΔ : c₁ * L * ΔE / ΔE = c₁ * L := by field_simp
  rw [hqΔ]
  have hδL1 : δ * L ≤ c₁ * ΔE * L := mul_le_mul_of_nonneg_right (min_le_left _ _) hL
  have hδL2 : δ * L ≤ (μ - c₁ * v) * L := mul_le_mul_of_nonneg_right (min_le_right _ _) hL
  have h1 : Real.exp (-(c₁ * L * ΔE) / 2) ≤ Real.exp (-(δ / 2) * L) :=
    Real.exp_le_exp.2 (by nlinarith)
  have h2 : Real.exp (v * (c₁ * L) - μ * m) ≤ Real.exp (3 * μ * R) * Real.exp (-δ * L) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hm hμ])
  have hpoly := Real.add_one_pow_mul_le_mul_exp (half_pos hδ) kg hL
  have h3 : N * (c₁ * L) * (Real.exp (3 * μ * R) * Real.exp (-δ * L)) ≤
      Kg * c₁ * Real.exp (3 * μ * R) * P * Real.exp (-(δ / 2) * L) := by
    have hsplit : Real.exp (-(δ / 2) * L) = Real.exp (δ / 2 * L) * Real.exp (-δ * L) := by
      rw [← Real.exp_add]; ring_nf
    have hNL : N * L ≤ Kg * (P * Real.exp (δ / 2 * L)) :=
      calc N * L ≤ Kg * (L + 1) ^ kg * L := by gcongr
        _ = Kg * ((L + 1) ^ kg * L) := by ring
        _ ≤ Kg * (P * Real.exp (δ / 2 * L)) := by gcongr
    rw [hsplit]
    have := mul_le_mul_of_nonneg_right hNL
      (by positivity : 0 ≤ c₁ * Real.exp (3 * μ * R) * Real.exp (-δ * L))
    nlinarith
  have hBwJ : 0 ≤ B * w * J := by positivity
  calc 3 * w * Real.exp (-(c₁ * L * ΔE) / 2) +
        B * w * J * N * (c₁ * L) * Real.exp (v * (c₁ * L) - μ * m)
      ≤ 3 * w * Real.exp (-(δ / 2) * L) +
          B * w * J * (N * (c₁ * L) * (Real.exp (3 * μ * R) * Real.exp (-δ * L))) := by
        have hNc : 0 ≤ B * w * J * N * (c₁ * L) := by positivity
        have := mul_le_mul_of_nonneg_left h2 hNc
        nlinarith
    _ ≤ 3 * w * Real.exp (-(δ / 2) * L) +
          B * w * J * (Kg * c₁ * Real.exp (3 * μ * R) * P * Real.exp (-(δ / 2) * L)) := by
        gcongr
    _ = w * (3 + B * Kg * c₁ * Real.exp (3 * μ * R) * P * J) * Real.exp (-(δ / 2) * L) := by
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

/-- **Eq. `facld` as an exponential decay in the projection radius.** Let every eigenvalue of
`H = ∑ₖ hₖ` equal `E₀` or be at least `E₀ + ΔE`. Fix `μ > 0` and `c₁ > 0` with `c₁ v < μ`, where
`v = 2 v_R |b₀| e^{2μR} + 1`. For each projection radius `l`, let `M_l` be the truncated filter
of `W` under `H_{s l} = ∑_{k ∈ s l} hₖ` at `q = c₁ l ΔE`, where every omitted term meeting
`K l` lies at distance at least `l - 3R` from `S`, and suppose the number of such terms is at
most `K_g (l + 1)^k`. Then there is `C' ≥ 0` such that, for every `l` and every ground vector
`ψ`, the component of `M_l ψ` orthogonal to the ground eigenspace has norm at most
`‖W‖ (3 + C' J) e^{-l / l_fac} ‖ψ‖` with `l_fac = 2 / min (c₁ ΔE) (μ - c₁ v)`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `facld` (lines 322–348) with the choice
`q = c₁ l_proj ΔE` (lines 337–349). -/
theorem exists_norm_sub_starProjection_truncated_apply_le_exp [NeZero d] [DecidableEq κ]
    {ΔE : ℝ} (hΔE : 0 < ΔE) (hH : (∑ k, h k).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ j, hH.eigenvalues j = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues j) (s : ℕ → Finset κ)
    (K : ℕ → Finset ι) (hsK : ∀ l, ∀ k ∈ s l, X k ⊆ K l) (S : Finset ι) (hSK : ∀ l, S ⊆ K l)
    {W : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hW : W ∈ supportedOperators d (S : Set ι)) (J : ℝ)
    (hJ : ∀ k, ‖h k‖ ≤ J) (hJ0 : 0 ≤ J) {μ c₁ : ℝ} (hμ : 0 < μ) (hc₁ : 0 < c₁)
    (hc₁v : c₁ * (2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) < μ)
    (hm : ∀ l, ∀ k ∉ s l, ¬Disjoint (X k) (K l) → ∀ x ∈ S, ∀ y ∈ X k,
      ((l - 3 * R : ℕ) : ℕ∞) ≤ G.edist x y)
    (Kg kg : ℕ) (hN : ∀ l, ((s l)ᶜ.filter (fun k => ¬Disjoint (X k) (K l))).card ≤
      Kg * (l + 1) ^ kg) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ l : ℕ, ∀ ψ ∈ groundEigenspace (∑ k, h k) E₀,
      ‖toEuclideanLin (gaussianFilteredTerm (c₁ * l * ΔE) ΔE (∑ k ∈ s l, h k) W) ψ -
          (groundEigenspace (∑ k, h k) E₀).starProjection
            (toEuclideanLin (gaussianFilteredTerm (c₁ * l * ΔE) ΔE (∑ k ∈ s l, h k) W) ψ)‖ ≤
        ‖W‖ * (3 + C' * J) * Real.exp (-(min (c₁ * ΔE)
          (μ - c₁ * (2 * vR * |b₀| * Real.exp (2 * μ * R) + 1)) / 2) * l) * ‖ψ‖ := by
  set v := 2 * vR * |b₀| * Real.exp (2 * μ * R) + 1
  set δ := min (c₁ * ΔE) (μ - c₁ * v)
  have hδ : 0 < δ := lt_min (mul_pos hc₁ hΔE) (by linarith)
  refine ⟨2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * Kg * c₁ *
    Real.exp (3 * μ * R) * ((kg + 1)! * Real.exp (δ / 2) / (δ / 2) ^ (kg + 1)), by positivity,
    fun l ψ hψ => ?_⟩
  have hb := norm_sub_starProjection_truncated_apply_le G X a ha h hHerm hSupport R hDiam vR hCard
    b₀ hBudget (by positivity : 0 ≤ c₁ * l * ΔE) hΔE hH hgap (s l) (K l) (hsK l) S (hSK l) hW J hJ
    μ hμ.le (l - 3 * R) (hm l) hψ
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg ψ))
  exact facld_bound_le_exp kg l R hΔE hc₁ hμ.le hc₁v (by positivity) (norm_nonneg W) hJ0
    (Nat.cast_nonneg _) (Nat.cast_nonneg Kg) (by exact_mod_cast hN l)

/-- **A unique gapped ground state is exponentially close to an eigenvector of `M_l`.** If `Ω`
is a unique ground state of `H = ∑ₖ hₖ` with gap `ΔE > 0`, then under the choices and the shell
growth of `exists_norm_sub_starProjection_truncated_apply_le_exp` there is `C' ≥ 0` with
`‖M_l Ω - ⟨Ω, M_l Ω⟩ Ω‖ ≤ ‖W‖ (3 + C' J) e^{-l / l_fac}` for every `l`, where
`l_fac = 2 / min (c₁ ΔE) (μ - c₁ v)`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
eq. `facld` (lines 322–348) with `q = c₁ l_proj ΔE` (lines 337–349), in the case of one ground
state (lines 375–387). -/
theorem exists_norm_truncated_apply_sub_inner_smul_le_exp [NeZero d] [DecidableEq κ]
    {ΔE : ℝ} (hΔE : 0 < ΔE) {E₀ : ℝ} {Ω : EuclideanSpace ℂ (ι → Fin d)}
    (hgs : Matrix.IsGappedGroundState (∑ k, h k) E₀ Ω ΔE) (s : ℕ → Finset κ)
    (K : ℕ → Finset ι) (hsK : ∀ l, ∀ k ∈ s l, X k ⊆ K l) (S : Finset ι) (hSK : ∀ l, S ⊆ K l)
    {W : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hW : W ∈ supportedOperators d (S : Set ι)) (J : ℝ)
    (hJ : ∀ k, ‖h k‖ ≤ J) (hJ0 : 0 ≤ J) {μ c₁ : ℝ} (hμ : 0 < μ) (hc₁ : 0 < c₁)
    (hc₁v : c₁ * (2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) < μ)
    (hm : ∀ l, ∀ k ∉ s l, ¬Disjoint (X k) (K l) → ∀ x ∈ S, ∀ y ∈ X k,
      ((l - 3 * R : ℕ) : ℕ∞) ≤ G.edist x y)
    (Kg kg : ℕ) (hN : ∀ l, ((s l)ᶜ.filter (fun k => ¬Disjoint (X k) (K l))).card ≤
      Kg * (l + 1) ^ kg) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ l : ℕ,
      ‖toEuclideanLin (gaussianFilteredTerm (c₁ * l * ΔE) ΔE (∑ k ∈ s l, h k) W) Ω -
          ⟪Ω, toEuclideanLin (gaussianFilteredTerm (c₁ * l * ΔE) ΔE (∑ k ∈ s l, h k) W) Ω⟫_ℂ •
            Ω‖ ≤
        ‖W‖ * (3 + C' * J) * Real.exp (-(min (c₁ * ΔE)
          (μ - c₁ * (2 * vR * |b₀| * Real.exp (2 * μ * R) + 1)) / 2) * l) := by
  set v := 2 * vR * |b₀| * Real.exp (2 * μ * R) + 1
  set δ := min (c₁ * ΔE) (μ - c₁ * v)
  have hδ : 0 < δ := lt_min (mul_pos hc₁ hΔE) (by linarith)
  refine ⟨2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * Kg * c₁ *
    Real.exp (3 * μ * R) * ((kg + 1)! * Real.exp (δ / 2) / (δ / 2) ^ (kg + 1)), by positivity,
    fun l => ?_⟩
  have hb := norm_truncated_apply_sub_inner_smul_le G X a ha h hHerm hSupport R hDiam vR hCard
    b₀ hBudget (by positivity : 0 ≤ c₁ * l * ΔE) hΔE hgs (s l) (K l) (hsK l) S (hSK l) hW J hJ
    μ hμ.le (l - 3 * R) (hm l)
  refine hb.trans ?_
  exact facld_bound_le_exp kg l R hΔE hc₁ hμ.le hc₁v (by positivity) (norm_nonneg W) hJ0
    (Nat.cast_nonneg _) (Nat.cast_nonneg Kg) (by exact_mod_cast hN l)

end Graph

end TNLean.Lattice
