/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TNLean.MPS.ParentHamiltonian.Martingale.AbstractCriterion
import TNLean.MPS.ParentHamiltonian.Martingale.AnalyticBounds
import TNLean.MPS.ParentHamiltonian.Martingale.MovingWindowCount
import TNLean.MPS.ParentHamiltonian.Martingale.ProjectionCancellation

/-!
# Full-range form of Nachtergaele's C1--C3 energy estimate

This file follows the summation in the proof of Theorem 2.1(i) in Nachtergaele,
arXiv:cond-mat/9410110, lines 1195--1259.

**Scope restriction (full finite range):** Conditions C2 and C3 in the source
are assumed only beyond their lower threshold \(n_l\), while C1 starts at the
corresponding window length; the printed proof nevertheless estimates every
martingale difference \(E_0,\ldots,E_{N-1}\). The theorem below instead assumes
the three estimates on the entire finite range. This extra hypothesis and the
required lower-endpoint repair are recorded in
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`. Thus the result is a
full-range version with the source coefficient, not a formalization of the
unrestricted source theorem.

**Local fix (zero C3 constant):** The source chooses
\(c_2=\epsilon_l/\sqrt{l+1}\) after requiring \(c_2>0\). When
\(\epsilon_l=0\), the proof below instead uses \(Q_nE_n=0\) and omits the
second weighted estimate. This zero-constant repair is recorded in the same
paper-gap note.
-/

open scoped BigOperators InnerProductSpace

namespace FrustrationFree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An energy lower bound on a subspace implies the corresponding norm
lower bound there. This is the direct Cauchy--Schwarz conversion and requires
neither finite dimensionality nor positivity of the operator. -/
theorem norm_lower_bound_of_energy_lower_bound
    {γ : ℝ} {H : E →ₗ[ℂ] E}
    (hEnergy : ∀ v ∈ (LinearMap.ker H)ᗮ,
      γ * ‖v‖ ^ 2 ≤ (⟪H v, v⟫_ℂ).re) :
    ∀ v ∈ (LinearMap.ker H)ᗮ, γ * ‖v‖ ≤ ‖H v‖ := by
  intro v hv
  have henergy := hEnergy v hv
  have hcauchy : (⟪H v, v⟫_ℂ).re ≤ ‖H v‖ * ‖v‖ :=
    re_inner_le_norm (𝕜 := ℂ) (H v) v
  by_cases hvzero : ‖v‖ = 0
  · simp [hvzero]
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hvzero)
    nlinarith

private theorem operator_inequality_of_energy_lower_bound
    [FiniteDimensional ℂ E] {γ : ℝ} (hγ : 0 < γ) {H : E →ₗ[ℂ] E}
    (hH : H.IsPositive)
    (hEnergy : ∀ v ∈ (LinearMap.ker H)ᗮ,
      γ * ‖v‖ ^ 2 ≤ (⟪H v, v⟫_ℂ).re) :
    ∀ v, γ * (⟪H v, v⟫_ℂ).re ≤ (⟪H v, H v⟫_ℂ).re := by
  classical
  intro v
  let p := (LinearMap.ker H).starProjection v
  let w := v - p
  have hp_mem : p ∈ LinearMap.ker H :=
    Submodule.starProjection_apply_mem (LinearMap.ker H) v
  have hHp : H p = 0 := LinearMap.mem_ker.mp hp_mem
  have hw : w ∈ (LinearMap.ker H)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal v
  have hv_eq : v = w + p := by
    dsimp only [w]
    abel
  have hHw : H w = H v := by
    simp only [w, map_sub, hHp, sub_zero]
  have hcross : ⟪H v, p⟫_ℂ = 0 := by
    rw [hH.isSymmetric v p, hHp, inner_zero_right]
  have hform : (⟪H v, v⟫_ℂ).re = (⟪H w, w⟫_ℂ).re := by
    calc
      (⟪H v, v⟫_ℂ).re = (⟪H v, w + p⟫_ℂ).re := by rw [← hv_eq]
      _ = (⟪H v, w⟫_ℂ + ⟪H v, p⟫_ℂ).re := by rw [inner_add_right]
      _ = (⟪H v, w⟫_ℂ).re := by rw [hcross, add_zero]
      _ = (⟪H w, w⟫_ℂ).re := by rw [hHw]
  have hgapnorm := norm_lower_bound_of_energy_lower_bound hEnergy w hw
  rw [hHw] at hgapnorm
  have hcauchy : (⟪H v, v⟫_ℂ).re ≤ ‖H v‖ * ‖w‖ := by
    rw [hform]
    calc
      (⟪H w, w⟫_ℂ).re ≤ ‖H w‖ * ‖w‖ :=
        re_inner_le_norm (𝕜 := ℂ) (H w) w
      _ = ‖H v‖ * ‖w‖ := by rw [hHw]
  calc
    γ * (⟪H v, v⟫_ℂ).re ≤ γ * (‖H v‖ * ‖w‖) :=
      mul_le_mul_of_nonneg_left hcauchy hγ.le
    _ = (γ * ‖w‖) * ‖H v‖ := by ring
    _ ≤ ‖H v‖ * ‖H v‖ :=
      mul_le_mul_of_nonneg_right hgapnorm (norm_nonneg (H v))
    _ = ‖H v‖ ^ 2 := by ring
    _ = (⟪H v, H v⟫_ℂ).re :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) (H v)).symm

namespace NestedGroundProjections

private theorem enpsi_identity
    (G : NestedGroundProjections (E := E)) (Q : ℕ → E →ₗ[ℂ] E)
    (N n l : ℕ) (hn : n < N) (v : E)
    (hzero : G.projection 0 = LinearMap.id)
    (hv : v ∈ (LinearMap.range (G.projection N))ᗮ)
    (hQ : (Q n).IsSymmetricProjection)
    (hcomm : ∀ m, m < n - l ∨ n < m →
      (G.martingaleDifference m).comp (Q n) =
        (Q n).comp (G.martingaleDifference m)) :
    ‖G.martingaleDifference n v‖ ^ 2 =
      (⟪((LinearMap.id : E →ₗ[ℂ] E) - Q n) v,
        G.martingaleDifference n v⟫_ℂ).re +
      (⟪∑ m ∈ Finset.Icc (n - l) n, G.martingaleDifference m v,
        Q n (G.martingaleDifference n v)⟫_ℂ).re := by
  let En := G.martingaleDifference n
  let T := (LinearMap.id : E →ₗ[ℂ] E) - Q n
  let q := Q n (En v)
  let w := ∑ m ∈ Finset.Icc (n - l) n, G.martingaleDifference m v
  have hEn : En.IsSymmetricProjection :=
    G.martingaleDifference_isSymmetricProjection n
  have hT : T.IsSymmetric := LinearMap.IsSymmetric.id.sub hQ.isSymmetric
  have hEnEn : En (En v) = En v := by
    have h := congrArg (fun S : E →ₗ[ℂ] E ↦ S v) hEn.isIdempotentElem.eq
    simpa [Module.End.mul_apply] using h
  have hself : (⟪v, En v⟫_ℂ).re = ‖En v‖ ^ 2 := by
    calc
      (⟪v, En v⟫_ℂ).re = (⟪v, En (En v)⟫_ℂ).re := by rw [hEnEn]
      _ = (⟪En v, En v⟫_ℂ).re := by rw [← hEn.isSymmetric v (En v)]
      _ = ‖En v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) (En v)
  have hcross : ⟪v, q⟫_ℂ = ⟪w, q⟫_ℂ := by
    have hresolve :=
      G.sum_martingaleDifference_apply_of_mem_orthogonal N v hzero hv
    have hcancel :=
      G.inner_sum_martingaleDifference_localProjection_eq_inner_sum_Icc
        (Q n) N n l hn hcomm v
    calc
      ⟪v, q⟫_ℂ =
          ⟪∑ m ∈ Finset.range N, G.martingaleDifference m v, q⟫_ℂ := by
            rw [hresolve]
      _ = ⟪v, ∑ m ∈ Finset.range N,
          G.martingaleDifference m q⟫_ℂ := by
            simp_rw [sum_inner, inner_sum]
            apply Finset.sum_congr rfl
            intro m _
            exact (G.martingaleDifference_isSymmetricProjection m).isSymmetric v q
      _ = ⟪w, q⟫_ℂ := hcancel
  have hsplit : (⟪v, En v⟫_ℂ).re =
      (⟪T v, En v⟫_ℂ).re + (⟪w, q⟫_ℂ).re := by
    have hsplitComplex : ⟪v, En v⟫_ℂ = ⟪T v, En v⟫_ℂ + ⟪w, q⟫_ℂ := by
      calc
        ⟪v, En v⟫_ℂ = ⟪v, T (En v) + q⟫_ℂ := by
          simp [T, q, En]
        _ = ⟪v, T (En v)⟫_ℂ + ⟪v, q⟫_ℂ := inner_add_right _ _ _
        _ = ⟪T v, En v⟫_ℂ + ⟪w, q⟫_ℂ := by
          rw [← hT v (En v), hcross]
    simpa using congrArg Complex.re hsplitComplex
  dsimp only [En, T, q, w] at hself hsplit ⊢
  exact hself ▸ hsplit

private theorem enpsi2
    (G : NestedGroundProjections (E := E)) (Q : ℕ → E →ₗ[ℂ] E)
    (N n l : ℕ) (hn : n < N) (v : E)
    (hzero : G.projection 0 = LinearMap.id)
    (hv : v ∈ (LinearMap.range (G.projection N))ᗮ)
    (hQ : (Q n).IsSymmetricProjection)
    (hcomm : ∀ m, m < n - l ∨ n < m →
      (G.martingaleDifference m).comp (Q n) =
        (Q n).comp (G.martingaleDifference m))
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ‖G.martingaleDifference n v‖ ^ 2 ≤
      (1 / (2 * c₁)) * ‖((LinearMap.id : E →ₗ[ℂ] E) - Q n) v‖ ^ 2 +
        (c₁ / 2) * ‖G.martingaleDifference n v‖ ^ 2 +
      (1 / (2 * c₂)) * ‖Q n (G.martingaleDifference n v)‖ ^ 2 +
        (c₂ / 2) *
          ‖∑ m ∈ Finset.Icc (n - l) n, G.martingaleDifference m v‖ ^ 2 := by
  have hid := enpsi_identity G Q N n l hn v hzero hv hQ hcomm
  have hfirst := re_inner_le_weighted_norm_sq
    (((LinearMap.id : E →ₗ[ℂ] E) - Q n) v)
    (G.martingaleDifference n v) hc₁
  have hsecond := re_inner_le_weighted_norm_sq
    (Q n (G.martingaleDifference n v))
    (∑ m ∈ Finset.Icc (n - l) n, G.martingaleDifference m v) hc₂
  have hre :
      (⟪Q n (G.martingaleDifference n v),
        ∑ m ∈ Finset.Icc (n - l) n, G.martingaleDifference m v⟫_ℂ).re =
      (⟪∑ m ∈ Finset.Icc (n - l) n, G.martingaleDifference m v,
        Q n (G.martingaleDifference n v)⟫_ℂ).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  rw [hre] at hsecond
  linarith

private theorem enpsi2_of_c2_c3
    (G : NestedGroundProjections (E := E)) (Q : ℕ → E →ₗ[ℂ] E)
    (localHamiltonian : ℕ → E →ₗ[ℂ] E)
    (N n l : ℕ) (hn : n < N) (v : E)
    (hzero : G.projection 0 = LinearMap.id)
    (hv : v ∈ (LinearMap.range (G.projection N))ᗮ)
    (hQ : (Q n).IsSymmetricProjection)
    (hcomm : ∀ m, m < n - l ∨ n < m →
      (G.martingaleDifference m).comp (Q n) =
        (Q n).comp (G.martingaleDifference m))
    {γ ε c₁ c₂ : ℝ} (hγ : 0 < γ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hC2 : γ * ‖((LinearMap.id : E →ₗ[ℂ] E) - Q n) v‖ ^ 2 ≤
      (⟪localHamiltonian n v, v⟫_ℂ).re)
    (hC3 : ‖Q n (G.martingaleDifference n v)‖ ^ 2 ≤
      ε ^ 2 * ‖G.martingaleDifference n v‖ ^ 2) :
    ‖G.martingaleDifference n v‖ ^ 2 ≤
      (1 / (2 * c₁ * γ)) * (⟪localHamiltonian n v, v⟫_ℂ).re +
      (c₁ / 2 + ε ^ 2 / (2 * c₂)) *
        ‖G.martingaleDifference n v‖ ^ 2 +
      (c₂ / 2) *
        ‖∑ m ∈ Finset.Icc (n - l) n, G.martingaleDifference m v‖ ^ 2 := by
  have hbase := enpsi2 G Q N n l hn v hzero hv hQ hcomm hc₁ hc₂
  have hC2' :
      (1 / (2 * c₁)) *
          ‖((LinearMap.id : E →ₗ[ℂ] E) - Q n) v‖ ^ 2 ≤
        (1 / (2 * c₁ * γ)) * (⟪localHamiltonian n v, v⟫_ℂ).re := by
    calc
      (1 / (2 * c₁)) *
          ‖((LinearMap.id : E →ₗ[ℂ] E) - Q n) v‖ ^ 2 =
          (1 / (2 * c₁ * γ)) *
            (γ * ‖((LinearMap.id : E →ₗ[ℂ] E) - Q n) v‖ ^ 2) := by
              field_simp [hc₁.ne', hγ.ne']
      _ ≤ (1 / (2 * c₁ * γ)) * (⟪localHamiltonian n v, v⟫_ℂ).re :=
        mul_le_mul_of_nonneg_left hC2 (by positivity)
  have hC3' :
      (1 / (2 * c₂)) * ‖Q n (G.martingaleDifference n v)‖ ^ 2 ≤
        (1 / (2 * c₂)) *
          (ε ^ 2 * ‖G.martingaleDifference n v‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hC3 (by positivity)
  calc
    ‖G.martingaleDifference n v‖ ^ 2 ≤
        (1 / (2 * c₁)) *
            ‖((LinearMap.id : E →ₗ[ℂ] E) - Q n) v‖ ^ 2 +
          (c₁ / 2) * ‖G.martingaleDifference n v‖ ^ 2 +
        (1 / (2 * c₂)) * ‖Q n (G.martingaleDifference n v)‖ ^ 2 +
          (c₂ / 2) *
            ‖∑ m ∈ Finset.Icc (n - l) n,
              G.martingaleDifference m v‖ ^ 2 := hbase
    _ ≤ (1 / (2 * c₁ * γ)) * (⟪localHamiltonian n v, v⟫_ℂ).re +
        (c₁ / 2 + ε ^ 2 / (2 * c₂)) *
          ‖G.martingaleDifference n v‖ ^ 2 +
        (c₂ / 2) *
          ‖∑ m ∈ Finset.Icc (n - l) n,
            G.martingaleDifference m v‖ ^ 2 := by
      calc
        _ ≤ (1 / (2 * c₁ * γ)) * (⟪localHamiltonian n v, v⟫_ℂ).re +
            (c₁ / 2) * ‖G.martingaleDifference n v‖ ^ 2 +
          (1 / (2 * c₂)) *
            (ε ^ 2 * ‖G.martingaleDifference n v‖ ^ 2) +
            (c₂ / 2) *
              ‖∑ m ∈ Finset.Icc (n - l) n,
                G.martingaleDifference m v‖ ^ 2 := by linarith
        _ = _ := by ring

private theorem enpsi_of_c2_c3_zero
    (G : NestedGroundProjections (E := E)) (Q : ℕ → E →ₗ[ℂ] E)
    (localHamiltonian : ℕ → E →ₗ[ℂ] E)
    (N n l : ℕ) (hn : n < N) (v : E)
    (hzero : G.projection 0 = LinearMap.id)
    (hv : v ∈ (LinearMap.range (G.projection N))ᗮ)
    (hQ : (Q n).IsSymmetricProjection)
    (hcomm : ∀ m, m < n - l ∨ n < m →
      (G.martingaleDifference m).comp (Q n) =
        (Q n).comp (G.martingaleDifference m))
    {γ c₁ : ℝ} (hγ : 0 < γ) (hc₁ : 0 < c₁)
    (hC2 : γ * ‖((LinearMap.id : E →ₗ[ℂ] E) - Q n) v‖ ^ 2 ≤
      (⟪localHamiltonian n v, v⟫_ℂ).re)
    (hqzero : Q n (G.martingaleDifference n v) = 0) :
    ‖G.martingaleDifference n v‖ ^ 2 ≤
      (1 / (2 * c₁ * γ)) * (⟪localHamiltonian n v, v⟫_ℂ).re +
      (c₁ / 2) * ‖G.martingaleDifference n v‖ ^ 2 := by
  have hid := enpsi_identity G Q N n l hn v hzero hv hQ hcomm
  rw [hqzero, inner_zero_right, Complex.zero_re, add_zero] at hid
  have hfirst := re_inner_le_weighted_norm_sq
    (((LinearMap.id : E →ₗ[ℂ] E) - Q n) v)
    (G.martingaleDifference n v) hc₁
  have hC2' :
      (1 / (2 * c₁)) *
          ‖((LinearMap.id : E →ₗ[ℂ] E) - Q n) v‖ ^ 2 ≤
        (1 / (2 * c₁ * γ)) * (⟪localHamiltonian n v, v⟫_ℂ).re := by
    calc
      (1 / (2 * c₁)) *
          ‖((LinearMap.id : E →ₗ[ℂ] E) - Q n) v‖ ^ 2 =
          (1 / (2 * c₁ * γ)) *
            (γ * ‖((LinearMap.id : E →ₗ[ℂ] E) - Q n) v‖ ^ 2) := by
              field_simp [hc₁.ne', hγ.ne']
      _ ≤ (1 / (2 * c₁ * γ)) * (⟪localHamiltonian n v, v⟫_ℂ).re :=
        mul_le_mul_of_nonneg_left hC2 (by positivity)
  linarith

/-- Full-range form of the summation in Nachtergaele's Theorem 2.1(i), in the
finite-filtration notation of its proof (arXiv:cond-mat/9410110, lines
1195--1259). Conditions C1 and C2 are stated as their quadratic-form
inequalities, and C3 is the source's literal operator-norm bound
\(\lVert Q_nE_n\rVert\leq\epsilon_l\).  The coefficient is exactly
\(\frac{\gamma_{l+1}}{d_{l+1}}
  (1-\epsilon_l\sqrt{l+1})^2\).

The finite sum runs over every index \(n=0,\ldots,N-1\), with only
\(G_0=\mathbf 1\) needed for the martingale resolution. Thus C1, C2, and C3
are assumed on that full finite range, which is stronger than the source's
lower-threshold hypotheses. The case \(\epsilon_l=0\) is treated separately,
since the printed choice \(c_2=\epsilon_l/\sqrt{l+1}\) is then not positive.
The proof uses the upper inequality in C1; its nonnegativity clause is retained
because it is part of the source's condition C1. -/
theorem energy_lower_bound_of_nachtergaele_c1_c3_full_range
    [FiniteDimensional ℂ E]
    (G : NestedGroundProjections (E := E)) (Q : ℕ → E →ₗ[ℂ] E)
    (localHamiltonian : ℕ → E →ₗ[ℂ] E) (H : E →ₗ[ℂ] E)
    (N l : ℕ) (v : E)
    (hzero : G.projection 0 = LinearMap.id)
    (hv : v ∈ (LinearMap.range (G.projection N))ᗮ)
    {γ d ε : ℝ} (hγ : 0 < γ) (hd : 0 < d) (hε : 0 ≤ ε)
    (hεlt : ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ))
    (hQ : ∀ n ∈ Finset.range N, (Q n).IsSymmetricProjection)
    (hcomm : ∀ n ∈ Finset.range N, ∀ m,
      m < n - l ∨ n < m →
        (G.martingaleDifference m).comp (Q n) =
          (Q n).comp (G.martingaleDifference m))
    (hC1 : ∀ x,
      0 ≤ ∑ n ∈ Finset.range N,
          (⟪localHamiltonian n x, x⟫_ℂ).re ∧
      (∑ n ∈ Finset.range N,
          (⟪localHamiltonian n x, x⟫_ℂ).re) ≤
        d * (⟪H x, x⟫_ℂ).re)
    (hC2 : ∀ n ∈ Finset.range N, ∀ x,
      γ * ‖((LinearMap.id : E →ₗ[ℂ] E) - Q n) x‖ ^ 2 ≤
        (⟪localHamiltonian n x, x⟫_ℂ).re)
    (hC3 : ∀ n ∈ Finset.range N,
      ‖(Q n).toContinuousLinearMap.comp
          (G.martingaleDifference n).toContinuousLinearMap‖ ≤ ε) :
    (γ / d) * (1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2 * ‖v‖ ^ 2 ≤
      (⟪H v, v⟫_ℂ).re := by
  have hactiveNorm :
      ∑ n ∈ Finset.range N, ‖G.martingaleDifference n v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← G.norm_sq_eq_sum_martingaleDifference_of_mem_orthogonal N v hzero hv]
  have hwindow :
      ∑ n ∈ Finset.range N,
          ‖∑ m ∈ Finset.Icc (n - l) n, G.martingaleDifference m v‖ ^ 2 ≤
        (l + 1) * ‖v‖ ^ 2 := by
    calc
      ∑ n ∈ Finset.range N,
          ‖∑ m ∈ Finset.Icc (n - l) n, G.martingaleDifference m v‖ ^ 2 =
          ∑ n ∈ Finset.range N, ∑ m ∈ Finset.Icc (n - l) n,
            ‖G.martingaleDifference m v‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro n _
              exact G.norm_sq_sum_martingaleDifference_finset
                (Finset.Icc (n - l) n) v
      _ ≤ (l + 1) *
          ∑ m ∈ Finset.range N, ‖G.martingaleDifference m v‖ ^ 2 :=
        movingWindow_sum_range_le
          (fun m ↦ ‖G.martingaleDifference m v‖ ^ 2) l N
          (fun m ↦ sq_nonneg ‖G.martingaleDifference m v‖)
      _ = (l + 1) * ‖v‖ ^ 2 := by rw [hactiveNorm]
  let s := Real.sqrt ((l + 1 : ℕ) : ℝ)
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hsquare : s ^ 2 = ((l + 1 : ℕ) : ℝ) := by
    exact Real.sq_sqrt (by positivity)
  have hεs : ε * s < 1 := by
    rw [lt_div_iff₀ hs] at hεlt
    exact hεlt
  have hδ : 0 < 1 - ε * s := sub_pos.mpr hεs
  have hC3point : ∀ n ∈ Finset.range N, ∀ x,
      ‖Q n (G.martingaleDifference n x)‖ ^ 2 ≤
        ε ^ 2 * ‖G.martingaleDifference n x‖ ^ 2 := by
    intro n hn x
    simpa using norm_sq_apply_projection_le_of_norm_comp_le
      (Q n).toContinuousLinearMap
      (G.martingaleDifference n).toContinuousLinearMap
      (G.martingaleDifference_isSymmetricProjection n) (hC3 n hn) x
  rcases hε.eq_or_lt with hεzero | hεpos
  · subst ε
    have hpoint : ∀ n ∈ Finset.range N,
        ‖G.martingaleDifference n v‖ ^ 2 ≤
          (1 / (2 * γ)) * (⟪localHamiltonian n v, v⟫_ℂ).re +
            (1 / 2) * ‖G.martingaleDifference n v‖ ^ 2 := by
      intro n hn
      have hbound : ‖Q n (G.martingaleDifference n v)‖ ^ 2 ≤ 0 := by
        simpa using hC3point n hn v
      have hqnorm : ‖Q n (G.martingaleDifference n v)‖ ^ 2 = 0 :=
        le_antisymm hbound (sq_nonneg _)
      have hqzero : Q n (G.martingaleDifference n v) = 0 := by
        rw [← norm_eq_zero]
        nlinarith [sq_nonneg ‖Q n (G.martingaleDifference n v)‖]
      simpa using enpsi_of_c2_c3_zero G Q localHamiltonian N n l
        (Finset.mem_range.mp hn) v
        hzero hv (hQ n hn) (hcomm n hn) hγ (by norm_num : (0 : ℝ) < 1)
        (hC2 n hn v) hqzero
    have hsumPoint := Finset.sum_le_sum fun n hn ↦ hpoint n hn
    have hsumPoint' : ‖v‖ ^ 2 ≤
        (1 / (2 * γ)) *
            (∑ n ∈ Finset.range N, (⟪localHamiltonian n v, v⟫_ℂ).re) +
          (1 / 2) * ‖v‖ ^ 2 := by
      simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, hactiveNorm] using hsumPoint
    have henergy :
        (1 / (2 * γ)) *
            (∑ n ∈ Finset.range N, (⟪localHamiltonian n v, v⟫_ℂ).re) ≤
          (1 / (2 * γ)) * (d * (⟪H v, v⟫_ℂ).re) :=
      mul_le_mul_of_nonneg_left (hC1 v).2 (by positivity)
    have hhalf : (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
        (1 / (2 * γ)) * (d * (⟪H v, v⟫_ℂ).re) := by
      linarith
    calc
      (γ / d) * (1 - 0 * s) ^ 2 * ‖v‖ ^ 2 =
          (2 * γ / d) * ((1 / 2 : ℝ) * ‖v‖ ^ 2) := by ring
      _ ≤ (2 * γ / d) *
          ((1 / (2 * γ)) * (d * (⟪H v, v⟫_ℂ).re)) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
      _ = (⟪H v, v⟫_ℂ).re := by
        field_simp [hγ.ne', hd.ne']
  · let c₁ := 1 - ε * s
    let c₂ := ε / s
    have hc₁ : 0 < c₁ := hδ
    have hc₂ : 0 < c₂ := div_pos hεpos hs
    have hεc₂ : ε ^ 2 / (2 * c₂) = ε * s / 2 := by
      dsimp only [c₂]
      field_simp [hεpos.ne', hs.ne']
    have hc₂window : (c₂ / 2) * ((l + 1 : ℕ) : ℝ) = ε * s / 2 := by
      dsimp only [c₂]
      rw [← hsquare]
      field_simp [hs.ne']
    have hpoint : ∀ n ∈ Finset.range N,
        ‖G.martingaleDifference n v‖ ^ 2 ≤
          (1 / (2 * c₁ * γ)) * (⟪localHamiltonian n v, v⟫_ℂ).re +
          (c₁ / 2 + ε * s / 2) * ‖G.martingaleDifference n v‖ ^ 2 +
          (c₂ / 2) *
            ‖∑ m ∈ Finset.Icc (n - l) n,
              G.martingaleDifference m v‖ ^ 2 := by
      intro n hn
      simpa only [hεc₂] using
        enpsi2_of_c2_c3 G Q localHamiltonian N n l
          (Finset.mem_range.mp hn) v hzero hv
          (hQ n hn) (hcomm n hn) hγ hc₁ hc₂ (hC2 n hn v) (hC3point n hn v)
    have hsumPoint := Finset.sum_le_sum fun n hn ↦ hpoint n hn
    have hsumPoint' : ‖v‖ ^ 2 ≤
        (1 / (2 * c₁ * γ)) *
            (∑ n ∈ Finset.range N, (⟪localHamiltonian n v, v⟫_ℂ).re) +
        (c₁ / 2 + ε * s / 2) * ‖v‖ ^ 2 +
        (c₂ / 2) *
          (∑ n ∈ Finset.range N,
            ‖∑ m ∈ Finset.Icc (n - l) n,
              G.martingaleDifference m v‖ ^ 2) := by
      simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, hactiveNorm] using hsumPoint
    have henergy :
        (1 / (2 * c₁ * γ)) *
            (∑ n ∈ Finset.range N, (⟪localHamiltonian n v, v⟫_ℂ).re) ≤
          (1 / (2 * c₁ * γ)) * (d * (⟪H v, v⟫_ℂ).re) :=
      mul_le_mul_of_nonneg_left (hC1 v).2 (by positivity)
    have hwindow' :
        (c₂ / 2) *
            (∑ n ∈ Finset.range N,
              ‖∑ m ∈ Finset.Icc (n - l) n,
                G.martingaleDifference m v‖ ^ 2) ≤
          (ε * s / 2) * ‖v‖ ^ 2 := by
      calc
        _ ≤ (c₂ / 2) * ((l + 1) * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hwindow (by positivity)
        _ = ((c₂ / 2) * ((l + 1 : ℕ) : ℝ)) * ‖v‖ ^ 2 := by
          push_cast
          ring
        _ = (ε * s / 2) * ‖v‖ ^ 2 := by rw [hc₂window]
    have hhalf : (c₁ / 2) * ‖v‖ ^ 2 ≤
        (1 / (2 * c₁ * γ)) * (d * (⟪H v, v⟫_ℂ).re) := by
      dsimp only [c₁]
      dsimp only [c₁] at hsumPoint' henergy
      linarith
    calc
      (γ / d) * (1 - ε * s) ^ 2 * ‖v‖ ^ 2 =
          (2 * (1 - ε * s) * γ / d) *
            (((1 - ε * s) / 2) * ‖v‖ ^ 2) := by ring
      _ ≤ (2 * (1 - ε * s) * γ / d) *
          ((1 / (2 * (1 - ε * s) * γ)) *
            (d * (⟪H v, v⟫_ℂ).re)) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
      _ = (⟪H v, v⟫_ℂ).re := by
        field_simp [hδ.ne', hγ.ne', hd.ne']

/-- Norm-gap form of the full-range C1--C3 estimate above. The ground-space
identity identifies the last filtration range with the kernel of the positive
Hamiltonian. The energy estimate and Cauchy--Schwarz supply the global
quadratic-form hypothesis used by
`spectralGap_of_martingale_of_finiteDimensional`. -/
theorem norm_lower_bound_of_nachtergaele_c1_c3_full_range
    [FiniteDimensional ℂ E]
    (G : NestedGroundProjections (E := E)) (Q : ℕ → E →ₗ[ℂ] E)
    (localHamiltonian : ℕ → E →ₗ[ℂ] E) (H : E →ₗ[ℂ] E)
    (N l : ℕ)
    (hzero : G.projection 0 = LinearMap.id)
    {γ d ε : ℝ} (hγ : 0 < γ) (hd : 0 < d) (hε : 0 ≤ ε)
    (hεlt : ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ))
    (hQ : ∀ n ∈ Finset.range N, (Q n).IsSymmetricProjection)
    (hcomm : ∀ n ∈ Finset.range N, ∀ m,
      m < n - l ∨ n < m →
        (G.martingaleDifference m).comp (Q n) =
          (Q n).comp (G.martingaleDifference m))
    (hC1 : ∀ x,
      0 ≤ ∑ n ∈ Finset.range N,
          (⟪localHamiltonian n x, x⟫_ℂ).re ∧
      (∑ n ∈ Finset.range N,
          (⟪localHamiltonian n x, x⟫_ℂ).re) ≤
        d * (⟪H x, x⟫_ℂ).re)
    (hC2 : ∀ n ∈ Finset.range N, ∀ x,
      γ * ‖((LinearMap.id : E →ₗ[ℂ] E) - Q n) x‖ ^ 2 ≤
        (⟪localHamiltonian n x, x⟫_ℂ).re)
    (hC3 : ∀ n ∈ Finset.range N,
      ‖(Q n).toContinuousLinearMap.comp
          (G.martingaleDifference n).toContinuousLinearMap‖ ≤ ε)
    (hH : H.IsPositive)
    (hground : LinearMap.range (G.projection N) = LinearMap.ker H) :
    ∀ v ∈ (LinearMap.ker H)ᗮ,
      (γ / d) * (1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2 * ‖v‖ ≤
        ‖H v‖ := by
  let gap := (γ / d) *
    (1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2
  have hs : 0 < Real.sqrt ((l + 1 : ℕ) : ℝ) :=
    Real.sqrt_pos.2 (by positivity)
  have hεs : ε * Real.sqrt ((l + 1 : ℕ) : ℝ) < 1 :=
    (lt_div_iff₀ hs).mp hεlt
  have hgap : 0 < gap := by
    dsimp only [gap]
    positivity
  apply spectralGap_of_martingale_of_finiteDimensional hgap hH
  apply operator_inequality_of_energy_lower_bound hgap hH
  intro v hv
  apply energy_lower_bound_of_nachtergaele_c1_c3_full_range G Q localHamiltonian H
    N l v hzero
  · rwa [hground]
  · exact hγ
  · exact hd
  · exact hε
  · exact hεlt
  · exact hQ
  · exact hcomm
  · exact hC1
  · exact hC2
  · exact hC3

end NestedGroundProjections

end FrustrationFree
