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
# Nachtergaele's C1--C3 energy estimate

This file follows the summation in the proof of Theorem 2.1(i) in Nachtergaele,
arXiv:cond-mat/9410110, lines 1195--1259.

Conditions C2 and C3 in the source, at lines 1043--1058 and 1083--1094, are
assumed only beyond their lower threshold \(n_l\), while C1, at lines
1030--1041, starts at the corresponding window length; the printed proof
nevertheless estimates every martingale difference \(E_0,\ldots,E_{N-1}\).

`energy_lower_bound_of_nachtergaele_c1_c3_threshold` assumes the three
estimates only on an index range \(n_0\leq n<N\). To obtain its C1 hypothesis
from the source, one chooses \(n_0\geq l\), as well as above the C2--C3
threshold; for smaller \(n_0\), its displayed C1 bound is an independent
stronger assumption. The theorem obtains the printed coefficient on the
martingale mass above the threshold, together with an explicit upper-bound
correction carried by the \(l\) differences immediately below it.

**Scope restriction (full finite range):**
`energy_lower_bound_of_nachtergaele_c1_c3_full_range` and
`norm_lower_bound_of_nachtergaele_c1_c3_full_range` are the case \(n_0=0\),
where that correction is empty. They assume the three estimates on the entire
finite range, which is stronger than the source's lower-threshold hypotheses.
This extra hypothesis and the required lower-endpoint repair are recorded in
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`. Thus they are a full-range
version with the source coefficient, not a formalization of the unrestricted
source theorem.

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

/-- Threshold form of the summation in the proof of Nachtergaele's Theorem
2.1(i) (arXiv:cond-mat/9410110, lines 1195--1259).

Condition C2 at lines 1043--1058 and condition C3 at lines 1083--1094 hold
only from a threshold onwards, while condition C1 at lines 1030--1041 begins
at the window length. This theorem assumes all three estimates directly on
\(n_0\leq n<N\). Its C2 and C3 hypotheses have the source forms, with C3 in
its literal operator-norm form \(\lVert Q_nE_n\rVert\leq\epsilon_l\). To
derive its C1 hypothesis from the source, choose \(n_0\geq l\), in addition
to choosing it above the C2--C3 onset; if \(n_0<l\), the stated C1 bound is an
independent stronger assumption.

Summing the per-index estimate over \(n_0\leq n<N\) gives the printed
coefficient
\(\frac{\gamma_{l+1}}{d_{l+1}}(1-\epsilon_l\sqrt{l+1})^2\)
on the martingale mass \(\sum_{n=n_0}^{N-1}\lVert E_n\psi\rVert^2\) above the
threshold, corrected by an upper bound for the moving-window contribution of
the \(l\) differences immediately below it. The coefficient is exact, while
the correction uses the uniform multiplicity bound \(l+1\). The correction
vanishes when \(n_0=0\), and then the conclusion is the printed estimate on
\(\lVert\psi\rVert^2\).

The case \(\epsilon_l=0\) is treated separately, since the printed choice
\(c_2=\epsilon_l/\sqrt{l+1}\) is then not positive; C3 gives \(Q_nE_n=0\)
instead.

**Scope restriction (martingale mass above the threshold):** The source
concludes the same coefficient on \(\lVert\psi\rVert^2\). The two conclusions
agree exactly when the martingale differences below the threshold vanish, and
the printed proof supplies no argument for the omitted indices. The
discrepancy is recorded in
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`. -/
theorem energy_lower_bound_of_nachtergaele_c1_c3_threshold
    [FiniteDimensional ℂ E]
    (G : NestedGroundProjections (E := E)) (Q : ℕ → E →ₗ[ℂ] E)
    (localHamiltonian : ℕ → E →ₗ[ℂ] E) (H : E →ₗ[ℂ] E)
    (N n₀ l : ℕ) (v : E) (hn₀ : n₀ ≤ N)
    (hzero : G.projection 0 = LinearMap.id)
    (hv : v ∈ (LinearMap.range (G.projection N))ᗮ)
    {γ d ε : ℝ} (hγ : 0 < γ) (hd : 0 < d) (hε : 0 ≤ ε)
    (hεlt : ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ))
    (hQ : ∀ n ∈ Finset.Ico n₀ N, (Q n).IsSymmetricProjection)
    (hcomm : ∀ n ∈ Finset.Ico n₀ N, ∀ m,
      m < n - l ∨ n < m →
        (G.martingaleDifference m).comp (Q n) =
          (Q n).comp (G.martingaleDifference m))
    (hC1 : ∀ x,
      0 ≤ ∑ n ∈ Finset.Ico n₀ N,
          (⟪localHamiltonian n x, x⟫_ℂ).re ∧
      (∑ n ∈ Finset.Ico n₀ N,
          (⟪localHamiltonian n x, x⟫_ℂ).re) ≤
        d * (⟪H x, x⟫_ℂ).re)
    (hC2 : ∀ n ∈ Finset.Ico n₀ N, ∀ x,
      γ * ‖((LinearMap.id : E →ₗ[ℂ] E) - Q n) x‖ ^ 2 ≤
        (⟪localHamiltonian n x, x⟫_ℂ).re)
    (hC3 : ∀ n ∈ Finset.Ico n₀ N,
      ‖(Q n).toContinuousLinearMap.comp
          (G.martingaleDifference n).toContinuousLinearMap‖ ≤ ε) :
    (γ / d) * (1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2 *
        ∑ n ∈ Finset.Ico n₀ N, ‖G.martingaleDifference n v‖ ^ 2 ≤
      (⟪H v, v⟫_ℂ).re +
        (γ / d) *
            ((1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) *
              (ε * Real.sqrt ((l + 1 : ℕ) : ℝ))) *
          ∑ m ∈ Finset.Ico (n₀ - l) n₀, ‖G.martingaleDifference m v‖ ^ 2 := by
  classical
  set s := Real.sqrt ((l + 1 : ℕ) : ℝ)
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hsquare : s ^ 2 = ((l + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hεs : ε * s < 1 := (lt_div_iff₀ hs).mp hεlt
  have hδ : 0 < 1 - ε * s := sub_pos.mpr hεs
  have hc₁γ : 0 < 2 * (1 - ε * s) * γ :=
    mul_pos (mul_pos (by norm_num) hδ) hγ
  have hinv : 0 ≤ 1 / (2 * (1 - ε * s) * γ) := one_div_nonneg.mpr hc₁γ.le
  have hC1' :
      (∑ n ∈ Finset.Ico n₀ N, (⟪localHamiltonian n v, v⟫_ℂ).re) ≤
        d * (⟪H v, v⟫_ℂ).re := (hC1 v).2
  have hC3point : ∀ n ∈ Finset.Ico n₀ N, ∀ x,
      ‖Q n (G.martingaleDifference n x)‖ ^ 2 ≤
        ε ^ 2 * ‖G.martingaleDifference n x‖ ^ 2 := by
    intro n hn x
    simpa using norm_sq_apply_projection_le_of_norm_comp_le
      (Q n).toContinuousLinearMap
      (G.martingaleDifference n).toContinuousLinearMap
      (G.martingaleDifference_isSymmetricProjection n) (hC3 n hn) x
  set P := ∑ n ∈ Finset.Ico n₀ N, ‖G.martingaleDifference n v‖ ^ 2 with hP
  set S := ∑ m ∈ Finset.Ico (n₀ - l) n₀, ‖G.martingaleDifference m v‖ ^ 2
    with hS
  set A := (⟪H v, v⟫_ℂ).re
  have hwindow :
      ∑ n ∈ Finset.Ico n₀ N,
          ‖∑ m ∈ Finset.Icc (n - l) n, G.martingaleDifference m v‖ ^ 2 ≤
        ((l : ℝ) + 1) * (S + P) := by
    have hsplit :
        (∑ m ∈ Finset.Ico (n₀ - l) n₀, ‖G.martingaleDifference m v‖ ^ 2) +
            ∑ m ∈ Finset.Ico n₀ N, ‖G.martingaleDifference m v‖ ^ 2 =
          ∑ m ∈ Finset.Ico (n₀ - l) N, ‖G.martingaleDifference m v‖ ^ 2 :=
      Finset.sum_Ico_consecutive _ (Nat.sub_le n₀ l) hn₀
    calc
      ∑ n ∈ Finset.Ico n₀ N,
          ‖∑ m ∈ Finset.Icc (n - l) n, G.martingaleDifference m v‖ ^ 2 =
          ∑ n ∈ Finset.Ico n₀ N, ∑ m ∈ Finset.Icc (n - l) n,
            ‖G.martingaleDifference m v‖ ^ 2 :=
        Finset.sum_congr rfl fun n _ ↦
          G.norm_sq_sum_martingaleDifference_finset (Finset.Icc (n - l) n) v
      _ ≤ ((l : ℝ) + 1) *
            ∑ m ∈ Finset.Ico (n₀ - l) N,
              ‖G.martingaleDifference m v‖ ^ 2 :=
        movingWindow_sum_Ico_le
          (fun m ↦ ‖G.martingaleDifference m v‖ ^ 2) l n₀ N
          (fun m ↦ sq_nonneg _)
      _ = ((l : ℝ) + 1) * (S + P) := by rw [hS, hP, hsplit]
  have key : ((1 - ε * s) / 2) * P ≤
      (1 / (2 * (1 - ε * s) * γ)) * (d * A) + (ε * s / 2) * S := by
    rcases hε.eq_or_lt with hεzero | hεpos
    · subst ε
      have hpoint : ∀ n ∈ Finset.Ico n₀ N,
          ‖G.martingaleDifference n v‖ ^ 2 ≤
            (1 / (2 * γ)) * (⟪localHamiltonian n v, v⟫_ℂ).re +
              (1 / 2) * ‖G.martingaleDifference n v‖ ^ 2 := by
        intro n hn
        have hnN : n < N := (Finset.mem_Ico.mp hn).2
        have hqzero : Q n (G.martingaleDifference n v) = 0 := by
          have hb : ‖Q n (G.martingaleDifference n v)‖ ^ 2 ≤ 0 := by
            simpa using hC3point n hn v
          have hnorm : ‖Q n (G.martingaleDifference n v)‖ = 0 := by
            nlinarith [norm_nonneg (Q n (G.martingaleDifference n v))]
          exact norm_eq_zero.mp hnorm
        simpa using enpsi_of_c2_c3_zero G Q localHamiltonian N n l hnN v
          hzero hv (hQ n hn) (hcomm n hn) hγ (by norm_num : (0 : ℝ) < 1)
          (hC2 n hn v) hqzero
      have hsum := Finset.sum_le_sum hpoint
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← hP] at hsum
      have hbudget :
          (1 / (2 * γ)) *
              (∑ n ∈ Finset.Ico n₀ N, (⟪localHamiltonian n v, v⟫_ℂ).re) ≤
            (1 / (2 * γ)) * (d * A) :=
        mul_le_mul_of_nonneg_left hC1' (by positivity)
      have hgoal : (1 / 2 : ℝ) * P ≤ (1 / (2 * γ)) * (d * A) := by linarith
      calc
        ((1 - 0 * s) / 2) * P = (1 / 2 : ℝ) * P := by ring
        _ ≤ (1 / (2 * γ)) * (d * A) := hgoal
        _ = (1 / (2 * (1 - 0 * s) * γ)) * (d * A) + (0 * s / 2) * S := by
          norm_num
    · have hc₂ : (0 : ℝ) < ε / s := div_pos hεpos hs
      have hεc₂ : ε ^ 2 / (2 * (ε / s)) = ε * s / 2 := by
        field_simp
      have hpoint : ∀ n ∈ Finset.Ico n₀ N,
          ‖G.martingaleDifference n v‖ ^ 2 ≤
            (1 / (2 * (1 - ε * s) * γ)) *
                (⟪localHamiltonian n v, v⟫_ℂ).re +
              ((1 - ε * s) / 2 + ε * s / 2) *
                ‖G.martingaleDifference n v‖ ^ 2 +
              ((ε / s) / 2) *
                ‖∑ m ∈ Finset.Icc (n - l) n,
                  G.martingaleDifference m v‖ ^ 2 := by
        intro n hn
        have hnN : n < N := (Finset.mem_Ico.mp hn).2
        simpa only [hεc₂] using
          enpsi2_of_c2_c3 G Q localHamiltonian N n l hnN v hzero hv
            (hQ n hn) (hcomm n hn) hγ hδ hc₂ (hC2 n hn v) (hC3point n hn v)
      have hsum := Finset.sum_le_sum hpoint
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum, ← hP] at hsum
      have hbudget :
          (1 / (2 * (1 - ε * s) * γ)) *
              (∑ n ∈ Finset.Ico n₀ N, (⟪localHamiltonian n v, v⟫_ℂ).re) ≤
            (1 / (2 * (1 - ε * s) * γ)) * (d * A) :=
        mul_le_mul_of_nonneg_left hC1' hinv
      have hcoef : ((ε / s) / 2) * ((l : ℝ) + 1) = ε * s / 2 := by
        rw [show ((l : ℝ) + 1) = s ^ 2 by rw [hsquare]; push_cast; ring]
        field_simp
      have hwin :
          ((ε / s) / 2) *
              (∑ n ∈ Finset.Ico n₀ N,
                ‖∑ m ∈ Finset.Icc (n - l) n,
                  G.martingaleDifference m v‖ ^ 2) ≤
            (ε * s / 2) * (S + P) := by
        calc
          _ ≤ ((ε / s) / 2) * (((l : ℝ) + 1) * (S + P)) :=
            mul_le_mul_of_nonneg_left hwindow (by positivity)
          _ = (((ε / s) / 2) * ((l : ℝ) + 1)) * (S + P) := by ring
          _ = (ε * s / 2) * (S + P) := by rw [hcoef]
      linarith
  have hmulpos : 0 < 2 * (1 - ε * s) * γ / d := div_pos hc₁γ hd
  calc
    (γ / d) * (1 - ε * s) ^ 2 * P =
        (2 * (1 - ε * s) * γ / d) * (((1 - ε * s) / 2) * P) := by ring
    _ ≤ (2 * (1 - ε * s) * γ / d) *
          ((1 / (2 * (1 - ε * s) * γ)) * (d * A) + (ε * s / 2) * S) :=
      mul_le_mul_of_nonneg_left key hmulpos.le
    _ = A + (γ / d) * ((1 - ε * s) * (ε * s)) * S := by
      field_simp

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
lower-threshold hypotheses. This is the threshold estimate
`energy_lower_bound_of_nachtergaele_c1_c3_threshold` at \(n_0=0\), where the
window correction below the threshold is empty and the martingale mass above
it is \(\lVert\psi\rVert^2\).
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
  have hnorm :
      ∑ n ∈ Finset.Ico 0 N, ‖G.martingaleDifference n v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← Finset.range_eq_Ico]
    exact (G.norm_sq_eq_sum_martingaleDifference_of_mem_orthogonal N v
      hzero hv).symm
  have h := energy_lower_bound_of_nachtergaele_c1_c3_threshold G Q
    localHamiltonian H N 0 l v (Nat.zero_le N) hzero hv hγ hd hε hεlt
    (by simpa only [Finset.range_eq_Ico] using hQ)
    (by simpa only [Finset.range_eq_Ico] using hcomm)
    (by simpa only [Finset.range_eq_Ico] using hC1)
    (by simpa only [Finset.range_eq_Ico] using hC2)
    (by simpa only [Finset.range_eq_Ico] using hC3)
  simpa only [Nat.zero_sub, Finset.Ico_self, Finset.sum_empty, mul_zero,
    add_zero, hnorm] using h

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
