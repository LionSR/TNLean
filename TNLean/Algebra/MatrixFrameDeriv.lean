/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Connected.Clopen
import TNLean.Algebra.MatrixEntrywiseDeriv

/-!
# Frames of matrices whose derivative stays in their span

Let `V γ i` be a finite family of complex matrices depending on a real
parameter, differentiable entry by entry, whose derivative at every
parameter is a combination of the family at the same parameter,
`V' γ i = ∑ i', X γ i i' • V γ i'`. If at every parameter the family has a
biorthogonal trace pairing, then the family at any parameter is an
invertible change of basis of the family at any other parameter of a
connected open set.

No regularity of the coefficients `X γ` is assumed. Near a parameter `t`,
the matrix `Q γ` of trace pairings of `V γ` against the dual family at `t`
satisfies `Q' = X Q` and `Q t = 1`, so `Q⁻¹ V` has zero derivative and
`V γ = Q γ V t`. An equivalence relation with open classes on a
connected set has one class.

## Main results

* `Matrix.hasDerivAt_inv_entries`: the derivative of the inverse of an
  entrywise differentiable family at a nonsingular point.
* `Matrix.eventually_exists_eq_sum_smul_of_hasDerivAt`: near a parameter
  with a biorthogonal pairing, the family is an invertible change of basis
  of the family at that parameter.
* `Matrix.exists_eq_sum_smul_of_hasDerivAt`: the same between any two
  parameters of a connected open set.
-/

open Filter Topology
open scoped Matrix BigOperators

namespace Matrix

variable {ι m n : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [Fintype n]

/-- The derivative of the inverse of an entrywise differentiable family of
square matrices at a nonsingular point is `-P⁻¹ P' P⁻¹`. -/
theorem hasDerivAt_inv_entries {t : ℝ} {P : ℝ → Matrix ι ι ℂ} {P' : Matrix ι ι ℂ}
    (hP : ∀ i j, HasDerivAt (fun s ↦ P s i j) (P' i j) t) (hdet : (P t).det ≠ 0)
    (i j : ι) :
    HasDerivAt (fun s ↦ (P s)⁻¹ i j) ((-((P t)⁻¹ * P' * (P t)⁻¹)) i j) t := by
  have hd : ∀ i j, HasDerivAt (fun s ↦ (P s)⁻¹ i j)
      (deriv (fun s ↦ (P s)⁻¹ i j) t) t := fun i j ↦
    (differentiableAt_inv_of_entries (fun i j ↦ (hP i j).differentiableAt) hdet i j).hasDerivAt
  set E : Matrix ι ι ℂ := Matrix.of fun i j ↦ deriv (fun s ↦ (P s)⁻¹ i j) t with hEdef
  have hev : ∀ᶠ s in 𝓝 t, (P s)⁻¹ * P s = 1 := by
    have hc := (differentiableAt_det_of_entries fun i j ↦ (hP i j).differentiableAt).continuousAt
    filter_upwards [hc.eventually_ne hdet] with s hs
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hs)
  have hzero : E * P t + (P t)⁻¹ * P' = 0 := by
    ext k l
    have h1 := hasDerivAt_mul_entries (F := fun s ↦ (P s)⁻¹) (F' := E) hd hP k l
    have h2 : HasDerivAt (fun s ↦ ((P s)⁻¹ * P s) k l) 0 t :=
      (hasDerivAt_const t ((1 : Matrix ι ι ℂ) k l)).congr_of_eventuallyEq
        (hev.mono fun s hs ↦ by simp only [hs])
    exact h1.unique h2
  have hu : IsUnit (P t).det := isUnit_iff_ne_zero.2 hdet
  have hE : E = -((P t)⁻¹ * P' * (P t)⁻¹) := by
    calc E = E * P t * (P t)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
      _ = -((P t)⁻¹ * P') * (P t)⁻¹ := by rw [eq_neg_of_add_eq_zero_left hzero]
      _ = -((P t)⁻¹ * P' * (P t)⁻¹) := by rw [Matrix.neg_mul]
  rw [← hE]
  exact hd i j

omit [DecidableEq ι] in
private theorem sum_smul_sum_smul {α : Type*} [AddCommMonoid α] [Module ℂ α]
    (A B : Matrix ι ι ℂ) (w : ι → α) (i : ι) :
    ∑ k, A i k • ∑ l, B k l • w l = ∑ l, (A * B) i l • w l := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_comm

/-- **A frame whose derivative stays in its span, near one parameter.**
Let the entries of `V γ i` be differentiable near `t`, with derivative
`∑ i', X γ i i' • V γ i'` at `γ`, and let `W` be a family with
`c tr (V t i W k) = δ_{ik}`. Then near `t`, `V γ i = ∑ k, G i k • V t k`
for an invertible matrix `G`. No regularity of `X` is assumed. -/
theorem eventually_exists_eq_sum_smul_of_hasDerivAt
    {V : ℝ → ι → Matrix m n ℂ} {X : ℝ → Matrix ι ι ℂ} {t : ℝ}
    (hV : ∀ᶠ s in 𝓝 t, ∀ i u v,
      HasDerivAt (fun r ↦ V r i u v) ((∑ i', X s i i' • V s i') u v) s)
    (W : ι → Matrix n m ℂ) (c : ℂ)
    (hW : ∀ i k, c * (V t i * W k).trace = if i = k then 1 else 0) :
    ∀ᶠ s in 𝓝 t, ∃ G : GL ι ℂ, ∀ i, V s i = ∑ k, (G : Matrix ι ι ℂ) i k • V t k := by
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ → Matrix ι ι ℂ, ∀ s i k, Q s i k = c * (V s i * W k).trace :=
    ⟨fun s ↦ Matrix.of fun i k ↦ c * (V s i * W k).trace, fun _ _ _ ↦ rfl⟩
  have hQ1 : Q t = 1 := by
    ext i k
    rw [hQ, hW, Matrix.one_apply]
  have hQd : ∀ᶠ s in 𝓝 t, ∀ i k, HasDerivAt (fun r ↦ Q r i k) ((X s * Q s) i k) s := by
    filter_upwards [hV] with s hs i k
    have h := (hasDerivAt_trace_of_entries fun u w ↦
      hasDerivAt_mul_entries (G := fun _ ↦ W k) (G' := 0) (hs i)
        (fun u v ↦ hasDerivAt_const s (W k u v)) u w).const_mul c
    simp only [hQ]
    convert h using 1
    rw [Matrix.mul_apply]
    simp only [hQ, Matrix.mul_zero, add_zero, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum,
      Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  have hdet : ∀ᶠ s in 𝓝 t, (Q s).det ≠ 0 := by
    have hc := (differentiableAt_det_of_entries fun i k ↦
      (hQd.self_of_nhds i k).differentiableAt).continuousAt
    exact hc.eventually_ne (by simp [hQ1])
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hV.and (hQd.and hdet))
  -- The coordinates `Q⁻¹ V` have zero derivative on the ball.
  have hF : ∀ s ∈ Metric.ball t ε, ∀ i u v,
      HasDerivAt (fun r ↦ ∑ i', (Q r)⁻¹ i i' * V r i' u v) 0 s := by
    intro s hs i u v
    obtain ⟨hVs, hQs, hds⟩ := hball s hs
    have hcol := hasDerivAt_mul_entries (F := fun r ↦ (Q r)⁻¹)
      (G := fun r ↦ Matrix.of fun i' (_ : Unit) ↦ V r i' u v)
      (G' := X s * Matrix.of fun i' (_ : Unit) ↦ V s i' u v)
      (hasDerivAt_inv_entries hQs hds) (fun i' _ ↦ by
        simpa only [Matrix.mul_apply, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
          smul_eq_mul] using hVs i' u v) i ()
    have hzero : -((Q s)⁻¹ * (X s * Q s) * (Q s)⁻¹) * Matrix.of (fun i' (_ : Unit) ↦ V s i' u v) +
        (Q s)⁻¹ * (X s * Matrix.of fun i' (_ : Unit) ↦ V s i' u v) = 0 := by
      rw [Matrix.mul_assoc ((Q s)⁻¹), Matrix.mul_assoc (X s),
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hds), Matrix.mul_one,
        Matrix.neg_mul, Matrix.mul_assoc, neg_add_cancel]
    rw [hzero] at hcol
    simpa [Matrix.mul_apply] using hcol
  have hconst : ∀ s ∈ Metric.ball t ε, ∀ i, ∑ i', (Q s)⁻¹ i i' • V s i' = V t i := by
    intro s hs i
    ext u v
    have h := (Metric.isOpen_ball).is_const_of_deriv_eq_zero
      (convex_ball t ε).isPreconnected
      (fun r hr ↦ (hF r hr i u v).differentiableAt.differentiableWithinAt)
      (fun r hr ↦ (hF r hr i u v).deriv) hs (Metric.mem_ball_self hε)
    simpa [Matrix.sum_apply, hQ1, Matrix.one_apply] using h
  filter_upwards [Metric.ball_mem_nhds t hε] with s hs
  have hu : IsUnit (Q s) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_ne_zero.2 (hball s hs).2.2)
  refine ⟨hu.unit, fun i ↦ ?_⟩
  simp only [IsUnit.unit_spec, ← hconst s hs, sum_smul_sum_smul,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), Matrix.one_apply,
    ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- **A frame whose derivative stays in its span is constant up to an
invertible change of basis.** On a connected open set `U`, let the entries
of `V γ i` be differentiable with derivative `∑ i', X γ i i' • V γ i'` at
every `γ ∈ U`, and let the family have a biorthogonal trace pairing at every
`γ ∈ U`. Then for `γ₀, γ ∈ U`, `V γ i = ∑ k, G i k • V γ₀ k` for an
invertible matrix `G`. No regularity of `X` is assumed. -/
theorem exists_eq_sum_smul_of_hasDerivAt {U : Set ℝ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) {V : ℝ → ι → Matrix m n ℂ} {X : ℝ → Matrix ι ι ℂ}
    (hV : ∀ s ∈ U, ∀ i u v,
      HasDerivAt (fun r ↦ V r i u v) ((∑ i', X s i i' • V s i') u v) s)
    (hW : ∀ s ∈ U, ∃ (W : ι → Matrix n m ℂ) (c : ℂ),
      ∀ i k, c * (V s i * W k).trace = if i = k then 1 else 0)
    {γ₀ γ : ℝ} (hγ₀ : γ₀ ∈ U) (hγ : γ ∈ U) :
    ∃ G : GL ι ℂ, ∀ i, V γ i = ∑ k, (G : Matrix ι ι ℂ) i k • V γ₀ k := by
  refine hUc.induction₂
    (fun x y ↦ ∃ G : GL ι ℂ, ∀ i, V y i = ∑ k, (G : Matrix ι ι ℂ) i k • V x k)
    (fun x hx ↦ ?_) ?_ ?_ hγ₀ hγ
  · obtain ⟨W, c, hWc⟩ := hW x hx
    exact nhdsWithin_le_nhds (eventually_exists_eq_sum_smul_of_hasDerivAt
      (Filter.eventually_of_mem (hUo.mem_nhds hx) hV) W c hWc)
  · rintro x y z - - - ⟨G₁, h₁⟩ ⟨G₂, h₂⟩
    refine ⟨G₂ * G₁, fun i ↦ ?_⟩
    simp only [h₂, h₁, sum_smul_sum_smul, Units.val_mul]
  · rintro x y - - ⟨G, h⟩
    refine ⟨G⁻¹, fun i ↦ ?_⟩
    simp only [h, sum_smul_sum_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]

end Matrix
