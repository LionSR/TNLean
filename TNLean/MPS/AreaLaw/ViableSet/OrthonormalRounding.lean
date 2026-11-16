/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.ViabilityStability
import TNLean.MPS.AreaLaw.ViableSet.PrefixColumn

/-!
# Rounding an orthonormal retained family

Replacing each vector of an orthonormal retained family within distance `θ`
changes any unit supported witness by at most the family cardinality times `θ`.
The estimate is independent of the dimension of the right block. It therefore
permits rational approximation after the sampled error-reduction step of Landau,
Vazirani and Vidick, arXiv:1307.5143v1, Claim `c:errorreduction`, lines 580–592.
-/

open scoped InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- Rounding an orthonormal family perturbs every vector in its span by at most
the family cardinality times the rounding error and the vector norm. -/
theorem norm_sub_sum_inner_smul_le_of_mem_orthonormal_span
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {r : ℕ} {u w : Fin r → E} (hu : Orthonormal ℂ u)
    {θ : ℝ} (hclose : ∀ j, ‖u j - w j‖ ≤ θ)
    {x : E} (hx : x ∈ Submodule.span ℂ (Set.range u)) :
    ‖x - ∑ j, ⟪u j, x⟫_ℂ • w j‖ ≤ (r : ℝ) * θ * ‖x‖ := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  have hrepr : ∑ j, ⟪u j, x⟫_ℂ • u j = x := by
    rw [← hc]
    simp only [hu.inner_right_fintype c]
  calc
    ‖x - ∑ j, ⟪u j, x⟫_ℂ • w j‖ =
        ‖∑ j, ⟪u j, x⟫_ℂ • (u j - w j)‖ := by
          congr 1
          calc
            x - ∑ j, ⟪u j, x⟫_ℂ • w j =
                (∑ j, ⟪u j, x⟫_ℂ • u j) - ∑ j, ⟪u j, x⟫_ℂ • w j :=
              congrArg (fun y ↦ y - ∑ j, ⟪u j, x⟫_ℂ • w j) hrepr.symm
            _ = _ := by simp only [smul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ j, ‖⟪u j, x⟫_ℂ • (u j - w j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin r, ‖x‖ * θ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      have hinner : ‖⟪u j, x⟫_ℂ‖ ≤ ‖x‖ := by
        simpa only [hu.norm_eq_one j, one_mul] using norm_inner_le_norm (u j) x
      exact mul_le_mul hinner (hclose j) (norm_nonneg _) (norm_nonneg _)
    _ = (r : ℝ) * θ * ‖x‖ := by simp; ring

/-- Rounding an orthonormal left family approximates every supported chain vector.
The error bound involves the family cardinality but no right-block dimension. -/
theorem exists_close_supported_vector_of_orthonormal_rounding
    {L q k r : ℕ} {u w : Fin r → LeftBlockVector L q k}
    (hu : Orthonormal ℂ u) {θ : ℝ} (hθ : 0 ≤ θ)
    (hclose : ∀ j, ‖u j - w j‖ ≤ θ)
    {φ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hφ : φ ∈ leftSupportSubmodule (Set.range u)) :
    ∃ ψ : EuclideanSpace ℂ (Fin L → Fin q),
      ψ ∈ leftSupportSubmodule (Set.range w) ∧
      ‖φ - ψ‖ ≤ (r : ℝ) * θ * ‖φ‖ := by
  classical
  let e := Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k)
  let T : LeftBlockVector L q k → LeftBlockVector L q k :=
    fun x ↦ ∑ j, ⟪u j, x⟫_ℂ • w j
  let ψ : EuclideanSpace ℂ (Fin L → Fin q) :=
    WithLp.toLp 2 fun σ ↦ T (cutColumn φ k (e σ).2) (e σ).1
  have hcolumn (b) : cutColumn ψ k b = T (cutColumn φ k b) := by
    ext a
    change T (cutColumn φ k (e (e.symm (a, b))).2) (e (e.symm (a, b))).1 = _
    rw [Equiv.apply_symm_apply]
  refine ⟨ψ, ?_, ?_⟩
  · apply mem_leftSupportSubmodule.mpr
    intro b
    rw [hcolumn]
    exact Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  · have hC : 0 ≤ (r : ℝ) * θ := mul_nonneg (Nat.cast_nonneg _) hθ
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
    calc
      ‖φ - ψ‖ ^ 2 = ∑ b, ‖cutColumn (φ - ψ) k b‖ ^ 2 :=
        (sum_norm_cutColumn_sq _).symm
      _ ≤ ∑ b, ((r : ℝ) * θ * ‖cutColumn φ k b‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro b _
        have hdiff : cutColumn (φ - ψ) k b = cutColumn φ k b - cutColumn ψ k b := by
          ext a
          rfl
        rw [hdiff, hcolumn]
        apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr
        exact norm_sub_sum_inner_smul_le_of_mem_orthonormal_span hu hclose (hφ b)
      _ = ((r : ℝ) * θ) ^ 2 * ∑ b, ‖cutColumn φ k b‖ ^ 2 := by
        simp only [mul_pow, Finset.mul_sum]
      _ = ((r : ℝ) * θ * ‖φ‖) ^ 2 := by rw [sum_norm_cutColumn_sq]; ring

/-- Uniform rounding of an orthonormal retained family enlarges the viability
error by at most twice its cardinality times the rounding error. -/
theorem IsViable.round_orthonormal
    {L q k r : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    {δ θ : ℝ} {u w : Fin r → LeftBlockVector L q k}
    (hviable : IsViable Γ δ (Set.range u)) (hu : Orthonormal ℂ u)
    (hΓ : ‖Γ‖ = 1) (hθ : 0 ≤ θ) (hsmall : (r : ℝ) * θ < 1)
    (hclose : ∀ j, ‖u j - w j‖ ≤ θ) :
    IsViable Γ (δ + 2 * r * θ) (Set.range w) := by
  obtain ⟨φ, hφnorm, hφoverlap, hφsupport⟩ := hviable
  obtain ⟨ψ, hψsupport, hψclose⟩ :=
    exists_close_supported_vector_of_orthonormal_rounding hu hθ hclose hφsupport
  have herr : ‖φ - ψ‖ ≤ (r : ℝ) * θ := by simpa only [hφnorm, mul_one] using hψclose
  convert isViable_of_close_supported_vector hΓ hsmall hφnorm hφoverlap hψsupport herr using 1
  ring

end TNLean.MPS.AreaLaw
