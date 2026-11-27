/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.RationalTensor.ViabilityStability
import TNLean.MPS.AreaLaw.ViableSet.PrefixColumn
import TNLean.MPS.AreaLaw.ViableSet.Span
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.RationalTensor.RationalTensorApproximation

/-!
# Rounding an orthonormal retained family

Replacing each vector of an orthonormal retained family within distance `θ`
changes any unit supported witness by at most the family cardinality times `θ`.
The estimate is independent of the dimension of the right block. It therefore
permits rational approximation after the sampled error-reduction step of Landau,
Vazirani and Vidick, arXiv:1307.5143v1, Claim `c:errorreduction`, lines 580–592.

## Rational approximation of a finite retained subspace

An orthonormal basis of the span of a finite family of matrix product states
has the finite-span bond bound. Rounding this basis gives a rational family
whose viability loss depends on the dimension of the retained subspace.
The family and its precision are chosen before the target vector.

This is an auxiliary approximation result for the finite-precision analysis
of Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`,
equation `eq:conv` and Claim `c:trim`, lines 472–478 and 549–559.
-/

open ManyBody (interval)

section

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
  let e := ManyBody.cutEquiv (fun _ ↦ Fin q) (interval L 0 k)
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

end

section

open scoped InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- Every finite family of left-open MPS admits a rational replacement of no
larger cardinality, with an explicit common parameter height and a prescribed
viability loss. The finite-span bond bound accounts for orthonormalizing its
span; no condition on the original vectors' norms or linear dependence is needed.
The replacement is chosen before every normalized target and viability error. -/
theorem exists_rational_leftFamily_approximation_of_orthonormalization
    {L q b n : ℕ} (V : Finset (LeftBlockVector L q (n + 1))) (hk : n + 1 ≤ L)
    (hMPS : ∀ v ∈ V, IsLeftOpenMPS b v) {ε : ℝ} (hε : 0 < ε) (hεone : ε < 1) :
    let b' := V.card * max 1 b
    let θ : ℝ := ε / (2 * (V.card + 1))
    let K : ℝ := (q ^ (n + 1) : ℝ) * (max 1 (max 1 b') : ℝ) ^ (n + 2) *
      (n + 2) * 2 ^ (n + 1)
    let t := Nat.clog 2 ⌈K / θ⌉₊
    ∃ T : Finset (LeftBlockVector L q (n + 1)),
      T.card ≤ V.card ∧
      (∀ w ∈ T, Nonempty
        (RationalLeftOpenMPSRepresentationOfHeight (2 ^ (2 * t + 5)) b' w)) ∧
      ∀ (Γ : EuclideanSpace ℂ (Fin L → Fin q)) (δ : ℝ),
        ‖Γ‖ = 1 → IsViable Γ δ (V : Set (LeftBlockVector L q (n + 1))) →
          IsViable Γ (δ + ε) (T : Set (LeftBlockVector L q (n + 1))) := by
  classical
  intro b' θ K t
  obtain ⟨r, u, hr, hu, hspan, humps⟩ :=
    exists_orthonormalBasis_isLeftOpenMPS_span V hMPS
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  choose w hrep hclose using fun j : Fin r ↦
    (humps j).exists_dyadic_rational_approximation_at_error hk (hu.norm_eq_one j) hθ
  let T := Finset.univ.image w
  have hbudget : 2 * (r : ℝ) * θ ≤ ε := by
    have hrreal : (r : ℝ) ≤ V.card := by exact_mod_cast hr
    have hrε := mul_le_mul_of_nonneg_right hrreal hε.le
    dsimp only [θ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 2 * ((V.card : ℝ) + 1))).mpr
    nlinarith
  have hsmall : (r : ℝ) * θ < 1 := by nlinarith
  refine ⟨T, Finset.card_image_le.trans (by simpa using hr), ?_, ?_⟩
  · intro v hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    exact hrep j
  · intro Γ δ hΓ hviable
    have huviable : IsViable Γ δ (Set.range u) := by
      obtain ⟨φ, hφ, hoverlap, hsupport⟩ := hviable
      refine ⟨φ, hφ, hoverlap, ?_⟩
      intro z
      rw [hspan]
      exact hsupport z
    have hwviable := huviable.round_orthonormal hu hΓ hθ.le hsmall hclose
    have hT : (T : Set (LeftBlockVector L q (n + 1))) = Set.range w := by
      simp only [T, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rw [hT]
    exact hwviable.mono_error (by linarith)

end TNLean.MPS.AreaLaw

end
