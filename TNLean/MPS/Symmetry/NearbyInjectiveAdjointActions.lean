/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.FrobeniusHilbert
import QICLean.Kraus.Injectivity
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr

/-!
# Uniform dependence of virtual adjoint actions on an injective tensor

An injective tensor has a surjective coefficient operator from its physical
Euclidean space to the Hilbert--Schmidt matrix space. The Gram right inverse
of this operator varies continuously near the tensor. Exact covariance then
expresses each virtual adjoint action in terms of the coefficient operator,
the transposed physical action, and this right inverse.

For a fixed unitary physical action, this expression gives one neighborhood
on which the virtual adjoint actions are close uniformly over the group.
The virtual matrices need not vary continuously and need not be supplied as
a continuous family. The physical action is transposed because coefficients
are column vectors. Under the usual inverse-group covariance convention,
the virtual matrix in the covariance identity is the representative at the
inverse group element.

These are finite-dimensional perturbation results relevant to the projective
symmetry argument in arXiv:1010.3732, Section II.F.2, equation
`eq:1d-sym:jointsym`, and Appendix C. They do not infer continuous injective
representatives from a physical gapped path.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix Matrix.Norms.Frobenius
open Filter Topology

namespace ContinuousLinearMap

private theorem norm_comp_sub_comp_le_of_norm_le_one
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (Φ Φ₀ : E →L[𝕜] F) (Ψ Ψ₀ : F →L[𝕜] E)
    (U : E →L[𝕜] E) (hU : ‖U‖ ≤ 1) :
    ‖Φ.comp (U.comp Ψ) - Φ₀.comp (U.comp Ψ₀)‖ ≤
      ‖Φ - Φ₀‖ * ‖Ψ‖ + ‖Φ₀‖ * ‖Ψ - Ψ₀‖ := by
  have hEq : Φ.comp (U.comp Ψ) - Φ₀.comp (U.comp Ψ₀) =
      (Φ - Φ₀).comp (U.comp Ψ) + Φ₀.comp (U.comp (Ψ - Ψ₀)) := by
    simp only [sub_comp, comp_sub]
    abel
  rw [hEq]
  calc
    ‖(Φ - Φ₀).comp (U.comp Ψ) + Φ₀.comp (U.comp (Ψ - Ψ₀))‖ ≤
        ‖(Φ - Φ₀).comp (U.comp Ψ)‖ + ‖Φ₀.comp (U.comp (Ψ - Ψ₀))‖ := norm_add_le _ _
    _ ≤ ‖Φ - Φ₀‖ * ‖U.comp Ψ‖ + ‖Φ₀‖ * ‖U.comp (Ψ - Ψ₀)‖ :=
      add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _)
    _ ≤ ‖Φ - Φ₀‖ * (‖U‖ * ‖Ψ‖) + ‖Φ₀‖ * (‖U‖ * ‖Ψ - Ψ₀‖) := by
      gcongr
      · exact opNorm_comp_le _ _
      · exact opNorm_comp_le _ _
    _ ≤ ‖Φ - Φ₀‖ * ‖Ψ‖ + ‖Φ₀‖ * ‖Ψ - Ψ₀‖ := by
      simpa only [one_mul] using (show
        ‖Φ - Φ₀‖ * (‖U‖ * ‖Ψ‖) + ‖Φ₀‖ * (‖U‖ * ‖Ψ - Ψ₀‖) ≤
          ‖Φ - Φ₀‖ * (1 * ‖Ψ‖) + ‖Φ₀‖ * (1 * ‖Ψ - Ψ₀‖) from by gcongr)

/-- Continuous coefficient maps yield a uniform perturbation bound after
composition with any family of contractions. -/
private theorem eventually_uniform_comp_sub_lt
    {𝕜 E F T G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace T]
    (Φ : T → E →L[𝕜] F) (Ψ : T → F →L[𝕜] E)
    (t₀ : T) (hΦ : ContinuousAt Φ t₀) (hΨ : ContinuousAt Ψ t₀)
    (U : G → E →L[𝕜] E) (hU : ∀ g, ‖U g‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t₀, ∀ g,
      ‖(Φ t).comp ((U g).comp (Ψ t)) -
        (Φ t₀).comp ((U g).comp (Ψ t₀))‖ < ε := by
  have hCont : ContinuousAt
      (fun t => ‖Φ t - Φ t₀‖ * ‖Ψ t‖ + ‖Φ t₀‖ * ‖Ψ t - Ψ t₀‖) t₀ :=
    ((hΦ.sub continuousAt_const).norm.mul hΨ.norm).add
      (continuousAt_const.mul (hΨ.sub continuousAt_const).norm)
  have hZero : Tendsto
      (fun t => ‖Φ t - Φ t₀‖ * ‖Ψ t‖ + ‖Φ t₀‖ * ‖Ψ t - Ψ t₀‖)
      (𝓝 t₀) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero, zero_mul, mul_zero, add_zero] using hCont.tendsto
  filter_upwards [hZero.eventually_lt_const hε] with t ht
  exact fun g => (norm_comp_sub_comp_le_of_norm_le_one
    (Φ t) (Φ t₀) (Ψ t) (Ψ t₀) (U g) (hU g)).trans_lt ht

end ContinuousLinearMap

namespace Matrix

/-- Bond conjugation acting on the Euclidean space of matrix entries. -/
noncomputable def conjugationEuclideanCLM {D : ℕ} (V : Matrix (Fin D) (Fin D) ℂ) :
    EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D) :=
  (frobeniusEuclideanMap ((LinearMap.mulRight ℂ Vᴴ).comp
    (LinearMap.mulLeft ℂ V))).toContinuousLinearMap

/-- Euclidean bond conjugation agrees with ordinary matrix conjugation. -/
theorem conjugationEuclideanCLM_apply {D : ℕ}
    (V X : Matrix (Fin D) (Fin D) ℂ) :
    conjugationEuclideanCLM V (frobeniusEquivEuclidean (Fin D) (Fin D) X) =
      frobeniusEquivEuclidean (Fin D) (Fin D) (V * X * Vᴴ) := by
  simp only [conjugationEuclideanCLM, LinearMap.coe_toContinuousLinearMap',
    frobeniusEuclideanMap_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, LinearMap.mulLeft_apply]

private theorem norm_toEuclideanCLM_transpose_le_one {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) ((U : Matrix (Fin d) (Fin d) ℂ)ᵀ)‖ ≤ 1 := by
  have hU : (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) ((U : Matrix (Fin d) (Fin d) ℂ)ᵀ) ∈
      unitary (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :=
    Unitary.map_mem (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ))
      (Matrix.transpose_mem_unitaryGroup_iff.mpr U.2)
  rcases subsingleton_or_nontrivial
      (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) with h | h
  · have : (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) ((U : Matrix (Fin d) (Fin d) ℂ)ᵀ) = 0 :=
      Subsingleton.elim _ _
    simp only [this, norm_zero, zero_le_one]
  · exact (CStarRing.norm_of_mem_unitary hU).le

end Matrix

namespace MPSTensor

/-- The coefficient map in Euclidean column-vector coordinates. -/
noncomputable def coefficientEuclideanMap {d D : ℕ} (C : MPSTensor d D) :
    EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D) :=
  (Matrix.toEuclideanLin (Matrix.of fun ab i => C i ab.2 ab.1)).toContinuousLinearMap

/-- The Euclidean coefficient map is the vectorized linear combination of the letters. -/
theorem coefficientEuclideanMap_apply {d D : ℕ} (C : MPSTensor d D)
    (x : EuclideanSpace ℂ (Fin d)) :
    coefficientEuclideanMap C x = Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
      (Fintype.linearCombination ℂ C (WithLp.ofLp x)) := by
  apply PiLp.ext
  intro ab
  simp only [coefficientEuclideanMap, LinearMap.coe_toContinuousLinearMap',
    Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
    Matrix.frobeniusEquivEuclidean_apply, Matrix.vec, Matrix.mulVec, dotProduct,
    Matrix.of_apply, Fintype.linearCombination_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, mul_comm]

private def coefficientMatrixLinear {d D : ℕ} :
    MPSTensor d D →ₗ[ℂ] Matrix (Fin D × Fin D) (Fin d) ℂ where
  toFun C := Matrix.of fun ab i => C i ab.2 ab.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def coefficientEuclideanMapLinear {d D : ℕ} :
    MPSTensor d D →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D)) :=
  LinearMap.toContinuousLinearMap.toLinearMap.comp
    ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin D × Fin D) (n := Fin d)).toLinearMap.comp
      coefficientMatrixLinear)

/-- The coefficient operator depends continuously on the tensor. -/
theorem continuous_coefficientEuclideanMap {d D : ℕ} :
    Continuous (fun C : MPSTensor d D => coefficientEuclideanMap C) :=
  coefficientEuclideanMapLinear.continuous_of_finiteDimensional

/-- Injectivity of the tensor makes its coefficient operator surjective. -/
theorem coefficientEuclideanMap_surjective_of_isInjective {d D : ℕ}
    (C : MPSTensor d D) (hC : Kraus.IsInjective C) :
    Function.Surjective (coefficientEuclideanMap C) := by
  have hLC : Function.Surjective (Fintype.linearCombination ℂ C) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hC
  intro x
  obtain ⟨u, hu⟩ := hLC ((Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm x)
  refine ⟨WithLp.toLp 2 u, ?_⟩
  rw [coefficientEuclideanMap_apply, WithLp.ofLp_toLp, hu]
  exact (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).apply_symm_apply x

private theorem isUnit_self_comp_adjoint_of_surjective {d D : ℕ}
    (Φ : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D))
    (hΦ : Function.Surjective Φ) : IsUnit (Φ.comp Φ.adjoint) := by
  have hRange : Φ.range = ⊤ := LinearMap.range_eq_top.mpr hΦ
  have hKer : Φ.adjoint.ker = ⊥ := by
    rw [← Φ.orthogonal_range, hRange, Submodule.top_orthogonal_eq_bot]
  have hInjAdj : Function.Injective Φ.adjoint := LinearMap.ker_eq_bot.mp hKer
  have hInj : Function.Injective (Φ.comp Φ.adjoint) := by
    simpa only [ContinuousLinearMap.coe_comp] using
      Φ.self_comp_adjoint_injective_iff.mpr hInjAdj
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hInj, LinearMap.injective_iff_surjective.mp hInj⟩

/-- The Gram right inverse of the Euclidean coefficient operator. -/
noncomputable def coefficientRightInverse {d D : ℕ} (C : MPSTensor d D) :
    EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
  (coefficientEuclideanMap C).adjoint.comp
    (Ring.inverse ((coefficientEuclideanMap C).comp (coefficientEuclideanMap C).adjoint))

private theorem coefficientEuclideanMap_comp_rightInverse_of_isUnit {d D : ℕ}
    (C : MPSTensor d D)
    (hUnit : IsUnit ((coefficientEuclideanMap C).comp
      (coefficientEuclideanMap C).adjoint)) :
    (coefficientEuclideanMap C).comp (coefficientRightInverse C) =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin D × Fin D)) := by
  change (coefficientEuclideanMap C).comp
    ((coefficientEuclideanMap C).adjoint.comp
      (Ring.inverse ((coefficientEuclideanMap C).comp
        (coefficientEuclideanMap C).adjoint))) = _
  rw [← ContinuousLinearMap.comp_assoc]
  exact Ring.mul_inverse_cancel _ hUnit

/-- The coefficient Gram formula is a right inverse for an injective tensor. -/
theorem coefficientEuclideanMap_comp_rightInverse_of_isInjective {d D : ℕ}
    (C : MPSTensor d D) (hC : Kraus.IsInjective C) :
    (coefficientEuclideanMap C).comp (coefficientRightInverse C) =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin D × Fin D)) := by
  have hUnit := isUnit_self_comp_adjoint_of_surjective (coefficientEuclideanMap C)
    (coefficientEuclideanMap_surjective_of_isInjective C hC)
  exact coefficientEuclideanMap_comp_rightInverse_of_isUnit C hUnit

private theorem continuous_coefficientGram {d D : ℕ} :
    Continuous (fun B : MPSTensor d D =>
      (coefficientEuclideanMap B).comp (coefficientEuclideanMap B).adjoint) := by
  have hΦ : Continuous (fun B : MPSTensor d D => coefficientEuclideanMap B) :=
    continuous_coefficientEuclideanMap
  exact hΦ.clm_comp (ContinuousLinearMap.adjoint.continuous.comp hΦ)

/-- The coefficient Gram right inverse is continuous at every injective tensor. -/
theorem continuousAt_coefficientRightInverse_of_isInjective {d D : ℕ}
    (C : MPSTensor d D) (hC : Kraus.IsInjective C) :
    ContinuousAt coefficientRightInverse C := by
  have hΦ : Continuous (fun B : MPSTensor d D => coefficientEuclideanMap B) :=
    continuous_coefficientEuclideanMap
  have hAdj : Continuous (fun B : MPSTensor d D => (coefficientEuclideanMap B).adjoint) :=
    ContinuousLinearMap.adjoint.continuous.comp hΦ
  have hGram : Continuous (fun B : MPSTensor d D =>
      (coefficientEuclideanMap B).comp (coefficientEuclideanMap B).adjoint) :=
    continuous_coefficientGram
  obtain ⟨u, hu⟩ := isUnit_self_comp_adjoint_of_surjective (coefficientEuclideanMap C)
    (coefficientEuclideanMap_surjective_of_isInjective C hC)
  have hInv : ContinuousAt Ring.inverse
      ((coefficientEuclideanMap C).comp (coefficientEuclideanMap C).adjoint) := by
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  have hInvGram : ContinuousAt (fun B : MPSTensor d D =>
      Ring.inverse ((coefficientEuclideanMap B).comp
        (coefficientEuclideanMap B).adjoint)) C :=
    ContinuousAt.comp (f := fun B : MPSTensor d D =>
      (coefficientEuclideanMap B).comp (coefficientEuclideanMap B).adjoint)
      hInv hGram.continuousAt
  exact hAdj.continuousAt.clm_comp hInvGram

/-- Tensor covariance intertwines the coefficient map with the transposed
physical action. -/
theorem coefficientEuclideanMap_covariance {d D : ℕ} (C : MPSTensor d D)
    (U : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin D) (Fin D) ℂ)
    (hCov : ∀ i, ∑ j, U i j • C j = V * C i * Vᴴ) :
    (coefficientEuclideanMap C).comp ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) Uᵀ) =
      (Matrix.conjugationEuclideanCLM V).comp (coefficientEuclideanMap C) := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨u, rfl⟩ := WithLp.toLp_surjective 2 x
  simp only [ContinuousLinearMap.comp_apply, Matrix.toEuclideanCLM_toLp,
    coefficientEuclideanMap_apply, Matrix.conjugationEuclideanCLM_apply]
  congr 1
  have hSum : Fintype.linearCombination ℂ C (Uᵀ *ᵥ u) =
      ∑ i, u i • (∑ j, U i j • C j) := by
    simp only [Fintype.linearCombination_apply, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [hSum]
  simp only [hCov, Fintype.linearCombination_apply, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- For an injective tensor, the virtual adjoint action is determined by the
physical action and the coefficient Gram right inverse. -/
theorem conjugationEuclideanCLM_eq_coefficients_of_isInjective {d D : ℕ}
    (C : MPSTensor d D) (hC : Kraus.IsInjective C)
    (U : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin D) (Fin D) ℂ)
    (hCov : ∀ i, ∑ j, U i j • C j = V * C i * Vᴴ) :
    Matrix.conjugationEuclideanCLM V = (coefficientEuclideanMap C).comp
      (((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) Uᵀ).comp
        (coefficientRightInverse C)) := by
  rw [← ContinuousLinearMap.comp_assoc, coefficientEuclideanMap_covariance C U V hCov,
    ContinuousLinearMap.comp_assoc, coefficientEuclideanMap_comp_rightInverse_of_isInjective C hC,
    ContinuousLinearMap.comp_id]

/-- Near an injective tensor, all virtual adjoint actions implementing the
same unitary physical action are uniformly close to the adjoint action at the
base tensor. No continuity of the virtual matrices is assumed. -/
theorem eventually_uniform_conjugationEuclideanCLM_of_covariance
    {G : Type*} {d D : ℕ} (C₀ : MPSTensor d D) (hC₀ : Kraus.IsInjective C₀)
    (U : G → Matrix.unitaryGroup (Fin d) ℂ)
    (V₀ : G → Matrix (Fin D) (Fin D) ℂ)
    (hCov₀ : ∀ g i, ∑ j, (U g : Matrix (Fin d) (Fin d) ℂ) i j • C₀ j =
      V₀ g * C₀ i * (V₀ g)ᴴ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ C in 𝓝 C₀, ∀ g (V : Matrix (Fin D) (Fin D) ℂ),
      (∀ i, ∑ j, (U g : Matrix (Fin d) (Fin d) ℂ) i j • C j = V * C i * Vᴴ) →
      ‖Matrix.conjugationEuclideanCLM V - Matrix.conjugationEuclideanCLM (V₀ g)‖ < ε := by
  have hUnit₀ := isUnit_self_comp_adjoint_of_surjective (coefficientEuclideanMap C₀)
    (coefficientEuclideanMap_surjective_of_isInjective C₀ hC₀)
  have hUnitEvent : ∀ᶠ C in 𝓝 C₀,
      IsUnit ((coefficientEuclideanMap C).comp (coefficientEuclideanMap C).adjoint) :=
    continuous_coefficientGram.continuousAt.eventually (Units.isOpen.mem_nhds hUnit₀)
  have hEstimate := ContinuousLinearMap.eventually_uniform_comp_sub_lt
    coefficientEuclideanMap coefficientRightInverse C₀
    continuous_coefficientEuclideanMap.continuousAt
    (continuousAt_coefficientRightInverse_of_isInjective C₀ hC₀)
    (fun g => (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ))
      ((U g : Matrix (Fin d) (Fin d) ℂ)ᵀ))
    (fun g => Matrix.norm_toEuclideanCLM_transpose_le_one (U g)) ε hε
  filter_upwards [hUnitEvent, hEstimate] with C hUnit hEstimate
  intro g V hCov
  have hVC : Matrix.conjugationEuclideanCLM V =
      (coefficientEuclideanMap C).comp
        (((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ))
          ((U g : Matrix (Fin d) (Fin d) ℂ)ᵀ)).comp (coefficientRightInverse C)) := by
    rw [← ContinuousLinearMap.comp_assoc,
      coefficientEuclideanMap_covariance C (U g) V hCov,
      ContinuousLinearMap.comp_assoc, coefficientEuclideanMap_comp_rightInverse_of_isUnit C hUnit,
      ContinuousLinearMap.comp_id]
  rw [hVC, conjugationEuclideanCLM_eq_coefficients_of_isInjective C₀ hC₀ (U g)
    (V₀ g) (hCov₀ g)]
  exact hEstimate g

end MPSTensor
