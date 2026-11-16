/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Module.Connected
import QICLean.Algebra.MatrixUnitaryBetween

/-!
# Paths of orthogonal matrices with a fixed determinant

Two real orthogonal matrices with the same determinant are joined by a path of
orthogonal matrices. By the Cartan--Dieudonné theorem an orthogonal map is a
product of reflections, an even number of them when its determinant is one.
On a space of dimension at least two any two reflections are joined by moving
the reflected unit vector along the sphere, so the product is joined to an
even power of one reflection, which is the identity.

The last statement transfers this to complex matrices with real entries that
are unitary between two finite coordinate spaces, as for the gates of a
standard form with real entries.

This is the step "the group of orthogonal transformations with a fixed
determinant is simply connected, we can always find a smooth orthogonal
interpolation" of arXiv:1703.09188, proof of Theorem `conjphs`, lines
1438--1442; only path-connectedness is used there.
-/

open scoped Matrix InnerProductSpace
open Module

noncomputable section

namespace Unitary

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The reflection in the hyperplane orthogonal to `v`, as a unitary operator.
For `v = 0` it is the identity. -/
def hyperplaneReflection (v : F) : unitary (F →L[ℝ] F) :=
  linearIsometryEquiv.symm (ℝ ∙ v)ᗮ.reflection

theorem coe_hyperplaneReflection (v : F) :
    (hyperplaneReflection v : F →L[ℝ] F) = ((ℝ ∙ v)ᗮ.reflection : F →L[ℝ] F) :=
  coe_symm_linearIsometryEquiv_apply _

theorem hyperplaneReflection_smul (v : F) {c : ℝ} (hc : c ≠ 0) :
    hyperplaneReflection (c • v) = hyperplaneReflection v := by
  simp only [hyperplaneReflection, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]

theorem hyperplaneReflection_zero : hyperplaneReflection (0 : F) = 1 := by
  apply linearIsometryEquiv.injective
  rw [hyperplaneReflection, MulEquiv.apply_symm_apply, map_one]
  ext x
  simp [Submodule.span_zero_singleton, Submodule.bot_orthogonal_eq_top,
    Submodule.reflection_eq_self_iff]

theorem hyperplaneReflection_mul_self (v : F) :
    hyperplaneReflection v * hyperplaneReflection v = 1 := by
  rw [hyperplaneReflection, ← map_mul, Submodule.reflection_mul_reflection, map_one]

/-- For a unit vector `s`, the reflection is `x ↦ x - 2 ⟪s, x⟫ s`. -/
theorem coe_hyperplaneReflection_of_norm_eq_one {s : F} (hs : ‖s‖ = 1) :
    (hyperplaneReflection s : F →L[ℝ] F) = 1 - (2 : ℝ) • (innerSL ℝ s).smulRight s := by
  ext x
  rw [coe_hyperplaneReflection]
  change (ℝ ∙ s)ᗮ.reflection x = _
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp [hs, two_smul]

/-- On a space of dimension at least two, any two reflections in hyperplanes
are joined in the unitary group. -/
theorem joined_hyperplaneReflection (hF : 1 < finrank ℝ F) {v w : F} (hv : v ≠ 0)
    (hw : w ≠ 0) : Joined (hyperplaneReflection v) (hyperplaneReflection w) := by
  have hrank : 1 < Module.rank ℝ F := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast hF
  have hsph := isPathConnected_sphere hrank (0 : F) zero_le_one
  have hmem : ∀ {u : F}, u ≠ 0 → ‖u‖⁻¹ • u ∈ Metric.sphere (0 : F) 1 := fun hu ↦ by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]
  obtain ⟨γ, hγ⟩ := hsph.joinedIn _ (hmem hv) _ (hmem hw)
  have hcont : Continuous fun t ↦ (hyperplaneReflection (γ t) : F →L[ℝ] F) := by
    have : (fun t ↦ (hyperplaneReflection (γ t) : F →L[ℝ] F)) =
        fun t ↦ 1 - (2 : ℝ) • (innerSL ℝ (γ t)).smulRight (γ t) := by
      funext t
      exact coe_hyperplaneReflection_of_norm_eq_one (mem_sphere_zero_iff_norm.mp (hγ t))
    rw [this]
    have h : Continuous fun t ↦ ContinuousLinearMap.smulRightL ℝ F F (innerSL ℝ (γ t)) (γ t) := by
      fun_prop
    exact continuous_const.sub ((continuous_const (y := (2 : ℝ))).smul h)
  have hv' := hyperplaneReflection_smul v (inv_ne_zero (norm_ne_zero_iff.mpr hv))
  have hw' := hyperplaneReflection_smul w (inv_ne_zero (norm_ne_zero_iff.mpr hw))
  refine ⟨⟨⟨fun t ↦ hyperplaneReflection (γ t), hcont.subtype_mk _⟩, ?_, ?_⟩⟩
  · simp [hv']
  · simp [hw']

omit [FiniteDimensional ℝ F] in
private theorem det_toLinearMap_mul (φ ψ : F ≃ₗᵢ[ℝ] F) :
    LinearMap.det (φ * ψ).toLinearMap = LinearMap.det φ.toLinearMap *
      LinearMap.det ψ.toLinearMap := by
  rw [← LinearMap.det_comp]
  rfl

open scoped Classical in
/-- A product of reflections in hyperplanes is joined to the power of one fixed
reflection by the number of nonzero normal vectors, and that power has the
parity of the determinant. -/
private theorem joined_list_prod_reflection (hF : 1 < finrank ℝ F) {e : F} (he : e ≠ 0)
    (l : List F) :
    Joined (linearIsometryEquiv.symm (l.map fun v ↦ (ℝ ∙ v)ᗮ.reflection).prod)
        (hyperplaneReflection e ^ (l.filter fun v ↦ decide (v ≠ 0)).length) ∧
      LinearMap.det (l.map fun v ↦ (ℝ ∙ v)ᗮ.reflection).prod.toLinearMap =
        (-1) ^ (l.filter fun v ↦ decide (v ≠ 0)).length := by
  induction l with
  | nil => exact ⟨Joined.refl _, LinearMap.det_id⟩
  | cons v l ih =>
    obtain ⟨hJ, hdet⟩ := ih
    simp only [List.map_cons, List.prod_cons, map_mul]
    rw [det_toLinearMap_mul, hdet, Submodule.det_reflection]
    by_cases hv : v = 0
    · subst hv
      have h0 := hyperplaneReflection_zero (F := F)
      rw [hyperplaneReflection] at h0
      rw [h0, one_mul, Submodule.orthogonal_orthogonal, Submodule.span_zero_singleton,
        finrank_bot, pow_zero, one_mul, List.filter_cons_of_neg (by simp)]
      exact ⟨hJ, rfl⟩
    · rw [List.filter_cons_of_pos (by simpa using hv), List.length_cons, pow_succ', pow_succ',
        Submodule.orthogonal_orthogonal, finrank_span_singleton hv, pow_one]
      exact ⟨(joined_hyperplaneReflection hF hv he).mul hJ, rfl⟩

/-- **Orthogonal maps of determinant one are joined to the identity.** On a
finite-dimensional real inner product space, a linear isometric equivalence of
determinant one is joined to the identity in the unitary group of operators.

Source: arXiv:1703.09188, proof of Theorem `conjphs`, lines 1438--1442. -/
theorem joined_one_linearIsometryEquiv_symm (φ : F ≃ₗᵢ[ℝ] F)
    (hdet : LinearMap.det φ.toLinearMap = 1) :
    Joined 1 (linearIsometryEquiv.symm φ) := by
  by_cases hF : 1 < finrank ℝ F
  · have : Nontrivial F := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
    obtain ⟨e, he⟩ := exists_ne (0 : F)
    obtain ⟨l, -, rfl⟩ := φ.reflections_generate_dim
    classical
    obtain ⟨hJ, hd⟩ := joined_list_prod_reflection hF he l
    rw [hdet] at hd
    obtain ⟨k, hk⟩ := ((neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hd.symm)
    rw [hk, ← two_mul, pow_mul, sq, hyperplaneReflection_mul_self, one_pow] at hJ
    exact hJ.symm
  · -- In dimension at most one, an isometry of determinant one is the identity.
    have hφ : φ = 1 := by
      rcases Nat.lt_or_ge (finrank ℝ F) 1 with h | h
      · have : Subsingleton F := (Module.finrank_zero_iff (R := ℝ)).mp (by omega)
        ext x
        exact Subsingleton.elim _ _
      · obtain ⟨c, hc⟩ : ∃ c : ℝ, φ.toLinearMap = c • LinearMap.id :=
          (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one (by omega) _).exists
        rw [hc, LinearMap.det_smul, LinearMap.det_id, mul_one, (by omega : finrank ℝ F = 1),
          pow_one] at hdet
        ext x
        have := congrArg (fun f : F →ₗ[ℝ] F ↦ f x) hc
        simpa [hdet] using this
    rw [hφ, map_one]

end Unitary

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem mem_unitary_starAlgEquiv {R S : Type*} [Ring R] [StarRing R] [Ring S]
    [StarRing S] [Algebra ℝ R] [Algebra ℝ S] (f : R ≃⋆ₐ[ℝ] S) {x : R} (hx : x ∈ unitary R) :
    f x ∈ unitary S := by
  rw [Unitary.mem_iff] at hx ⊢
  rw [← map_star, ← map_mul, ← map_mul, hx.1, hx.2, map_one]
  exact ⟨rfl, rfl⟩

/-- **Real orthogonal matrices of determinant one are joined to the identity**
in the orthogonal group.

Source: arXiv:1703.09188, proof of Theorem `conjphs`, lines 1438--1442. -/
theorem joined_one_unitaryGroup_real (A : unitaryGroup n ℝ)
    (hA : (A : Matrix n n ℝ).det = 1) : Joined 1 A := by
  let E := EuclideanSpace ℝ n
  let T := toEuclideanCLM (n := n) (𝕜 := ℝ)
  let U : unitary (E →L[ℝ] E) := ⟨T A, mem_unitary_starAlgEquiv T A.2⟩
  have hdet : LinearMap.det (Unitary.linearIsometryEquiv U).toLinearMap = 1 := by
    have : (Unitary.linearIsometryEquiv U).toLinearMap = toEuclideanLin (A : Matrix n n ℝ) :=
      LinearMap.ext fun x ↦ rfl
    rw [this, toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin, hA]
  have hJ := Unitary.joined_one_linearIsometryEquiv_symm _ hdet
  rw [MulEquiv.symm_apply_apply] at hJ
  have hc : Continuous fun f : E →L[ℝ] E ↦ T.symm f :=
    LinearMap.continuous_of_finiteDimensional T.symm.toAlgEquiv.toLinearMap
  let ψ : unitary (E →L[ℝ] E) → unitaryGroup n ℝ := fun u ↦
    ⟨T.symm u, mem_unitary_starAlgEquiv T.symm u.2⟩
  have hψ : Continuous ψ := (hc.comp continuous_subtype_val).subtype_mk _
  have h1 : ψ 1 = 1 := Subtype.ext (map_one T.symm)
  have hU : ψ U = A := Subtype.ext (T.symm_apply_apply _)
  simpa [h1, hU] using hJ.map hψ

/-- Two real orthogonal matrices with the same determinant are joined in the
orthogonal group. Source: arXiv:1703.09188, proof of Theorem `conjphs`,
lines 1438--1442. -/
theorem joined_unitaryGroup_real_of_det_eq (A B : unitaryGroup n ℝ)
    (h : (A : Matrix n n ℝ).det = (B : Matrix n n ℝ).det) : Joined A B := by
  have hA : (A : Matrix n n ℝ).det * (A : Matrix n n ℝ).det = 1 := by
    have := congrArg det (Unitary.mem_iff.mp A.2).1
    rwa [det_mul, star_eq_conjTranspose, det_conjTranspose, det_one,
      star_trivial] at this
  have hC : ((B * star A : unitaryGroup n ℝ) : Matrix n n ℝ).det = 1 := by
    change ((B : Matrix n n ℝ) * star (A : Matrix n n ℝ)).det = 1
    rw [det_mul, star_eq_conjTranspose, det_conjTranspose,
      star_trivial, ← h, hA]
  have := (joined_one_unitaryGroup_real _ hC).mul (Joined.refl A)
  rwa [one_mul, mul_assoc, Unitary.star_mul_self, mul_one] at this

/-- **Real unitary gates with the same determinant are joined.** Let `A` and
`B` be complex matrices with real entries that are unitary between the
coordinate spaces `k` and `m`. If their determinants, read through one
identification `e` of `m` with `k`, agree, then `A` and `B` are joined by a
path of such matrices.

Source: arXiv:1703.09188, proof of Theorem `conjphs`, lines 1438--1442
("since the group of orthogonal transformations with a fixed determinant is
simply connected, we can always find a smooth orthogonal interpolation"). -/
theorem IsUnitaryBetween.joinedIn_real_of_det_eq {m k : Type*} [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k] (e : m ≃ k) {A B : Matrix m k ℂ}
    (hA : A.IsUnitaryBetween) (hB : B.IsUnitaryBetween)
    (hAr : A.map (starRingEnd ℂ) = A) (hBr : B.map (starRingEnd ℂ) = B)
    (hdet : (A.submatrix id e).det = (B.submatrix id e).det) :
    JoinedIn {X : Matrix m k ℂ | X.IsUnitaryBetween ∧ X.map (starRingEnd ℂ) = X} A B := by
  -- Real parts of the square matrices read through `e`.
  have hreal : ∀ {X : Matrix m k ℂ}, X.map (starRingEnd ℂ) = X →
      ((X.submatrix id e).map Complex.re).map Complex.ofRealHom = X.submatrix id e := by
    intro X hX
    ext i j
    have := congrFun (congrFun hX i) (e j)
    simp only [map_apply, submatrix_apply, id_eq, Complex.ofRealHom_eq_coe] at this ⊢
    exact Complex.conj_eq_iff_re.mp this
  have hinj : Function.Injective (fun R : Matrix m m ℝ ↦ R.map Complex.ofRealHom) :=
    fun R S h ↦ by
      ext i j
      exact Complex.ofReal_injective (congrFun (congrFun h i) j)
  have hstar : ∀ R : Matrix m m ℝ, (R.map Complex.ofRealHom)ᴴ = (star R).map Complex.ofRealHom :=
    fun R ↦ by
      ext i j
      simp [conjTranspose_apply, star_apply]
  have hunit : ∀ {X : Matrix m k ℂ}, X.IsUnitaryBetween → X.map (starRingEnd ℂ) = X →
      (X.submatrix id e).map Complex.re ∈ unitaryGroup m ℝ := by
    intro X hX hXr
    have hsq : (X.submatrix id e).IsUnitaryBetween := by
      simpa [reindex_apply] using hX.reindex X (Equiv.refl m) e.symm
    have hU := (isUnitaryBetween_iff_mem_unitaryGroup _).mp hsq
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose] at hU
    have hU' : ((X.submatrix id e).map Complex.re).map Complex.ofRealHom *
        (((X.submatrix id e).map Complex.re).map Complex.ofRealHom)ᴴ = 1 := by
      rw [hreal hXr]
      exact hU
    rw [hstar, ← Matrix.map_mul] at hU'
    rw [mem_unitaryGroup_iff]
    apply hinj
    change _ = (1 : Matrix m m ℝ).map Complex.ofRealHom
    exact hU'.trans (Matrix.map_one _ (map_zero _) (map_one _)).symm
  let Ar : unitaryGroup m ℝ := ⟨_, hunit hA hAr⟩
  let Br : unitaryGroup m ℝ := ⟨_, hunit hB hBr⟩
  have hdetR : (Ar : Matrix m m ℝ).det = (Br : Matrix m m ℝ).det := by
    apply Complex.ofReal_injective
    have h₁ := (Complex.ofRealHom.map_det (Ar : Matrix m m ℝ)).symm
    have h₂ := (Complex.ofRealHom.map_det (Br : Matrix m m ℝ)).symm
    simp only [RingHom.mapMatrix_apply] at h₁ h₂
    change Complex.ofRealHom _ = Complex.ofRealHom _
    rw [← h₁, ← h₂]
    change (((A.submatrix id e).map Complex.re).map Complex.ofRealHom).det =
      (((B.submatrix id e).map Complex.re).map Complex.ofRealHom).det
    rw [hreal hAr, hreal hBr, hdet]
  obtain ⟨γ⟩ := joined_unitaryGroup_real_of_det_eq Ar Br hdetR
  let F : unitaryGroup m ℝ → Matrix m k ℂ := fun g ↦
    ((g : Matrix m m ℝ).map Complex.ofRealHom).submatrix id e.symm
  have hF : Continuous F :=
    ((continuous_subtype_val.matrix_map Complex.continuous_ofReal).matrix_submatrix _ _)
  have hback : ∀ {X : Matrix m k ℂ}, X.map (starRingEnd ℂ) = X →
      (((X.submatrix id e).map Complex.re).map Complex.ofRealHom).submatrix id e.symm = X := by
    intro X hX
    rw [hreal hX]
    ext i j
    simp
  refine ⟨(γ.map hF).cast (hback hAr).symm (hback hBr).symm, fun t ↦ ⟨?_, ?_⟩⟩
  · have hsq : (((γ t : unitaryGroup m ℝ) : Matrix m m ℝ).map Complex.ofRealHom) ∈
        unitaryGroup m ℂ := by
      have h := (γ t).2
      rw [mem_unitaryGroup_iff] at h ⊢
      rw [star_eq_conjTranspose, hstar, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _)
        (map_one _)]
    have := ((isUnitaryBetween_iff_mem_unitaryGroup _).mpr hsq).reindex _ (Equiv.refl m) e
    simpa [reindex_apply, F] using this
  · ext i j
    simp [F]

end Matrix

end
