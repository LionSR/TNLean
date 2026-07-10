/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.RFP.CommutingBridge

/-!
# Appendix B tensor powers and two-site support

This file develops the local support construction arising from the Appendix B
basic-vector expression in arXiv:1606.00608, equations (3.16)--(3.18).  It
constructs every tensor power of the physical isometry, inserts the virtual bond
vector on two sites, identifies the resulting physical image with
\(G_2(\Lambda U)\), and constructs its orthogonal support projector.

The subsequent three-site commutator still requires the virtual projector onto
\(\mathbb C\varphi\), its two adjacent placements, and the spectator-complement
argument for the possibly non-surjective physical isometry.  That boundary is
recorded in `docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### Tensor powers of the physical isometry -/

/-- The coefficient map for the tensor power
\(U^{\otimes N}:(\mathcal H_a\otimes\mathcal H_b)^{\otimes N}
\to\mathcal H_{\mathrm{phys}}^{\otimes N}\).

For a virtual-pair configuration \(p=(p_t)_{t=0}^{N-1}\), its image has
coefficient
\[
  (U^{\otimes N}v)_\sigma
  =\sum_p\prod_{t=0}^{N-1}U^{\sigma_t}_{(p_t)_a,(p_t)_b}\,v_p.
\]

Source: arXiv:1606.00608, basic-vector equation (3.17), lines 564--578. -/
noncomputable def AppendixBStructuralData.physicalIsometryTensorPower
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) (N : ℕ) :
    (((Fin N → Fin D × Fin D) → ℂ) →ₗ[ℂ] NSiteSpace d N) where
  toFun v σ := ∑ p : Fin N → Fin D × Fin D,
    (∏ t : Fin N, hStruct.U (σ t) (p t).1 (p t).2) * v p
  map_add' v w := by
    funext σ
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext σ
    change (∑ p : Fin N → Fin D × Fin D,
      (∏ t : Fin N, hStruct.U (σ t) (p t).1 (p t).2) * (c * v p)) =
        c * ∑ p : Fin N → Fin D × Fin D,
          (∏ t : Fin N, hStruct.U (σ t) (p t).1 (p t).2) * v p
    calc
      _ = ∑ p : Fin N → Fin D × Fin D,
          c * ((∏ t : Fin N, hStruct.U (σ t) (p t).1 (p t).2) * v p) := by
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ = _ := by rw [Finset.mul_sum]

/-- The conjugate coefficient map \(U^{*\otimes N}\) associated with the
physical tensor power.

Source: arXiv:1606.00608, pair-index isometry equation (3.16) and basic-vector
equation (3.17), lines 549--578. -/
noncomputable def AppendixBStructuralData.physicalIsometryTensorPowerLeftInverse
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) (N : ℕ) :
    (NSiteSpace d N →ₗ[ℂ] ((Fin N → Fin D × Fin D) → ℂ)) where
  toFun ψ p := ∑ σ : Cfg d N,
    (∏ t : Fin N, star (hStruct.U (σ t) (p t).1 (p t).2)) * ψ σ
  map_add' ψ φ := by
    funext p
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c ψ := by
    funext p
    change (∑ σ : Cfg d N,
      (∏ t : Fin N, star (hStruct.U (σ t) (p t).1 (p t).2)) * (c * ψ σ)) =
        c * ∑ σ : Cfg d N,
          (∏ t : Fin N, star (hStruct.U (σ t) (p t).1 (p t).2)) * ψ σ
    calc
      _ = ∑ σ : Cfg d N,
          c * ((∏ t : Fin N, star (hStruct.U (σ t) (p t).1 (p t).2)) * ψ σ) := by
        apply Finset.sum_congr rfl
        intro σ _
        ring
      _ = _ := by rw [Finset.mul_sum]

/-- The source pair-index isometry equation gives
\(U^{*\otimes N}U^{\otimes N}=1\) at every tensor power.

Source: arXiv:1606.00608, equations (3.16)--(3.17), lines 549--578. -/
@[simp] theorem AppendixBStructuralData.physicalIsometryTensorPowerLeftInverse_comp
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) (N : ℕ) :
    (hStruct.physicalIsometryTensorPowerLeftInverse N).comp
        (hStruct.physicalIsometryTensorPower N) = 1 := by
  classical
  apply LinearMap.ext
  intro v
  funext p
  change (∑ σ : Cfg d N,
    (∏ t : Fin N, star (hStruct.U (σ t) (p t).1 (p t).2)) *
      ∑ q : Fin N → Fin D × Fin D,
        (∏ t : Fin N, hStruct.U (σ t) (q t).1 (q t).2) * v q) = v p
  let g (q : Fin N → Fin D × Fin D) (t : Fin N) (i : Fin d) : ℂ :=
    star (hStruct.U i (p t).1 (p t).2) * hStruct.U i (q t).1 (q t).2
  have hfactor (q : Fin N → Fin D × Fin D) :
      Finset.univ.sum (fun σ : Cfg d N ↦
        Finset.univ.prod fun t : Fin N ↦ g q t (σ t)) =
        Finset.univ.prod (fun t : Fin N ↦ Finset.univ.sum fun i : Fin d ↦ g q t i) := by
    simpa only [Fintype.piFinset_univ] using
      (Finset.sum_prod_piFinset (R := ℂ) (Finset.univ : Finset (Fin d))
        (fun t i ↦ g q t i))
  have hdelta (q : Fin N → Fin D × Fin D) :
      (∏ t : Fin N, if p t = q t then (1 : ℂ) else 0) =
        if p = q then 1 else 0 := by
    by_cases hpq : p = q
    · subst q
      simp
    · rw [if_neg hpq]
      have hpoint : ∃ t : Fin N, p t ≠ q t := by
        apply not_forall.mp
        intro h
        exact hpq (funext h)
      obtain ⟨t, ht⟩ := hpoint
      exact Finset.prod_eq_zero (Finset.mem_univ t) (if_neg ht)
  calc
    _ = ∑ σ : Cfg d N, ∑ q : Fin N → Fin D × Fin D,
        ((∏ t : Fin N, star (hStruct.U (σ t) (p t).1 (p t).2)) *
          (∏ t : Fin N, hStruct.U (σ t) (q t).1 (q t).2)) * v q := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = ∑ q : Fin N → Fin D × Fin D,
        (∑ σ : Cfg d N, (∏ t : Fin N,
          star (hStruct.U (σ t) (p t).1 (p t).2) *
            hStruct.U (σ t) (q t).1 (q t).2)) * v q := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      rw [← Finset.sum_mul]
      simp_rw [← Finset.prod_mul_distrib]
    _ = ∑ q : Fin N → Fin D × Fin D,
        (Finset.univ.prod fun t : Fin N ↦ ∑ i : Fin d,
          star (hStruct.U i (p t).1 (p t).2) *
            hStruct.U i (q t).1 (q t).2) * v q := by
      apply Finset.sum_congr rfl
      intro q _
      rw [show (∑ σ : Cfg d N, ∏ t : Fin N,
          star (hStruct.U (σ t) (p t).1 (p t).2) *
            hStruct.U (σ t) (q t).1 (q t).2) =
          ∏ t : Fin N, ∑ i : Fin d,
            star (hStruct.U i (p t).1 (p t).2) *
              hStruct.U i (q t).1 (q t).2 by
        simpa [g] using hfactor q]
    _ = v p := by
      simp_rw [hStruct.hU_pair]
      simp_rw [hdelta]
      simp

/-- Every tensor power of the physical map is injective.

Source: arXiv:1606.00608, equations (3.16)--(3.17), lines 549--578. -/
theorem AppendixBStructuralData.physicalIsometryTensorPower_injective
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) (N : ℕ) :
    Function.Injective (hStruct.physicalIsometryTensorPower N) :=
  LinearMap.injective_of_comp_eq_id _ _
    (hStruct.physicalIsometryTensorPowerLeftInverse_comp N)

/-! ### The two-site virtual bond -/

/-- Insert the bond vector
\(\varphi=\sum_b\lambda_b\lvert b,b\rangle\) between two virtual site pairs.

For outer-boundary coefficients \(v_{a,c}\), the resulting four-index tensor is
\[
  (I_\varphi v)_{(a,b),(b',c)}
  =\delta_{b,b'}\lambda_b v_{a,c}.
\]

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
noncomputable def AppendixBStructuralData.twoSiteBondInsertion
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    ((Fin D × Fin D → ℂ) →ₗ[ℂ] ((Fin 2 → Fin D × Fin D) → ℂ)) where
  toFun v p :=
    if (p 0).2 = (p 1).1 then
      (hStruct.Λ (p 0).2 : ℂ) * v ((p 0).1, (p 1).2)
    else 0
  map_add' v w := by
    funext p
    by_cases h : (p 0).2 = (p 1).1
    · simp [h, mul_add]
    · simp [h]
  map_smul' c v := by
    funext p
    by_cases h : (p 0).2 = (p 1).1
    · simp [h, mul_assoc, mul_comm]
    · simp [h]

/-- The two-site basic-vector embedding
\(U^{\otimes 2}I_\varphi\), with the bond vector inserted between the two
neighboring virtual sites.

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
noncomputable def AppendixBStructuralData.twoSiteBasicEmbedding
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    ((Fin D × Fin D → ℂ) →ₗ[ℂ] NSiteSpace d 2) :=
  (hStruct.physicalIsometryTensorPower 2).comp hStruct.twoSiteBondInsertion

/-- Identify a boundary matrix \(Y\) with its two outer virtual indices by
\(v_{a,c}=\lambda_aY_{c,a}\).

Strict positivity of the diagonal weights makes this map surjective. It is the
boundary reparametrization that relates the two-site matrix-product map to the
bond-insertion expression.

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
noncomputable def AppendixBStructuralData.weightedTwoSiteBoundary
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    (Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] (Fin D × Fin D → ℂ)) where
  toFun X ac := (hStruct.Λ ac.1 : ℂ) * X ac.2 ac.1
  map_add' X Y := by
    funext ac
    simp only [Pi.add_apply, Matrix.add_apply, mul_add]
  map_smul' c X := by
    funext ac
    change (hStruct.Λ ac.1 : ℂ) * (c * X ac.2 ac.1) =
      c * ((hStruct.Λ ac.1 : ℂ) * X ac.2 ac.1)
    ring

/-- The weighted outer-boundary parametrization is surjective.

Source: arXiv:1606.00608, Theorem 3.11 and equations (3.17)--(3.18), lines
543--578. -/
theorem AppendixBStructuralData.weightedTwoSiteBoundary_surjective
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    Function.Surjective hStruct.weightedTwoSiteBoundary := by
  intro v
  refine ⟨fun c a ↦ (hStruct.Λ a : ℂ)⁻¹ * v (a, c), ?_⟩
  funext ac
  simp [AppendixBStructuralData.weightedTwoSiteBoundary,
    ne_of_gt (hStruct.hΛ_pos ac.1)]

/-- The bond-insertion expression is the two-site matrix-product map after the
weighted boundary reparametrization:
\[
  U^{\otimes2}I_\varphi(v_Y)=\Gamma_2(\Lambda U)(Y),
  \qquad (v_Y)_{a,c}=\lambda_aY_{c,a}.
\]

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
theorem AppendixBStructuralData.twoSiteBasicEmbedding_comp_weightedBoundary
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    hStruct.twoSiteBasicEmbedding.comp hStruct.weightedTwoSiteBoundary =
      groundSpaceMap hStruct.coreTensor 2 := by
  classical
  apply LinearMap.ext
  intro X
  funext σ
  rw [groundSpaceMap_apply]
  change (∑ p : Fin 2 → Fin D × Fin D,
      (∏ t : Fin 2, hStruct.U (σ t) (p t).1 (p t).2) *
        (if (p 0).2 = (p 1).1 then
          (hStruct.Λ (p 0).2 : ℂ) *
            ((hStruct.Λ (p 0).1 : ℂ) * X (p 1).2 (p 0).1)
        else 0)) =
      Matrix.trace (evalWord hStruct.coreTensor (List.ofFn σ) * X)
  calc
    _ = ∑ p₀ : Fin D × Fin D, ∑ p₁ : Fin D × Fin D,
        hStruct.U (σ 0) p₀.1 p₀.2 * hStruct.U (σ 1) p₁.1 p₁.2 *
          (if p₀.2 = p₁.1 then
            (hStruct.Λ p₀.2 : ℂ) * ((hStruct.Λ p₀.1 : ℂ) * X p₁.2 p₀.1)
          else 0) := by
      rw [← (finTwoArrowEquiv (Fin D × Fin D)).symm.sum_comp]
      rw [Fintype.sum_prod_type]
      simp [finTwoArrowEquiv_symm_apply, Fin.prod_univ_two]
    _ = ∑ a : Fin D, ∑ b : Fin D, ∑ c : Fin D,
        hStruct.U (σ 0) a b * hStruct.U (σ 1) b c *
          ((hStruct.Λ b : ℂ) * ((hStruct.Λ a : ℂ) * X c a)) := by
      simp [Fintype.sum_prod_type]
    _ = Matrix.trace (evalWord hStruct.coreTensor (List.ofFn σ) * X) := by
      rw [show evalWord hStruct.coreTensor (List.ofFn σ) =
          hStruct.coreTensor (σ 0) * hStruct.coreTensor (σ 1) by
        simp [evalWord, List.ofFn_succ, List.ofFn_zero]]
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
      simp only [AppendixBStructuralData.coreTensor_apply, Matrix.diagonal_mul]
      simp_rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro b _
      ring

/-- The two-site bond-insertion image is exactly the Appendix B basic support:
\[
  \operatorname{ran}(U^{\otimes2}I_\varphi)=G_2(\Lambda U).
\]

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
theorem AppendixBStructuralData.twoSiteBasicEmbedding_range
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    LinearMap.range hStruct.twoSiteBasicEmbedding = hStruct.twoSiteBasicSpace := by
  rw [AppendixBStructuralData.twoSiteBasicSpace, groundSpace]
  apply le_antisymm
  · rintro ψ ⟨v, rfl⟩
    obtain ⟨X, rfl⟩ := hStruct.weightedTwoSiteBoundary_surjective v
    refine ⟨X, ?_⟩
    exact (LinearMap.congr_fun hStruct.twoSiteBasicEmbedding_comp_weightedBoundary X).symm
  · rintro ψ ⟨X, rfl⟩
    refine ⟨hStruct.weightedTwoSiteBoundary X, ?_⟩
    exact LinearMap.congr_fun hStruct.twoSiteBasicEmbedding_comp_weightedBoundary X

/-- The orthogonal support projector of the two-site basic-vector image
\(G_2(\Lambda U)\).

The virtual orthogonal projector onto \(\mathbb C\varphi\), its two adjacent
placements on a three-site virtual chain, and their transport to
range-restricted overlapping operators remain separate steps. These operators
must then be extended to the full physical \(AX\) and \(XB\) support projectors.
Since \(U\) need not be surjective, this extension must account for the
spectator complement of \(UU^*\).

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578, and
Definition D.2, lines 2205--2218. -/
noncomputable def AppendixBStructuralData.twoSiteBasicSupportProjection
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2 :=
  let e := WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)
  e.toLinearMap.comp ((groundSpaceES hStruct.coreTensor 2).starProjection.toLinearMap.comp
    e.symm.toLinearMap)

/-- The range of the two-site support projector is the Appendix B basic support.

Source: arXiv:1606.00608, lines 511--524 and 564--578. -/
theorem AppendixBStructuralData.twoSiteBasicSupportProjection_range
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    LinearMap.range hStruct.twoSiteBasicSupportProjection = hStruct.twoSiteBasicSpace := by
  rw [AppendixBStructuralData.twoSiteBasicSpace]
  ext ψ
  constructor
  · rintro ⟨v, rfl⟩
    change (WithLp.linearEquiv 2 ℂ (NSiteSpace d 2))
      ((groundSpaceES hStruct.coreTensor 2).starProjection
        ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm v)) ∈
        groundSpace hStruct.coreTensor 2
    apply (mem_groundSpaceES_iff hStruct.coreTensor 2 _).1
    exact Submodule.starProjection_apply_mem _ _
  · intro hψ
    refine ⟨ψ, ?_⟩
    change (WithLp.linearEquiv 2 ℂ (NSiteSpace d 2))
      ((groundSpaceES hStruct.coreTensor 2).starProjection
        ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm ψ)) = ψ
    have hψES : (WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm ψ ∈
        groundSpaceES hStruct.coreTensor 2 := by
      apply (mem_groundSpaceES_iff hStruct.coreTensor 2 _).2
      simpa using hψ
    rw [Submodule.starProjection_eq_self_iff.mpr hψES,
      LinearEquiv.apply_symm_apply]

/-- The two-site support projector is complementary to the canonical parent
interaction of the core tensor:
\(P_{G_2(\Lambda U)}=1-q_2(\Lambda U)\).

Source: arXiv:1606.00608, parent construction, lines 511--524. -/
theorem AppendixBStructuralData.twoSiteBasicSupportProjection_eq_complement
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    hStruct.twoSiteBasicSupportProjection =
      1 - parentInteraction hStruct.coreTensor 2 := by
  apply LinearMap.ext
  intro v
  change (WithLp.linearEquiv 2 ℂ (NSiteSpace d 2))
      ((groundSpaceES hStruct.coreTensor 2).starProjection
        ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm v)) =
    v - (WithLp.linearEquiv 2 ℂ (NSiteSpace d 2))
      ((groundSpaceES hStruct.coreTensor 2)ᗮ.starProjection
        ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm v))
  rw [Submodule.starProjection_orthogonal_val]
  simp

/-- The two-site basic support operator is idempotent.

Source: arXiv:1606.00608, parent construction, lines 511--524. -/
theorem AppendixBStructuralData.twoSiteBasicSupportProjection_idempotent
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    hStruct.twoSiteBasicSupportProjection * hStruct.twoSiteBasicSupportProjection =
      hStruct.twoSiteBasicSupportProjection := by
  rw [hStruct.twoSiteBasicSupportProjection_eq_complement]
  apply LinearMap.ext
  intro v
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub]
  have hq := LinearMap.congr_fun (parentInteraction_idempotent hStruct.coreTensor 2) v
  simp only [Module.End.mul_apply] at hq
  rw [hq]
  abel

/-- The range of the support projector is the range of the bond-insertion
embedding \(U^{\otimes2}I_\varphi\).

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
theorem AppendixBStructuralData.twoSiteBasicSupportProjection_range_eq_embedding
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    LinearMap.range hStruct.twoSiteBasicSupportProjection =
      LinearMap.range hStruct.twoSiteBasicEmbedding := by
  rw [hStruct.twoSiteBasicSupportProjection_range,
    hStruct.twoSiteBasicEmbedding_range]

/-- The canonical parent interaction annihilates every vector in the two-site
bond-insertion image.

Source: arXiv:1606.00608, parent construction, lines 511--524, and equations
(3.17)--(3.18), lines 564--578. -/
theorem AppendixBStructuralData.parentInteraction_apply_twoSiteBasicEmbedding
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (v : Fin D × Fin D → ℂ) :
    parentInteraction hStruct.coreTensor 2 (hStruct.twoSiteBasicEmbedding v) = 0 := by
  apply parentInteraction_apply_mem_groundSpace
  rw [← AppendixBStructuralData.twoSiteBasicSpace]
  rw [← hStruct.twoSiteBasicEmbedding_range]
  exact ⟨v, rfl⟩

/-- The two-site support projector fixes the bond-insertion image pointwise.

Source: arXiv:1606.00608, parent construction, lines 511--524, and equations
(3.17)--(3.18), lines 564--578. -/
theorem AppendixBStructuralData.twoSiteBasicSupportProjection_apply_embedding
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (v : Fin D × Fin D → ℂ) :
    hStruct.twoSiteBasicSupportProjection (hStruct.twoSiteBasicEmbedding v) =
      hStruct.twoSiteBasicEmbedding v := by
  rw [hStruct.twoSiteBasicSupportProjection_eq_complement]
  simp [LinearMap.sub_apply, Module.End.one_apply,
    hStruct.parentInteraction_apply_twoSiteBasicEmbedding v]

/-- The range, complement, and pointwise characterization of the two-site
basic support projector.

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578, and
Definition D.2, lines 2205--2218. -/
theorem AppendixBStructuralData.twoSiteBasicSupportProjection_spec
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    hStruct.twoSiteBasicSupportProjection * hStruct.twoSiteBasicSupportProjection =
        hStruct.twoSiteBasicSupportProjection ∧
      LinearMap.range hStruct.twoSiteBasicSupportProjection =
        LinearMap.range hStruct.twoSiteBasicEmbedding ∧
      hStruct.twoSiteBasicSupportProjection =
        1 - parentInteraction hStruct.coreTensor 2 ∧
      ∀ v : Fin D × Fin D → ℂ,
        parentInteraction hStruct.coreTensor 2 (hStruct.twoSiteBasicEmbedding v) = 0 ∧
        hStruct.twoSiteBasicSupportProjection (hStruct.twoSiteBasicEmbedding v) =
          hStruct.twoSiteBasicEmbedding v := by
  exact ⟨hStruct.twoSiteBasicSupportProjection_idempotent,
    hStruct.twoSiteBasicSupportProjection_range_eq_embedding,
    hStruct.twoSiteBasicSupportProjection_eq_complement,
    fun v ↦ ⟨hStruct.parentInteraction_apply_twoSiteBasicEmbedding v,
      hStruct.twoSiteBasicSupportProjection_apply_embedding v⟩⟩

end MPSTensor
