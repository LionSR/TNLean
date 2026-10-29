/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteStandardFormSourceCuts
import TNLean.MPS.MPU.StaircaseUnitarity
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Minimal supplied half factors from the shifted gate

The columns of each supplied half factor are independent because their
contraction is the unitary shifted gate. A kernel vector of one half factor,
tensored with a fixed coordinate of the other intermediate space, would be
a kernel vector of that gate. Ordinary linear algebra therefore gives actual
left inverses without assuming isometric half factors or canonical form.

The actual four-spin gate is unitary. Applying the same kernel argument
to its adjoint proves that both displayed right cut factors have right
inverses. Thus all four factors have their full intermediate ranks, and
the displayed dimensions equal the ranks of the actual two source cuts.

Source: CPSV17, arXiv:1703.09188, equations `vdagger` and `StandardForm`,
lines 532–543 and 603–617. These are properties of the supplied open data;
no global-to-local symmetry implication is asserted here.
-/

open scoped Matrix Kronecker BigOperators ComplexOrder

namespace MPOTensor.TwoSiteStandardFormData

private theorem firstHalf_mulVec_injective_of_isometry
    {P B R L : Type*} [Fintype P] [Fintype B] [Fintype R] [Fintype L]
    [DecidableEq P] [DecidableEq B] [DecidableEq R] [DecidableEq L]
    (X₁ : Matrix (P × B) (R) ℂ)
    (X₂ : Matrix (B × P) (L) ℂ)
    (v : Matrix (P × P) (R × L) ℂ)
    (hv : v.IsIsometry)
    (hfac : ∀ i j s t, v (i, j) (s, t) =
      ∑ β : B, X₁ (i, β) s * X₂ (β, j) t)
    (t₀ : L) : Function.Injective X₁.mulVec := by
  classical
  change Function.Injective X₁.mulVecLin
  rw [← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
  intro z hz
  let w : R × L → ℂ := fun st ↦ if st.2 = t₀ then z st.1 else 0
  have hw : v *ᵥ w = 0 := by
    funext ij
    rcases ij with ⟨i, j⟩
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, w,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    simp_rw [hfac, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro β _
    have hβ := congrFun hz (i, β)
    change (∑ s : R, X₁ (i, β) s * z s) = 0 at hβ
    calc
      ∑ s : R, X₁ (i, β) s * X₂ (β, j) t₀ * z s =
          X₂ (β, j) t₀ * ∑ s : R, X₁ (i, β) s * z s := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = 0 := by rw [hβ, mul_zero]
  have hGram : vᴴ * v = 1 := hv
  have hzero : w = 0 := by
    calc
      w = (1 : Matrix (R × L) (R × L) ℂ) *ᵥ w :=
        (Matrix.one_mulVec w).symm
      _ = (vᴴ * v) *ᵥ w := congrArg (fun M ↦ M *ᵥ w) hGram.symm
      _ = vᴴ *ᵥ (v *ᵥ w) := (Matrix.mulVec_mulVec w vᴴ v).symm
      _ = 0 := by rw [hw, Matrix.mulVec_zero]
  funext s
  have h := congrFun hzero (s, t₀)
  simpa only [w, ↓reduceIte, Pi.zero_apply] using h

private theorem secondHalf_mulVec_injective_of_isometry
    {P B R L : Type*} [Fintype P] [Fintype B] [Fintype R] [Fintype L]
    [DecidableEq P] [DecidableEq B] [DecidableEq R] [DecidableEq L]
    (X₁ : Matrix (P × B) R ℂ) (X₂ : Matrix (B × P) L ℂ)
    (v : Matrix (P × P) (R × L) ℂ) (hv : v.IsIsometry)
    (hfac : ∀ i j s t, v (i, j) (s, t) = ∑ β : B, X₁ (i, β) s * X₂ (β, j) t)
    (s₀ : R) : Function.Injective X₂.mulVec := by
  let v' := Matrix.reindex (Equiv.prodComm P P)
    (Equiv.prodComm R L) v
  have hv' : v'.IsIsometry := hv.reindex v
    (Equiv.prodComm P P) (Equiv.prodComm R L)
  have hfac' : ∀ i j s t, v' (i, j) (s, t) =
      ∑ β : B, X₂ (β, i) s * X₁ (j, β) t := by
    intro i j s t
    change v (j, i) (t, s) = _
    rw [hfac]
    apply Finset.sum_congr rfl
    intro β _
    ring
  have hinj := firstHalf_mulVec_injective_of_isometry
    (fun p s ↦ X₂ (p.2, p.1) s) (fun p t ↦ X₁ (p.2, p.1) t)
    v' hv' hfac' s₀
  intro x y hxy
  apply hinj
  funext p
  exact congrFun hxy (p.2, p.1)

variable {d D ℓ r : ℕ} {W : MPOTensor (d * d) D}
  {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
  {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}

/-- The actual right supplied half factor has independent columns. Source:
CPSV17, `vdagger` and `StandardForm`, lines 532–543 and 603–617. -/
theorem X₁_mulVec_injective (S : TwoSiteStandardFormData W u v) :
    Function.Injective S.X₁.mulVec :=
  firstHalf_mulVec_injective_of_isometry S.X₁ S.X₂ v S.v_unitary.1 S.v_apply
    ⟨0, S.left_pos⟩

/-- The actual left supplied half factor has independent columns. Source:
CPSV17, `vdagger` and `StandardForm`, lines 532–543 and 603–617. -/
theorem X₂_mulVec_injective (S : TwoSiteStandardFormData W u v) :
    Function.Injective S.X₂.mulVec :=
  secondHalf_mulVec_injective_of_isometry S.X₁ S.X₂ v S.v_unitary.1 S.v_apply
    ⟨0, S.right_pos⟩

/-- Both supplied half factors have actual left inverses, derived from their
unitary contraction. No normalization of the factors is an input. Source:
CPSV17, `vdagger` and `StandardForm`, lines 532–543 and 603–617. -/
theorem exists_left_inverses (S : TwoSiteStandardFormData W u v) :
    ∃ (L₁ : Matrix (Fin r) (Fin d × Fin D) ℂ)
      (L₂ : Matrix (Fin ℓ) (Fin D × Fin d) ℂ),
      L₁ * S.X₁ = 1 ∧ L₂ * S.X₂ = 1 := by
  obtain ⟨L₁, hL₁⟩ := (Matrix.toLin' S.X₁).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr S.X₁_mulVec_injective)
  obtain ⟨L₂, hL₂⟩ := (Matrix.toLin' S.X₂).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr S.X₂_mulVec_injective)
  refine ⟨LinearMap.toMatrix' L₁, LinearMap.toMatrix' L₂, ?_, ?_⟩
  · simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hL₁
  · simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hL₂

/-- The first actual cut's displayed left factor has full column rank.
Source: CPSV17, `eq:block-twosites`, lines 1237–1244. -/
theorem cutX₁_mulVec_injective (S : TwoSiteStandardFormData W u v) :
    Function.Injective S.cutX₁.mulVec := by
  classical
  intro x y hxy
  funext as
  have hslice : (fun s ↦ x (as.1, s)) = fun s ↦ y (as.1, s) := by
    apply S.X₁_mulVec_injective
    funext p
    have h := congrFun hxy (finProdFinEquiv (as.1, p.1), p.2)
    simpa only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, cutX₁,
      Equiv.symm_apply_apply, Matrix.one_apply, ite_mul, zero_mul, one_mul,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte] using h
  exact congrFun hslice as.2

/-- The second actual cut's displayed left factor has full column rank.
Source: CPSV17, `eq:block-twosites`, lines 1237–1244. -/
theorem cutX₂_mulVec_injective (S : TwoSiteStandardFormData W u v) :
    Function.Injective S.cutX₂.mulVec := by
  classical
  intro x y hxy
  funext tb
  have hslice : (fun t ↦ x (t, tb.2)) = fun t ↦ y (t, tb.2) := by
    apply S.X₂_mulVec_injective
    funext p
    have h := congrFun hxy (p.1, finProdFinEquiv (p.2, tb.2))
    simpa only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, cutX₂,
      Equiv.symm_apply_apply, Matrix.one_apply, mul_ite, ite_mul, mul_zero,
      zero_mul, mul_one, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] using h
  exact congrFun hslice tb.1

/-- The literal four-spin contraction of supplied unitary gates is unitary.
Source: CPSV17, `eq:block-twosites`, lines 1237–1244. -/
theorem fourSpinGate_isUnitaryBetween (S : TwoSiteStandardFormData W u v) :
    (staircaseMiddle (A := Fin ℓ) (E := Fin r) v * (u ⊗ₖ u)).IsUnitaryBetween := by
  classical
  let A := staircaseMiddle (A := Fin ℓ) (E := Fin r) v * (u ⊗ₖ u)
  have hAi : A.IsIsometry := (staircaseMiddle_isIsometry v S.v_unitary.1).mul _ _
    (S.u_unitary.1.kronecker u u S.u_unitary.1)
  have hcard : ℓ * r = d * d := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      le_antisymm (S.u_unitary.2.card_le u) (S.u_unitary.1.card_le u)
  have hcardA : Fintype.card ((Fin ℓ × Fin d) × (Fin d × Fin r)) =
      Fintype.card ((Fin d × Fin d) × (Fin d × Fin d)) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    calc
      ℓ * d * (d * r) = (ℓ * r) * (d * d) := by ring
      _ = (d * d) * (d * d) := by rw [hcard]
  exact hAi.isUnitaryBetween_of_card_eq A hcardA

private theorem cutY_adjoint_mulVec_injective (S : TwoSiteStandardFormData W u v) :
    Function.Injective S.cutY₁ᴴ.mulVec ∧ Function.Injective S.cutY₂ᴴ.mulVec := by
  classical
  let A := staircaseMiddle (A := Fin ℓ) (E := Fin r) v * (u ⊗ₖ u)
  have hAh : Aᴴ.IsIsometry := S.fourSpinGate_isUnitaryBetween.2.conjTranspose A
  let Y₂h : Matrix ((Fin d × Fin d) × Fin D) (Fin ℓ × Fin d) ℂ :=
    fun p tb ↦ star (S.cutY₂ tb (finProdFinEquiv p.1, p.2))
  let Y₁h : Matrix (Fin D × (Fin d × Fin d)) (Fin d × Fin r) ℂ :=
    fun p as ↦ star (S.cutY₁ as (p.1, finProdFinEquiv p.2))
  have hfac : ∀ i j s t, Aᴴ (i, j) (s, t) =
      ∑ β : Fin D, Y₂h (i, β) s * Y₁h (β, j) t := by
    intro i j s t
    have h := congrArg (fun M ↦ star (M (s, t) (i, j)))
      S.cutY₂_cutY₁_eq_staircaseMiddle_mul_kronecker
    simpa only [Matrix.conjTranspose_apply, Y₂h, Y₁h, A, star_sum, star_mul',
      mul_comm] using h.symm
  have h₂ := firstHalf_mulVec_injective_of_isometry Y₂h Y₁h Aᴴ hAh hfac
    (⟨0, S.phys_pos⟩, ⟨0, S.right_pos⟩)
  have h₁ := secondHalf_mulVec_injective_of_isometry Y₂h Y₁h Aᴴ hAh hfac
    (⟨0, S.left_pos⟩, ⟨0, S.phys_pos⟩)
  constructor
  · intro x y hxy
    apply h₁
    funext p
    exact congrFun hxy (p.1, finProdFinEquiv p.2)
  · intro x y hxy
    apply h₂
    funext p
    exact congrFun hxy (finProdFinEquiv p.1, p.2)

/-- Both displayed right factors have actual right inverses. They follow
from the unitary four-spin contraction, rather than a supplied inverse or
normalization. Source: CPSV17, `eq:block-twosites`, lines 1237–1244. -/
theorem exists_cutY_right_inverses (S : TwoSiteStandardFormData W u v) :
    ∃ (Z₁ : Matrix (Fin D × Fin (d * d)) (Fin d × Fin r) ℂ)
      (Z₂ : Matrix (Fin (d * d) × Fin D) (Fin ℓ × Fin d) ℂ),
      S.cutY₁ * Z₁ = 1 ∧ S.cutY₂ * Z₂ = 1 := by
  obtain ⟨h₁, h₂⟩ := cutY_adjoint_mulVec_injective S
  obtain ⟨L₁, hL₁⟩ := (Matrix.toLin' S.cutY₁ᴴ).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr h₁)
  obtain ⟨L₂, hL₂⟩ := (Matrix.toLin' S.cutY₂ᴴ).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr h₂)
  have hM₁ : LinearMap.toMatrix' L₁ * S.cutY₁ᴴ = 1 := by
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hL₁
  have hM₂ : LinearMap.toMatrix' L₂ * S.cutY₂ᴴ = 1 := by
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hL₂
  refine ⟨(LinearMap.toMatrix' L₁)ᴴ, (LinearMap.toMatrix' L₂)ᴴ, ?_, ?_⟩
  · simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one] using congrArg Matrix.conjTranspose hM₁
  · simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one] using congrArg Matrix.conjTranspose hM₂

private theorem rank_eq_card_of_mulVec_injective
    {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) (hM : Function.Injective M.mulVec) :
    M.rank = Fintype.card n := by
  rw [Matrix.rank, LinearMap.finrank_range_of_inj hM, Module.finrank_fintype_fun_eq_card]

/-- All four displayed factors have the full rank of their retained
intermediate coordinate spaces. No canonical presentation is needed.
Source: CPSV17, `eq:sf-svd` and `eq:block-twosites`, lines 479–506 and 1237–1244. -/
theorem cut_factor_ranks (S : TwoSiteStandardFormData W u v) :
    S.cutX₁.rank = d * r ∧ S.cutY₁.rank = d * r ∧
      S.cutX₂.rank = ℓ * d ∧ S.cutY₂.rank = ℓ * d := by
  obtain ⟨hY₁, hY₂⟩ := cutY_adjoint_mulVec_injective S
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_prod, Fintype.card_fin] using
      rank_eq_card_of_mulVec_injective S.cutX₁ S.cutX₁_mulVec_injective
  · rw [← Matrix.rank_conjTranspose]
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      rank_eq_card_of_mulVec_injective S.cutY₁ᴴ hY₁
  · simpa only [Fintype.card_prod, Fintype.card_fin] using
      rank_eq_card_of_mulVec_injective S.cutX₂ S.cutX₂_mulVec_injective
  · rw [← Matrix.rank_conjTranspose]
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      rank_eq_card_of_mulVec_injective S.cutY₂ᴴ hY₂

/-- The displayed intermediate dimensions are the ranks of the actual
source cuts of any supplied standard form. Source: CPSV17, `defnrl`,
`eq:block-twosites`, lines 697–704 and 1237–1244. -/
theorem sourceRanks_eq (S : TwoSiteStandardFormData W u v) :
    r[W] = d * r ∧ ℓ[W] = ℓ * d := by
  obtain ⟨Z₁, Z₂, hZ₁, hZ₂⟩ := S.exists_cutY_right_inverses
  obtain ⟨hX₁, _, hX₂, _⟩ := S.cut_factor_ranks
  constructor
  · change (sourceCutM₁ W).rank = d * r
    rw [S.sourceCutM₁_eq_cutX₁_mul_cutY₁]
    apply le_antisymm ((Matrix.rank_mul_le_left _ _).trans_eq hX₁)
    calc
      d * r = S.cutX₁.rank := hX₁.symm
      _ = (S.cutX₁ * S.cutY₁ * Z₁).rank := by rw [Matrix.mul_assoc, hZ₁, Matrix.mul_one]
      _ ≤ (S.cutX₁ * S.cutY₁).rank := Matrix.rank_mul_le_left _ _
  · change (sourceCutM₂ W).rank = ℓ * d
    rw [S.sourceCutM₂_eq_cutX₂_mul_cutY₂]
    apply le_antisymm ((Matrix.rank_mul_le_left _ _).trans_eq hX₂)
    calc
      ℓ * d = S.cutX₂.rank := hX₂.symm
      _ = (S.cutX₂ * S.cutY₂ * Z₂).rank := by rw [Matrix.mul_assoc, hZ₂, Matrix.mul_one]
      _ ≤ (S.cutX₂ * S.cutY₂).rank := Matrix.rank_mul_le_left _ _

end MPOTensor.TwoSiteStandardFormData
