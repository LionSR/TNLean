/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteStandardForm
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Minimal supplied half factors from the shifted gate

The columns of each supplied half factor are independent because their
contraction is the unitary shifted gate. A kernel vector of one half factor,
tensored with a fixed coordinate of the other intermediate space, would be
a kernel vector of that gate. Ordinary linear algebra therefore gives actual
left inverses without assuming isometric half factors or canonical form.

Source: CPSV17, arXiv:1703.09188, equations `vdagger` and `StandardForm`,
lines 532–543 and 603–617. These are properties of the supplied open data;
no global-to-local symmetry implication is asserted here.
-/

open scoped Matrix BigOperators

namespace MPOTensor.TwoSiteStandardFormData

private theorem firstHalf_mulVec_injective_of_isometry
    {d D ℓ r : ℕ}
    (X₁ : Matrix (Fin d × Fin D) (Fin r) ℂ)
    (X₂ : Matrix (Fin D × Fin d) (Fin ℓ) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (hv : v.IsIsometry)
    (hfac : ∀ i j s t, v (i, j) (s, t) =
      ∑ β : Fin D, X₁ (i, β) s * X₂ (β, j) t)
    (t₀ : Fin ℓ) : Function.Injective X₁.mulVec := by
  classical
  change Function.Injective X₁.mulVecLin
  rw [← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
  intro z hz
  let w : Fin r × Fin ℓ → ℂ := fun st ↦ if st.2 = t₀ then z st.1 else 0
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
    change (∑ s : Fin r, X₁ (i, β) s * z s) = 0 at hβ
    calc
      ∑ s : Fin r, X₁ (i, β) s * X₂ (β, j) t₀ * z s =
          X₂ (β, j) t₀ * ∑ s : Fin r, X₁ (i, β) s * z s := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = 0 := by rw [hβ, mul_zero]
  have hGram : vᴴ * v = 1 := hv
  have hzero : w = 0 := by
    calc
      w = (1 : Matrix (Fin r × Fin ℓ) (Fin r × Fin ℓ) ℂ) *ᵥ w :=
        (Matrix.one_mulVec w).symm
      _ = (vᴴ * v) *ᵥ w := congrArg (fun M ↦ M *ᵥ w) hGram.symm
      _ = vᴴ *ᵥ (v *ᵥ w) := (Matrix.mulVec_mulVec w vᴴ v).symm
      _ = 0 := by rw [hw, Matrix.mulVec_zero]
  funext s
  have h := congrFun hzero (s, t₀)
  simpa only [w, ↓reduceIte, Pi.zero_apply] using h

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
    Function.Injective S.X₂.mulVec := by
  let v' := Matrix.reindex (Equiv.prodComm (Fin d) (Fin d))
    (Equiv.prodComm (Fin r) (Fin ℓ)) v
  have hv' : v'.IsIsometry := S.v_unitary.1.reindex v
    (Equiv.prodComm (Fin d) (Fin d)) (Equiv.prodComm (Fin r) (Fin ℓ))
  have hfac : ∀ i j s t, v' (i, j) (s, t) =
      ∑ β : Fin D, S.X₂ (β, i) s * S.X₁ (j, β) t := by
    intro i j s t
    change v (j, i) (t, s) = _
    rw [S.v_apply]
    apply Finset.sum_congr rfl
    intro β _
    ring
  have hinj := firstHalf_mulVec_injective_of_isometry
    (fun p s ↦ S.X₂ (p.2, p.1) s) (fun p t ↦ S.X₁ (p.2, p.1) t)
    v' hv' hfac ⟨0, S.right_pos⟩
  intro x y hxy
  apply hinj
  funext p
  exact congrFun hxy (p.2, p.1)

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

end MPOTensor.TwoSiteStandardFormData
