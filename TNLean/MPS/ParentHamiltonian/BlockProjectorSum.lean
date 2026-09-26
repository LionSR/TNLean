/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockSubspaceOverlap
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Sums of block ground-space projectors

Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (i), bounds the
difference between the sum of the block projectors and the projector onto
their joint span. The proof uses the off-diagonal pairing estimate `5d`. Part (ii) follows
from a comparison of three families of projectors. The statements here
assume the within-family and cross-family overlap bounds explicitly; the
application to overlapping physical intervals requires these bounds separately.
-/

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace Submodule

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι] [DecidableEq ι]

private theorem sum_offDiagonal_eq_sub_diagonal (f : ι → ι → ℂ) :
    (∑ i, ∑ j, if i = j then 0 else f i j) =
      (∑ i, ∑ j, f i j) - ∑ i, f i i := by
  have hsplit (i j : ι) : (if i = j then 0 else f i j) =
      f i j - if i = j then f i i else 0 := by
    rcases eq_or_ne i j with rfl | hij <;> simp [*]
  simp_rw [hsplit, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

private theorem norm_sum_offDiagonal_le (f : ι → ι → ℂ) :
    ‖∑ i, ∑ j, if i = j then 0 else f i j‖ ≤
      ∑ i, ∑ j, if i = j then 0 else ‖f i j‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  simpa only [apply_ite, norm_zero] using norm_sum_le Finset.univ
    (fun j ↦ if i = j then 0 else f i j)

private theorem inner_sum_starProjection_sum_sub (V : ι → Submodule ℂ E)
    (v : ∀ i, V i) (z : E) :
    ⟪z, (∑ i, (V i).starProjection) (∑ i, (v i : E)) - ∑ i, (v i : E)⟫_ℂ =
      ∑ i, ∑ j, if i = j then 0 else ⟪(V i).starProjection z, (v j : E)⟫_ℂ := by
  rw [sum_offDiagonal_eq_sub_diagonal]
  simp only [inner_sub_right, sum_apply, inner_sum, map_sum,
    inner_starProjection_left_eq_right, starProjection_eq_self_iff.mpr (v _).property]
  rw [Finset.sum_comm]

private theorem norm_inner_sum_starProjection_sub_le
    (V : ι → Submodule ℂ E) (B : Matrix ι ι ℝ)
    (hdiag : ∀ i, B i i = 0) (hB : ‖B‖ < 1)
    (hpair : ∀ i j, i ≠ j → ∀ u ∈ V i, ∀ v ∈ V j,
      ‖⟪u, v⟫_ℂ‖ ≤ B i j * ‖u‖ * ‖v‖)
    {u : E} (hu : u ∈ ⨆ i, V i) (z : E) :
    ‖⟪z, (∑ i, (V i).starProjection) u - u⟫_ℂ‖ ≤
      ‖B‖ / (1 - ‖B‖) * ‖(∑ i, (V i).starProjection) z‖ * ‖u‖ := by
  obtain ⟨v, rfl⟩ := (mem_iSup_finset_iff_exists_sum (s := Finset.univ) V u).mp
    (by simpa using hu)
  rw [inner_sum_starProjection_sum_sub]
  have htri := norm_sum_offDiagonal_le (fun i j ↦ ⟪(V i).starProjection z, (v j : E)⟫_ℂ)
  have hbound := sum_offDiagonal_norm_inner_le_of_overlapMatrix
    (fun i ↦ (V i).starProjection z) (fun i ↦ (v i : E)) B hdiag hB
    (fun i j hij ↦ hpair i j hij _ ((V i).starProjection_apply_mem z)
      _ ((V j).starProjection_apply_mem z))
    (fun i j hij ↦ hpair i j hij _ (v i).property _ (v j).property)
    (fun i j hij ↦ hpair i j hij _ ((V i).starProjection_apply_mem z) _ (v j).property)
  simpa only [sum_apply] using htri.trans hbound

private theorem norm_sum_starProjection_sub_iSup_le_mul
    (V : ι → Submodule ℂ E) (B : Matrix ι ι ℝ)
    (hdiag : ∀ i, B i i = 0) (hB : ‖B‖ < 1)
    (hpair : ∀ i j, i ≠ j → ∀ u ∈ V i, ∀ v ∈ V j,
      ‖⟪u, v⟫_ℂ‖ ≤ B i j * ‖u‖ * ‖v‖) :
    ‖(∑ i, (V i).starProjection) - (⨆ i, V i).starProjection‖ ≤
      ‖B‖ / (1 - ‖B‖) * ‖∑ i, (V i).starProjection‖ := by
  let X : E →L[ℂ] E := ∑ i, (V i).starProjection
  let P := (⨆ i, V i).starProjection
  have hXP (x : E) : X (P x) = X x := by
    simp only [X, sum_apply]
    apply Finset.sum_congr rfl fun i _ ↦ ?_
    exact congrArg (fun T : E →L[ℂ] E ↦ T x)
      (starProjection_comp_starProjection_of_le (le_iSup V i))
  have hδ : 0 ≤ ‖B‖ / (1 - ‖B‖) := div_nonneg (norm_nonneg _) (sub_pos.mpr hB).le
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (mul_nonneg hδ (norm_nonneg X))
  intro x z hx hz
  rw [inner_re_symm]
  apply (RCLike.re_le_norm _).trans
  have h := norm_inner_sum_starProjection_sub_le V B hdiag hB hpair
    ((⨆ i, V i).starProjection_apply_mem x) z
  change ‖⟪z, X (P x) - P x⟫_ℂ‖ ≤
    ‖B‖ / (1 - ‖B‖) * ‖X z‖ * ‖P x‖ at h
  rw [hXP] at h
  calc
    _ ≤ ‖B‖ / (1 - ‖B‖) * ‖X z‖ * ‖P x‖ := h
    _ ≤ ‖B‖ / (1 - ‖B‖) * (‖X‖ * ‖z‖) * ‖x‖ := by
      gcongr
      · exact X.le_opNorm _
      · exact (⨆ i, V i).norm_starProjection_apply_le x
    _ = _ := by rw [hx, hz]; ring

/-- Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (i),
equation `boundXm` (local source lines 2442--2531): the sum of the block
projectors is close to the projector onto their joint span. Here
`δ = ‖B‖ / (1 - ‖B‖)`, with `‖B‖ < 1/2`. -/
theorem norm_sum_starProjection_sub_iSup_le
    (V : ι → Submodule ℂ E) (B : Matrix ι ι ℝ)
    (hdiag : ∀ i, B i i = 0) (hB : ‖B‖ < 1 / 2)
    (hpair : ∀ i j, i ≠ j → ∀ u ∈ V i, ∀ v ∈ V j,
      ‖⟪u, v⟫_ℂ‖ ≤ B i j * ‖u‖ * ‖v‖) :
    let δ := ‖B‖ / (1 - ‖B‖)
    ‖(∑ i, (V i).starProjection) - (⨆ i, V i).starProjection‖ ≤ δ / (1 - δ) := by
  let X : E →L[ℂ] E := ∑ i, (V i).starProjection
  let P := (⨆ i, V i).starProjection
  let δ := ‖B‖ / (1 - ‖B‖)
  have hB₁ : ‖B‖ < 1 := by linarith
  have hδ : 0 ≤ δ := div_nonneg (norm_nonneg _) (sub_pos.mpr hB₁).le
  have hδ₁ : δ < 1 := (div_lt_one (sub_pos.mpr hB₁)).mpr (by linarith)
  have hnorm : ‖X‖ ≤ ‖X - P‖ + 1 := by
    calc
      ‖X‖ = ‖(X - P) + P‖ := by rw [sub_add_cancel]
      _ ≤ ‖X - P‖ + ‖P‖ := norm_add_le _ _
      _ ≤ ‖X - P‖ + 1 := add_le_add_right (⨆ i, V i).starProjection_norm_le _
  have h := norm_sum_starProjection_sub_iSup_le_mul V B hdiag hB₁ hpair
  change ‖X - P‖ ≤ δ / (1 - δ)
  apply (le_div_iff₀ (sub_pos.mpr hδ₁)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hnorm hδ]

/-- The norm of the sum of block projectors is at most `(1 - δ)⁻¹`.
This is the consequence of `boundXm` used in Nachtergaele,
arXiv:cond-mat/9410110, Lemma `commutation` (ii), lines 2533--2577. -/
theorem norm_sum_starProjection_le_of_overlapMatrix
    (V : ι → Submodule ℂ E) (B : Matrix ι ι ℝ)
    (hdiag : ∀ i, B i i = 0) (hB : ‖B‖ < 1 / 2)
    (hpair : ∀ i j, i ≠ j → ∀ u ∈ V i, ∀ v ∈ V j,
      ‖⟪u, v⟫_ℂ‖ ≤ B i j * ‖u‖ * ‖v‖) :
    let δ := ‖B‖ / (1 - ‖B‖)
    ‖∑ i, (V i).starProjection‖ ≤ 1 / (1 - δ) := by
  let X : E →L[ℂ] E := ∑ i, (V i).starProjection
  let P := (⨆ i, V i).starProjection
  let δ := ‖B‖ / (1 - ‖B‖)
  have hB₁ : ‖B‖ < 1 := by linarith
  have hδ₁ : δ < 1 := (div_lt_one (sub_pos.mpr hB₁)).mpr (by linarith)
  have h := norm_sum_starProjection_sub_iSup_le V B hdiag hB hpair
  change ‖X - P‖ ≤ δ / (1 - δ) at h
  change ‖X‖ ≤ 1 / (1 - δ)
  calc
    ‖X‖ = ‖(X - P) + P‖ := by rw [sub_add_cancel]
    _ ≤ ‖X - P‖ + ‖P‖ := norm_add_le _ _
    _ ≤ δ / (1 - δ) + 1 := add_le_add h (⨆ i, V i).starProjection_norm_le
    _ = 1 / (1 - δ) := by field_simp [ne_of_gt (sub_pos.mpr hδ₁)]; ring

private theorem inner_sum_starProjection_comp_sub_sum
    (U V : ι → Submodule ℂ E) (x z : E) :
    ⟪z, (((∑ i, (U i).starProjection).comp (∑ j, (V j).starProjection)) -
      ∑ i, (U i).starProjection.comp (V i).starProjection) x⟫_ℂ =
    ∑ i, ∑ j, if i = j then 0 else
      ⟪(U i).starProjection z, (V j).starProjection x⟫_ℂ := by
  rw [sum_offDiagonal_eq_sub_diagonal]
  simp only [sub_apply, ContinuousLinearMap.comp_apply, sum_apply, map_sum,
    inner_sub_right, inner_sum, inner_starProjection_left_eq_right]
  rw [Finset.sum_comm]

/-- The off-diagonal terms in the product of two sums of block projectors
are bounded by the overlap coefficient times the norms of the two sums.
This is the use of `5d` in Nachtergaele, arXiv:cond-mat/9410110,
Lemma `commutation` (ii), lines 2550--2577. -/
theorem norm_sum_starProjection_comp_sub_sum_le
    (U V : ι → Submodule ℂ E) (B : Matrix ι ι ℝ)
    (hdiag : ∀ i, B i i = 0) (hB : ‖B‖ < 1)
    (hU : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j,
      ‖⟪u, v⟫_ℂ‖ ≤ B i j * ‖u‖ * ‖v‖)
    (hV : ∀ i j, i ≠ j → ∀ u ∈ V i, ∀ v ∈ V j,
      ‖⟪u, v⟫_ℂ‖ ≤ B i j * ‖u‖ * ‖v‖)
    (hUV : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ V j,
      ‖⟪u, v⟫_ℂ‖ ≤ B i j * ‖u‖ * ‖v‖) :
    ‖((∑ i, (U i).starProjection).comp (∑ j, (V j).starProjection)) -
      ∑ i, (U i).starProjection.comp (V i).starProjection‖ ≤
      ‖B‖ / (1 - ‖B‖) * ‖∑ i, (U i).starProjection‖ * ‖∑ i, (V i).starProjection‖ := by
  let X : E →L[ℂ] E := ∑ i, (U i).starProjection
  let Y : E →L[ℂ] E := ∑ i, (V i).starProjection
  have hδ : 0 ≤ ‖B‖ / (1 - ‖B‖) := div_nonneg (norm_nonneg _) (sub_pos.mpr hB).le
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le
    (mul_nonneg (mul_nonneg hδ (norm_nonneg X)) (norm_nonneg Y))
  intro x z hx hz
  rw [inner_re_symm]
  apply (RCLike.re_le_norm _).trans
  rw [inner_sum_starProjection_comp_sub_sum]
  have h := sum_offDiagonal_norm_inner_le_of_overlapMatrix
    (fun i ↦ (U i).starProjection z) (fun i ↦ (V i).starProjection x) B hdiag hB
    (fun i j hij ↦ hU i j hij _ ((U i).starProjection_apply_mem z)
      _ ((U j).starProjection_apply_mem z))
    (fun i j hij ↦ hV i j hij _ ((V i).starProjection_apply_mem x)
      _ ((V j).starProjection_apply_mem x))
    (fun i j hij ↦ hUV i j hij _ ((U i).starProjection_apply_mem z)
      _ ((V j).starProjection_apply_mem x))
  have h' := (norm_sum_offDiagonal_le
    (fun i j ↦ ⟪(U i).starProjection z, (V j).starProjection x⟫_ℂ)).trans h
  calc
    _ ≤ ‖B‖ / (1 - ‖B‖) * ‖X z‖ * ‖Y x‖ := by
      simpa only [X, Y, sum_apply] using h'
    _ ≤ ‖B‖ / (1 - ‖B‖) * (‖X‖ * ‖z‖) * (‖Y‖ * ‖x‖) := by
      gcongr
      · exact X.le_opNorm _
      · exact Y.le_opNorm _
    _ = _ := by rw [hx, hz]; ring

/-- Joint-projector comparison from Nachtergaele,
arXiv:cond-mat/9410110, Lemma `commutation` (ii), lines 2533--2589.
The families represent the left, right, and full-interval block spaces;
the full-interval spaces are contained in the left spaces. The remaining
error is the sum of the individual block projector errors. -/
theorem norm_iSup_starProjection_sub_comp_le_of_overlapMatrix
    (U V W : ι → Submodule ℂ E) (B : Matrix ι ι ℝ)
    (hdiag : ∀ i, B i i = 0) (hB : ‖B‖ < 1 / 2)
    (hWU : ∀ i, W i ≤ U i)
    (hU : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j,
      ‖⟪u, v⟫_ℂ‖ ≤ B i j * ‖u‖ * ‖v‖)
    (hV : ∀ i j, i ≠ j → ∀ u ∈ V i, ∀ v ∈ V j,
      ‖⟪u, v⟫_ℂ‖ ≤ B i j * ‖u‖ * ‖v‖)
    (hUV : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ V j,
      ‖⟪u, v⟫_ℂ‖ ≤ B i j * ‖u‖ * ‖v‖) :
    let δ := ‖B‖ / (1 - ‖B‖)
    ‖(⨆ i, W i).starProjection -
      (⨆ i, U i).starProjection.comp (⨆ i, V i).starProjection‖ ≤
      4 * δ / (1 - δ) ^ 2 +
        ∑ i, ‖(W i).starProjection - (U i).starProjection.comp (V i).starProjection‖ := by
  let XU : E →L[ℂ] E := ∑ i, (U i).starProjection
  let XV : E →L[ℂ] E := ∑ i, (V i).starProjection
  let XW : E →L[ℂ] E := ∑ i, (W i).starProjection
  let PU := (⨆ i, U i).starProjection
  let PV := (⨆ i, V i).starProjection
  let PW := (⨆ i, W i).starProjection
  let Z : E →L[ℂ] E := ∑ i, (U i).starProjection.comp (V i).starProjection
  let δ := ‖B‖ / (1 - ‖B‖)
  let a := δ / (1 - δ)
  let q := 1 / (1 - δ)
  have hB₁ : ‖B‖ < 1 := by linarith
  have hδ : 0 ≤ δ := div_nonneg (norm_nonneg _) (sub_pos.mpr hB₁).le
  have hδ₁ : δ < 1 := (div_lt_one (sub_pos.mpr hB₁)).mpr (by linarith)
  have ha : 0 ≤ a := div_nonneg hδ (sub_pos.mpr hδ₁).le
  have hq : 1 ≤ q := (le_div_iff₀ (sub_pos.mpr hδ₁)).mpr (by linarith)
  have hbounds (F : ι → Submodule ℂ E)
      (hF : ∀ i j, i ≠ j → ∀ u ∈ F i, ∀ v ∈ F j,
        ‖⟪u, v⟫_ℂ‖ ≤ B i j * ‖u‖ * ‖v‖) :
      ‖(∑ i, (F i).starProjection) - (⨆ i, F i).starProjection‖ ≤ a ∧
        ‖∑ i, (F i).starProjection‖ ≤ q :=
    ⟨norm_sum_starProjection_sub_iSup_le F B hdiag hB hF,
      norm_sum_starProjection_le_of_overlapMatrix F B hdiag hB hF⟩
  have hUb := hbounds U hU
  have hVb := hbounds V hV
  have hWb := hbounds W (fun i j hij u hu v hv ↦ hU i j hij u (hWU i hu) v (hWU j hv))
  have hFull : ‖PW - XW‖ ≤ a := by
    rw [norm_sub_rev]
    exact hWb.1
  have hSame : ‖XW - Z‖ ≤
      ∑ i, ‖(W i).starProjection - (U i).starProjection.comp (V i).starProjection‖ := by
    dsimp only [XW, Z]
    rw [← Finset.sum_sub_distrib]
    exact norm_sum_le _ _
  have hOff : ‖Z - XU.comp XV‖ ≤ a * q := by
    calc
      _ = ‖XU.comp XV - Z‖ := norm_sub_rev _ _
      _ ≤ δ * ‖XU‖ * ‖XV‖ :=
        norm_sum_starProjection_comp_sub_sum_le U V B hdiag hB₁ hU hV hUV
      _ ≤ δ * q * q := by gcongr <;> first | exact hUb.2 | exact hVb.2
      _ = a * q := by dsimp only [a, q]; ring
  have hProd : ‖XU.comp XV - PU.comp PV‖ ≤ a * q + a := by
    have hid : XU.comp XV - PU.comp PV =
        (XU - PU).comp XV + PU.comp (XV - PV) := by
      rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
      abel
    rw [hid]
    calc
      _ ≤ ‖(XU - PU).comp XV‖ + ‖PU.comp (XV - PV)‖ := norm_add_le _ _
      _ ≤ ‖XU - PU‖ * ‖XV‖ + ‖PU‖ * ‖XV - PV‖ :=
        add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
          (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ a * q + 1 * a := by
        gcongr
        · exact hUb.1
        · exact hVb.2
        · exact (⨆ i, U i).starProjection_norm_le
        · exact hVb.1
      _ = _ := by ring
  have htriangle₁ := dist_triangle PW XW (PU.comp PV)
  have htriangle₂ := dist_triangle XW Z (PU.comp PV)
  have htriangle₃ := dist_triangle Z (XU.comp XV) (PU.comp PV)
  simp only [dist_eq_norm] at htriangle₁ htriangle₂ htriangle₃
  have haq : a ≤ a * q := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hq ha
  have hcoeff : 4 * (a * q) = 4 * δ / (1 - δ) ^ 2 := by
    dsimp only [a, q]
    field_simp [ne_of_gt (sub_pos.mpr hδ₁)]
  change ‖PW - PU.comp PV‖ ≤ _
  calc
    _ ≤ 4 * (a * q) +
        ∑ i, ‖(W i).starProjection - (U i).starProjection.comp (V i).starProjection‖ := by
      linarith only [htriangle₁, htriangle₂, htriangle₃, hFull, hSame, hOff, hProd, haq]
    _ = _ := by rw [hcoeff]

end Submodule
