/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryMap.BlockSubspaceOverlap
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Sums of block ground-space projectors

Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (i), bounds the
difference between the sum of the block projectors and the projector onto
their joint span. The proof uses the off-diagonal pairing estimate `5d`. Part (ii) follows
from a comparison of three families of projectors. The statements here
assume the within-family and cross-family overlap bounds explicitly; the
application to overlapping physical intervals requires these bounds separately.

It also contains the following results.

* `Submodule.tendsto_norm_sum_starProjection_sub_iSup_zero`,
  `Submodule.tendsto_norm_iSup_starProjection_comp_zero_of_sector_compressions`: from sector
  compressions to the full ground-space compression.
-/

section BlockProjectorSum

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
  obtain ⟨v, rfl⟩ := exists_sum_eq_of_mem_iSup V hu
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
\(\delta = \lVert B\rVert/(1-\lVert B\rVert)\), with \(\lVert B\rVert<1/2\). -/
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

/-- The norm of the sum of block projectors is at most \((1-\delta)^{-1}\).
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

end BlockProjectorSum

section GroundSpaceSectorCompressionDecay

/-!
## From sector compressions to the full ground-space compression

For a finite family of asymptotically orthogonal subspaces, the sum of their
orthogonal projections approaches the orthogonal projection onto their joint
span. Consequently, a uniformly bounded observable whose compression from a
fixed sector into every sector tends to zero has vanishing compression into
the full joint space. The Hilbert spaces may vary along an arbitrary filter.

The projection comparison is Nachtergaele, arXiv:cond-mat/9410110,
Lemma commutation (i), equation boundXm. Its use here is a finite-sector
consequence, not an assumption of uniqueness of finite-chain ground states.
-/

open Filter
open scoped BigOperators Topology InnerProductSpace Matrix.Norms.L2Operator

namespace Submodule

private theorem exists_small_projector_sum_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ‖ε • C‖ < 1 / 2 ∧
      (let δ := ‖ε • C‖ / (1 - ‖ε • C‖); δ / (1 - δ) < η) := by
  have hM : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) • C) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul
      (tendsto_const_nhds (x := C))
  have hβ : Tendsto (fun n : ℕ => ‖(1 / ((n : ℝ) + 1)) • C‖) atTop (𝓝 0) := by
    simpa using hM.norm
  have hδ : Tendsto (fun n : ℕ => ‖(1 / ((n : ℝ) + 1)) • C‖ /
      (1 - ‖(1 / ((n : ℝ) + 1)) • C‖)) atTop (𝓝 0) := by
    simpa only [Pi.div_apply, sub_zero, zero_div] using!
      hβ.div (tendsto_const_nhds.sub hβ) (show (1 : ℝ) - 0 ≠ 0 by norm_num)
  have hcoef := hδ.div (tendsto_const_nhds.sub hδ) (show (1 : ℝ) - 0 ≠ 0 by norm_num)
  simp only [sub_zero, zero_div] at hcoef
  obtain ⟨n, hn, hcn⟩ :=
    (((tendsto_order.1 hβ).2 (1 / 2) (by norm_num)).and
      ((tendsto_order.1 hcoef).2 η hη)).exists
  exact ⟨1 / ((n : ℝ) + 1), by positivity, hn, hcn⟩

variable {κ ι : Type*} [Fintype ι] {l : Filter κ}
  {E : κ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)] [∀ n, FiniteDimensional ℂ (E n)]

/-- Asymptotic orthogonality of finitely many sector subspaces makes the
sum of their projections converge in norm to the joint-space projection.
This is the limiting consequence of Nachtergaele, arXiv:cond-mat/9410110,
Lemma commutation (i), equation boundXm. -/
theorem tendsto_norm_sum_starProjection_sub_iSup_zero
    (G : (n : κ) → ι → Submodule ℂ (E n))
    (hOverlap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in l, ∀ i j, i ≠ j →
      ∀ x ∈ G n i, ∀ y ∈ G n j, ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖) :
    Tendsto (fun n => ‖(∑ i, (G n i).starProjection) - (⨆ i, G n i).starProjection‖)
      l (𝓝 0) := by
  classical
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (norm_nonneg _)
  · intro η hη
    let C : Matrix ι ι ℝ := fun i j => if i = j then 0 else 1
    obtain ⟨ε, hε, hB, hcoef⟩ := exists_small_projector_sum_error C hη
    filter_upwards [hOverlap ε hε] with n hn
    have hentry (i j : ι) : (ε • C) i j = ε * C i j := rfl
    refine (norm_sum_starProjection_sub_iSup_le (G n) (ε • C) ?_ hB ?_).trans_lt hcoef
    · intro i
      simp [hentry, C]
    · intro i j hij x hx y hy
      simpa [hentry, C, hij] using hn i j hij x hx y hy

private theorem norm_iSup_starProjection_comp_le_sector_sum
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (G : ι → Submodule ℂ F) (W : Submodule ℂ F)
    (X : F →L[ℂ] F) :
    ‖(⨆ i, G i).starProjection.comp (X.comp W.starProjection)‖ ≤
      ‖(∑ i, (G i).starProjection) - (⨆ i, G i).starProjection‖ * ‖X‖ +
        ∑ i, ‖(G i).starProjection.comp (X.comp W.starProjection)‖ := by
  let Q := ∑ i, (G i).starProjection
  let P := (⨆ i, G i).starProjection
  let Y := X.comp W.starProjection
  have hY : ‖Y‖ ≤ ‖X‖ := by
    have h := mul_le_mul_of_nonneg_left W.starProjection_norm_le (norm_nonneg X)
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa only [mul_one] using h)
  have hEq : P.comp Y = (P - Q).comp Y + Q.comp Y := by
    rw [ContinuousLinearMap.sub_comp, sub_add_cancel]
  change ‖P.comp Y‖ ≤ ‖Q - P‖ * ‖X‖ + ∑ i, ‖(G i).starProjection.comp Y‖
  rw [hEq]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa only [norm_sub_rev] using
        mul_le_mul_of_nonneg_left hY (norm_nonneg (P - Q)))
  · rw [show Q.comp Y = ∑ i, (G i).starProjection.comp Y from
      ContinuousLinearMap.finsetSum_comp _ _]
    exact norm_sum_le _ _

omit [Fintype ι] in
/-- Vanishing compressions into each of finitely many asymptotically
orthogonal sectors imply vanishing compression into their joint span, when
the observables are eventually uniformly bounded. The distinguished input
subspace need not be one of the sectors. This is the finite-sector use of
Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (i), equation boundXm. -/
theorem tendsto_norm_iSup_starProjection_comp_zero_of_sector_compressions [Finite ι]
    (G : (n : κ) → ι → Submodule ℂ (E n)) (W : (n : κ) → Submodule ℂ (E n))
    (X : (n : κ) → E n →L[ℂ] E n) {C : ℝ}
    (hOverlap : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in l, ∀ i j, i ≠ j →
      ∀ x ∈ G n i, ∀ y ∈ G n j, ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖)
    (hX : ∀ᶠ n in l, ‖X n‖ ≤ C)
    (hSector : ∀ i, Tendsto (fun n =>
      ‖(G n i).starProjection.comp ((X n).comp (W n).starProjection)‖) l (𝓝 0)) :
    Tendsto (fun n =>
      ‖(⨆ i, G n i).starProjection.comp ((X n).comp (W n).starProjection)‖) l (𝓝 0) := by
  let := Fintype.ofFinite ι
  have hError := tendsto_norm_sum_starProjection_sub_iSup_zero G hOverlap
  have hSum : Tendsto (fun n => ∑ i,
      ‖(G n i).starProjection.comp ((X n).comp (W n).starProjection)‖) l (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ => hSector i)
  have hUpper : Tendsto (fun n =>
      ‖(∑ i, (G n i).starProjection) - (⨆ i, G n i).starProjection‖ * C +
        ∑ i, ‖(G n i).starProjection.comp ((X n).comp (W n).starProjection)‖)
        l (𝓝 0) := by
    simpa only [zero_mul, zero_add] using (hError.mul_const C).add hSum
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hUpper
  filter_upwards [hX] with n hn
  exact (norm_iSup_starProjection_comp_le_sector_sum (G n) (W n) (X n)).trans
    (add_le_add (mul_le_mul_of_nonneg_left hn (norm_nonneg _)) le_rfl)

end Submodule

end GroundSpaceSectorCompressionDecay
