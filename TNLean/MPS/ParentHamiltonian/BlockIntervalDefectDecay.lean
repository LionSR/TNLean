/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockIntervalProjectors
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Decay of the joint block projector error

For a finite family of tensors, uniform decay of the distinct-block
overlaps and of the individual-block projector errors implies uniform
decay of the joint projector error. This follows from the finite-family estimate in
Nachtergaele, arXiv:cond-mat/9410110, Section 6, Lemma `commutation`.
-/

open Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem exists_small_overlapMatrix (C : Matrix ι ι ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ‖ε • C‖ < 1 / 2 ∧
      (let δ := ‖ε • C‖ / (1 - ‖ε • C‖); 4 * δ / (1 - δ) ^ 2 < η) := by
  have hM : Tendsto (fun n : ℕ ↦ (1 / ((n : ℝ) + 1)) • C) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul
      (tendsto_const_nhds (x := C))
  have hβ : Tendsto (fun n : ℕ ↦ ‖(1 / ((n : ℝ) + 1)) • C‖) atTop (𝓝 0) := by
    simpa using hM.norm
  have hδ : Tendsto (fun n : ℕ ↦ ‖(1 / ((n : ℝ) + 1)) • C‖ /
      (1 - ‖(1 / ((n : ℝ) + 1)) • C‖)) atTop (𝓝 0) := by
    simpa only [Pi.div_apply, sub_zero, zero_div] using!
      hβ.div (tendsto_const_nhds.sub hβ) (show (1 : ℝ) - 0 ≠ 0 by norm_num)
  have hcoef := ((tendsto_const_nhds (x := (4 : ℝ))).mul hδ).div
    ((tendsto_const_nhds.sub hδ).pow 2) (show ((1 : ℝ) - 0) ^ 2 ≠ 0 by norm_num)
  simp only [mul_zero, sub_zero, one_pow, zero_div] at hcoef
  obtain ⟨n, hn, hcn⟩ :=
    (((tendsto_order.1 hβ).2 (1 / 2) (by norm_num)).and
      ((tendsto_order.1 hcoef).2 η hη)).exists
  exact ⟨1 / ((n : ℝ) + 1), by positivity, hn, hcn⟩

end

private theorem norm_projector_defect_adjoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (U V W : Submodule ℂ E) :
    ‖W.starProjection - U.starProjection.comp V.starProjection‖ =
      ‖V.starProjection.comp U.starProjection - W.starProjection‖ := by
  change ‖W.starProjection - U.starProjection * V.starProjection‖ =
    ‖V.starProjection * U.starProjection - W.starProjection‖
  rw [← norm_star (W.starProjection - U.starProjection * V.starProjection),
    star_sub, star_mul, (isSelfAdjoint_starProjection U).star_eq,
    (isSelfAdjoint_starProjection V).star_eq, (isSelfAdjoint_starProjection W).star_eq,
    norm_sub_rev]

namespace MPSTensor

variable {ι : Type*} [Finite ι] {d : ℕ} {D : ι → ℕ}

/-- Uniform decay of the pairwise overlaps and the individual-block errors
implies uniform decay of the joint projector error. This is the last
estimate in Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii),
combined with the limits in Section 6. -/
theorem eventually_iSup_groundSpaceES_projector_defect_le
    (A : ∀ i, MPSTensor d (D i))
    (hOverlap : ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℕ in atTop,
      ∀ i j, i ≠ j → ∀ x ∈ groundSpaceES (A i) L,
        ∀ y ∈ groundSpaceES (A j) L, ‖inner ℂ x y‖ ≤ ε * ‖x‖ * ‖y‖)
    (hBlock : ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℕ in atTop, ∀ i K Q, 0 < Q →
      ‖(reassocTailBoundaryMapES (A i) K L Q).range.starProjection.comp
            (leftBoundaryMapES (A i) (K + L) Q).range.starProjection -
          (groundSpaceES (A i) (K + L + Q)).starProjection‖ ≤ ε)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ L : ℕ in atTop, ∀ K Q : ℕ, 0 < Q →
      let U := fun i ↦ (leftBoundaryMapES (A i) (K + L) Q).range
      let V := fun i ↦ (reassocTailBoundaryMapES (A i) K L Q).range
      ‖(⨆ i, groundSpaceES (A i) (K + L + Q)).starProjection -
        (⨆ i, U i).starProjection.comp (⨆ i, V i).starProjection‖ ≤ η := by
  classical
  let := Fintype.ofFinite ι
  let C : Matrix ι ι ℝ := fun i j ↦ if i = j then 0 else 1
  obtain ⟨ε, hε, hB, hcoef⟩ := exists_small_overlapMatrix C
    (show 0 < η / ((Fintype.card ι : ℝ) + 1) by positivity)
  filter_upwards [hOverlap ε hε,
    hBlock (η / ((Fintype.card ι : ℝ) + 1)) (by positivity)]
    with L hOL hBL K Q hQ
  have hentry (i j : ι) : (ε • C) i j = ε * C i j := rfl
  have hbound := norm_iSup_groundSpaceES_sub_comp_le_of_overlapMatrix
    A K L Q (ε • C) (fun i ↦ by simp [hentry, C]) hB
    (fun i j ↦ by
      simpa only [hentry, C, mul_ite, mul_zero, mul_one] using
        (ite_nonneg (le_refl (0 : ℝ)) hε.le : 0 ≤ if i = j then 0 else ε))
    (fun i j hij x hx y hy ↦ by simpa [hentry, C, hij] using! hOL i j hij x hx y hy)
  have herr : (∑ i, ‖(groundSpaceES (A i) (K + L + Q)).starProjection -
      (leftBoundaryMapES (A i) (K + L) Q).range.starProjection.comp
        (reassocTailBoundaryMapES (A i) K L Q).range.starProjection‖) ≤
        ∑ _i : ι, η / ((Fintype.card ι : ℝ) + 1) :=
    Finset.sum_le_sum fun i _ ↦
      (norm_projector_defect_adjoint _ _ _).trans_le (hBL i K Q hQ)
  have hsum : η / ((Fintype.card ι : ℝ) + 1) +
      (∑ _i : ι, η / ((Fintype.card ι : ℝ) + 1)) = η := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  exact (hbound.trans (add_le_add hcoef.le herr)).trans_eq hsum

end MPSTensor
