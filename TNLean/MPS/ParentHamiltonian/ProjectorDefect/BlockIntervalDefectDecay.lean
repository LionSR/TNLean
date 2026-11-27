/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.DFinsupp
import QICLean.Analysis.Projection.OverlapMatrix
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import QICLean.Analysis.Projection.ProjectorSumConvergence
import TNLean.MPS.ParentHamiltonian.BoundaryMap.SpectatorOverlap
import Mathlib.Analysis.SpecificLimits.Basic
import TNLean.MPS.ParentHamiltonian.BoundaryMap.BlockGroundSpaceOverlap
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.C3Threshold
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockSumIntervalSpaces

/-!
# Joint projectors on overlapping MPS intervals

Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii), compares the
joint ground-space projectors on overlapping intervals. Here the overlap
matrix on the common interval is supplied explicitly. Its bound extends
to both full physical ranges without a loss depending on the spectator
lengths. The individual block projector errors remain on the right-hand side.

## Decay of the joint block projector error

For a finite family of tensors, uniform decay of the distinct-block
overlaps and of the individual-block projector errors implies uniform
decay of the joint projector error. This follows from the finite-family estimate in
Nachtergaele, arXiv:cond-mat/9410110, Section 6, Lemma `commutation`.

## Uniform projector error decay for inequivalent primitive blocks

For finitely many pairwise inequivalent normalized primitive tensors, the
projector error for two overlapping intervals tends to zero as the overlap
length tends to infinity, uniformly in the outer interval lengths. This is
the consequence of Nachtergaele, arXiv:cond-mat/9410110, Section 6, Lemma
`commutation` (ii), used in condition C3′ with a positive right interval.

## Projector error decay for a block-diagonal tensor

A weighted direct sum of pairwise inequivalent normalized primitive tensors
has uniformly small interval projector error when the overlap is sufficiently
long. The nonzero block weights do not affect the interval ground spaces.
This is the estimate from Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma `commutation` (ii), applied to the ground spaces of the direct sum.
-/

open MPTensor

section

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace MPSTensor
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} {D : ι → ℕ}

/-- The physical interval comparison underlying Nachtergaele,
arXiv:cond-mat/9410110, Lemma `commutation` (ii), lines 2533--2589.
The matrix bounds the distinct-block ground-space overlaps on the common
interval of length \(L\). The bound is uniform in the spectator lengths
\(K,Q\); the remaining errors are the individual block projector defects. -/
theorem norm_iSup_groundSpaceES_sub_comp_le_of_overlapMatrix
    (A : ∀ i, MPSTensor d (D i)) (K L Q : ℕ) (B : Matrix ι ι ℝ)
    (hdiag : ∀ i, B i i = 0) (hB : ‖B‖ < 1 / 2)
    (hBnonneg : ∀ i j, 0 ≤ B i j)
    (hpair : ∀ i j, i ≠ j → ∀ x ∈ groundSpaceES (A i) L,
      ∀ y ∈ groundSpaceES (A j) L, ‖⟪x, y⟫_ℂ‖ ≤ B i j * ‖x‖ * ‖y‖) :
    let U := fun i ↦ (leftBoundaryMapES (A i) (K + L) Q).range
    let V := fun i ↦ (reassocTailBoundaryMapES (A i) K L Q).range
    let δ := ‖B‖ / (1 - ‖B‖)
    ‖(⨆ i, groundSpaceES (A i) (K + L + Q)).starProjection -
      (⨆ i, U i).starProjection.comp (⨆ i, V i).starProjection‖ ≤
      4 * δ / (1 - δ) ^ 2 + ∑ i,
        ‖(groundSpaceES (A i) (K + L + Q)).starProjection -
          (U i).starProjection.comp (V i).starProjection‖ := by
  have hWU (i : ι) : groundSpaceES (A i) (K + L + Q) ≤
      (leftBoundaryMapES (A i) (K + L) Q).range := by
    rw [← range_groundSpaceMapES,
      ← leftBoundaryMapES_comp_leftVirtualMapES (A i) (K + L) Q]
    exact LinearMap.range_comp_le_range _ _
  exact Submodule.norm_iSup_starProjection_sub_comp_le_of_overlapMatrix
    (fun i ↦ (leftBoundaryMapES (A i) (K + L) Q).range)
    (fun i ↦ (reassocTailBoundaryMapES (A i) K L Q).range)
    (fun i ↦ groundSpaceES (A i) (K + L + Q)) B hdiag hB hWU
    (fun i j hij _ ⟨x, hx⟩ _ ⟨y, hy⟩ ↦ hx ▸ hy ▸
      norm_inner_leftBoundaryMapES_le (A i) (A j) K L Q (hBnonneg i j)
        (hpair i j hij) x y)
    (fun i j hij _ ⟨x, hx⟩ _ ⟨y, hy⟩ ↦ hx ▸ hy ▸
      norm_inner_reassocTailBoundaryMapES_le (A i) (A j) K L Q (hBnonneg i j)
        (hpair i j hij) x y)
    (fun i j hij _ ⟨x, hx⟩ _ ⟨y, hy⟩ ↦ hx ▸ hy ▸
      norm_inner_left_reassocTailBoundaryMapES_le (A i) (A j) K L Q (hBnonneg i j)
        (hpair i j hij) x y)

end MPSTensor

end

section

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

end

section

open Filter
open scoped Topology ComplexOrder

namespace MPSTensor

variable {ι : Type*} [Finite ι] {d : ℕ} {D : ι → ℕ} [∀ i, NeZero (D i)]

/-- Uniform decay of the joint interval projector error for inequivalent
primitive blocks. The block dimensions may differ. The right outer interval
has positive length, as required in Nachtergaele, arXiv:cond-mat/9410110,
condition C3′; the estimate follows from Lemma `commutation` (ii) and the
limits in Section 6. -/
theorem eventually_iSup_groundSpaceES_projector_defect_le_of_inequivalent
    (A : ∀ i, MPSTensor d (D i))
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, Kraus.HasComplementaryFixedPointGap (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ L : ℕ in atTop, ∀ K Q : ℕ, 0 < Q →
      let U := fun i ↦ (leftBoundaryMapES (A i) (K + L) Q).range
      let V := fun i ↦ (reassocTailBoundaryMapES (A i) K L Q).range
      ‖(⨆ i, groundSpaceES (A i) (K + L + Q)).starProjection -
        (⨆ i, U i).starProjection.comp (⨆ i, V i).starProjection‖ ≤ η := by
  refine eventually_iSup_groundSpaceES_projector_defect_le A ?_ ?_ hη
  · exact fun ε hε ↦ eventually_all.2 fun i ↦ eventually_all.2 fun j ↦
      eventually_all.2 fun hij ↦
        (hP i).eventually_norm_inner_groundSpaceES_le_of_inequivalent
          (hP j) (hρ i) (hρ j) (hDistinct i j hij) hε
  · exact fun ε hε ↦ eventually_all.2 fun i ↦
      (hP i).eventually_wholeIncrement_groundProjection_defect_le (hρ i) hε

end MPSTensor

end

section

open Filter
open scoped Topology ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [∀ j, NeZero (dim j)]

/-- The projector error of a weighted direct sum tends uniformly to zero
in the overlap length. This is the consequence of Nachtergaele,
arXiv:cond-mat/9410110, Lemma `commutation` (ii), used in condition C3′
with a positive right outer interval. The block coefficients are nonzero. -/
theorem eventually_toTensorFromBlocks_projector_defect_le
    (μ : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    {η : ℝ} (hη : 0 < η) :
    let B := toTensorFromBlocks (α := Fin d) (μ := μ) A
    ∀ᶠ L : ℕ in atTop, ∀ K Q : ℕ, 0 < Q →
      ‖(groundSpaceES B (K + L + Q)).starProjection -
        (leftBoundaryMapES B (K + L) Q).range.starProjection.comp
          (reassocTailBoundaryMapES B K L Q).range.starProjection‖ ≤ η := by
  filter_upwards [eventually_iSup_groundSpaceES_projector_defect_le_of_inequivalent
    A ρ hP hρ hDistinct hη] with L hL K Q hQ
  simpa only [groundSpaceES_toTensorFromBlocks_eq_iSup μ A hμ,
    range_leftBoundaryMapES_toTensorFromBlocks_eq_iSup μ A hμ,
    range_reassocTailBoundaryMapES_toTensorFromBlocks_eq_iSup μ A hμ] using hL K Q hQ

end MPSTensor

end
