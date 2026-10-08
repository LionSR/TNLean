/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockProjectorSum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# From sector compressions to the full ground-space compression

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
