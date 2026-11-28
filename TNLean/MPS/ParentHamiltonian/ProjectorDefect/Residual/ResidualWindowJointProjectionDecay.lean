/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.Sector.ResidualBoundaryGram
import QICLean.Analysis.Projection.ProjectionProductDefect
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.Residual.ResidualWindowMixedGramDecay
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.Residual.ResidualWindowLeftSectorSum
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.Residual.ResidualWindowRightSectorSum
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.Residual.ResidualWindowFullSectorSum
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.Residual.ResidualWindowCrossOverlap
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.Sector.PeriodicPrimitiveGroundSpace
import TNLean.MPS.CanonicalForm.BNT.Separation
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.Residual.ResidualWindowLeftGroundSpace

/-!
# Joint residual window projection decay

The same-sector supported cancellation and the different-sector overlap
estimate combine with the three sector projection-sum estimates. Thus the
product of the joint right and left projections approaches the joint full
projection. For a periodic tensor, all primitive, faithful, separation, and
tail-support data are derived from its cyclic isometric resolution.

Source: Nachtergaele, arXiv:cond-mat/9410110, commutation (i)--(ii),
lines 2442--2531 and equation (3.15), lines 1567--1574; DCCSP17,
arXiv:1708.00029, Lemma bdcf and equation Aoffdiag.
The projections here act in the exact triple configuration coordinates.
The identification with original interval projections is a separate
isometric transport.

## The physical residual cover projection limit

For a normalized periodic tensor, the joint right, left, and full residual
window spaces are the images of the corresponding original-chain boundary
spaces under one physical configuration isometry. The joint-sector defect
therefore has exactly the norm of the original cover defect. Reversal of the
projection order is accounted for by the adjoint, rather than by assuming
that the two projections commute.

**Scope restriction (periodic tensor presentation):** The result concerns
an explicitly supplied normalized periodic tensor. The passage from a
general GVBS presentation to this tensor presentation remains separate;
see docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma commutation (ii), lines 2442--2531, and Section 6.
-/

open MPTensor

section

open scoped Matrix InnerProductSpace ComplexOrder

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {D L : ℕ}

/-- Primitive, faithful, inequivalent sectors with exact correlated-tail
Gram projections have a vanishing joint window projection defect, with
arbitrary exterior lengths. Source: Nachtergaele, arXiv:cond-mat/9410110,
commutation (i)--(ii), lines 2442--2531. The algebraic support hypotheses
are explicit; the following periodic consequence derives them. -/
theorem tendsto_norm_residualWindow_joint_projection_comp_sub_zero
    [NeZero D] {ι : Type*} [Finite ι] {dim : ι → ℕ} [∀ j, NeZero (dim j)]
    (A : MPTensor α (Fin D)) (B : ∀ j, MPTensor (Fin L → α) (Fin (dim j)))
    (V : ∀ j, Matrix (Fin D) (Fin (dim j)) ℂ)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : dim j = dim i, ¬ GaugePhaseEquiv (e ▸ B j) (B i))
    (Q : ι → ℕ → Matrix (Fin D) (Fin D) ℂ)
    (hQ : ∀ j r, IsOrthogonalProjection (Q j r))
    (hGram : ∀ j r, (∑ τ : (Fin r → α), (Kraus.evalWord A (List.ofFn τ))ᴴ *
      (V j * (V j)ᴴ) * Kraus.evalWord A (List.ofFn τ) : Matrix (Fin D) (Fin D) ℂ) = Q j r)
    {κ : Type*} {f : Filter κ} {K M r : κ → ℕ} (hM : Filter.Tendsto M f Filter.atTop) :
    Filter.Tendsto (fun n =>
      ‖(⨆ j, (residualWindowRightMapES A (B j) (V j) (K n) (M n) (r n)).range).starProjection.comp
        (⨆ j, (residualWindowLeftMapES (B j) (K n) (M n) (r n)).range).starProjection -
        (⨆ j, (residualWindowMapES A (B j) (V j) (K n) (M n) (r n)).range).starProjection‖)
      f (nhds 0) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  refine Submodule.tendsto_norm_starProjection_comp_sub_zero_of_sector_errors
    (fun n => ⨆ j, (residualWindowRightMapES A (B j) (V j) (K n) (M n) (r n)).range)
    (fun n => ⨆ j, (residualWindowLeftMapES (B j) (K n) (M n) (r n)).range)
    (fun n => ⨆ j, (residualWindowMapES A (B j) (V j) (K n) (M n) (r n)).range)
    (fun n j => (residualWindowRightMapES A (B j) (V j) (K n) (M n) (r n)).range)
    (fun n j => (residualWindowLeftMapES (B j) (K n) (M n) (r n)).range)
    (fun n j => (residualWindowMapES A (B j) (V j) (K n) (M n) (r n)).range)
    ?_ ?_ ?_ ?_ ?_
  · simpa only [norm_sub_rev] using
      tendsto_norm_residualWindowRight_sector_projection_sum_sub_iSup_zero
        A B V ρ hP hρ hDistinct hM
  · simpa only [norm_sub_rev] using
      tendsto_norm_residualWindowLeft_sector_projection_sum_sub_iSup_zero B ρ hP hρ hDistinct hM
  · exact tendsto_norm_residualWindow_sector_projection_sum_sub_iSup_zero
      A B V ρ hP hρ hDistinct hM
  · exact fun j => (hP j).residualWindow_projection_comp_sub_tendsto_zero
      (hρ j) A (V j) (Q j) (hQ j) (hGram j) hM
  · exact fun i j hij => (hP i).residualWindow_cross_projection_tendsto_zero_of_inequivalent
      A (V i) (hP j) (hρ i) (hρ j) (hDistinct i j hij) hM
/-- A periodic tensor supplies a cyclic isometric resolution whose joint
right-left window projection defect vanishes along every diverging common
blocked interval. Both exterior lengths may vary arbitrarily. No primitive
sector, faithful matrix, separation, or row-support data are assumed.
Source: Nachtergaele, arXiv:cond-mat/9410110, commutation (i)--(ii),
lines 2442--2531; the cyclic resolution is DCCSP17, arXiv:1708.00029,
Lemma bdcf and equation Aoffdiag. -/
theorem IsPeriodic.exists_residualWindow_joint_projection_comp_sub_tendsto_zero
    {m : ℕ} {A : MPTensor α (Fin D)} (hA : IsPeriodic m A) :
    ∃ (dim : Fin m → ℕ) (hdim : ∀ j, 0 < dim j),
      let _ : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
      ∃ (B : ∀ j, MPTensor (Fin m → α) (Fin (dim j)))
        (V : ∀ j, Matrix (Fin D) (Fin (dim j)) ℂ),
        (∀ j, (V j)ᴴ * V j = 1) ∧ (∑ j, V j * (V j)ᴴ) = 1 ∧
        (∀ j i, Kraus.block A m i * V j = V j * B j i) ∧
        (∀ j i, (V j)ᴴ * Kraus.block A m i = B j i * (V j)ᴴ) ∧
        ∀ K r : ℕ → ℕ, Filter.Tendsto (fun M =>
          ‖(⨆ j, (residualWindowRightMapES A (B j) (V j) (K M) M (r M)).range).starProjection.comp
            (⨆ j, (residualWindowLeftMapES (B j) (K M) M (r M)).range).starProjection -
            (⨆ j, (residualWindowMapES A (B j) (V j) (K M) M (r M)).range).starProjection‖)
          Filter.atTop (nhds 0) := by
  classical
  let _ : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  let _ : NeZero D := ⟨hA.bondDim_ne_zero⟩
  obtain ⟨dim, hdim, B, P, V, ρ, hP, hρ, hDistinct, hProj, hSum,
    hShift, hIso, hV, hInt, hCoInt⟩ := hA.exists_cyclic_primitive_sector_resolution
  let _ : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  let Q (j : Fin m) (r : ℕ) := P (j - r • (1 : Fin m))
  have hQ : ∀ j r, IsOrthogonalProjection (Q j r) :=
    fun j r => hProj (j - r • (1 : Fin m))
  have hGram (j : Fin m) (r : ℕ) :
      (∑ τ : (Fin r → α), (Kraus.evalWord A (List.ofFn τ))ᴴ * (V j * (V j)ᴴ) *
        Kraus.evalWord A (List.ofFn τ) : Matrix (Fin D) (Fin D) ℂ) = Q j r := by
    simpa only [Q, hV] using
      sum_word_conjTranspose_inverseCyclic_projection_mul_word A P hA.leftCanonical hShift j r
  have hSep : ∀ i j, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i) := hDistinct.forall_ne_transport
  have hResolution : (∑ j, V j * (V j)ᴴ) = 1 := by simpa only [hV] using hSum
  refine ⟨dim, hdim, B, V, hIso, hResolution, hInt, hCoInt, ?_⟩
  intro K r
  exact tendsto_norm_residualWindow_joint_projection_comp_sub_zero
    A B V ρ hP hρ hSep Q hQ hGram Filter.tendsto_id

end MPSTensor

end

section

open scoped Matrix BigOperators ComplexOrder
namespace MPSTensor
variable {α : Type*} [Fintype α] [DecidableEq α] {D m : ℕ}

/-- Periodicity derives the vanishing physical cover projection defect,
uniformly along every prefix and tail selection as the overlap tends to
infinity. Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma commutation (ii), lines 2442--2531, and Section 6. -/
theorem IsPeriodic.residual_cover_projection_defect_tendsto_zero
    {A : MPTensor α (Fin D)} (hA : IsPeriodic m A) (K r : ℕ → ℕ) :
    Filter.Tendsto (fun M =>
      ‖((groundSpace A (K M * m + M * m + r M)).map (WithLp.linearEquiv 2 ℂ
          _).symm.toLinearMap).starProjection -
        (leftBoundaryMapES A (K M * m + M * m) (r M)).range.starProjection.comp
          (reassocTailBoundaryMapES A (K M * m) (M * m) (r M)).range.starProjection‖)
      Filter.atTop (nhds 0) := by
  obtain ⟨dim, hdim, B, V, hV, hSum, hInt, hCoInt, hJoint⟩ :=
    hA.exists_residualWindow_joint_projection_comp_sub_tendsto_zero
  let : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  have hNorm (M : ℕ) :
      ‖(⨆ j, (residualWindowRightMapES A (B j) (V j) (K M) M (r M)).range).starProjection.comp
          (⨆ j, (residualWindowLeftMapES (B j) (K M) M (r M)).range).starProjection -
        (⨆ j, (residualWindowMapES A (B j) (V j) (K M) M (r M)).range).starProjection‖ =
      ‖((groundSpace A (K M * m + M * m + r M)).map (WithLp.linearEquiv 2 ℂ
          _).symm.toLinearMap).starProjection -
        (leftBoundaryMapES A (K M * m + M * m) (r M)).range.starProjection.comp
          (reassocTailBoundaryMapES A (K M * m) (M * m) (r M)).range.starProjection‖ := by
    simp only [iSup_range_residualWindowRightMapES_eq_reindex_reassocTailBoundaryMapES
      A B V hSum hCoInt,
      iSup_range_residualWindowLeftMapES_eq_reindex_cover_leftBoundaryMapES
        A B V hV hSum hInt,
      iSup_range_residualWindowMapES_eq_reindex_map_groundSpace_cover A B V hSum hCoInt]
    exact Submodule.norm_map_starProjection_comp_sub_eq _ _ _ _
  simpa only [hNorm] using hJoint K r

end MPSTensor

end
