/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.ResidueCoverGapCriterion
import TNLean.MPS.ParentHamiltonian.PeriodicOriginalIntersection
import TNLean.Algebra.UniformSelectionBounds

/-!
# From residual cover projection limits to an open-chain gap

Suppose a periodic tensor has a vanishing three-interval projection defect
along every choice of the prefix and tail lengths, as the overlap length
in periods tends to infinity. An elementary selection argument gives one
overlap length for which the defect is at most one half for every prefix
and tail. Periodicity supplies a canonical range with exact open kernels;
the residue cover criterion then supplies one positive norm gap at all
sufficiently large original lengths.

This is a limit criterion: the stated projection-defect convergence is an
explicit hypothesis. No tensor-specific proof of that convergence is made
in this module. The result is not an unconditional periodic tensor gap
theorem.

Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii), and equations (3.12)--(3.16).
-/

open scoped InnerProductSpace
namespace MPSTensor
variable {d D m : ℕ}

/-- Vanishing physical cover defects along every prefix and tail selection
imply a common canonical open-parent gap at every sufficiently large original
length. The range and exact open kernels are derived from periodicity.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma commutation (ii), and equations (3.12)--(3.16). The projection limit
remains an explicit hypothesis of this auxiliary criterion. -/
theorem IsPeriodic.exists_pos_openParentHamiltonianES_gap_of_residue_cover_limit
    [NeZero d] {A : MPSTensor d D} (hA : IsPeriodic m A)
    (hDefect : ∀ K r : ℕ → ℕ, Filter.Tendsto (fun M =>
      ‖(groundSpaceES A (K M * m + M * m + r M)).starProjection -
        (leftBoundaryMapES A (K M * m + M * m) (r M)).range.starProjection.comp
          (reassocTailBoundaryMapES A (K M * m) (M * m) (r M)).range.starProjection‖)
      Filter.atTop (nhds 0)) :
    ∃ R : ℕ, 0 < R ∧
      (∀ N, R ≤ N → LinearMap.ker (openParentHamiltonianES A R N) = groundSpaceES A N) ∧
      ∃ N₀ : ℕ, R ≤ N₀ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N, N₀ ≤ N → ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A R N))ᗮ,
        δ * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖ := by
  obtain ⟨R, hR, hKernel⟩ := hA.exists_ker_openParentHamiltonianES_eq_groundSpaceES
  let e (M : ℕ) (z : ℕ × ℕ) : ℝ :=
    ‖(groundSpaceES A (z.1 * m + M * m + z.2)).starProjection -
      (leftBoundaryMapES A (z.1 * m + M * m) z.2).range.starProjection.comp
        (reassocTailBoundaryMapES A (z.1 * m) (M * m) z.2).range.starProjection‖
  have hUniform : ∀ᶠ M in Filter.atTop, ∀ z, e M z ≤ (1 / 2 : ℝ) :=
    Filter.eventually_forall_le_of_tendsto_all_selections e
      (fun x => hDefect (fun M => (x M).1) (fun M => (x M).2)) (by norm_num)
  obtain ⟨M, hM, hRM⟩ := (hUniform.and (Filter.eventually_ge_atTop R)).exists
  have hRW : R ≤ M * m := hRM.trans (Nat.le_mul_of_pos_right M hA.period_pos)
  obtain ⟨δ, hδ, hGap⟩ :=
    hA.exists_pos_openParentHamiltonianES_gap_all_of_residue_cover_defect (K₀ := 0)
      hR hRW (fun N => hKernel R N le_rfl) (fun K _ r _ => hM (K, r))
  exact ⟨R, hR, (fun N hN => hKernel R N le_rfl hN), M * m, hRW, δ, hδ,
    by simpa only [Nat.zero_add] using hGap⟩

end MPSTensor

