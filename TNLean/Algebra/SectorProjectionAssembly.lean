/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Order.Field

/-!
# Assembly of finitely many sector projections

Let `U`, `V`, and `W` be joint subspaces, and let `S i`, `T i`, and `C i`
be their sector subspaces. If each joint projection is approximated by the
sum of its sector projections, then the defect `P_U P_V - P_W` is bounded
by the three approximation errors and the finite sum of the sector defects.
On the diagonal the relevant defect is `P_(S i) P_(T i) - P_(C i)`;
off the diagonal it is `P_(S i) P_(T j)`.

The resulting norm convergence theorem permits the Hilbert spaces to vary
and the filter to be arbitrary. Sector orthogonality is not assumed; its
asymptotic consequences are supplied as projection-sum and cross-sector
estimates. In particular, this module does not establish those tensor-specific
estimates.

Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii),
lines 2442--2531, and Lemma disjoint, lines 1744--1820. The results here are
finite-sum operator estimates used to assemble those projection comparisons.
-/

open scoped BigOperators
namespace Submodule

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [Fintype ι] [DecidableEq ι]

/-- The joint projection defect is controlled by projection-sum errors,
paired sector defects, and cross-sector overlaps. Source: Nachtergaele,
arXiv:cond-mat/9410110, Lemma commutation (ii), lines 2442--2531. -/
theorem norm_starProjection_comp_sub_le_sector_errors
    (U V W : Submodule 𝕜 E) (S T C : ι → Submodule 𝕜 E) :
    ‖U.starProjection.comp V.starProjection - W.starProjection‖ ≤
      ‖U.starProjection - ∑ i, (S i).starProjection‖ +
      (Fintype.card ι : ℝ) * ‖V.starProjection - ∑ i, (T i).starProjection‖ +
      (∑ i, ∑ j, ‖(S i).starProjection.comp (T j).starProjection -
        (if i = j then (C i).starProjection else 0)‖) +
      ‖(∑ i, (C i).starProjection) - W.starProjection‖ := by
  classical
  let P := ∑ i, (S i).starProjection
  let Q := ∑ i, (T i).starProjection
  let Z := ∑ i, (C i).starProjection
  have hSum : (∑ i, ∑ j, ((S i).starProjection * (T j).starProjection -
      (if i = j then (C i).starProjection else 0))) = P * Q - Z := by
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, P, Q, Z]
  have hP : ‖P‖ ≤ (Fintype.card ι : ℝ) := by
    calc
      _ ≤ ∑ i, ‖(S i).starProjection‖ := norm_sum_le _ _
      _ ≤ ∑ _ : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => (S i).starProjection_norm_le
      _ = _ := by simp
  have hFirst : ‖(U.starProjection - P) * V.starProjection‖ ≤ ‖U.starProjection - P‖ :=
    (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left V.starProjection_norm_le
      (norm_nonneg _)).trans_eq (mul_one _))
  have hSecond : ‖P * (V.starProjection - Q)‖ ≤
      (Fintype.card ι : ℝ) * ‖V.starProjection - Q‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
  have hMiddle : ‖P * Q - Z‖ ≤
      ∑ i, ∑ j, ‖(S i).starProjection * (T j).starProjection -
        (if i = j then (C i).starProjection else 0)‖ := by
    rw [← hSum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
  have hAlg : U.starProjection * V.starProjection - W.starProjection =
      ((U.starProjection - P) * V.starProjection + P * (V.starProjection - Q)) +
        (P * Q - Z) + (Z - W.starProjection) := by noncomm_ring
  change ‖U.starProjection * V.starProjection - W.starProjection‖ ≤ _
  rw [hAlg]
  calc
    _ ≤ ‖(U.starProjection - P) * V.starProjection‖ +
        ‖P * (V.starProjection - Q)‖ + ‖P * Q - Z‖ + ‖Z - W.starProjection‖ :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := add_le_add (add_le_add (add_le_add hFirst hSecond) hMiddle) le_rfl

omit [DecidableEq ι] in
/-- Vanishing sector defects and projection-sum errors imply vanishing
joint projection defect. The ambient Hilbert spaces may vary with the index.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii),
lines 2442--2531, and Lemma disjoint, lines 1744--1820. The corresponding
sectorwise estimates are explicit hypotheses. -/
theorem tendsto_norm_starProjection_comp_sub_zero_of_sector_errors
    {α : Type*} {f : Filter α} {F : α → Type*}
    [∀ a, NormedAddCommGroup (F a)] [∀ a, InnerProductSpace 𝕜 (F a)]
    [∀ a, FiniteDimensional 𝕜 (F a)]
    (U V W : (a : α) → Submodule 𝕜 (F a))
    (S T C : (a : α) → ι → Submodule 𝕜 (F a))
    (hU : Filter.Tendsto (fun a =>
      ‖(U a).starProjection - ∑ i, (S a i).starProjection‖) f (nhds 0))
    (hV : Filter.Tendsto (fun a =>
      ‖(V a).starProjection - ∑ i, (T a i).starProjection‖) f (nhds 0))
    (hW : Filter.Tendsto (fun a =>
      ‖(∑ i, (C a i).starProjection) - (W a).starProjection‖) f (nhds 0))
    (hDiag : ∀ i, Filter.Tendsto (fun a =>
      ‖(S a i).starProjection.comp (T a i).starProjection - (C a i).starProjection‖)
      f (nhds 0))
    (hCross : ∀ i j, i ≠ j → Filter.Tendsto (fun a =>
      ‖(S a i).starProjection.comp (T a j).starProjection‖) f (nhds 0)) :
    Filter.Tendsto (fun a =>
      ‖(U a).starProjection.comp (V a).starProjection - (W a).starProjection‖)
      f (nhds 0) := by
  classical
  have hTerm (i j : ι) : Filter.Tendsto (fun a =>
      ‖(S a i).starProjection.comp (T a j).starProjection -
        (if i = j then (C a i).starProjection else 0)‖) f (nhds 0) := by
    by_cases hij : i = j
    · simpa only [hij, ite_true] using hDiag j
    · simpa only [ite_eq_right hij, sub_zero] using hCross i j hij
  have hSum : Filter.Tendsto (fun a =>
      ∑ i, ∑ j, ‖(S a i).starProjection.comp (T a j).starProjection -
        (if i = j then (C a i).starProjection else 0)‖) f (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ =>
        tendsto_finsetSum Finset.univ (fun j _ => hTerm i j))
  have hUpper : Filter.Tendsto (fun a =>
      ‖(U a).starProjection - ∑ i, (S a i).starProjection‖ +
      (Fintype.card ι : ℝ) * ‖(V a).starProjection - ∑ i, (T a i).starProjection‖ +
      (∑ i, ∑ j, ‖(S a i).starProjection.comp (T a j).starProjection -
        (if i = j then (C a i).starProjection else 0)‖) +
      ‖(∑ i, (C a i).starProjection) - (W a).starProjection‖) f (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      ((hU.add (hV.const_mul (Fintype.card ι : ℝ))).add hSum).add hW
  exact squeeze_zero' (Filter.Eventually.of_forall fun a => norm_nonneg _)
    (Filter.Eventually.of_forall fun a =>
      norm_starProjection_comp_sub_le_sector_errors (U a) (V a) (W a) (S a) (T a) (C a))
    hUpper

end Submodule
