/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BirthRegions.RepairStages.RepairStage
import TNLean.PEPS.AreaLaw.BirthRegions.RepairStages.RepairDescendantCounts
import TNLean.PEPS.AreaLaw.BirthRegions.Stars.RepairInductionMetric
import TNLean.PEPS.AreaLaw.BirthRegions.RepairStages.RepairDepth

/-!
# A uniform bound for the total number of repair marks

For a fixed stopping scale greater than one, the total number of actual mark
occurrences in any finite sequence of generations is bounded by a constant
times the boundary size and the square of the width factor. The constant is
chosen before the geometric data and the number of generations.

The count is partitioned by the actual initial ancestors. The polynomial
bound for each root and the weighted initial-mark estimate then give the
uniform sum. Finiteness of each actual mark family is proved by the existing
repair construction. The metric hypotheses are precisely those required by
the per-root descendant estimate. No empty generation is assumed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:descendant-count` and
`geometry:total-repairs`, lines 668–692. This is the finite-prefix mark-count
estimate in the total-repair argument.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

It also contains the following results.

* `TNLean.PEPS.AreaLaw.Geometry.repairMarkAncestor_prefix_layer_le`,
  `TNLean.PEPS.AreaLaw.Geometry.exists_repairMarkAncestor_prefix_layer_bound`: counting descendants
  of one initial repair mark.
-/

section RepairRootPrefixCount

/-!
## Counting descendants of one initial repair mark

For a fixed stopping scale greater than one, the number of descendants of
one actual initial mark in any finite sequence of generations is bounded
by a polynomial in its initial layer index. The constant is chosen before
the domain, the initial mark, the layer, and the number of generations.
The only condition on the layer is the corresponding upper bound for the
scale of the given mark. The initial mark family is unchanged.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:descendant-count`, lines 670–686.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- **Descendant prefix count of one initial mark, with an explicit constant.**
The descendants of one actual initial mark through any finite number of
generations, whenever its scale is at most `2 ^ k`, number at most
`K (k + 1) ^ K` with `K = repairDescendantLayerConstant S_* 1`.
Source: area-law Section 11, `geometry:descendant-count`, lines 670–686. -/
theorem repairMarkAncestor_prefix_layer_le {Sstar : ℝ} (hSstar : 1 < Sstar) :
    ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ)
      (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (a₀ : ℝ),
      RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
        (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀ →
      ∀ (p : (repairStage o Λ A C k₀ hC h₀ Sstar 0).markIndex) (k : ℕ),
        (repairStage o Λ A C k₀ hC h₀ Sstar 0).scale p ≤ (2 : ℝ) ^ k →
        ∀ N : ℕ,
          ∑ j ∈ Finset.range N,
              (Nat.card {q : (repairStage o Λ A C k₀ hC h₀ Sstar (0 + j)).markIndex //
                repairMarkAncestor o Λ A C k₀ hC h₀ Sstar 0 j q = p} : ℝ) ≤
            repairDescendantLayerConstant Sstar 1 *
              ((k : ℝ) + 1) ^ repairDescendantLayerConstant Sstar 1 := by
  intro o Λ A C k₀ hC h₀ a₀ h p k hpk N
  set K := repairDescendantLayerConstant Sstar 1
  have hK : 0 < K := repairDescendantLayerConstant_pos Sstar 1
  have hcount := sum_pow_le_repairDescendantLayerConstant hSstar (M := 1) zero_lt_one
  induction N with
  | zero =>
    simpa only [Finset.range_zero, Finset.sum_empty] using
      (show 0 ≤ K * ((k : ℝ) + 1) ^ K by positivity)
  | succ N ih =>
    by_cases hzero : Nat.card
        {q : (repairStage o Λ A C k₀ hC h₀ Sstar (0 + N)).markIndex //
          repairMarkAncestor o Λ A C k₀ hC h₀ Sstar 0 N q = p} = 0
    · simpa only [Finset.sum_range_succ, hzero, Nat.cast_zero, add_zero] using ih
    · obtain ⟨q⟩ := (Nat.card_ne_zero.mp hzero).1
      have hm : Sstar ≤ repairHalfSide^[N]
          ((repairStage o Λ A C k₀ hC h₀ Sstar 0).scale p) := by
        simpa only [repairStage_scale_eq_iterate, q.property] using h.le_scale (0 + N) q.val
      refine (Finset.sum_le_sum fun j _ ↦ ?_).trans
        (hcount k _ (h.scale_pos 0 p) (by simpa only [one_mul] using hpk) N hm)
      exact_mod_cast card_repairMarkAncestor_fiber_le o Λ A C k₀ hC h₀ Sstar 0 j p

/-- A uniform bound for the descendants of one actual initial mark through
any finite number of generations, whenever its scale is at most `2 ^ k`.
The constant depends only on the stopping scale; it is
`repairDescendantLayerConstant S_* 1` (`repairMarkAncestor_prefix_layer_le`).
This is the per-mark estimate preceding the sum over the chosen initial family.
Source: area-law Section 11, `geometry:descendant-count`, lines 670–686. -/
theorem exists_repairMarkAncestor_prefix_layer_bound {Sstar : ℝ} (hSstar : 1 < Sstar) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ)
        (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (a₀ : ℝ),
        RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
          (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀ →
        ∀ (p : (repairStage o Λ A C k₀ hC h₀ Sstar 0).markIndex) (k : ℕ),
          (repairStage o Λ A C k₀ hC h₀ Sstar 0).scale p ≤ (2 : ℝ) ^ k →
          ∀ N : ℕ,
            ∑ j ∈ Finset.range N,
                (Nat.card {q : (repairStage o Λ A C k₀ hC h₀ Sstar (0 + j)).markIndex //
                  repairMarkAncestor o Λ A C k₀ hC h₀ Sstar 0 j q = p} : ℝ) ≤
              K * ((k : ℝ) + 1) ^ K :=
  ⟨_, repairDescendantLayerConstant_pos Sstar 1, repairMarkAncestor_prefix_layer_le hSstar⟩

end TNLean.PEPS.AreaLaw.Geometry

end

end RepairRootPrefixCount

section RepairTotalMarkPrefixCount

noncomputable section

open ManyBody (edgeBoundary planeDomainGraph)

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The mark-count coefficient `576 K B` of the repair stages with stopping scale
`S_*`, where `K = repairDescendantLayerConstant S_* 1` and
`B = polynomialDyadicBudget K`. This is the coefficient `M_t` of the
two-family decomposition. Auxiliary to the explicit constant of Theorem 1.1
(`docs/notes/arealaw2d_explicit_constant.tex`).
Source: area-law Section 11, `geometry:descendant-count` and
`geometry:total-repairs`, lines 668–692. -/
def repairMarkCountConstant (Sstar : ℝ) : ℝ :=
  576 * repairDescendantLayerConstant Sstar 1 *
    polynomialDyadicBudget (repairDescendantLayerConstant Sstar 1)

/-- The mark-count coefficient is positive. -/
theorem repairMarkCountConstant_pos (Sstar : ℝ) : 0 < repairMarkCountConstant Sstar :=
  mul_pos (mul_pos (by norm_num) (repairDescendantLayerConstant_pos Sstar 1))
    (polynomialDyadicBudget_pos _)

/-- **Mark count with an explicit coefficient.** All actual mark occurrences
before any finite cutoff number at most `M_t (2 C₀ + 1) ^ 2 |∂A|` with
`M_t = repairMarkCountConstant S_*`, under the metric hypotheses.
Source: area-law Section 11, `geometry:descendant-count` and
`geometry:total-repairs`, lines 668–692. -/
theorem repairStage_markIndex_prefix_le {Sstar : ℝ} (hSstar : 1 < Sstar)
    (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ)
    (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (a₀ : ℝ)
    (h : RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
      (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀) (N : ℕ) :
    ∑ j ∈ Finset.range N,
        (Nat.card (repairStage o Λ A C k₀ hC h₀ Sstar j).markIndex : ℝ) ≤
      repairMarkCountConstant Sstar * (2 * (C : ℝ) + 1) ^ 2 *
        (edgeBoundary (planeDomainGraph Λ) A).card := by
  classical
  rw [repairMarkCountConstant]
  set K := repairDescendantLayerConstant Sstar 1
  have hK : 0 < K := repairDescendantLayerConstant_pos Sstar 1
  have hroot := repairMarkAncestor_prefix_layer_le hSstar
  let D := repairStage o Λ A C k₀ hC h₀ Sstar
  let (j : ℕ) : Fintype (D j).markIndex :=
    @Fintype.ofFinite _ (finite_repairStage_markIndex o Λ A C k₀ hC h₀ Sstar j)
  have hcard (j : ℕ) :
      (Nat.card (D (0 + j)).markIndex : ℝ) =
        ∑ p : (D 0).markIndex,
          (Nat.card {q : (D (0 + j)).markIndex //
            repairMarkAncestor o Λ A C k₀ hC h₀ Sstar 0 j q = p} : ℝ) := by
    exact_mod_cast (Nat.card_congr
      (Equiv.sigmaFiberEquiv (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar 0 j))).symm.trans
        Nat.card_sigma
  let w (p : (D 0).markIndex) : ℝ :=
    ∑ j ∈ Finset.range N,
      (Nat.card {q : (D (0 + j)).markIndex //
        repairMarkAncestor o Λ A C k₀ hC h₀ Sstar 0 j q = p} : ℝ)
  have hw := initialRepairStage_weighted_sum_le K hK.le o Λ A C k₀ hC h₀ w
    (fun p k _ hpk ↦ hroot o Λ A C k₀ hC h₀ a₀ h p k hpk N)
  change (∑ᶠ p : (D 0).markIndex, w p) ≤ _ at hw
  simp only [finsum_eq_sum_of_fintype, w] at hw
  rw [Finset.sum_comm] at hw
  simpa only [← hcard, Nat.zero_add] using hw

/-- A numerical bound for all actual mark occurrences before any finite
cutoff, chosen before the origin, domain, cut, width, lower layer, and cutoff;
it is `repairMarkCountConstant S_*` (`repairStage_markIndex_prefix_le`).
The existing metric hypotheses are used by the per-root descendant theorem.
Source: area-law Section 11, `geometry:descendant-count` and
`geometry:total-repairs`, lines 668–692. -/
theorem exists_uniform_repairStage_markIndex_prefix_bound {Sstar : ℝ}
    (hSstar : 1 < Sstar) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ)
        (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (a₀ : ℝ),
        RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
          (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀ →
        ∀ N : ℕ,
          ∑ j ∈ Finset.range N,
              (Nat.card (repairStage o Λ A C k₀ hC h₀ Sstar j).markIndex : ℝ) ≤
            M * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary (planeDomainGraph Λ) A).card :=
  ⟨_, repairMarkCountConstant_pos Sstar, repairStage_markIndex_prefix_le hSstar⟩

end TNLean.PEPS.AreaLaw.Geometry

end

end RepairTotalMarkPrefixCount
