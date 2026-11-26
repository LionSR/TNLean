/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.SetTheory.Cardinal.Finite
import TNLean.PEPS.AreaLaw.BirthRegions.RepairStages.RepairDescendants
import TNLean.PEPS.AreaLaw.BirthRegions.RepairStages.RepairDepth

/-!
# Counting actual repair occurrences

Each child occurrence retains its parent and one of the nine centered
offsets. These data determine the occurrence, independently of geometric
separation of the mark locations. Since the initial mark set is finite,
every actual generation has finitely many mark occurrences. A fixed mark
has at most `9 ^ n` mark descendants after `n` generations.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, child marks, lines 404–409 and 506–514;
and `geometry:descendant-count`, lines 670–681.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

It also contains the following results.

* `TNLean.PEPS.AreaLaw.Geometry.card_repairTerminalInteriorSites_prefix_le`: terminal sites in
  finitely many repair generations.
-/

section RepairDescendantCounts

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ)
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- The recorded pair of centered-offset indices of an actual child.
Source: area-law Section 11, lines 404–409 and 506–514. -/
def repairMarkOffset (j : ℕ) (q : (𝔇 (j + 1)).markIndex) : Fin 3 × Fin 3 :=
  (show RepairNextMarkIndex j (𝔇 j).scale Sstar from q).2.2

/-- An actual child occurrence is determined by its parent occurrence and
its recorded offset. No assertion about distinct spatial locations is used.
Source: area-law Section 11, lines 404–409 and 506–514. -/
theorem repairMarkParent_repairMarkOffset_injective (j : ℕ) :
    Function.Injective (fun q : (𝔇 (j + 1)).markIndex ↦
      (repairMarkParent o Λ A C k₀ hC h₀ Sstar j q,
        repairMarkOffset o Λ A C k₀ hC h₀ Sstar j q)) := by
  exact fun q r h ↦
    Prod.ext (Subtype.ext (q.1.property.trans r.1.property.symm))
      (Prod.ext (Subtype.ext (congrArg Prod.fst h))
        (congrArg (fun z : (𝔇 j).markIndex × (Fin 3 × Fin 3) ↦ z.2) h))

/-- The actual mark carrier is finite at every generation, without any
metric hypotheses on the repair.
Source: area-law Section 11, initial marks, lines 325–363, and child marks,
lines 404–409 and 506–514. -/
theorem finite_repairStage_markIndex (j : ℕ) : Finite (𝔇 j).markIndex := by
  exact Nat.rec (motive := fun j ↦ Finite (𝔇 j).markIndex) (by
    dsimp only [repairStage, initialRepairStage]
    infer_instance)
    (fun j ih ↦
      letI := ih
      Finite.of_injective _
        (repairMarkParent_repairMarkOffset_injective o Λ A C k₀ hC h₀ Sstar j)) j

/-- Descendants of a fixed mark are determined by their parent descendant
and their recorded offset.
Source: area-law Section 11, child marks, lines 404–409 and 506–514, and
`geometry:descendant-count`, lines 670–681. -/
theorem repairMarkAncestor_parent_offset_injective (i n : ℕ)
    (p : (𝔇 i).markIndex) :
    Function.Injective (fun q :
        {q : (𝔇 (i + (n + 1))).markIndex //
          repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i (n + 1) q = p} ↦
      ((⟨repairMarkParent o Λ A C k₀ hC h₀ Sstar (i + n) q.val, q.property⟩ :
          {q : (𝔇 (i + n)).markIndex //
            repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n q = p}),
        repairMarkOffset o Λ A C k₀ hC h₀ Sstar (i + n) q.val)) := by
  exact fun q r h ↦ Subtype.ext
    (repairMarkParent_repairMarkOffset_injective o Λ A C k₀ hC h₀ Sstar (i + n)
      (congrArg
        (fun z : {q : (𝔇 (i + n)).markIndex //
            repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n q = p} × (Fin 3 × Fin 3) ↦
          (z.1.val, z.2)) h))

/-- The number of descendants of a fixed mark grows by at most a factor
of nine in one generation.
Source: area-law Section 11, `geometry:descendant-count`, lines 670–681. -/
theorem card_repairMarkAncestor_fiber_succ_le (i n : ℕ)
    (p : (𝔇 i).markIndex) :
    Nat.card {q : (𝔇 (i + (n + 1))).markIndex //
      repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i (n + 1) q = p} ≤
      Nat.card {q : (𝔇 (i + n)).markIndex //
        repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n q = p} * 9 := by
  simpa only [Nat.card_prod, Nat.card_fin] using
    (letI := finite_repairStage_markIndex o Λ A C k₀ hC h₀ Sstar (i + n)
     Nat.card_le_card_of_injective _
       (repairMarkAncestor_parent_offset_injective o Λ A C k₀ hC h₀ Sstar i n p))

/-- A mark has at most `9 ^ n` actual mark descendants after `n` generations.
Source: area-law Section 11, `geometry:descendant-count`, lines 670–681. -/
theorem card_repairMarkAncestor_fiber_le (i n : ℕ) (p : (𝔇 i).markIndex) :
    Nat.card {q : (𝔇 (i + n)).markIndex //
      repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n q = p} ≤ 9 ^ n := by
  exact Nat.rec
    (motive := fun n ↦ Nat.card {q : (𝔇 (i + n)).markIndex //
      repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n q = p} ≤ 9 ^ n)
    ((Nat.card_le_card_of_injective
      (fun _ : {q : (𝔇 (i + 0)).markIndex //
          repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i 0 q = p} ↦ (0 : Fin 1))
      (fun q r _ ↦ Subtype.ext (q.property.trans r.property.symm))).trans_eq
        (Nat.card_fin 1))
    (fun n ih ↦
      (card_repairMarkAncestor_fiber_succ_le o Λ A C k₀ hC h₀ Sstar i n p).trans
        ((Nat.mul_le_mul_right 9 ih).trans_eq (pow_succ (9 : ℕ) n).symm)) n

end TNLean.PEPS.AreaLaw.Geometry

end

end RepairDescendantCounts

section RepairTerminalPrefixSites

/-!
## Terminal sites in finitely many repair generations

The sites of a cut lying in terminal interiors before generation `N` are
bounded by the number of marks in those generations, multiplied by the
uniform bound for the lattice sites in one terminal square. Overlaps between
terminal squares can only reduce the number of sampled sites.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:bad-sites`, lines 694–707.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ)
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

open scoped Classical in
/-- The cut sites in terminal interiors before generation `N` are bounded
by the sum of the actual mark counts in those generations, multiplied by
`(2 * Sstar + 1)²`. Source: area-law Section 11, `geometry:bad-sites`,
lines 694–707, the finite-union counting step. -/
theorem card_repairTerminalInteriorSites_prefix_le (N : ℕ) :
    ((A.filter (fun x ↦ integerPoint x.val ∈
      ⋃ j < N, repairTerminalInteriorSet
        (𝔇 j).location (𝔇 j).scale Sstar)).card : ℝ) ≤
      (2 * Sstar + 1) ^ 2 *
        ∑ j ∈ Finset.range N, (Nat.card (𝔇 j).markIndex : ℝ) := by
  classical
  let (j : ℕ) : Fintype (𝔇 j).markIndex :=
    @Fintype.ofFinite _ (finite_repairStage_markIndex o Λ A C k₀ hC h₀ Sstar j)
  let T (j : ℕ) : Finset (𝔇 j).markIndex :=
    Finset.univ.filter (fun p ↦ repairHalfSide ((𝔇 j).scale p) < Sstar)
  let Q (j : ℕ) : Finset ↥Λ :=
    (T j).biUnion (fun p ↦
      closedSquareSample Λ ((𝔇 j).location p) (repairHalfSide ((𝔇 j).scale p)))
  have hsub : A.filter (fun x ↦ integerPoint x.val ∈
      ⋃ j < N, repairTerminalInteriorSet (𝔇 j).location (𝔇 j).scale Sstar) ⊆
      (Finset.range N).biUnion Q := by
    intro x hx
    simp only [Finset.mem_filter, Set.mem_iUnion, repairTerminalInteriorSet] at hx
    obtain ⟨_, j, hj, p, hp⟩ := hx
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj,
      Finset.mem_biUnion.mpr ⟨p.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.property⟩, ?_⟩⟩
    simpa only [mem_closedSquareSample, repairSquare, Metric.mem_closedBall,
      Prod.dist_eq, Real.dist_eq, max_le_iff, integerPoint] using (interior_subset hp)
  have hQ (j : ℕ) : ((Q j).card : ℝ) ≤
      (2 * Sstar + 1) ^ 2 * (Nat.card (𝔇 j).markIndex : ℝ) := by
    calc
      ((Q j).card : ℝ) ≤ ∑ p ∈ T j,
          ((closedSquareSample Λ ((𝔇 j).location p)
            (repairHalfSide ((𝔇 j).scale p))).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := T j)
          (t := fun p ↦ closedSquareSample Λ ((𝔇 j).location p)
            (repairHalfSide ((𝔇 j).scale p))))
      _ ≤ ((T j).card : ℝ) * (2 * Sstar + 1) ^ 2 := by
        simpa only [nsmul_eq_mul] using
          (Finset.sum_le_card_nsmul (T j)
            (fun p ↦ ((closedSquareSample Λ ((𝔇 j).location p)
              (repairHalfSide ((𝔇 j).scale p))).card : ℝ))
            ((2 * Sstar + 1) ^ 2) (fun p hp ↦
              card_closedSquareSample_repairHalfSide_le Λ _ (Finset.mem_filter.mp hp).2))
      _ ≤ (2 * Sstar + 1) ^ 2 * (Nat.card (𝔇 j).markIndex : ℝ) := by
        simpa only [Nat.card_eq_fintype_card, mul_comm] using
          (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_univ (T j)))
            (sq_nonneg (2 * Sstar + 1)))
  calc
    _ ≤ (((Finset.range N).biUnion Q).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ j ∈ Finset.range N, ((Q j).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := Finset.range N) (t := Q))
    _ ≤ _ := by
      simpa only [Finset.mul_sum] using
        (Finset.sum_le_sum (s := Finset.range N) (fun j _ ↦ hQ j))

end TNLean.PEPS.AreaLaw.Geometry

end

end RepairTerminalPrefixSites
