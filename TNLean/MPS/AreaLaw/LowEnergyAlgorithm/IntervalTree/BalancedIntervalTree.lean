/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.Chain
import Mathlib.Analysis.InnerProductSpace.PiL2
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTrimming.AdjacentIntervalMerge
import Mathlib.Logic.Function.DependsOn

/-!
# Balanced recursive interval spaces

An interval is divided into two adjacent intervals until its length is at
most a prescribed positive width. The retained space is the full local
space at a leaf and the actual chosen merge operation at an internal node.
This is an auxiliary recursive construction for ALVV,
arXiv:1602.08828v2, the merge algorithm, lines 1662–1677, and the
degenerate-ground-space analysis, lines 1777–1817.

The operation is not assumed to have any analytic property in the
definition. An induction transfers a separately proved leaf and merge
invariant to the actual recursively constructed spaces. No probability or
efficient representation is asserted.

## The internal intervals of the balanced recursion

Only the internal intervals descended from the specified root are listed.
Each parent follows its two child lists, in the same midpoint subdivision
as `balancedIntervalSpace`. This supplies the finite collection of merges
for the probability estimate in ALVV, arXiv:1602.08828v2,
Figure `fig:algo1` and lines 1777–1817.

## Bounds for the actual internal intervals

Every internal interval in a balanced root's merge list lies within that
root and has length greater than the leaf width. This identifies the
actual coordinates used when summing local failure probabilities for ALVV,
arXiv:1602.08828v2, Figure `fig:algo1` and lines 1777–1817.

## Closure of the actual root merge list under descendants

A long interval occurs in its own internal merge list. Every internal
descendant of a listed interval is also in the original root list.
The statements use only the existing balanced merge list and introduce
no additional tree. Auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1` and lines 1777–1817.

## Interval operations with arbitrary independent coordinates

Each long interval uses its own coordinate and the actual tensor product
of its two adjacent child spaces. The coordinate may contain several
successive samples. The retained spaces are those of the existing balanced
interval recursion. This is an auxiliary construction for ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817.

## Measurability for interval operations with independent coordinates

A jointly Borel parent construction gives Borel retained projections in
the existing balanced recursion. Each retained space uses only coordinates
of intervals no longer than itself. The coordinate may contain an entire
finite sequence of samples. This is a conditional analytic auxiliary for
ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. Parent
measurability is an explicit hypothesis; no sampling-success estimate is
assumed or concluded.

## Balanced interval spaces from actual local choices

A fixed family of candidate parent spaces and successful local choices defines
one actual merge operation. Its balanced recursion inherits the invariant at
every interval. The chosen candidate at each parent is retained explicitly.
This is a choice-based auxiliary for ALVV, arXiv:1602.08828v2, the merge
construction, lines 1662–1677, and its induction, lines 1777–1817. It asserts
neither measurable dependence on the children nor an adaptive probability.
-/

section

open ManyBody (interval)

namespace TNLean.MPS.AreaLaw

/-- The actual intervals whose lengths exceed the leaf width. Supporting
ALVV, arXiv:1602.08828v2, merge geometry, lines 1662–1677. -/
abbrev LongIntervalIndex (L width : ℕ) :=
  {J : ℕ × ℕ // J.1 ≤ J.2 ∧ J.2 ≤ L ∧ width < J.2 - J.1}

/-- A retained-space operation on actual adjacent interval coordinates.
Supporting ALVV, arXiv:1602.08828v2, merge algorithm, lines 1662–1677. -/
abbrev IntervalMergeOperation (L q : ℕ) :=
  ∀ (p k r : ℕ), p ≤ k → k ≤ r →
    Submodule ℂ (EuclideanSpace ℂ (interval L p k → Fin q)) →
    Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q)) →
    Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))

/-- The actual balanced recursion, with the whole local space retained at
short leaves. Supporting ALVV, arXiv:1602.08828v2, merge algorithm,
lines 1662–1677. The leaf width and operation are fixed before the recursion. -/
noncomputable def balancedIntervalSpace {L q : ℕ} (operation : IntervalMergeOperation L q)
    (width : ℕ) (hwidth : 1 ≤ width) (p r : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) :=
  if hshort : r - p ≤ width then ⊤ else
    let k := p + (r - p) / 2
    operation p k r (by omega) (by omega)
      (balancedIntervalSpace operation width hwidth p k)
      (balancedIntervalSpace operation width hwidth k r)
termination_by r - p
decreasing_by all_goals omega

/-- A short leaf is exactly the full local space. Supporting ALVV,
arXiv:1602.08828v2, merge initialization, lines 1650–1662. -/
theorem balancedIntervalSpace_of_short {L q width p r : ℕ}
    (operation : IntervalMergeOperation L q) (hwidth : 1 ≤ width)
    (hshort : r - p ≤ width) :
    balancedIntervalSpace operation width hwidth p r = ⊤ := by
  rw [balancedIntervalSpace]
  split
  · rfl
  · contradiction

/-- A leaf and parent invariant holds for every actual recursively selected
space, when the parent step may use that the cut is the actual midpoint.
Supporting ALVV, arXiv:1602.08828v2, merge algorithm, lines 1662–1677.
The midpoint lets an invariant depend on the level of a node through its
length, as for the shrinking low-density windows of `t:alg2`, lines 1869–1878. -/
theorem balancedIntervalSpace_invariant_of_midpoint {L q width : ℕ}
    (operation : IntervalMergeOperation L q) (hwidth : 1 ≤ width)
    (P : ∀ p r : ℕ, Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) → Prop)
    (hleaf : ∀ (p r : ℕ), p ≤ r → r ≤ L → r - p ≤ width → P p r ⊤)
    (hnode : ∀ (p r : ℕ) (hpk : p ≤ p + (r - p) / 2) (hkr : p + (r - p) / 2 ≤ r),
      r ≤ L → width < r - p →
      ∀ (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L p (p + (r - p) / 2) → Fin q)))
        (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L (p + (r - p) / 2) r → Fin q))),
      P p (p + (r - p) / 2) S1 → P (p + (r - p) / 2) r S2 →
        P p r (operation p (p + (r - p) / 2) r hpk hkr S1 S2))
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    P p r (balancedIntervalSpace operation width hwidth p r) := by
  suffices ∀ n p r : ℕ, r - p = n → p ≤ r → r ≤ L →
      P p r (balancedIntervalSpace operation width hwidth p r) from
    this (r - p) p r rfl hpr hrL
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p r hlen hpr hrL
    by_cases hshort : r - p ≤ width
    · rw [balancedIntervalSpace_of_short operation hwidth hshort]
      exact hleaf p r hpr hrL hshort
    · have hpk : p ≤ p + (r - p) / 2 := by omega
      have hkr : p + (r - p) / 2 ≤ r := by omega
      have hS1 := ih (p + (r - p) / 2 - p) (by omega) p (p + (r - p) / 2) rfl hpk
        (hkr.trans hrL)
      have hS2 := ih (r - (p + (r - p) / 2)) (by omega) (p + (r - p) / 2) r rfl hkr hrL
      have hdef : balancedIntervalSpace operation width hwidth p r =
          operation p (p + (r - p) / 2) r hpk hkr
            (balancedIntervalSpace operation width hwidth p (p + (r - p) / 2))
            (balancedIntervalSpace operation width hwidth (p + (r - p) / 2) r) := by
        rw [balancedIntervalSpace]
        split
        · contradiction
        · rfl
      rw [hdef]
      exact hnode p r hpk hkr hrL (by omega) _ _ hS1 hS2

/-- A leaf and parent invariant holds for every actual recursively selected
space. Supporting ALVV, arXiv:1602.08828v2, merge algorithm,
lines 1662–1677. The conclusion concerns the defined recursion, rather than
a supplied family of final viable spaces. -/
theorem balancedIntervalSpace_invariant {L q width : ℕ}
    (operation : IntervalMergeOperation L q) (hwidth : 1 ≤ width)
    (P : ∀ p r : ℕ, Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) → Prop)
    (hleaf : ∀ (p r : ℕ), p ≤ r → r ≤ L → r - p ≤ width → P p r ⊤)
    (hnode : ∀ (p k r : ℕ) (hpk : p ≤ k) (hkr : k ≤ r), r ≤ L → width < r - p →
      ∀ (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L p k → Fin q)))
        (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q))),
      P p k S1 → P k r S2 → P p r (operation p k r hpk hkr S1 S2))
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    P p r (balancedIntervalSpace operation width hwidth p r) :=
  balancedIntervalSpace_invariant_of_midpoint operation hwidth P hleaf
    (fun p r hpk hkr hrL hlong ↦ hnode p _ r hpk hkr hrL hlong) p r hpr hrL

end TNLean.MPS.AreaLaw

end

section

namespace TNLean.MPS.AreaLaw

/-- The internal intervals of the actual midpoint recursion, with each
parent following its descendants. Short leaves contribute no merge.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
def balancedIntervalMergeList (width : ℕ) (hwidth : 1 ≤ width) (p r : ℕ) :
    List (ℕ × ℕ) :=
  if _hshort : r - p ≤ width then [] else
    let k := p + (r - p) / 2
    balancedIntervalMergeList width hwidth p k ++
      balancedIntervalMergeList width hwidth k r ++ [(p, r)]
termination_by r - p
decreasing_by all_goals omega

/-- The actual root hierarchy has at most one fewer merge than sites.
This counts only descendants of the specified root, not all overlapping
intervals. Supporting ALVV, arXiv:1602.08828v2, lines 1797–1817. -/
theorem length_balancedIntervalMergeList_le (width : ℕ) (hwidth : 1 ≤ width)
    (p r : ℕ) :
    (balancedIntervalMergeList width hwidth p r).length ≤ r - p - 1 := by
  suffices ∀ n p r : ℕ, r - p = n →
      (balancedIntervalMergeList width hwidth p r).length ≤ r - p - 1 from
    this (r - p) p r rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p r hlen
    by_cases hshort : r - p ≤ width
    · rw [balancedIntervalMergeList, dite_eq_left hshort]
      exact Nat.zero_le _
    · rw [balancedIntervalMergeList, dite_eq_right hshort]
      simp only [List.length_append, List.length_singleton]
      have hleft := ih ((p + (r - p) / 2) - p) (by omega) p (p + (r - p) / 2) rfl
      have hright := ih (r - (p + (r - p) / 2)) (by omega) (p + (r - p) / 2) r rfl
      omega

end TNLean.MPS.AreaLaw

end

section

namespace TNLean.MPS.AreaLaw

/-- The actual merge list contains only long subintervals of its root.
This concerns the descendants of one root, rather than all overlapping
intervals. Supporting ALVV, arXiv:1602.08828v2, lines 1777–1817. -/
theorem bounds_of_mem_balancedIntervalMergeList (width : ℕ) (hwidth : 1 ≤ width)
    (p r : ℕ) (hpr : p ≤ r) {J : ℕ × ℕ}
    (hJ : J ∈ balancedIntervalMergeList width hwidth p r) :
    p ≤ J.1 ∧ J.1 ≤ J.2 ∧ J.2 ≤ r ∧ width < J.2 - J.1 := by
  suffices ∀ n p r : ℕ, r - p = n → p ≤ r → ∀ J : ℕ × ℕ,
      J ∈ balancedIntervalMergeList width hwidth p r →
      p ≤ J.1 ∧ J.1 ≤ J.2 ∧ J.2 ≤ r ∧ width < J.2 - J.1 from
    this (r - p) p r rfl hpr J hJ
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p r hlen hpr J hJ
    by_cases hshort : r - p ≤ width
    · rw [balancedIntervalMergeList, dite_eq_left hshort] at hJ
      exact (List.not_mem_nil hJ).elim
    · rw [balancedIntervalMergeList, dite_eq_right hshort] at hJ
      simp only [List.mem_append, List.mem_singleton] at hJ
      rcases hJ with (hJ | hJ) | rfl
      · have hleft := ih ((p + (r - p) / 2) - p) (by omega)
          p (p + (r - p) / 2) rfl (by omega) J hJ
        omega
      · have hright := ih (r - (p + (r - p) / 2)) (by omega)
          (p + (r - p) / 2) r rfl (by omega) J hJ
        omega
      · omega

end TNLean.MPS.AreaLaw

end

section

namespace TNLean.MPS.AreaLaw

/-- A long interval is the final internal node of its own merge list.
Auxiliary to ALVV, arXiv:1602.08828v2, lines 1777–1817. -/
theorem self_mem_balancedIntervalMergeList (width : ℕ) (hwidth : 1 ≤ width)
    (p r : ℕ) (hlong : width < r - p) :
    (p, r) ∈ balancedIntervalMergeList width hwidth p r := by
  rw [balancedIntervalMergeList, dite_eq_right (by omega : ¬r - p ≤ width)]
  simp only [List.mem_append, List.mem_singleton]
  tauto

/-- Internal descendants of an interval in the actual root list remain
in that same root list. Auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1777–1817. -/
theorem mem_balancedIntervalMergeList_trans (width : ℕ) (hwidth : 1 ≤ width)
    {p r : ℕ} {J K : ℕ × ℕ}
    (hJ : J ∈ balancedIntervalMergeList width hwidth p r)
    (hK : K ∈ balancedIntervalMergeList width hwidth J.1 J.2) :
    K ∈ balancedIntervalMergeList width hwidth p r := by
  suffices ∀ n p r : ℕ, r - p = n →
      ∀ J K : ℕ × ℕ, J ∈ balancedIntervalMergeList width hwidth p r →
        K ∈ balancedIntervalMergeList width hwidth J.1 J.2 →
        K ∈ balancedIntervalMergeList width hwidth p r from
    this (r - p) p r rfl J K hJ hK
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p r hlen J K hJ hK
    by_cases hshort : r - p ≤ width
    · rw [balancedIntervalMergeList, dite_eq_left hshort] at hJ
      cases hJ
    · rw [balancedIntervalMergeList, dite_eq_right hshort] at hJ ⊢
      simp only [List.mem_append, List.mem_singleton] at hJ ⊢
      rcases hJ with (hJ | hJ) | hJ
      · have hleft := ih ((p + (r - p) / 2) - p) (by omega)
          p (p + (r - p) / 2) rfl J K hJ hK
        tauto
      · have hright := ih (r - (p + (r - p) / 2)) (by omega)
          (p + (r - p) / 2) r rfl J K hJ hK
        tauto
      · subst J
        rw [balancedIntervalMergeList, dite_eq_right hshort] at hK
        simpa only [List.mem_append, List.mem_singleton] using hK

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

namespace TNLean.MPS.AreaLaw

/-- The genuine finite endpoint coordinate of a valid long interval.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
def LongIntervalIndex.coordinate {L width : ℕ} (J : LongIntervalIndex L width) :
    Fin (L + 1) × Fin (L + 1) :=
  (⟨J.val.1, Nat.lt_succ_of_le (J.property.1.trans J.property.2.1)⟩,
    ⟨J.val.2, Nat.lt_succ_of_le J.property.2.1⟩)

/-- Apply the prescribed parent map to its actual adjacent child merge
and its own interval coordinate. Short and out-of-range parents are set
to the full space and are unused inside a valid balanced root.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
noncomputable def independentIntervalOperation {L q width : ℕ}
    {Ω : Fin (L + 1) × Fin (L + 1) → Type*}
    (parent : ∀ J : LongIntervalIndex L width,
      Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)) →
      Ω (LongIntervalIndex.coordinate J) →
      Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)))
    (U : ∀ J, Ω J) : IntervalMergeOperation L q :=
  fun p k r hpk hkr S1 S2 ↦
    if hrL : r ≤ L then
      if hlong : width < r - p then
        parent ⟨(p, r), hpk.trans hkr, hrL, hlong⟩
          (adjacentIntervalMerge L q p k r hpk hkr S1 S2)
          (U (LongIntervalIndex.coordinate
            (⟨(p, r), hpk.trans hkr, hrL, hlong⟩ : LongIntervalIndex L width)))
      else ⊤
    else ⊤

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Joint parent measurability gives the actual balanced tree's Borel
projection and dependence only on no longer interval coordinates.
The parent hypothesis concerns its actual composition with a measurable
candidate, not a selected successful event. Conditional auxiliary for
ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
theorem measurable_projectionMatrix_and_dependsOn_independentIntervalTree
    {L q width : ℕ} {Ω : Fin (L + 1) × Fin (L + 1) → Type*}
    [∀ J, MeasurableSpace (Ω J)]
    (parent : ∀ J : LongIntervalIndex L width,
      Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)) →
      Ω (LongIntervalIndex.coordinate J) →
      Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)))
    (hparent : ∀ (J : LongIntervalIndex L width)
      (W : (∀ I, Ω I) →
        Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))),
      Measurable (fun U ↦ (Matrix.toEuclideanCLM
        (n := interval L J.val.1 J.val.2 → Fin q) (𝕜 := ℂ)).symm (W U).starProjection) →
      Measurable (fun x : (∀ I, Ω I) × Ω (LongIntervalIndex.coordinate J) ↦
        (Matrix.toEuclideanCLM (n := interval L J.val.1 J.val.2 → Fin q) (𝕜 := ℂ)).symm
          (parent J (W x.1) x.2).starProjection))
    (hwidth : 1 ≤ width) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    let S := fun U ↦ balancedIntervalSpace
      (independentIntervalOperation parent U) width hwidth p r
    Measurable (fun U ↦ (Matrix.toEuclideanCLM
      (n := interval L p r → Fin q) (𝕜 := ℂ)).symm (S U).starProjection) ∧
    DependsOn S {J : Fin (L + 1) × Fin (L + 1) | J.2.val - J.1.val ≤ r - p} := by
  classical
  intro retained
  let S := fun (p r : ℕ) (U : (∀ I, Ω I)) ↦
    balancedIntervalSpace (independentIntervalOperation parent U) width hwidth p r
  suffices ∀ n p r : ℕ, r - p = n → p ≤ r → r ≤ L →
      Measurable (fun U ↦ (Matrix.toEuclideanCLM
        (n := interval L p r → Fin q) (𝕜 := ℂ)).symm (S p r U).starProjection) ∧
      DependsOn (S p r)
        {J : Fin (L + 1) × Fin (L + 1) | J.2.val - J.1.val ≤ r - p} from
    this (r - p) p r rfl hpr hrL
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p r hlen hpr hrL
    by_cases hshort : r - p ≤ width
    · have hS : S p r = fun _ ↦ ⊤ := by
        funext U
        exact balancedIntervalSpace_of_short _ hwidth hshort
      constructor
      · rw [hS]
        exact measurable_const
      · intro U V _hcoords
        rw [hS]
    · let k := p + (r - p) / 2
      have hpk : p ≤ k := by dsimp only [k]; omega
      have hkr : k ≤ r := by dsimp only [k]; omega
      have hlong : width < r - p := by omega
      obtain ⟨hleft, hleft_dep⟩ := ih (k - p) (by dsimp only [k]; omega)
        p k rfl hpk (hkr.trans hrL)
      obtain ⟨hright, hright_dep⟩ := ih (r - k) (by dsimp only [k]; omega)
        k r rfl hkr hrL
      let J : LongIntervalIndex L width := ⟨(p, r), hpr, hrL, hlong⟩
      let coord := LongIntervalIndex.coordinate J
      let W := fun U ↦ adjacentIntervalMerge L q p k r hpk hkr (S p k U) (S k r U)
      have hW := measurable_projectionMatrix_adjacentIntervalMerge hpk hkr
        (S p k) (S k r) hleft hright
      have hnode := hparent J W hW
      have hsample := hnode.comp (measurable_id.prodMk (measurable_pi_apply coord))
      have hvalue (U : (∀ I, Ω I)) : S p r U =
          parent J (W U) (U coord) := by
        change balancedIntervalSpace
          (independentIntervalOperation parent U) width hwidth p r = _
        rw [balancedIntervalSpace, dite_eq_right hshort]
        simp only [independentIntervalOperation, dite_eq_left hrL, dite_eq_left hlong]
        rfl
      constructor
      · simpa only [Function.comp_def, id_eq, hvalue] using hsample
      · intro U V hcoords
        have hleft_eq : S p k U = S p k V := hleft_dep fun I hI ↦
          hcoords I (hI.trans (by omega : k - p ≤ r - p))
        have hright_eq : S k r U = S k r V := hright_dep fun I hI ↦
          hcoords I (hI.trans (by omega : r - k ≤ r - p))
        have hcoord : U coord = V coord := hcoords coord (by
          change r - p ≤ r - p
          exact le_rfl)
        have hW_eq : W U = W V := by
          dsimp only [W]
          rw [hleft_eq, hright_eq]
        rw [hvalue U, hvalue V, hW_eq, hcoord]

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

namespace TNLean.MPS.AreaLaw

/-- Successful choices for each valid pair of children construct one actual
merge operation and its balanced recursion. The candidate index is retained
in every parent equality; final viable spaces are not assumed. Supporting
ALVV, arXiv:1602.08828v2, lines 1662–1677 and 1777–1817. -/
theorem exists_balanced_interval_tree_of_choices {L q width : ℕ} (hwidth : 1 ≤ width)
    (P : ∀ p r : ℕ, Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) → Prop)
    (I : ∀ (J : LongIntervalIndex L width) (k : ℕ)
      (_hpk : J.val.1 ≤ k) (_hkr : k ≤ J.val.2),
      Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)) →
      Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q)) → Type*)
    (candidate : ∀ (J : LongIntervalIndex L width) (k : ℕ)
      (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
      (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
      (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
      I J k hpk hkr S1 S2 →
        Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)))
    (hleaf : ∀ (p r : ℕ), p ≤ r → r ≤ L → r - p ≤ width → P p r ⊤)
    (hchoice : ∀ (J : LongIntervalIndex L width) (k : ℕ)
      (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
      (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
      (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
      P J.val.1 k S1 → P k J.val.2 S2 →
      ∃ i : I J k hpk hkr S1 S2, P J.val.1 J.val.2 (candidate J k hpk hkr S1 S2 i)) :
    ∃ operation : IntervalMergeOperation L q,
      (∀ (J : LongIntervalIndex L width) (k : ℕ)
        (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
        (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
        (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
        P J.val.1 k S1 → P k J.val.2 S2 →
        ∃ i : I J k hpk hkr S1 S2,
          operation J.val.1 k J.val.2 hpk hkr S1 S2 = candidate J k hpk hkr S1 S2 i ∧
          P J.val.1 J.val.2 (operation J.val.1 k J.val.2 hpk hkr S1 S2)) ∧
      ∀ (p r : ℕ), p ≤ r → r ≤ L →
        P p r (balancedIntervalSpace operation width hwidth p r) := by
  classical
  let operation : IntervalMergeOperation L q := fun p k r hpk hkr S1 S2 ↦
    if h : (p ≤ r ∧ r ≤ L ∧ width < r - p) ∧ P p k S1 ∧ P k r S2 then
      candidate ⟨(p, r), h.1⟩ k hpk hkr S1 S2
        (Classical.choose (hchoice ⟨(p, r), h.1⟩ k hpk hkr S1 S2 h.2.1 h.2.2))
    else ⊤
  have hoperation (J : LongIntervalIndex L width) (k : ℕ)
      (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
      (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
      (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q)))
      (hS1 : P J.val.1 k S1) (hS2 : P k J.val.2 S2) :
      ∃ i : I J k hpk hkr S1 S2,
        operation J.val.1 k J.val.2 hpk hkr S1 S2 = candidate J k hpk hkr S1 S2 i ∧
        P J.val.1 J.val.2 (operation J.val.1 k J.val.2 hpk hkr S1 S2) := by
    let i := Classical.choose (hchoice J k hpk hkr S1 S2 hS1 hS2)
    have hi := Classical.choose_spec (hchoice J k hpk hkr S1 S2 hS1 hS2)
    have heq : operation J.val.1 k J.val.2 hpk hkr S1 S2 = candidate J k hpk hkr S1 S2 i := by
      dsimp only [operation]
      split_ifs with h
      · rfl
      · exact False.elim (h ⟨J.property, hS1, hS2⟩)
    exact ⟨i, heq, heq.symm ▸ hi⟩
  clear_value operation
  refine ⟨operation, hoperation, ?_⟩
  intro p r hpr hrL
  apply balancedIntervalSpace_invariant operation hwidth P hleaf ?_ p r hpr hrL
  intro p k r hpk hkr hrL hlong S1 S2 hS1 hS2
  let J : LongIntervalIndex L width := ⟨(p, r), hpk.trans hkr, hrL, hlong⟩
  exact (hoperation J k hpk hkr S1 S2 hS1 hS2).choose_spec.2

end TNLean.MPS.AreaLaw

end
