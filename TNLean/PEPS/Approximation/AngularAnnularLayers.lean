/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Data.Finset.Max
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Ext
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.RCases

/-!
# Dyadic annular layers and cumulative angular separation

The ambient plane is `ℝ × ℝ` with its standard product (supremum) metric.
The physical target is an arbitrary set, and the marked points form a finite
set. In particular, no shape, connectedness, or nonemptiness assumption is
made about either set.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, Proposition 3.4 (`prop:angular`),
`02-information.tex`, lines 636–690, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The proofs below are an original formalization of the manuscript. No
upstream Lean proof text was reused. This file contains only the geometric
scale/layer argument, not the conditional-information estimate.
-/

noncomputable section

namespace TNLean.PEPS.Approximation

/-- The manuscript's scale `s_j = 2⁻ʲ n`, written with a natural power. -/
def dyadicScale (n : ℝ) (j : ℕ) : ℝ := n / (2 : ℝ) ^ j

@[simp] theorem dyadicScale_zero (n : ℝ) : dyadicScale n 0 = n := by
  simp [dyadicScale]

theorem dyadicScale_pos {n : ℝ} (hn : 0 < n) (j : ℕ) :
    0 < dyadicScale n j := by
  unfold dyadicScale
  positivity

theorem dyadicScale_nonneg {n : ℝ} (hn : 0 ≤ n) (j : ℕ) :
    0 ≤ dyadicScale n j := by
  unfold dyadicScale
  positivity

theorem dyadicScale_succ (n : ℝ) (j : ℕ) :
    dyadicScale n (j + 1) = dyadicScale n j / 2 := by
  simp only [dyadicScale, pow_succ, div_mul_eq_div_div]

theorem two_mul_dyadicScale_succ (n : ℝ) (j : ℕ) :
    2 * dyadicScale n (j + 1) = dyadicScale n j := by
  rw [dyadicScale_succ]
  ring

theorem dyadicScale_antitone {n : ℝ} (hn : 0 ≤ n) :
    Antitone (dyadicScale n) := by
  apply antitone_nat_of_succ_le
  intro j
  rw [dyadicScale_succ]
  have hs := dyadicScale_nonneg hn j
  linarith

theorem dyadicScale_le {n : ℝ} (hn : 0 ≤ n) (j : ℕ) :
    dyadicScale n j ≤ n := by
  simpa using dyadicScale_antitone hn (Nat.zero_le j)

/-- Every scale after the outermost one has twice its side at most `n`. -/
theorem two_mul_dyadicScale_le {n : ℝ} (hn : 0 ≤ n) {j : ℕ} (hj : 0 < j) :
    2 * dyadicScale n j ≤ n := by
  cases j with
  | zero => omega
  | succ j =>
      rw [two_mul_dyadicScale_succ]
      exact dyadicScale_le hn j

/-- A finite dyadic stopping index, with the exact terminal-scale bounds
used in the source. -/
structure DyadicCutoff (n t : ℝ) where
  last : ℕ
  lower : t ≤ dyadicScale n last
  upper : dyadicScale n last < 2 * t

/-- The stopping index is constructed from `0 < t ≤ n`, rather than supplied
as an additional geometric assumption. Source: lines 665–669. -/
theorem exists_dyadicCutoff {n t : ℝ} (ht : 0 < t) (htn : t ≤ n) :
    Nonempty (DyadicCutoff n t) := by
  have hratio : 1 ≤ n / t := (le_div_iff₀ ht).2 (by simpa using htn)
  obtain ⟨m, hmlo, hmhi⟩ :=
    exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  have hp : 0 < (2 : ℝ) ^ m := by positivity
  have hlo := (le_div_iff₀ ht).1 hmlo
  have hhi := (div_lt_iff₀ ht).1 hmhi
  rw [pow_succ] at hhi
  refine ⟨⟨m, ?_, ?_⟩⟩
  · change t ≤ n / (2 : ℝ) ^ m
    apply (le_div_iff₀ hp).2
    nlinarith
  · change n / (2 : ℝ) ^ m < 2 * t
    apply (div_lt_iff₀ hp).2
    nlinarith

/-- A selected cutoff, available uniformly for every `0 < t ≤ n`. -/
def chooseDyadicCutoff {n t : ℝ} (ht : 0 < t) (htn : t ≤ n) :
    DyadicCutoff n t := Classical.choice (exists_dyadicCutoff ht htn)

theorem DyadicCutoff.lower_at {n t : ℝ} (c : DyadicCutoff n t)
    (hn : 0 ≤ n) {j : ℕ} (hj : j ≤ c.last) : t ≤ dyadicScale n j :=
  c.lower.trans (dyadicScale_antitone hn hj)

/-- Capped distance to the finite marked set: the minimum of the cap `n`
and all distances to marked points. Inserting the cap also gives the
manuscript's empty-mark convention: the capped distance is then `n`. -/
def cappedMarkDistance (n : ℝ) (V : Finset (ℝ × ℝ)) (x : ℝ × ℝ) : ℝ := by
  classical
  exact (insert n (V.image (fun v => dist x v))).min'
    (Finset.insert_nonempty _ _)

@[simp] theorem cappedMarkDistance_empty (n : ℝ) (x : ℝ × ℝ) :
    cappedMarkDistance n ∅ x = n := by
  classical
  simp [cappedMarkDistance]

/-- For nonempty marks the cap is literally the minimum of `n` and the
attained finite point-to-mark distance. -/
theorem cappedMarkDistance_eq_min_of_nonempty (n : ℝ)
    {V : Finset (ℝ × ℝ)} (hV : V.Nonempty) (x : ℝ × ℝ) :
    cappedMarkDistance n V x =
      min n ((V.image (fun v => dist x v)).min' (hV.image _)) := by
  classical
  exact Finset.min'_insert n _ (hV.image _)

theorem le_cappedMarkDistance_iff (n r : ℝ) (V : Finset (ℝ × ℝ))
    (x : ℝ × ℝ) :
    r ≤ cappedMarkDistance n V x ↔ r ≤ n ∧ ∀ v ∈ V, r ≤ dist x v := by
  classical
  rw [cappedMarkDistance, Finset.le_min'_iff]
  constructor
  · intro h
    refine ⟨h n (Finset.mem_insert_self _ _), ?_⟩
    intro v hv
    exact h (dist x v) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hv))
  · rintro ⟨hn, hV⟩ z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hn
    · rcases Finset.mem_image.mp hz with ⟨v, hv, rfl⟩
      exact hV v hv

theorem cappedMarkDistance_le_cap (n : ℝ) (V : Finset (ℝ × ℝ))
    (x : ℝ × ℝ) : cappedMarkDistance n V x ≤ n := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem cappedMarkDistance_le_dist (n : ℝ) {V : Finset (ℝ × ℝ)}
    (x : ℝ × ℝ) {v : ℝ × ℝ} (hv : v ∈ V) :
    cappedMarkDistance n V x ≤ dist x v := by
  classical
  exact Finset.min'_le _ _
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hv))

theorem cappedMarkDistance_nonneg {n : ℝ} (hn : 0 ≤ n)
    (V : Finset (ℝ × ℝ)) (x : ℝ × ℝ) : 0 ≤ cappedMarkDistance n V x :=
  (le_cappedMarkDistance_iff n 0 V x).2 ⟨hn, fun _ _ => dist_nonneg⟩

/-- Below the cap, a small capped distance supplies an actual marked point.
This is the bridge from annular layers to bounded square covers. -/
theorem cappedMarkDistance_lt_iff {n r : ℝ} (hr : r ≤ n)
    (V : Finset (ℝ × ℝ)) (x : ℝ × ℝ) :
    cappedMarkDistance n V x < r ↔ ∃ v ∈ V, dist x v < r := by
  classical
  constructor
  · intro h
    by_contra! hfar
    have hle := (le_cappedMarkDistance_iff n r V x).2 ⟨hr, hfar⟩
    exact (not_lt_of_ge hle) h
  · rintro ⟨v, hv, hnear⟩
    exact (cappedMarkDistance_le_dist n x hv).trans_lt hnear

/-- Literal source layers. The lower threshold is omitted exactly in the
last layer; the upper threshold is omitted exactly in layer zero. Thus
`m = 0` gives a single layer equal to all of `X`. -/
def annularLayer (X : Set (ℝ × ℝ)) (n : ℝ) (V : Finset (ℝ × ℝ))
    (m j : ℕ) : Set (ℝ × ℝ) :=
  {x | x ∈ X ∧ j ≤ m ∧
    (j = m ∨ dyadicScale n j ≤ cappedMarkDistance n V x) ∧
    (j = 0 ∨ cappedMarkDistance n V x < 2 * dyadicScale n j)}

@[simp] theorem annularLayer_sole (X : Set (ℝ × ℝ)) (n : ℝ)
    (V : Finset (ℝ × ℝ)) : annularLayer X n V 0 0 = X := by
  ext x
  simp [annularLayer]

/-- The outer layer contains all points at distance at least `n` from every
mark, including all points when there are no marks. -/
theorem annularLayer_first (X : Set (ℝ × ℝ)) (n : ℝ)
    (V : Finset (ℝ × ℝ)) {m : ℕ} (hm : 0 < m) :
    annularLayer X n V m 0 = {x | x ∈ X ∧ ∀ v ∈ V, n ≤ dist x v} := by
  ext x
  simp [annularLayer, ne_of_lt hm, le_cappedMarkDistance_iff]

theorem annularLayer_middle (X : Set (ℝ × ℝ)) (n : ℝ)
    (V : Finset (ℝ × ℝ)) {m j : ℕ} (hj : 0 < j) (hjm : j < m) :
    annularLayer X n V m j =
      {x | x ∈ X ∧ dyadicScale n j ≤ cappedMarkDistance n V x ∧
        cappedMarkDistance n V x < 2 * dyadicScale n j} := by
  ext x
  simp [annularLayer, ne_of_gt hj, ne_of_lt hjm, hjm.le]

theorem annularLayer_last (X : Set (ℝ × ℝ)) (n : ℝ)
    (V : Finset (ℝ × ℝ)) {m : ℕ} (hm : 0 < m) :
    annularLayer X n V m m =
      {x | x ∈ X ∧ cappedMarkDistance n V x < 2 * dyadicScale n m} := by
  ext x
  simp [annularLayer, ne_of_gt hm]

/-- In a nonfinal inner layer, the lower bound holds for every mark and
an actual mark attains the strict upper bound. These are the source's
uncapped annular conditions, written without an extended-real infimum. -/
theorem mem_annularLayer_middle_iff {n : ℝ} (hn : 0 ≤ n)
    {X : Set (ℝ × ℝ)} {V : Finset (ℝ × ℝ)} {m j : ℕ}
    (hj : 0 < j) (hjm : j < m) {x : ℝ × ℝ} :
    x ∈ annularLayer X n V m j ↔
      x ∈ X ∧ (∀ v ∈ V, dyadicScale n j ≤ dist x v) ∧
        ∃ v ∈ V, dist x v < 2 * dyadicScale n j := by
  rw [annularLayer_middle X n V hj hjm]
  change (x ∈ X ∧ dyadicScale n j ≤ cappedMarkDistance n V x ∧
    cappedMarkDistance n V x < 2 * dyadicScale n j) ↔ _
  rw [le_cappedMarkDistance_iff,
    cappedMarkDistance_lt_iff (two_mul_dyadicScale_le hn hj) V x]
  simp only [dyadicScale_le hn j, true_and]

/-- The last nonsolo layer has the source's uncapped strict upper cutoff. -/
theorem mem_annularLayer_last_iff {n : ℝ} (hn : 0 ≤ n)
    {X : Set (ℝ × ℝ)} {V : Finset (ℝ × ℝ)} {m : ℕ}
    (hm : 0 < m) {x : ℝ × ℝ} :
    x ∈ annularLayer X n V m m ↔
      x ∈ X ∧ ∃ v ∈ V, dist x v < 2 * dyadicScale n m := by
  rw [annularLayer_last X n V hm]
  change (x ∈ X ∧ cappedMarkDistance n V x < 2 * dyadicScale n m) ↔ _
  rw [cappedMarkDistance_lt_iff (two_mul_dyadicScale_le hn hm) V x]

theorem annularLayer_subset (X : Set (ℝ × ℝ)) (n : ℝ)
    (V : Finset (ℝ × ℝ)) (m j : ℕ) : annularLayer X n V m j ⊆ X :=
  fun _ hx => hx.1

/-- The cumulative processed set is defined as the actual union of the
layers with indices at most `j`. -/
def cumulativeLayer (X : Set (ℝ × ℝ)) (n : ℝ) (V : Finset (ℝ × ℝ))
    (m j : ℕ) : Set (ℝ × ℝ) :=
  {x | ∃ i, i ≤ j ∧ x ∈ annularLayer X n V m i}

@[simp] theorem cumulativeLayer_zero (X : Set (ℝ × ℝ)) (n : ℝ)
    (V : Finset (ℝ × ℝ)) (m : ℕ) :
    cumulativeLayer X n V m 0 = annularLayer X n V m 0 := by
  ext x
  constructor
  · rintro ⟨i, hi, hx⟩
    have hi0 : i = 0 := by omega
    exact hi0 ▸ hx
  · intro hx
    exact ⟨0, le_rfl, hx⟩

theorem cumulativeLayer_subset (X : Set (ℝ × ℝ)) (n : ℝ)
    (V : Finset (ℝ × ℝ)) (m j : ℕ) : cumulativeLayer X n V m j ⊆ X := by
  rintro x ⟨i, _, hx⟩
  exact hx.1

theorem annularLayer_subset_cumulativeLayer (X : Set (ℝ × ℝ)) (n : ℝ)
    (V : Finset (ℝ × ℝ)) (m j : ℕ) :
    annularLayer X n V m j ⊆ cumulativeLayer X n V m j :=
  fun _ hx => ⟨j, le_rfl, hx⟩

theorem cumulativeLayer_mono (X : Set (ℝ × ℝ)) (n : ℝ)
    (V : Finset (ℝ × ℝ)) (m : ℕ) : Monotone (cumulativeLayer X n V m) := by
  intro i j hij x hx
  obtain ⟨k, hki, hk⟩ := hx
  exact ⟨k, hki.trans hij, hk⟩

/-- Adding the next literal layer gives exactly the next processed set. -/
theorem cumulativeLayer_succ (X : Set (ℝ × ℝ)) (n : ℝ)
    (V : Finset (ℝ × ℝ)) (m j : ℕ) :
    cumulativeLayer X n V m (j + 1) =
      cumulativeLayer X n V m j ∪ annularLayer X n V m (j + 1) := by
  ext x
  constructor
  · rintro ⟨i, hi, hx⟩
    by_cases hij : i ≤ j
    · exact Or.inl ⟨i, hij, hx⟩
    · have heq : i = j + 1 := by omega
      exact Or.inr (heq ▸ hx)
  · rintro (⟨i, hi, hx⟩ | hx)
    · exact ⟨i, by omega, hx⟩
    · exact ⟨j + 1, le_rfl, hx⟩

private theorem exists_layer_le_of_threshold (X : Set (ℝ × ℝ)) (n : ℝ)
    (V : Finset (ℝ × ℝ)) (m : ℕ) :
    ∀ j, j ≤ m → ∀ x ∈ X,
      (j = m ∨ dyadicScale n j ≤ cappedMarkDistance n V x) →
      ∃ i, i ≤ j ∧ x ∈ annularLayer X n V m i := by
  intro j
  induction j with
  | zero =>
      intro hj x hx hthreshold
      exact ⟨0, le_rfl, hx, hj, hthreshold, Or.inl rfl⟩
  | succ j ih =>
      intro hj x hx hthreshold
      by_cases hprev : dyadicScale n j ≤ cappedMarkDistance n V x
      · obtain ⟨i, hij, hi⟩ := ih (by omega) x hx (Or.inr hprev)
        exact ⟨i, by omega, hi⟩
      · refine ⟨j + 1, le_rfl, hx, hj, hthreshold, Or.inr ?_⟩
        rw [two_mul_dyadicScale_succ]
        exact lt_of_not_ge hprev

/-- Before the last scale the cumulative set has exactly the corresponding
lower distance cutoff; at the last scale it is all of `X`. -/
theorem mem_cumulativeLayer_iff {X : Set (ℝ × ℝ)} {n : ℝ}
    (hn : 0 ≤ n) {V : Finset (ℝ × ℝ)} {m j : ℕ} (hj : j ≤ m)
    {x : ℝ × ℝ} :
    x ∈ cumulativeLayer X n V m j ↔
      x ∈ X ∧ (j = m ∨ dyadicScale n j ≤ cappedMarkDistance n V x) := by
  constructor
  · rintro ⟨i, hij, hx, him, hthreshold, _⟩
    refine ⟨hx, ?_⟩
    rcases hthreshold with him' | hdist
    · exact Or.inl (by omega)
    · exact Or.inr ((dyadicScale_antitone hn hij).trans hdist)
  · rintro ⟨hx, hthreshold⟩
    exact exists_layer_le_of_threshold X n V m j hj x hx hthreshold

@[simp] theorem cumulativeLayer_last {n : ℝ} (hn : 0 ≤ n)
    (X : Set (ℝ × ℝ)) (V : Finset (ℝ × ℝ)) (m : ℕ) :
    cumulativeLayer X n V m m = X := by
  ext x
  simp [mem_cumulativeLayer_iff hn le_rfl]

/-- Exhaustion by the literal annular layers, including the sole-layer
case and empty marked sets. -/
theorem exists_mem_annularLayer {n : ℝ} (hn : 0 ≤ n)
    {X : Set (ℝ × ℝ)} {V : Finset (ℝ × ℝ)} (m : ℕ)
    {x : ℝ × ℝ} (hx : x ∈ X) :
    ∃ j, j ≤ m ∧ x ∈ annularLayer X n V m j := by
  have hc : x ∈ cumulativeLayer X n V m m := by
    rw [cumulativeLayer_last hn]
    exact hx
  exact hc

/-- Distinct layers do not overlap. The strict upper cutoff assigns every
dyadic boundary to the farther layer. -/
theorem annularLayer_disjoint {n : ℝ} (hn : 0 ≤ n)
    (X : Set (ℝ × ℝ)) (V : Finset (ℝ × ℝ)) (m : ℕ)
    {i j : ℕ} (hij : i < j) :
    Disjoint (annularLayer X n V m i) (annularLayer X n V m j) := by
  apply Set.disjoint_left.2
  intro x hx hy
  have hi : dyadicScale n i ≤ cappedMarkDistance n V x := by
    rcases hx.2.2.1 with him | hi
    · have hjm := hy.2.1
      omega
    · exact hi
  have hj : cappedMarkDistance n V x < 2 * dyadicScale n j := by
    rcases hy.2.2.2 with hj0 | hj
    · omega
    · exact hj
  have hscale := dyadicScale_antitone hn (show i + 1 ≤ j by omega)
  have htwice := two_mul_dyadicScale_succ n i
  linarith

/-- Previously processed points are disjoint from the next new layer. -/
theorem cumulativeLayer_disjoint_next {n : ℝ} (hn : 0 ≤ n)
    (X : Set (ℝ × ℝ)) (V : Finset (ℝ × ℝ)) (m j : ℕ) :
    Disjoint (cumulativeLayer X n V m j) (annularLayer X n V m (j + 1)) := by
  apply Set.disjoint_left.2
  rintro x ⟨i, hij, hx⟩ hy
  exact (Set.disjoint_left.1 (annularLayer_disjoint hn X V m
    (i := i) (j := j + 1) (by omega))) hx hy

/-- Every later layer has a genuine marked point less than `2s_j` away.
In particular no later layer exists for the empty marked set. Source:
lines 685–689. -/
theorem exists_mark_near_of_mem_annularLayer {n : ℝ} (hn : 0 ≤ n)
    {X : Set (ℝ × ℝ)} {V : Finset (ℝ × ℝ)} {m j : ℕ}
    (hj : 0 < j) {x : ℝ × ℝ} (hx : x ∈ annularLayer X n V m j) :
    ∃ v ∈ V, dist x v < 2 * dyadicScale n j := by
  apply (cappedMarkDistance_lt_iff (two_mul_dyadicScale_le hn hj) V x).1
  exact hx.2.2.2.resolve_left (ne_of_gt hj)

@[simp] theorem annularLayer_empty_marks_zero (X : Set (ℝ × ℝ))
    (n : ℝ) (m : ℕ) : annularLayer X n ∅ m 0 = X := by
  ext x
  simp [annularLayer]

theorem annularLayer_empty_marks_of_pos {n : ℝ} (hn : 0 ≤ n)
    (X : Set (ℝ × ℝ)) (m : ℕ) {j : ℕ} (hj : 0 < j) :
    annularLayer X n ∅ m j = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro x hx
  obtain ⟨v, hv, _⟩ := exists_mark_near_of_mem_annularLayer hn hj hx
  exact Finset.notMem_empty v hv

/-- The angular premise in pairwise form. This formulation also handles an
empty exterior without adopting a real-valued distance-to-empty convention.
Source: equation `eq:info-angular-separation`, lines 648–652. -/
def AngularSeparation (X E : Set (ℝ × ℝ)) (n t a : ℝ)
    (V : Finset (ℝ × ℝ)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ E, a * max t (cappedMarkDistance n V x) ≤ dist x y

/-- Every nonfinal cumulative layer retains the stronger separation `a s_j`.
Source: the sentence following `eq:info-cumulative-separation`. -/
theorem cumulativeLayer_separation_nonfinal {X E : Set (ℝ × ℝ)}
    {n t a : ℝ} {V : Finset (ℝ × ℝ)} {m j : ℕ}
    (hn : 0 ≤ n) (ha : 0 ≤ a) (hsep : AngularSeparation X E n t a V)
    (hj : j < m) {x y : ℝ × ℝ}
    (hx : x ∈ cumulativeLayer X n V m j) (hy : y ∈ E) :
    a * dyadicScale n j ≤ dist x y := by
  obtain ⟨hxX, hthreshold⟩ := (mem_cumulativeLayer_iff hn hj.le).1 hx
  have hdist := hthreshold.resolve_left (ne_of_lt hj)
  have hmax : dyadicScale n j ≤ max t (cappedMarkDistance n V x) :=
    hdist.trans (le_max_right _ _)
  exact (mul_le_mul_of_nonneg_left hmax ha).trans (hsep x hxX y hy)

/-- The exact uniform cumulative separation from the source, including the
last and sole layers. The factor `1/2` follows from the constructed bound
`s_m < 2t`, not an additional separation assumption. -/
theorem cumulativeLayer_separation {X E : Set (ℝ × ℝ)}
    {n t a : ℝ} {V : Finset (ℝ × ℝ)} (c : DyadicCutoff n t)
    (hn : 0 ≤ n) (ha : 0 ≤ a) (hsep : AngularSeparation X E n t a V)
    {j : ℕ} (hj : j ≤ c.last) {x y : ℝ × ℝ}
    (hx : x ∈ cumulativeLayer X n V c.last j) (hy : y ∈ E) :
    a * dyadicScale n j / 2 ≤ dist x y := by
  obtain ⟨hxX, hthreshold⟩ := (mem_cumulativeLayer_iff hn hj).1 hx
  have hhalf : dyadicScale n j / 2 ≤ max t (cappedMarkDistance n V x) := by
    rcases hthreshold with hfinal | hdist
    · have hterminal : dyadicScale n j < 2 * t := by
        simpa [hfinal] using c.upper
      have htmax : t ≤ max t (cappedMarkDistance n V x) := le_max_left _ _
      linarith
    · have hs := dyadicScale_nonneg hn j
      have hdmax : cappedMarkDistance n V x ≤
          max t (cappedMarkDistance n V x) := le_max_right _ _
      linarith
  calc
    a * dyadicScale n j / 2 = a * (dyadicScale n j / 2) := by ring
    _ ≤ a * max t (cappedMarkDistance n V x) := mul_le_mul_of_nonneg_left hhalf ha
    _ ≤ dist x y := hsep x hxX y hy

end TNLean.PEPS.Approximation
