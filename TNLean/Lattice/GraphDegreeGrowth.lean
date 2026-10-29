/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Degree bounds and local interaction budgets

A graph of degree at most `D` has at most `(D+1)^r` sites in a closed ball
of radius `r`. A sitewise budget `B` bounds the total weight of interaction
terms meeting a region `K` by `B * K.card`. These two estimates provide
exponential shell bounds without a polynomial growth hypothesis.

The application is Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 169–190 and the truncated-dynamics estimate at lines 1469–1505.
-/

namespace TNLean.Lattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The closed ball in the extended graph metric. -/
noncomputable def graphClosedBall (G : SimpleGraph ι) (x : ι) (r : ℕ) : Finset ι :=
  Finset.univ.filter fun y ↦ G.edist x y ≤ r

omit [DecidableEq ι] in
@[simp] theorem mem_graphClosedBall (G : SimpleGraph ι) (x y : ι) (r : ℕ) :
    y ∈ graphClosedBall G x r ↔ G.edist x y ≤ r := by
  classical
  simp [graphClosedBall]

omit [DecidableEq ι] in
/-- A degree bound gives an exponential bound for closed balls. -/
theorem card_graphClosedBall_le (G : SimpleGraph ι) [DecidableRel G.Adj]
    (D : ℕ) (hD : ∀ x, G.degree x ≤ D) (x : ι) (r : ℕ) :
    (graphClosedBall G x r).card ≤ (D + 1) ^ r := by
  classical
  induction r with
  | zero =>
    have heq : graphClosedBall G x 0 = {x} := by
      ext y
      simp only [mem_graphClosedBall, Nat.cast_zero, nonpos_iff_eq_zero,
        G.edist_eq_zero_iff, Finset.mem_singleton]
      exact eq_comm
    simp [heq]
  | succ r ih =>
    have hsub : graphClosedBall G x (r + 1) ⊆
        (graphClosedBall G x r).biUnion (fun y ↦ insert y (G.neighborFinset y)) := by
      intro z hz
      have hz' : G.edist z x ≤ (r + 1 : ℕ) := by
        simpa only [mem_graphClosedBall, G.edist_comm] using hz
      obtain ⟨p, hp⟩ := G.exists_walk_of_edist_ne_top
        (ne_top_of_le_ne_top (by simp) hz')
      cases p with
      | nil =>
        exact Finset.mem_biUnion.mpr ⟨x, by simp, by simp⟩
      | @cons z y x hzy p =>
        have hlen : p.length + 1 ≤ r + 1 := by
          exact_mod_cast (hp.symm ▸ hz')
        have hy : y ∈ graphClosedBall G x r := by
          rw [mem_graphClosedBall, G.edist_comm]
          exact p.edist_le.trans (by exact_mod_cast (by omega : p.length ≤ r))
        exact Finset.mem_biUnion.mpr ⟨y, hy,
          Finset.mem_insert_of_mem ((G.mem_neighborFinset y z).mpr hzy.symm)⟩
    calc (graphClosedBall G x (r + 1)).card
        ≤ ((graphClosedBall G x r).biUnion
          (fun y ↦ insert y (G.neighborFinset y))).card := Finset.card_le_card hsub
      _ ≤ (graphClosedBall G x r).card * (D + 1) := by
        apply Finset.card_biUnion_le_card_mul
        intro y _
        exact (Finset.card_insert_le _ _).trans (by
          rw [G.card_neighborFinset_eq_degree]
          exact Nat.add_le_add_right (hD y) 1)
      _ ≤ (D + 1) ^ r * (D + 1) := Nat.mul_le_mul_right _ ih
      _ = (D + 1) ^ (r + 1) := (pow_succ _ _).symm


section Anchor

variable {κ : Type*} [Fintype κ]

omit [Fintype ι] in
/-- A local support budget also bounds the weights assigned to any one anchor contained
in those supports. This is the norm-budget reduction in Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `oibu`, lines 1689–1694. -/
theorem sum_weight_anchor_le_of_support_budget (X : κ → Finset ι) (a : κ → ι)
    (ha : ∀ i, a i ∈ X i) (w : κ → ℝ) (hw : ∀ i, 0 ≤ w i) (B : ℝ)
    (hBudget : ∀ x, ∑ i ∈ Finset.univ.filter (fun i ↦ x ∈ X i), w i ≤ B) (x : ι) :
    ∑ i ∈ Finset.univ.filter (fun i ↦ a i = x), w i ≤ B := by
  classical
  refine le_trans ?_ (hBudget x)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun i hi ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [← hi]; exact ha i) (fun i _ _ ↦ hw i)

end Anchor

/-- Group nonnegative coefficients by their anchors and apply a bound on each fibre. -/
theorem sum_weight_mul_comp_le_budget_mul_sum {κ : Type*} [Fintype κ]
    (a : κ → ι) (w : κ → ℝ) (B : ℝ)
    (hBudget : ∀ y, ∑ k ∈ Finset.univ.filter (fun k ↦ a k = y), w k ≤ B)
    (f : ι → ℝ) (hf : ∀ y, 0 ≤ f y) :
    ∑ k, w k * f (a k) ≤ B * ∑ y, f y := by
  classical
  calc _ = ∑ y, ∑ k ∈ Finset.univ.filter (fun k ↦ a k = y), w k * f (a k) :=
        (Finset.sum_fiberwise_of_maps_to (fun k _ ↦ Finset.mem_univ (a k)) _).symm
    _ = ∑ y, (∑ k ∈ Finset.univ.filter (fun k ↦ a k = y), w k) * f y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k hk ↦ by rw [(Finset.mem_filter.mp hk).2]
    _ ≤ ∑ y, B * f y := Finset.sum_le_sum fun y _ ↦
      mul_le_mul_of_nonneg_right (hBudget y) (hf y)
    _ = B * ∑ y, f y := (Finset.mul_sum _ _ _).symm

omit [Fintype ι] in
/-- A sitewise interaction budget bounds the total weight of terms meeting a region. -/
theorem sum_weight_meeting_le_card_mul_budget {κ : Type*} [Fintype κ]
    (X : κ → Finset ι) (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (B : ℝ)
    (hBudget : ∀ x, ∑ k ∈ Finset.univ.filter (fun k ↦ x ∈ X k), w k ≤ B)
    (K : Finset ι) (t : Finset κ) (ht : ∀ k ∈ t, ¬Disjoint (X k) K) :
    ∑ k ∈ t, w k ≤ (K.card : ℝ) * B := by
  classical
  calc ∑ k ∈ t, w k
      ≤ ∑ k ∈ t, ∑ x ∈ K, if x ∈ X k then w k else 0 := by
        apply Finset.sum_le_sum
        intro k hk
        obtain ⟨x, hxX, hxK⟩ := Finset.not_disjoint_iff.mp (ht k hk)
        have hsingle := Finset.single_le_sum
          (f := fun x ↦ if x ∈ X k then w k else 0)
          (fun x _ ↦ by split_ifs <;> first | exact hw k | exact le_rfl) hxK
        simpa [hxX] using hsingle
    _ ≤ ∑ k, ∑ x ∈ K, if x ∈ X k then w k else 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ ↦ Finset.sum_nonneg fun x _ ↦ by
          split_ifs <;> first | exact hw k | exact le_rfl)
    _ = ∑ x ∈ K, ∑ k ∈ Finset.univ.filter (fun k ↦ x ∈ X k), w k := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ ∑ _x ∈ K, B := Finset.sum_le_sum fun x _ ↦ hBudget x
    _ = (K.card : ℝ) * B := by simp


/-- The weighted shell has an exponential bound derived from a degree bound. -/
theorem sum_weight_meeting_graphClosedBall_le {κ : Type*} [Fintype κ]
    (G : SimpleGraph ι) [DecidableRel G.Adj] (D : ℕ) (hD : ∀ x, G.degree x ≤ D)
    (X : κ → Finset ι) (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (B : ℝ) (hB : 0 ≤ B)
    (hBudget : ∀ x, ∑ k ∈ Finset.univ.filter (fun k ↦ x ∈ X k), w k ≤ B)
    (x : ι) (l C : ℕ) (K : Finset ι) (hK : K ⊆ graphClosedBall G x (l + C))
    (t : Finset κ) (ht : ∀ k ∈ t, ¬Disjoint (X k) K) :
    ∑ k ∈ t, w k ≤ B * (D + 1 : ℝ) ^ C * Real.exp (Real.log (D + 1) * l) := by
  have hb := sum_weight_meeting_le_card_mul_budget X w hw B hBudget K t ht
  have hc := (Finset.card_le_card hK).trans (card_graphClosedBall_le G D hD x (l + C))
  have heq : Real.exp (Real.log (D + 1) * l) = (D + 1 : ℝ) ^ l := by
    rw [mul_comm (Real.log (D + 1)), Real.exp_nat_mul, Real.exp_log (by positivity)]
  rw [heq]
  calc ∑ k ∈ t, w k ≤ (K.card : ℝ) * B := hb
    _ ≤ (D + 1 : ℝ) ^ (l + C) * B :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hB
    _ = B * (D + 1 : ℝ) ^ C * (D + 1 : ℝ) ^ l := by rw [pow_add]; ring


omit [DecidableEq ι] in
/-- A retained term centred in a ball acts inside the ball enlarged by its range. -/
theorem graphClosedBall_subset_of_mem (G : SimpleGraph ι) (x i : ι) (l R : ℕ)
    (hi : i ∈ graphClosedBall G x l) :
    graphClosedBall G i R ⊆ graphClosedBall G x (l + R) := by
  intro y hy
  rw [mem_graphClosedBall] at hi hy ⊢
  exact (G.edist_triangle (u := x) (v := i) (w := y)).trans
    (by simpa only [Nat.cast_add] using add_le_add hi hy)

omit [DecidableEq ι] in
/-- Omitted centres lie far from every site of the original and omitted supports. -/
theorem graphClosedBall_separation (G : SimpleGraph ι) (x k : ι) (l R : ℕ)
    (hk : k ∉ graphClosedBall G x l) {z y : ι}
    (hz : z ∈ graphClosedBall G x R) (hy : y ∈ graphClosedBall G k R) :
    ((l - 2 * R : ℕ) : ℕ∞) ≤ G.edist z y := by
  simp only [mem_graphClosedBall] at hk hz hy
  by_cases hl : 2 * R ≤ l
  · by_contra! hd
    have hbound : G.edist x k ≤ (R : ℕ∞) + (l - 2 * R : ℕ) + R := by
      calc G.edist x k ≤ G.edist x z + G.edist z k := G.edist_triangle
        _ ≤ G.edist x z + (G.edist z y + G.edist y k) :=
          add_le_add le_rfl G.edist_triangle
        _ ≤ (R : ℕ∞) + ((l - 2 * R : ℕ) + R) :=
          add_le_add hz
            (add_le_add hd.le (by simpa only [G.edist_comm] using hy))
        _ = _ := by ac_rfl
    have heq : (R : ℕ∞) + (l - 2 * R : ℕ) + R = (l : ℕ) := by
      rw [← Nat.cast_add, ← Nat.cast_add]
      congr 1
      omega
    exact hk (heq ▸ hbound)
  · simp [Nat.sub_eq_zero_of_le (by omega : l ≤ 2 * R)]


end TNLean.Lattice
