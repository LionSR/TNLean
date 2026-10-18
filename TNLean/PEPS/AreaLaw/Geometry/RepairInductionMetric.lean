/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairDescendants
import TNLean.PEPS.AreaLaw.Geometry.RepairDepth
import TNLean.PEPS.AreaLaw.Geometry.RepairInitialMarkFacts

/-!
# Metric invariants of the uniform repair induction

Fix an isolation constant `0 < a₀ ≤ 1` and a stopping scale `S_* > 0` with
`d(S) ≤ (a₀ / 1000) S` for every `S ≥ S_*`. Suppose every initial mark has
scale at least `S_*` and distinct initial marks satisfy
`‖v - w‖_∞ ≥ a₀ max(S_v, S_w)`. Then, for the actual repair stages:

* every mark of every generation has scale at least `S_*`;
* distinct marks of every generation satisfy the same separation inequality;
* the simultaneous removal squares of one generation are disjoint;
* every descendant mark and every descendant birth region of a mark `(v, S)`
  lies within sup distance `2 d(S)` of `v`;
* the isolated-star square `v + [-a₀ S, a₀ S]²` of every mark avoids the
  closed terminal squares of all earlier generations;
* every branch terminates after finitely many generations.

These are the assertions of the uniform repair induction that follow from
the scale margins and the separation inequality alone; they use no property
of the current regions.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:trim-margins`, lines 380–394, and
`geometry:repair-induction`, lines 471–485 with its proof, lines 487–496 and
516–542.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Written from the manuscript; no upstream Lean text is reused.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Each centered child offset has sup norm at most one.
Source: area-law Section 11, `geometry:repair-induction`, lines 506–512. -/
theorem norm_repairChildOffset_le (e : Fin 3 × Fin 3) : ‖repairChildOffset e‖ ≤ 1 := by
  obtain ⟨a, b⟩ := e
  fin_cases a <;> fin_cases b <;> norm_num [repairChildOffset, Prod.norm_def]

private theorem one_le_dist_fin_three {a b : Fin 3} (h : a ≠ b) :
    1 ≤ dist ((a.val : ℝ) - 1) ((b.val : ℝ) - 1) := by
  rw [Real.dist_eq]
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl h | norm_num

/-- Distinct centered child offsets are at sup distance at least one.
Source: area-law Section 11, `geometry:repair-induction`, line 516. -/
theorem one_le_dist_repairChildOffset {e f : Fin 3 × Fin 3} (h : e ≠ f) :
    1 ≤ dist (repairChildOffset e) (repairChildOffset f) := by
  rw [Prod.dist_eq]
  by_cases h₁ : e.1 = f.1
  · have h₂ : e.2 ≠ f.2 := fun h₂ ↦ h (Prod.ext h₁ h₂)
    exact (one_le_dist_fin_three h₂).trans (le_max_right _ _)
  · exact (one_le_dist_fin_three h₁).trans (le_max_left _ _)

/-- A child lies within sup distance `d(S)` of its parent.
Source: area-law Section 11, `geometry:repair-induction`, lines 506–512 and
529–531. -/
theorem dist_repairChildLocation_le {ι : Type*} (v : ι → ℝ × ℝ) (S : ι → ℝ)
    (Sstar : ℝ) (q : RepairChildIndex S Sstar) :
    dist (repairChildLocation v S Sstar q) (v q.1.val) ≤ repairHalfSide (S q.1.val) := by
  rw [repairChildLocation, dist_self_add_left, norm_smul, Real.norm_of_nonneg
    (repairHalfSide_pos _).le]
  exact mul_le_of_le_one_right (repairHalfSide_pos _).le (norm_repairChildOffset_le _)

/-- The closed birth of a replacement lies in the removal square of its parent.
Source: area-law Section 11, lines 404–417. -/
theorem repairReplacementBirthRegion_subset_repairSquare {ι : Type*} (v : ℝ × ℝ)
    (S : ℝ) (ξ : ι → Fin 2) (σ : RepairFanSlot → ι) (H : RepairFanRun ξ σ) :
    repairReplacementBirthRegion v S ξ σ H ⊆ repairSquare v S := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' : y ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by
    have hcover := cellFanRunRegions_cover (-1, -1) 1 (0, 0) repairFanSplit
      (repairExteriorColor ξ σ)
    rw [← closedBall_cellFanCenter_eq_closure_dyadicCell] at hcover
    have hc : cellFanCenter (-1, -1) 1 (0, 0) = 0 := by
      simp [cellFanCenter, Prod.ext_iff]
    have := hcover ▸ Set.mem_iUnion.mpr ⟨H, hy⟩
    simpa [hc] using this
  rw [repairSquare, Metric.mem_closedBall, repairAffineMap, dist_self_add_left, norm_smul,
    Real.norm_of_nonneg (repairHalfSide_pos _).le]
  exact mul_le_of_le_one_right (repairHalfSide_pos _).le (by simpa using hy')

section Stages

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C k₀ : ℕ)
  (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- A mark of the next generation has the removal half-side of its parent as
its scale. Source: area-law Section 11, lines 404–409. -/
theorem repairStage_scale_succ (j : ℕ) (q : (𝔇 (j + 1)).markIndex) :
    (𝔇 (j + 1)).scale q =
      repairHalfSide ((𝔇 j).scale (repairMarkParent o Λ A C k₀ hC h₀ Sstar j q)) :=
  rfl

/-- The parent of a mark of the next generation is nonterminal.
Source: area-law Section 11, lines 401–409. -/
theorem le_repairHalfSide_repairMarkParent (j : ℕ) (q : (𝔇 (j + 1)).markIndex) :
    Sstar ≤ repairHalfSide ((𝔇 j).scale (repairMarkParent o Λ A C k₀ hC h₀ Sstar j q)) :=
  (show RepairNextMarkIndex j (𝔇 j).scale Sstar from q).2.1.property

/-- A mark of the next generation lies within sup distance `d(S)` of its parent.
Source: area-law Section 11, lines 404–409 and 529–531. -/
theorem dist_repairMarkParent_le (j : ℕ) (q : (𝔇 (j + 1)).markIndex) :
    dist ((𝔇 (j + 1)).location q)
        ((𝔇 j).location (repairMarkParent o Λ A C k₀ hC h₀ Sstar j q)) ≤
      repairHalfSide ((𝔇 j).scale (repairMarkParent o Λ A C k₀ hC h₀ Sstar j q)) :=
  dist_repairChildLocation_le (𝔇 j).location (𝔇 j).scale Sstar
    (show RepairNextMarkIndex j (𝔇 j).scale Sstar from q).2

@[simp]
theorem repairMarkAncestor_zero (i : ℕ) (q : (𝔇 (i + 0)).markIndex) :
    repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i 0 q = q :=
  rfl

theorem repairMarkAncestor_succ (i n : ℕ) (q : (𝔇 (i + (n + 1))).markIndex) :
    repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i (n + 1) q =
      repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n
        (repairMarkParent o Λ A C k₀ hC h₀ Sstar (i + n) q) :=
  rfl

/-- The birth of a fresh replacement lies in the removal square of its parent.
Source: area-law Section 11, lines 404–417. -/
theorem repairStage_birth_subset_repairSquare (j : ℕ) (x : (𝔇 (j + 1)).regionIndex)
    (m : (𝔇 j).markIndex) (hx : repairRegionParent o Λ A C k₀ hC h₀ Sstar j x = some m) :
    (𝔇 (j + 1)).birth x ⊆ repairSquare ((𝔇 j).location m) ((𝔇 j).scale m) := by
  revert x
  let : Nonempty (𝔇 j).regionIndex := ⟨(𝔇 j).dummy⟩
  change ∀ x : RepairRegionIndex j (𝔇 j).scale Sstar (𝔇 j).color
      (repairCurrentAssignments (𝔇 j).current (𝔇 j).location (𝔇 j).scale),
    Sum.elim (fun _ ↦ none) (fun q ↦ some q.2.1.val) x = some m →
      repairNextBirthRegion j (𝔇 j).birth (𝔇 j).location (𝔇 j).scale Sstar (𝔇 j).color
        (repairCurrentAssignments (𝔇 j).current (𝔇 j).location (𝔇 j).scale) x ⊆
      repairSquare ((𝔇 j).location m) ((𝔇 j).scale m)
  rintro (i | ⟨_, ⟨P, hP⟩, H⟩) hx
  · simp at hx
  · obtain rfl : P = m := by simpa using hx
    exact repairReplacementBirthRegion_subset_repairSquare _ _ _ _ H

variable {o Λ A C k₀ hC h₀ Sstar}

/-- Hypotheses on the isolation constant and stopping scale: `0 < a₀ ≤ 1`,
`S_* > 0`, the margin `d(S) ≤ (a₀ / 1000) S` for `S ≥ S_*`, initial scales at
least `S_*`, and the initial separation inequality.
Source: area-law Section 11, `geometry:trim-margins`, lines 380–394, and
`geometry:initial-stars`, lines 336–339. -/
structure RepairMetricHypotheses (a₀ : ℝ) : Prop where
  pos : 0 < a₀
  le_one : a₀ ≤ 1
  stop_pos : 0 < Sstar
  margin : ∀ S, Sstar ≤ S → repairHalfSide S ≤ a₀ / 1000 * S
  initial_scale : ∀ p, Sstar ≤ (𝔇 0).scale p
  initial_separated : ∀ p q, p ≠ q →
    a₀ * max ((𝔇 0).scale p) ((𝔇 0).scale q) ≤ dist ((𝔇 0).location p) ((𝔇 0).location q)

namespace RepairMetricHypotheses

variable {a₀ : ℝ} (h : RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
  (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀)
include h

/-- Every mark of every generation has scale at least `S_*`.
Source: area-law Section 11, lines 393–409. -/
theorem le_scale : ∀ j p, Sstar ≤ (𝔇 j).scale p
  | 0, p => h.initial_scale p
  | j + 1, p => le_repairHalfSide_repairMarkParent o Λ A C k₀ hC h₀ Sstar j p

theorem scale_pos (j : ℕ) (p : (𝔇 j).markIndex) : 0 < (𝔇 j).scale p :=
  h.stop_pos.trans_le (h.le_scale j p)

/-- The margin at an actual mark scale.
Source: area-law Section 11, `geometry:trim-margins`, lines 386–391. -/
theorem halfSide_le (j : ℕ) (p : (𝔇 j).markIndex) :
    repairHalfSide ((𝔇 j).scale p) ≤ a₀ / 1000 * (𝔇 j).scale p :=
  h.margin _ (h.le_scale j p)

theorem two_mul_halfSide_le (j : ℕ) (p : (𝔇 j).markIndex) :
    2 * repairHalfSide ((𝔇 j).scale p) ≤ (𝔇 j).scale p := by
  have := h.halfSide_le j p
  have := h.scale_pos j p
  have : a₀ / 1000 * (𝔇 j).scale p ≤ 1 / 2 * (𝔇 j).scale p :=
    mul_le_mul_of_nonneg_right (by linarith [h.le_one]) this.le
  linarith

/-- Distinct marks of a generation are separated by `a₀` times the larger
scale, at every generation, with the same constant.
Source: area-law Section 11, `geometry:repair-induction`, lines 477–478 and
516–524. -/
theorem separated : ∀ j (p q : (𝔇 j).markIndex), p ≠ q →
    a₀ * max ((𝔇 j).scale p) ((𝔇 j).scale q) ≤ dist ((𝔇 j).location p) ((𝔇 j).location q)
  | 0 => h.initial_separated
  | j + 1 => by
    have hsep := separated j
    have hmargin := h.halfSide_le j
    have hpos := h.scale_pos j
    have ha₀ := h.pos
    have ha₁ := h.le_one
    change ∀ p q : RepairNextMarkIndex j (𝔇 j).scale Sstar, p ≠ q →
      a₀ * max (repairChildScale (𝔇 j).scale Sstar p.2)
          (repairChildScale (𝔇 j).scale Sstar q.2) ≤
        dist (repairChildLocation (𝔇 j).location (𝔇 j).scale Sstar p.2)
          (repairChildLocation (𝔇 j).location (𝔇 j).scale Sstar q.2)
    rintro ⟨⟨n, rfl⟩, ⟨P, hP⟩, e⟩ ⟨⟨m, rfl⟩, ⟨Q, hQ⟩, f⟩ hne
    simp only [repairChildScale]
    by_cases hPQ : P = Q
    · subst hPQ
      have hef : e ≠ f := fun hef ↦ hne (by subst hef; rfl)
      rw [max_self, repairChildLocation, repairChildLocation, dist_add_left, dist_smul₀,
        Real.norm_of_nonneg (repairHalfSide_pos _).le]
      exact mul_comm a₀ _ ▸ mul_le_mul_of_nonneg_left
        (ha₁.trans (one_le_dist_repairChildOffset hef)) (repairHalfSide_pos _).le
    · set M := max ((𝔇 j).scale P) ((𝔇 j).scale Q)
      have hPQd := hsep P Q hPQ
      have hp := dist_repairChildLocation_le (𝔇 j).location (𝔇 j).scale Sstar
        (⟨P, hP⟩, e)
      have hq := dist_repairChildLocation_le (𝔇 j).location (𝔇 j).scale Sstar
        (⟨Q, hQ⟩, f)
      simp only at hp hq
      have htri := dist_triangle4 ((𝔇 j).location P)
        (repairChildLocation (𝔇 j).location (𝔇 j).scale Sstar (⟨P, hP⟩, e))
        (repairChildLocation (𝔇 j).location (𝔇 j).scale Sstar (⟨Q, hQ⟩, f))
        ((𝔇 j).location Q)
      have e1 := dist_comm ((𝔇 j).location P)
        (repairChildLocation (𝔇 j).location (𝔇 j).scale Sstar (⟨P, hP⟩, e))
      have hM : 0 ≤ M := (hpos P).le.trans (le_max_left _ _)
      have hdP : repairHalfSide ((𝔇 j).scale P) ≤ a₀ / 1000 * M :=
        (hmargin P).trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))
      have hdQ : repairHalfSide ((𝔇 j).scale Q) ≤ a₀ / 1000 * M :=
        (hmargin Q).trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))
      have hmax : a₀ * max (repairHalfSide ((𝔇 j).scale P))
          (repairHalfSide ((𝔇 j).scale Q)) ≤ a₀ * M / 1000 := by
        calc _ ≤ a₀ * (a₀ / 1000 * M) :=
              mul_le_mul_of_nonneg_left (max_le hdP hdQ) ha₀.le
          _ = a₀ * (a₀ * M) / 1000 := by ring
          _ ≤ 1 * (a₀ * M) / 1000 := by gcongr
          _ = a₀ * M / 1000 := by ring
      have : 0 ≤ a₀ * M := mul_nonneg ha₀.le hM
      have h1 : a₀ / 1000 * M = a₀ * M / 1000 := by ring
      linarith

/-- The simultaneous removal squares of one generation are disjoint.
Source: area-law Section 11, `geometry:repair-induction`, lines 478 and
487–496. -/
theorem disjoint_repairSquare (j : ℕ) (p q : (𝔇 j).markIndex) (hpq : p ≠ q) :
    Disjoint (repairSquare ((𝔇 j).location p) ((𝔇 j).scale p))
      (repairSquare ((𝔇 j).location q) ((𝔇 j).scale q)) := by
  apply Metric.closedBall_disjoint_closedBall
  have hsep := h.separated j p q hpq
  have hp := h.halfSide_le j p
  have hq := h.halfSide_le j q
  have hM : 0 < max ((𝔇 j).scale p) ((𝔇 j).scale q) :=
    (h.scale_pos j p).trans_le (le_max_left _ _)
  have h1 : a₀ / 1000 * (𝔇 j).scale p ≤ a₀ / 1000 * max ((𝔇 j).scale p) ((𝔇 j).scale q) :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith [h.pos])
  have h2 : a₀ / 1000 * (𝔇 j).scale q ≤ a₀ / 1000 * max ((𝔇 j).scale p) ((𝔇 j).scale q) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith [h.pos])
  have h3 := mul_pos h.pos hM
  nlinarith

/-- A descendant of positive generation, together with its scale, stays within
`2 d(S)` of its ancestor `(v, S)`.
Source: area-law Section 11, `geometry:repair-induction`, lines 482–484 and
529–536. -/
theorem dist_ancestor_add_scale_le (i : ℕ) :
    ∀ (n : ℕ) (q : (𝔇 (i + (n + 1))).markIndex),
      dist ((𝔇 (i + (n + 1))).location q)
          ((𝔇 i).location (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i (n + 1) q)) +
        (𝔇 (i + (n + 1))).scale q ≤
      2 * repairHalfSide ((𝔇 i).scale (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i (n + 1) q))
  | 0, q => by
    have := dist_repairMarkParent_le o Λ A C k₀ hC h₀ Sstar i q
    change dist ((𝔇 (i + 1)).location q)
        ((𝔇 i).location (repairMarkParent o Λ A C k₀ hC h₀ Sstar i q)) +
      (𝔇 (i + 1)).scale q ≤
      2 * repairHalfSide ((𝔇 i).scale (repairMarkParent o Λ A C k₀ hC h₀ Sstar i q))
    rw [repairStage_scale_succ]
    linarith
  | n + 1, q => by
    obtain ⟨q', hq'⟩ : ∃ q', repairMarkParent o Λ A C k₀ hC h₀ Sstar (i + (n + 1)) q = q' :=
      ⟨_, rfl⟩
    have ih := dist_ancestor_add_scale_le i n q'
    have hq : dist ((𝔇 (i + (n + 1 + 1))).location q) ((𝔇 (i + (n + 1))).location q') ≤
        repairHalfSide ((𝔇 (i + (n + 1))).scale q') := by
      rw [← hq']; exact dist_repairMarkParent_le o Λ A C k₀ hC h₀ Sstar (i + (n + 1)) q
    have h2 := h.two_mul_halfSide_le (i + (n + 1)) q'
    have htri := dist_triangle ((𝔇 (i + (n + 1 + 1))).location q)
      ((𝔇 (i + (n + 1))).location q')
      ((𝔇 i).location (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i (n + 1) q'))
    have hs : (𝔇 (i + (n + 1 + 1))).scale q = repairHalfSide ((𝔇 (i + (n + 1))).scale q') := by
      rw [← hq']; rfl
    rw [repairMarkAncestor_succ (n := n + 1), hq', hs]
    linarith

/-- Every descendant mark of `(v, S)` lies within sup distance `2 d(S)` of `v`.
Source: area-law Section 11, `geometry:repair-induction`, lines 482–484. -/
theorem dist_descendant_le (i n : ℕ) (q : (𝔇 (i + n)).markIndex) :
    dist ((𝔇 (i + n)).location q)
        ((𝔇 i).location (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n q)) ≤
      2 * repairHalfSide ((𝔇 i).scale (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n q)) := by
  cases n with
  | zero => simpa using (repairHalfSide_pos _).le
  | succ n =>
    have := h.dist_ancestor_add_scale_le i n q
    have := h.scale_pos _ q
    linarith

/-- Every descendant birth region of `(v, S)` lies within sup distance
`2 d(S)` of `v`.
Source: area-law Section 11, `geometry:repair-induction`, lines 482–484. -/
theorem birth_descendant_subset (i n : ℕ) (x : (𝔇 (i + n + 1)).regionIndex)
    (m : (𝔇 (i + n)).markIndex)
    (hx : repairRegionParent o Λ A C k₀ hC h₀ Sstar (i + n) x = some m) :
    (𝔇 (i + n + 1)).birth x ⊆
      Metric.closedBall ((𝔇 i).location (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n m))
        (2 * repairHalfSide ((𝔇 i).scale (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n m))) := by
  refine (repairStage_birth_subset_repairSquare o Λ A C k₀ hC h₀ Sstar (i + n) x m hx).trans
    (Metric.closedBall_subset_closedBall' ?_)
  cases n with
  | zero =>
    change repairHalfSide ((𝔇 i).scale m) + dist ((𝔇 i).location m) ((𝔇 i).location m) ≤
      2 * repairHalfSide ((𝔇 i).scale m)
    rw [dist_self]
    linarith [repairHalfSide_pos ((𝔇 i).scale m)]
  | succ n =>
    have := h.dist_ancestor_add_scale_le i n m
    have := h.two_mul_halfSide_le _ m
    have := repairHalfSide_pos ((𝔇 (i + (n + 1))).scale m)
    linarith

/-- Along a branch the scales at least halve at each generation, and a
descendant of positive generation has scale at most the removal half-side of
its ancestor.
Source: area-law Section 11, `geometry:repair-induction`, lines 538–541. -/
theorem scale_mul_two_pow_le (i : ℕ) :
    ∀ (n : ℕ) (q : (𝔇 (i + n)).markIndex),
      (𝔇 (i + n)).scale q * 2 ^ n ≤
        (𝔇 i).scale (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n q)
  | 0, q => by simp
  | n + 1, q => by
    have ih := scale_mul_two_pow_le i n (repairMarkParent o Λ A C k₀ hC h₀ Sstar (i + n) q)
    have h2 : 2 * (𝔇 (i + (n + 1))).scale q ≤
        (𝔇 (i + n)).scale (repairMarkParent o Λ A C k₀ hC h₀ Sstar (i + n) q) :=
      h.two_mul_halfSide_le (i + n) _
    rw [repairMarkAncestor_succ, pow_succ]
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) n]

theorem scale_le_halfSide_ancestor (i : ℕ) :
    ∀ (n : ℕ) (q : (𝔇 (i + (n + 1))).markIndex),
      (𝔇 (i + (n + 1))).scale q ≤
        repairHalfSide ((𝔇 i).scale (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i (n + 1) q))
  | 0, q => le_of_eq (repairStage_scale_succ o Λ A C k₀ hC h₀ Sstar i q)
  | n + 1, q => by
    obtain ⟨q', hq'⟩ : ∃ q', repairMarkParent o Λ A C k₀ hC h₀ Sstar (i + (n + 1)) q = q' :=
      ⟨_, rfl⟩
    have ih := scale_le_halfSide_ancestor i n q'
    have h2 := h.two_mul_halfSide_le (i + (n + 1)) q'
    have := repairHalfSide_pos ((𝔇 (i + (n + 1))).scale q')
    have hs : (𝔇 (i + (n + 1 + 1))).scale q = repairHalfSide ((𝔇 (i + (n + 1))).scale q') := by
      rw [← hq']; rfl
    rw [repairMarkAncestor_succ (n := n + 1), hq', hs]
    linarith

/-- Each branch terminates after finitely many generations.
Source: area-law Section 11, `geometry:repair-induction`, lines 484 and
538–541. -/
theorem terminates (i : ℕ) (p : (𝔇 i).markIndex) :
    ∃ n, ∀ q, repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n q ≠ p := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((𝔇 i).scale p / Sstar) one_lt_two
  refine ⟨n, fun q hq ↦ ?_⟩
  have h1 := h.scale_mul_two_pow_le i n q
  rw [hq] at h1
  have h2 := mul_le_mul_of_nonneg_right (h.le_scale _ q)
    (pow_pos (two_pos : (0 : ℝ) < 2) n).le
  rw [div_lt_iff₀ h.stop_pos] at hn
  linarith

/-- The isolated-star square of every mark avoids the closed terminal
squares of all earlier generations.
Source: area-law Section 11, `geometry:repair-induction`, lines 474–476 and
526–536. -/
theorem disjoint_earlierTerminalSquares (j : ℕ) (p : (𝔇 j).markIndex) :
    Disjoint (Metric.closedBall ((𝔇 j).location p) (a₀ * (𝔇 j).scale p))
      (repairEarlierTerminalSquares o Λ A C k₀ hC h₀ Sstar j) := by
  rw [Set.disjoint_left]
  intro x hxp hxt
  simp only [repairEarlierTerminalSquares, Set.mem_iUnion] at hxt
  obtain ⟨i, hij, ⟨t, ht⟩, hx⟩ := hxt
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hij
  set a := repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i (n + 1) p
  have hnonterm : Sstar ≤ repairHalfSide ((𝔇 i).scale a) :=
    (h.le_scale _ p).trans (h.scale_le_halfSide_ancestor i n p)
  have hat : a ≠ t := by
    rintro rfl
    exact absurd hnonterm (not_le.mpr ht)
  have hsep := h.separated i a t hat
  have hda := h.dist_ancestor_add_scale_le i n p
  have hxt' : dist x ((𝔇 i).location t) ≤ repairHalfSide ((𝔇 i).scale t) :=
    Metric.mem_closedBall.mp hx
  have hxp' : dist x ((𝔇 (i + (n + 1))).location p) ≤ a₀ * (𝔇 (i + (n + 1))).scale p :=
    hxp
  have hstar : a₀ * (𝔇 (i + (n + 1))).scale p ≤ (𝔇 (i + (n + 1))).scale p :=
    mul_le_of_le_one_left (h.scale_pos _ p).le h.le_one
  have htri := dist_triangle4 ((𝔇 i).location a) ((𝔇 (i + (n + 1))).location p) x
    ((𝔇 i).location t)
  have e1 := dist_comm ((𝔇 i).location a) ((𝔇 (i + (n + 1))).location p)
  have e2 := dist_comm ((𝔇 (i + (n + 1))).location p) x
  have hdA := h.halfSide_le i a
  have hdT := h.halfSide_le i t
  set M := max ((𝔇 i).scale a) ((𝔇 i).scale t)
  have hM : 0 < M := (h.scale_pos i a).trans_le (le_max_left _ _)
  have h1 : a₀ / 1000 * (𝔇 i).scale a ≤ a₀ / 1000 * M :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith [h.pos])
  have h2 : a₀ / 1000 * (𝔇 i).scale t ≤ a₀ / 1000 * M :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith [h.pos])
  have h3 := mul_pos h.pos hM
  have h4 : a₀ / 1000 * M = a₀ * M / 1000 := by ring
  linarith

end RepairMetricHypotheses

end Stages

/-- The initial stage assigns every mark the side `2 ^ fineScaleIndex k` of
an incident cell of a layer `k ≥ k₀`, and distinct initial marks are
separated by a quarter of the larger scale.
Source: area-law Section 11, lines 325–330, and `geometry:initial-stars`,
lines 336–339 and 352–363. -/
theorem initialRepairStage_scale_separated (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
    (A : Finset (Site Λ)) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) :
    (∀ p, ∃ k, k₀ ≤ k ∧
      (initialRepairStage o Λ A C k₀ hC h₀).scale p = (2 : ℝ) ^ fineScaleIndex k) ∧
    ∀ p q, p ≠ q →
      max ((initialRepairStage o Λ A C k₀ hC h₀).scale p)
          ((initialRepairStage o Λ A C k₀ hC h₀).scale q) / 4 ≤
        dist ((initialRepairStage o Λ A C k₀ hC h₀).location p)
          ((initialRepairStage o Λ A C k₀ hC h₀).location q) := by
  have hspec := initialRepairStage_mark_spec o Λ A C k₀ hC h₀
  refine ⟨fun p ↦ ?_, hspec.2.2.2.2.1⟩
  obtain ⟨_, k, _, hk, _, _, hS⟩ := hspec.2.2.1 p
  exact ⟨k, hk, hS⟩

/-- For every `0 < a₀ ≤ 1/4` there is a threshold `T` such that every
stopping scale `S_* ≥ T` satisfies the margin `d(S) ≤ (a₀ / 1000) S` for
`S ≥ S_*`, and, for each layer width, the initial stage has scales at least
`S_*` once the lower layer index is large. The initial separation holds with
constant `1/4`, hence with `a₀`.
Source: area-law Section 11, `geometry:trim-margins`, lines 380–394, and
`geometry:initial-stars`, lines 336–339. -/
theorem exists_repairMetricHypotheses {a₀ : ℝ} (ha₀ : 0 < a₀) (ha₀' : a₀ ≤ 1 / 4) :
    ∃ T : ℝ, ∀ Sstar, T ≤ Sstar → ∀ C : ℕ, ∃ K : ℕ,
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (k₀ : ℕ)
        (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀), K ≤ k₀ →
          RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
            (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀ := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (eventually_repairHalfSide_le ha₀)
  refine ⟨max T 1, fun Sstar hSstar C ↦ ?_⟩
  have hSpos : 0 < Sstar := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hSstar)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt Sstar (one_lt_two : (1 : ℝ) < 2)
  have hζ : (0 : ℝ) < Exponents.zeta := by
    norm_num [Exponents.zeta, Exponents.geometryDelta]
  refine ⟨⌈(m : ℝ) / Exponents.zeta⌉₊, fun o Λ A k₀ hC h₀ hK ↦ ?_⟩
  obtain ⟨hscale, hsep⟩ := initialRepairStage_scale_separated o Λ A C k₀ hC h₀
  refine ⟨ha₀, by linarith, hSpos, fun S hS ↦ hT S ((le_max_left _ _).trans (hSstar.trans hS)),
    fun p ↦ ?_, fun p q hpq ↦ ?_⟩
  · obtain ⟨k, hk, hS⟩ := hscale p
    change Sstar ≤ (initialRepairStage o Λ A C k₀ hC h₀).scale p
    rw [hS]
    refine hm.le.trans (pow_le_pow_right₀ one_le_two ?_)
    apply Nat.le_floor
    have hK' : (m : ℝ) / Exponents.zeta ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hK.trans hk)
    rw [div_le_iff₀ hζ] at hK'
    linarith
  · have h1 := hsep p q hpq
    have h2 : 0 ≤ max ((initialRepairStage o Λ A C k₀ hC h₀).scale p)
        ((initialRepairStage o Λ A C k₀ hC h₀).scale q) := by
      obtain ⟨k, -, hS⟩ := hscale p
      exact (hS ▸ pow_nonneg zero_le_two _ : (0 : ℝ) ≤ _).trans (le_max_left _ _)
    change a₀ * max ((initialRepairStage o Λ A C k₀ hC h₀).scale p)
        ((initialRepairStage o Λ A C k₀ hC h₀).scale q) ≤
      dist ((initialRepairStage o Λ A C k₀ hC h₀).location p)
        ((initialRepairStage o Λ A C k₀ hC h₀).location q)
    nlinarith

end TNLean.PEPS.AreaLaw.Geometry
