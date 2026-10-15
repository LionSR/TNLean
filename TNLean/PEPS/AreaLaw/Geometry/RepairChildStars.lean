/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairChildCones

/-!
# Isolated stars at the children of one repair

Let a parent at `v` with assigned scale `S` carry a local radial model in an
open square of radius `r ≥ 3 d / 2` about `v`, where `d = d(S)`. Remove the
closed square `v + [-d, d]²` from the old regions and add, for every
connected run of equal exterior labels, the interior of its transported
triangles, with the opposite label. Then each of the nine children
`c = v + d e` has an isolated star of every radius `ρ < d / 2`.

The wedge assignment at a child gives each child wedge the old identifier of
the parent wedge containing it when the child wedge lies outside the removal
square, and the replacement run of that parent wedge when it lies inside.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 393–417, and
`geometry:repair-induction`, lines 497–514.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Written from the manuscript; no upstream Lean text is reused.
-/

noncomputable section

open scoped Topology

namespace TNLean.PEPS.AreaLaw.Geometry

theorem norm_repairFanStart (s : RepairFanSlot) : ‖repairFanStart s‖ = 1 := by
  have h : repairFanStart s ∈ repairFanCone s := by
    refine ⟨?_, ?_⟩ <;> simp only [repairCross]
    · nlinarith
    · have := repairCross_start_direction s
      simp only [repairCross] at this
      linarith
  rw [norm_eq_of_mem_repairFanCone h, repairCross_start_direction]
  simp [repairCross, mul_comm]

theorem norm_repairFanDirection (s : RepairFanSlot) : ‖repairFanDirection s‖ = 1 := by
  rw [← repairFanStart_next]
  exact norm_repairFanStart _

/-- A point of a closed triangle in an open set is a limit of interior points
of the triangle in that set.
Auxiliary to area-law Section 11, lines 340–348. -/
theorem mem_closure_interior_triangle_inter {c x : ℝ × ℝ} {r : ℝ} {s : RepairFanSlot}
    {N : Set (ℝ × ℝ)} (hr : 0 < r) (hN : IsOpen N) (hxN : x ∈ N)
    (hx : x - c ∈ repairFanCone s) (hxr : ‖x - c‖ ≤ r) :
    x ∈ closure ({z | z - c ∈ repairFanOpenCone s ∧ ‖z - c‖ < r} ∩ N) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hN x hxN
  set q : ℝ × ℝ := c + (r / 4) • (repairFanStart s + repairFanDirection s)
  have hq : ‖q - c‖ ≤ r / 2 := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by positivity)]
    have := norm_add_le (repairFanStart s) (repairFanDirection s)
    rw [norm_repairFanStart, norm_repairFanDirection] at this
    nlinarith
  set t := min 1 (min ε δ / (2 * (‖q - x‖ + 1)))
  have hpos : 0 < min ε δ := lt_min hε hδ
  have ht : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have hdist : dist x (x + t • (q - x)) < min ε δ := by
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg ht.le]
    have : t ≤ min ε δ / (2 * (‖q - x‖ + 1)) := min_le_right _ _
    calc t * ‖q - x‖ ≤ t * (‖q - x‖ + 1) := by nlinarith [norm_nonneg (q - x)]
      _ ≤ min ε δ / (2 * (‖q - x‖ + 1)) * (‖q - x‖ + 1) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = min ε δ / 2 := by field_simp
      _ < min ε δ := by linarith
  refine ⟨x + t • (q - x), ⟨⟨?_, ?_⟩, hball ?_⟩, hdist.trans_le (min_le_left _ _)⟩
  · have h1 := repairCross_start_direction s
    obtain ⟨hx₁, hx₂⟩ := hx
    have e : x + t • (q - x) - c = (1 - t) • (x - c) +
        (t * (r / 4)) • (repairFanStart s + repairFanDirection s) := by
      simp only [q]
      ext <;> simp <;> ring
    rw [e]
    simp only [repairFanOpenCone, Set.mem_ofPred_eq]
    simp only [repairCross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at h1 hx₁ hx₂ ⊢
    have h1t : 0 ≤ 1 - t := by linarith
    have hrt : 0 < t * (r / 4) := by positivity
    constructor <;> nlinarith [mul_nonneg h1t hx₁, mul_nonneg h1t hx₂]
  · have e : x + t • (q - x) - c = (1 - t) • (x - c) + t • (q - c) := by
      ext <;> simp <;> ring
    rw [e]
    calc ‖(1 - t) • (x - c) + t • (q - c)‖ ≤ ‖(1 - t) • (x - c)‖ + ‖t • (q - c)‖ :=
          norm_add_le _ _
      _ = (1 - t) * ‖x - c‖ + t * ‖q - c‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
            Real.norm_of_nonneg ht.le]
      _ ≤ (1 - t) * r + t * (r / 2) := by
          gcongr
      _ < r := by nlinarith
  · rw [Metric.mem_ball, dist_comm]
    exact hdist.trans_le (min_le_right _ _)

/-- Closures agree on an open set where the sets agree.
Auxiliary to area-law Section 11, lines 497–514. -/
theorem closure_inter_eq_of_inter_eq {A B N : Set (ℝ × ℝ)} (hN : IsOpen N)
    (h : A ∩ N = B ∩ N) : closure A ∩ N = closure B ∩ N := by
  have key : ∀ {A B : Set (ℝ × ℝ)}, A ∩ N = B ∩ N → closure A ∩ N ⊆ closure B ∩ N := by
    intro A B h x ⟨hx, hxN⟩
    refine ⟨?_, hxN⟩
    have := hN.closure_inter ⟨hx, hxN⟩
    rw [h] at this
    exact closure_mono Set.inter_subset_left this
  exact le_antisymm (key h) (key h.symm)

section Child

variable {ι : Type*}

/-- The parent wedge containing a child wedge.
Source: area-law Section 11, `geometry:repair-induction`, lines 497–514. -/
def repairChildSlotParent (e : Fin 3 × Fin 3) (t : RepairFanSlot) : RepairFanSlot :=
  repairSlotOfCode (repairChildParentCode e (repairSlotCode t))

/-- Whether a child wedge lies inside the removal square of its parent.
Source: area-law Section 11, `geometry:repair-induction`, lines 497–514. -/
def repairChildSlotInside (e : Fin 3 × Fin 3) (t : RepairFanSlot) : Bool :=
  repairChildInside e (repairSlotCode t)

/-- The replacement run containing a wedge.
Source: area-law Section 11, lines 404–417. -/
def repairFanRunOf (ξ : ι → Fin 2) (σ : RepairFanSlot → ι) (s : RepairFanSlot) :
    RepairFanRun ξ σ :=
  (cellFanRunGraph (-1, -1) 1 (0, 0) repairFanSplit
    (repairExteriorColor ξ σ)).connectedComponentMk s

/-- The wedge assignment at a child: the old identifier of the parent wedge
outside the removal square, and the replacement run of the parent wedge
inside it.
Source: area-law Section 11, `geometry:repair-induction`, lines 497–514. -/
def repairChildAssignment {κ : Type*} (ξ : ι → Fin 2) (σ : RepairFanSlot → ι)
    (old : ι → κ) (fresh : RepairFanRun ξ σ → κ) (e : Fin 3 × Fin 3) :
    RepairFanSlot → κ := fun t ↦
  if repairChildSlotInside e t then fresh (repairFanRunOf ξ σ (repairChildSlotParent e t))
  else old (σ (repairChildSlotParent e t))

/-- The child-wedge facts in slot form, for a point `x` of the open square of
half-side `d / 2` about the child `v + d e`.
Source: area-law Section 11, `geometry:repair-induction`, lines 497–514. -/
theorem repairChild_facts {v x : ℝ × ℝ} {d : ℝ} (hd : 0 < d) (e : Fin 3 × Fin 3)
    (hx : x ∈ Metric.ball (v + d • repairChildOffset e) (d / 2)) (t : RepairFanSlot) :
    (x - (v + d • repairChildOffset e) ∈ repairFanCone t →
      x - v ∈ repairFanCone (repairChildSlotParent e t)) ∧
    (x - (v + d • repairChildOffset e) ∈ repairFanOpenCone t →
      x - v ∈ repairFanOpenCone (repairChildSlotParent e t)) ∧
    (repairChildSlotInside e t = true →
      x - (v + d • repairChildOffset e) ∈ repairFanCone t → ‖x - v‖ ≤ d) ∧
    (repairChildSlotInside e t = true →
      x - (v + d • repairChildOffset e) ∈ repairFanOpenCone t → ‖x - v‖ < d) ∧
    (repairChildSlotInside e t = false →
      x - (v + d • repairChildOffset e) ∈ repairFanCone t → ¬‖x - v‖ < d) ∧
    (repairChildSlotInside e t = false →
      x - (v + d • repairChildOffset e) ∈ repairFanOpenCone t → ¬‖x - v‖ ≤ d) := by
  have hy : ‖x - v - d • repairChildOffset e‖ < d / 2 := by
    rw [sub_sub, ← dist_eq_norm]
    exact hx
  have h := isRepairChildConeCompatible_holds e ⟨repairSlotCode t, repairSlotCode_lt t⟩ hd
    (x - v) hy
  simp only [IsRepairChildConeCompatible, repairSlotOfCode_code, sub_sub] at h
  exact h

variable {v : ℝ × ℝ} {d : ℝ} {e : Fin 3 × Fin 3}

/-- A point of the child square outside the removal square, in a parent cone,
lies in an outer child cone of that parent wedge.
Source: area-law Section 11, `geometry:repair-induction`, lines 497–514. -/
theorem exists_outer_child_cone (hd : 0 < d) {x : ℝ × ℝ}
    (hx : x ∈ Metric.ball (v + d • repairChildOffset e) (d / 2)) (hxd : d < ‖x - v‖)
    {s : RepairFanSlot} (hs : x - v ∈ repairFanCone s) :
    ∃ t, repairChildSlotInside e t = false ∧ repairChildSlotParent e t = s ∧
      x - (v + d • repairChildOffset e) ∈ repairFanCone t := by
  set c := v + d • repairChildOffset e
  set O := Metric.ball c (d / 2) ∩ (Metric.closedBall v d)ᶜ
  have hO : IsOpen O := Metric.isOpen_ball.inter Metric.isClosed_closedBall.isOpen_compl
  have hxO : x ∈ O := ⟨hx, by simpa [dist_eq_norm] using hxd⟩
  have hcl := mem_closure_openCone_inter hO hxO hs
  set F := ⋃ t : {t : RepairFanSlot // repairChildSlotInside e t = false ∧
    repairChildSlotParent e t = s}, {z : ℝ × ℝ | z - c ∈ repairFanCone t.val}
  have hF : IsClosed F := isClosed_iUnion_of_finite fun t ↦ isClosed_repairFanCone_at c t.val
  have hsub : {z | z - v ∈ repairFanOpenCone s} ∩ O ⊆ F := by
    rintro z ⟨hzs, hzO, hzQ⟩
    obtain ⟨t, ht⟩ := exists_mem_repairFanCone (z - c)
    have hf := repairChild_facts hd e hzO t
    have hp : s = repairChildSlotParent e t :=
      eq_of_mem_repairFanOpenCone_of_mem_repairFanCone hzs (hf.1 ht)
    have hin : repairChildSlotInside e t = false := by
      by_contra hne
      rw [Bool.not_eq_false] at hne
      exact hzQ (by simpa [dist_eq_norm] using hf.2.2.1 hne ht)
    exact Set.mem_iUnion.mpr ⟨⟨t, hin, hp.symm⟩, ht⟩
  obtain ⟨⟨t, hin, hp⟩, ht⟩ := Set.mem_iUnion.mp (hF.closure_subset_iff.mpr hsub hcl)
  exact ⟨t, hin, hp, ht⟩

/-- A point of the child square in the removal square, in a parent cone, lies
in an inner child cone of that parent wedge.
Source: area-law Section 11, `geometry:repair-induction`, lines 497–514. -/
theorem exists_inner_child_cone (hd : 0 < d) {x : ℝ × ℝ}
    (hx : x ∈ Metric.ball (v + d • repairChildOffset e) (d / 2)) (hxd : ‖x - v‖ ≤ d)
    {s : RepairFanSlot} (hs : x - v ∈ repairFanCone s) :
    ∃ t, repairChildSlotInside e t = true ∧ repairChildSlotParent e t = s ∧
      x - (v + d • repairChildOffset e) ∈ repairFanCone t := by
  set c := v + d • repairChildOffset e
  have hcl := mem_closure_interior_triangle_inter hd Metric.isOpen_ball hx hs hxd
  set F := ⋃ t : {t : RepairFanSlot // repairChildSlotInside e t = true ∧
    repairChildSlotParent e t = s}, {z : ℝ × ℝ | z - c ∈ repairFanCone t.val}
  have hF : IsClosed F := isClosed_iUnion_of_finite fun t ↦ isClosed_repairFanCone_at c t.val
  have hsub : {z | z - v ∈ repairFanOpenCone s ∧ ‖z - v‖ < d} ∩ Metric.ball c (d / 2) ⊆ F := by
    rintro z ⟨⟨hzs, hzd⟩, hzN⟩
    obtain ⟨t, ht⟩ := exists_mem_repairFanCone (z - c)
    have hf := repairChild_facts hd e hzN t
    have hp : s = repairChildSlotParent e t :=
      eq_of_mem_repairFanOpenCone_of_mem_repairFanCone hzs (hf.1 ht)
    have hin : repairChildSlotInside e t = true := by
      by_contra hne
      rw [Bool.not_eq_true] at hne
      exact hf.2.2.2.2.1 hne ht hzd
    exact Set.mem_iUnion.mpr ⟨⟨t, hin, hp.symm⟩, ht⟩
  obtain ⟨⟨t, hin, hp⟩, ht⟩ := Set.mem_iUnion.mp (hF.closure_subset_iff.mpr hsub hcl)
  exact ⟨t, hin, hp, ht⟩

/-- A point of the child square not inside the open removal square lies in an
outer child cone.
Source: area-law Section 11, `geometry:repair-induction`, lines 497–514. -/
theorem exists_outer_child_cone_of_le (hd : 0 < d) {x : ℝ × ℝ}
    (hx : x ∈ Metric.ball (v + d • repairChildOffset e) (d / 2)) (hxd : d ≤ ‖x - v‖) :
    ∃ t, repairChildSlotInside e t = false ∧
      x - (v + d • repairChildOffset e) ∈ repairFanCone t := by
  set c := v + d • repairChildOffset e
  have hxv : x - v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hxd
    linarith
  set F := ⋃ t : {t : RepairFanSlot // repairChildSlotInside e t = false},
    {z : ℝ × ℝ | z - c ∈ repairFanCone t.val}
  have hF : IsClosed F := isClosed_iUnion_of_finite fun t ↦ isClosed_repairFanCone_at c t.val
  have hcl : x ∈ closure (Metric.ball c (d / 2) ∩ (Metric.closedBall v d)ᶜ) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball x hx
    set t := min ε δ / (2 * (‖x - v‖ + 1))
    have hpos : 0 < min ε δ := lt_min hε hδ
    have ht : 0 < t := by positivity
    have hdist : dist x (x + t • (x - v)) < min ε δ := by
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg ht.le]
      calc t * ‖x - v‖ ≤ t * (‖x - v‖ + 1) := by nlinarith [norm_nonneg (x - v)]
        _ = min ε δ / 2 := by simp only [t]; field_simp
        _ < min ε δ := by linarith
    refine ⟨x + t • (x - v), ⟨hball ?_, ?_⟩, hdist.trans_le (min_le_left _ _)⟩
    · rw [Metric.mem_ball, dist_comm]
      exact hdist.trans_le (min_le_right _ _)
    · simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, not_le]
      have : x + t • (x - v) - v = (1 + t) • (x - v) := by
        ext <;> simp <;> ring
      rw [this, norm_smul, Real.norm_of_nonneg (by linarith)]
      nlinarith [norm_pos_iff.mpr hxv]
  have hsub : Metric.ball c (d / 2) ∩ (Metric.closedBall v d)ᶜ ⊆ F := by
    rintro z ⟨hzN, hzQ⟩
    obtain ⟨t, ht⟩ := exists_mem_repairFanCone (z - c)
    have hf := repairChild_facts hd e hzN t
    have hin : repairChildSlotInside e t = false := by
      by_contra hne
      rw [Bool.not_eq_false] at hne
      exact hzQ (by simpa [dist_eq_norm] using hf.2.2.1 hne ht)
    exact Set.mem_iUnion.mpr ⟨⟨t, hin⟩, ht⟩
  obtain ⟨⟨t, hin⟩, ht⟩ := Set.mem_iUnion.mp (hF.closure_subset_iff.mpr hsub hcl)
  exact ⟨t, hin, ht⟩

end Child

end TNLean.PEPS.AreaLaw.Geometry
