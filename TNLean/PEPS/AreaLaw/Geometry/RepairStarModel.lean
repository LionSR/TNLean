/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairFanCones

/-!
# Isolated stars from a local radial model

Let `τ` assign identifiers to the eight wedges about a point `c`. The closed
sector of an identifier `i` is the union of the closed cones at `c` of the
wedges assigned `i`, and the active rays are the rays from `c` between
consecutive wedges with different identifiers.

A labelled region family has an isolated star of radius `ρ` about `c` as soon
as, in an open square of a larger radius about `c`, the closure of each region
is its closed sector and each region contains its closed sector with the
active rays removed, provided consecutive wedges have equal labels exactly
when they have equal identifiers. Conversely, an isolated star gives this
local model in the open square of its radius.

The proofs only use that two closed cones meet in the origin or in a common
ray, that open cones meet no other cone, and that closed cones are limits of
their open cones.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 340–349, and
`geometry:repair-induction`, lines 497–514.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Written from the manuscript; no upstream Lean text is reused.
-/

noncomputable section

open scoped Topology

namespace TNLean.PEPS.AreaLaw.Geometry

variable {ι : Type*}

/-- The closed sector about `c` of the identifier `i` under the wedge
assignment `τ`. Source: area-law Section 11, lines 341–345. -/
def repairSectorSet (τ : RepairFanSlot → ι) (c : ℝ × ℝ) (i : ι) : Set (ℝ × ℝ) :=
  {x | ∃ s, τ s = i ∧ x - c ∈ repairFanCone s}

/-- The active rays about `c` of the wedge assignment `τ`: the rays between
consecutive wedges with different identifiers.
Source: area-law Section 11, lines 341–348. -/
def repairActiveRaySet (τ : RepairFanSlot → ι) (c : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x | ∃ s, τ s ≠ τ (cellFanNext s) ∧ SameRay ℝ (x - c) (repairFanDirection s)}

theorem isClosed_repairFanCone_at (c : ℝ × ℝ) (s : RepairFanSlot) :
    IsClosed {x : ℝ × ℝ | x - c ∈ repairFanCone s} := by
  have hc₁ : Continuous fun x : ℝ × ℝ ↦ repairCross (repairFanStart s) (x - c) := by
    unfold repairCross; fun_prop
  have hc₂ : Continuous fun x : ℝ × ℝ ↦ repairCross (x - c) (repairFanDirection s) := by
    unfold repairCross; fun_prop
  exact (isClosed_le continuous_const hc₁).inter (isClosed_le continuous_const hc₂)

theorem isClosed_repairSectorSet (τ : RepairFanSlot → ι) (c : ℝ × ℝ) (i : ι) :
    IsClosed (repairSectorSet τ c i) := by
  have : repairSectorSet τ c i =
      ⋃ s : {s : RepairFanSlot // τ s = i}, {x | x - c ∈ repairFanCone s.val} := by
    ext x
    simp [repairSectorSet]
  rw [this]
  exact isClosed_iUnion_of_finite fun s ↦ isClosed_repairFanCone_at c s.val

theorem isClosed_repairActiveRaySet (τ : RepairFanSlot → ι) (c : ℝ × ℝ) :
    IsClosed (repairActiveRaySet τ c) := by
  have : repairActiveRaySet τ c =
      ⋃ s : {s : RepairFanSlot // τ s ≠ τ (cellFanNext s)},
        {x | SameRay ℝ (x - c) (repairFanDirection s.val)} := by
    ext x
    simp [repairActiveRaySet]
  rw [this]
  exact isClosed_iUnion_of_finite fun s ↦ isClosed_setOf_sameRay_direction c s.val

/-- The `k`-fold perimeter successor of a slot.
Auxiliary to area-law Section 11, lines 341–345. -/
def repairNextIter : ℕ → RepairFanSlot → RepairFanSlot
  | 0, s => s
  | k + 1, s => cellFanNext (repairNextIter k s)

/-- Iterating the perimeter successor reaches every slot.
Auxiliary to area-law Section 11, lines 341–345. -/
theorem exists_repairNextIter_eq (s u : RepairFanSlot) :
    ∃ k : ℕ, repairNextIter k s = u := by
  have hcode : ∀ k : ℕ, repairSlotCode (repairNextIter k s) = (repairSlotCode s + k) % 8 := by
    intro k
    induction k with
    | zero => simp [repairNextIter, Nat.mod_eq_of_lt (repairSlotCode_lt s)]
    | succ k ih =>
      simp only [repairNextIter]
      rw [repairSlotCode_next, ih]
      omega
  refine ⟨(repairSlotCode u + 8 - repairSlotCode s) % 8, repairSlotCode_injective ?_⟩
  rw [hcode]
  have := repairSlotCode_lt s
  have := repairSlotCode_lt u
  omega

/-- An assignment that is constant along every perimeter step is constant.
Auxiliary to area-law Section 11, lines 344–345. -/
theorem eq_of_forall_eq_next {τ : RepairFanSlot → ι} (h : ∀ s, τ s = τ (cellFanNext s))
    (s u : RepairFanSlot) : τ s = τ u := by
  obtain ⟨k, rfl⟩ := exists_repairNextIter_eq s u
  induction k with
  | zero => rfl
  | succ k ih => exact ih.trans (h _)

/-- A nonconstant assignment has an active ray, and the center lies on it.
Auxiliary to area-law Section 11, lines 341–345. -/
theorem center_mem_repairActiveRaySet {τ : RepairFanSlot → ι} {s u : RepairFanSlot}
    (h : τ s ≠ τ u) (c : ℝ × ℝ) : c ∈ repairActiveRaySet τ c := by
  by_contra hc
  apply h
  apply eq_of_forall_eq_next
  intro t
  by_contra ht
  exact hc ⟨t, ht, by simp⟩

/-- A common point of two closed cones at `c` whose wedges carry different
identifiers lies on an active ray.
Auxiliary to area-law Section 11, lines 341–345 and 497–504. -/
theorem mem_repairActiveRaySet_of_mem_two {τ : RepairFanSlot → ι} {c x : ℝ × ℝ}
    {s u : RepairFanSlot} (hs : x - c ∈ repairFanCone s) (hu : x - c ∈ repairFanCone u)
    (h : τ s ≠ τ u) : x ∈ repairActiveRaySet τ c := by
  have hsu : s ≠ u := fun e ↦ h (e ▸ rfl)
  by_cases h₁ : u = cellFanNext s
  · subst h₁
    exact ⟨s, h, (mem_repairFanCone_inter_next_iff s _).mp ⟨hs, hu⟩⟩
  by_cases h₂ : s = cellFanNext u
  · subst h₂
    exact ⟨u, fun e ↦ h e.symm, (mem_repairFanCone_inter_next_iff u _).mp ⟨hu, hs⟩⟩
  have hx : x - c = 0 := eq_zero_of_mem_repairFanCone hsu h₁ h₂ hs hu
  rw [sub_eq_zero] at hx
  subst hx
  exact center_mem_repairActiveRaySet h x

/-- A closed sector with the active rays removed is open.
Auxiliary to area-law Section 11, lines 341–348. -/
theorem isOpen_repairSectorSet_diff (τ : RepairFanSlot → ι) (c : ℝ × ℝ) (i : ι) :
    IsOpen (repairSectorSet τ c i \ repairActiveRaySet τ c) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨⟨s, hs, hx⟩, hxa⟩
  have h₁ : ∀ᶠ z in 𝓝 x, z ∉ repairActiveRaySet τ c :=
    (isClosed_repairActiveRaySet τ c).isOpen_compl.mem_nhds hxa
  have h₂ : ∀ᶠ z in 𝓝 x, ∀ u : RepairFanSlot, x - c ∉ repairFanCone u →
      z - c ∉ repairFanCone u := by
    rw [Filter.eventually_all]
    intro u
    by_cases hu : x - c ∈ repairFanCone u
    · exact Filter.Eventually.of_forall fun _ h ↦ absurd hu h
    · filter_upwards [(isClosed_repairFanCone_at c u).isOpen_compl.mem_nhds hu] with z hz
      exact fun _ ↦ hz
  filter_upwards [h₁, h₂] with z hz₁ hz₂
  refine ⟨?_, hz₁⟩
  obtain ⟨u, hu⟩ := exists_mem_repairFanCone (z - c)
  have hxu : x - c ∈ repairFanCone u := by
    by_contra h
    exact hz₂ u h hu
  refine ⟨u, ?_, hu⟩
  by_contra hne
  exact hxa (mem_repairActiveRaySet_of_mem_two hx hxu fun e ↦ hne (e.symm.trans hs))

theorem mem_repairSectorSet_self (τ : RepairFanSlot → ι) {c x : ℝ × ℝ} {s : RepairFanSlot}
    (hx : x - c ∈ repairFanCone s) : x ∈ repairSectorSet τ c (τ s) :=
  ⟨s, rfl, hx⟩

/-- **Isolated star from a local radial model.** Suppose that in the open
square of radius `ρ' > ρ` about `c`, each region has closure equal to its
closed sector, each region contains its closed sector minus the active rays,
and consecutive wedges have equal labels exactly when they have equal
identifiers. Then the closed square of radius `ρ` is an isolated star.
Source: area-law Section 11, `geometry:initial-stars`, lines 340–349, and
`geometry:repair-induction`, lines 506–514. -/
theorem isIsolatedStar_of_model {R : ι → Set (ℝ × ℝ)} {ξ : ι → Fin 2} {c : ℝ × ℝ}
    {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ') (τ : RepairFanSlot → ι)
    (hcl : ∀ i, closure (R i) ∩ Metric.ball c ρ' = repairSectorSet τ c i ∩ Metric.ball c ρ')
    (hmem : ∀ i, (repairSectorSet τ c i \ repairActiveRaySet τ c) ∩ Metric.ball c ρ' ⊆ R i)
    (hcol : ∀ s, ξ (τ s) = ξ (τ (cellFanNext s)) ↔ τ s = τ (cellFanNext s)) :
    IsIsolatedStar R ξ c ρ := by
  have hint : ∀ i, (repairSectorSet τ c i \ repairActiveRaySet τ c) ∩ Metric.ball c ρ' ⊆
      interior (R i) := fun i ↦
    interior_maximal (hmem i) ((isOpen_repairSectorSet_diff τ c i).inter Metric.isOpen_ball)
  have hball : Metric.closedBall c ρ ⊆ Metric.ball c ρ' := Metric.closedBall_subset_ball hρρ'
  refine ⟨τ, fun s ↦ ?_, fun i ↦ ?_, fun x hx ↦ ?_, hcol, fun hn ↦ ?_⟩
  · intro z hz
    rw [interior_repairCurrentFanTriangle hρ] at hz
    obtain ⟨hzc, hzn⟩ := hz
    refine hmem _ ⟨⟨mem_repairSectorSet_self τ (repairFanOpenCone_subset s hzc), ?_⟩, ?_⟩
    · rintro ⟨t, -, ht⟩
      exact not_sameRay_of_mem_repairFanOpenCone hzc ht
    · rw [Metric.mem_ball, dist_eq_norm]
      linarith
  · have : closure (R i) ∩ Metric.closedBall c ρ =
        repairSectorSet τ c i ∩ Metric.closedBall c ρ := by
      rw [← Set.inter_eq_right.mpr hball, ← Set.inter_assoc, hcl i, Set.inter_assoc]
    rw [this]
    ext x
    simp only [repairSectorSet, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion,
      Metric.mem_closedBall, dist_eq_norm, mem_repairCurrentFanTriangle_iff hρ,
      Subtype.exists, exists_prop]
    constructor
    · rintro ⟨⟨s, hs, hx⟩, hn⟩
      exact ⟨s, hs, hx, hn⟩
    · rintro ⟨s, hs, hx, hn⟩
      exact ⟨⟨s, hs, hx⟩, hn⟩
  · have hxb := hball hx
    constructor
    · rintro ⟨i, hi⟩
      by_contra hxa
      have hxcl : x ∈ closure (R i) := frontier_subset_closure hi
      have : x ∈ repairSectorSet τ c i := ((hcl i).subset ⟨hxcl, hxb⟩).1
      exact hi.2 (hint i ⟨⟨this, hxa⟩, hxb⟩)
    · rintro ⟨t, ht, hray⟩
      have hboth := (mem_repairFanCone_inter_next_iff t _).mpr hray
      refine ⟨τ t, ?_, ?_⟩
      · exact ((hcl (τ t)).symm.subset ⟨mem_repairSectorSet_self τ hboth.1, hxb⟩).1
      · intro hxi
        have hN : IsOpen (interior (R (τ t)) ∩ Metric.ball c ρ') :=
          isOpen_interior.inter Metric.isOpen_ball
        have hcl' := mem_closure_openCone_inter hN ⟨hxi, hxb⟩ hboth.2
        obtain ⟨z, hz, hzN⟩ := closure_nonempty_iff.mp ⟨x, hcl'⟩
        have hzR : z ∈ closure (R (τ t)) := subset_closure (interior_subset hzN.1)
        obtain ⟨⟨u, hu, hzu⟩, -⟩ := (hcl (τ t)).subset ⟨hzR, hzN.2⟩
        have := eq_of_mem_repairFanOpenCone_of_mem_repairFanCone hz hzu
        subst this
        exact ht hu.symm
  · have hconst := eq_of_forall_eq_next hn
    set s₀ : RepairFanSlot := ⟨0, 0⟩
    refine ⟨τ s₀, fun x hx ↦ hmem (τ s₀) ⟨⟨?_, ?_⟩, hball hx⟩⟩
    · obtain ⟨u, hu⟩ := exists_mem_repairFanCone (x - c)
      exact ⟨u, hconst u s₀, hu⟩
    · rintro ⟨t, ht, -⟩
      exact ht (hn t)

/-- **Local radial model of an isolated star.** In the open square of its
radius, an isolated star has closures equal to the closed sectors, and each
closed sector minus the active rays lies in the interior of its region.
Source: area-law Section 11, `geometry:initial-stars`, lines 340–349. -/
theorem IsIsolatedStar.exists_model {R : ι → Set (ℝ × ℝ)} {ξ : ι → Fin 2} {c : ℝ × ℝ}
    {ρ : ℝ} (h : IsIsolatedStar R ξ c ρ) (hρ : 0 < ρ) :
    ∃ σ : RepairFanSlot → ι,
      (∀ i, closure (R i) ∩ Metric.ball c ρ = repairSectorSet σ c i ∩ Metric.ball c ρ) ∧
      (∀ i, (repairSectorSet σ c i \ repairActiveRaySet σ c) ∩ Metric.ball c ρ ⊆
        interior (R i)) ∧
      (∀ s, ξ (σ s) = ξ (σ (cellFanNext s)) ↔ σ s = σ (cellFanNext s)) ∧
      (∀ s, interior (repairCurrentFanTriangle c ρ s) ⊆ R (σ s)) := by
  obtain ⟨σ, hsub, hdecomp, hfront, hcolor, -⟩ := h
  have hball : Metric.ball c ρ ⊆ Metric.closedBall c ρ := Metric.ball_subset_closedBall
  have hcl : ∀ i, closure (R i) ∩ Metric.ball c ρ = repairSectorSet σ c i ∩ Metric.ball c ρ := by
    intro i
    ext x
    constructor
    · rintro ⟨hxcl, hxb⟩
      have hx := (hdecomp i).subset ⟨hxcl, hball hxb⟩
      obtain ⟨⟨s, hs⟩, hxs⟩ := Set.mem_iUnion.mp hx
      exact ⟨⟨s, hs, ((mem_repairCurrentFanTriangle_iff hρ s x).mp hxs).1⟩, hxb⟩
    · rintro ⟨⟨s, hs, hx⟩, hxb⟩
      have hn : ‖x - c‖ ≤ ρ := by
        rw [← dist_eq_norm]
        exact (Metric.mem_ball.mp hxb).le
      have hU : x ∈ ⋃ s : {s : RepairFanSlot // σ s = i}, repairCurrentFanTriangle c ρ s.val :=
        Set.mem_iUnion.mpr ⟨⟨s, hs⟩, (mem_repairCurrentFanTriangle_iff hρ s x).mpr ⟨hx, hn⟩⟩
      exact ⟨((hdecomp i).symm.subset hU).1, hxb⟩
  refine ⟨σ, hcl, fun i x ⟨⟨hxs, hxa⟩, hxb⟩ ↦ ?_, hcolor, hsub⟩
  have hxcl : x ∈ closure (R i) := ((hcl i).symm.subset ⟨hxs, hxb⟩).1
  by_contra hxi
  exact hxa ((hfront x (hball hxb)).mp ⟨i, hxcl, hxi⟩)

end TNLean.PEPS.AreaLaw.Geometry
