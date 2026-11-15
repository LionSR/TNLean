/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.IntegerCellExteriorCollar
import TNLean.PEPS.TorusDualPhysicalAvoidance
import TNLean.PEPS.TorusNativeFluxHolonomy
import Mathlib.Tactic.Tauto

/-!
# Flux transport on the genuine exterior integer collar

Every safe exterior collar edge has an adjacent dual plaquette with an observed
corner. A native dual path avoiding all such forbidden plaquettes therefore
crosses no collar edge. Its actual group-valued transport on that edge is the
identity, without centrality. This is local geometry for the exterior-block
argument in SCP10, arXiv:1001.3807v3, Theorem 6.9 and Lemma 6.14,
lines 1935–1990 and 2199–2214. See
`docs/paper-gaps/scp10_untwisted_flux_boundary.tex`.
-/

noncomputable section
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
local instance collarAvoidanceQuiver : Quiver X := torusDualQuiver width height
local instance collarAvoidanceWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance collarAvoidanceHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩

private def intVertex (a : ℤ × ℤ) : X := ((a.1 : ZMod width), (a.2 : ZMod height))

private theorem step_zero (R : Finset X) {a b : X} (e : TorusDualStep a b)
    (ha : a ∉ torusIncidentDualPlaquettes R) (hb : b ∉ torusIncidentDualPlaquettes R)
    (v : X) :
    ((v ∈ torusIncidentDualPlaquettes R ∨ (v.1, v.2 - 1) ∈ torusIncidentDualPlaquettes R) →
      e.crossings.1 v = 0) ∧
    ((v ∈ torusIncidentDualPlaquettes R ∨ (v.1 - 1, v.2) ∈ torusIncidentDualPlaquettes R) →
      e.crossings.2 v = 0) := by
  cases e with
  | east x y =>
    refine ⟨fun _ => rfl, ?_⟩
    intro hv
    have hne : v ≠ (x + 1, y) := by
      rintro rfl
      rcases hv with hv | hv
      · exact hb hv
      · exact ha (by simpa only [add_sub_cancel_right] using hv)
    simp [TorusDualStep.crossings, torusPointMass, hne]
  | west x y =>
    refine ⟨fun _ => rfl, ?_⟩
    intro hv
    have hne : v ≠ (x + 1, y) := by
      rintro rfl
      rcases hv with hv | hv
      · exact ha hv
      · exact hb (by simpa only [add_sub_cancel_right] using hv)
    simp [TorusDualStep.crossings, torusPointMass, hne]
  | north x y =>
    refine ⟨?_, fun _ => rfl⟩
    intro hv
    have hne : v ≠ (x, y + 1) := by
      rintro rfl
      rcases hv with hv | hv
      · exact hb hv
      · exact ha (by simpa only [add_sub_cancel_right] using hv)
    simp [TorusDualStep.crossings, torusPointMass, hne]
  | south x y =>
    refine ⟨?_, fun _ => rfl⟩
    intro hv
    have hne : v ≠ (x, y + 1) := by
      rintro rfl
      rcases hv with hv | hv
      · exact ha hv
      · exact hb (by simpa only [add_sub_cancel_right] using hv)
    simp [TorusDualStep.crossings, torusPointMass, hne]

private theorem path_zero (R : Finset X) {a b : X} (p : TorusDualPath a b)
    (h : ∀ v ∈ (torusDualPathGraphWalk p).support, v ∉ torusIncidentDualPlaquettes R) :
    ∀ v : X,
      ((v ∈ torusIncidentDualPlaquettes R ∨
        (v.1, v.2 - 1) ∈ torusIncidentDualPlaquettes R) →
        (torusDualPathCrossings p).1 v = 0) ∧
      ((v ∈ torusIncidentDualPlaquettes R ∨
        (v.1 - 1, v.2) ∈ torusIncidentDualPlaquettes R) →
        (torusDualPathCrossings p).2 v = 0) := by
  revert h
  induction p with
  | nil => intro _ v; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | @cons b c p e ih =>
    intro h v
    have hp : ∀ w ∈ (torusDualPathGraphWalk p).support,
        w ∉ torusIncidentDualPlaquettes R := by
      intro w hw
      apply h w
      simp only [torusDualPathGraphWalk, SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl hw
    have hb := hp b (torusDualPathGraphWalk p).end_mem_support
    have hc := h c (torusDualPathGraphWalk (p.cons e)).end_mem_support
    obtain ⟨hph, hpv⟩ := ih hp v
    obtain ⟨heh, hev⟩ := step_zero R e hb hc v
    constructor
    · intro hv
      change (torusDualPathCrossings p).1 v + e.crossings.1 v = 0
      rw [hph hv, heh hv, zero_add]
    · intro hv
      change (torusDualPathCrossings p).2 v + e.crossings.2 v = 0
      rw [hpv hv, hev hv, zero_add]

private theorem near_horizontal (q a : ℤ × ℤ)
    (hq : IsIntegerCellNear q a) (hr : IsIntegerCellNear (q + (1, 0)) a)
    (haq : a ≠ q) (har : a ≠ q + (1, 0)) :
    (a.1 = q.1 ∨ a.1 = q.1 + 1) ∧ (a.2 = q.2 - 1 ∨ a.2 = q.2 + 1) := by
  obtain ⟨hx, hy⟩ := hq
  obtain ⟨hx', hy'⟩ := hr
  have hne : ¬ (a.1 = q.1 ∧ a.2 = q.2) := fun h => haq (Prod.ext h.1 h.2)
  have hne' : ¬ (a.1 = q.1 + 1 ∧ a.2 = q.2) :=
    fun h => har (Prod.ext (by simpa using h.1) (by simpa using h.2))
  simp only [Prod.fst_add, Prod.snd_add, add_zero] at hx' hy'
  have := abs_le.mp hx
  have := abs_le.mp hy
  have := abs_le.mp hx'
  have := abs_le.mp hy'
  constructor <;> omega

private theorem near_vertical (q a : ℤ × ℤ)
    (hq : IsIntegerCellNear q a) (hr : IsIntegerCellNear (q + (0, 1)) a)
    (haq : a ≠ q) (har : a ≠ q + (0, 1)) :
    (a.1 = q.1 - 1 ∨ a.1 = q.1 + 1) ∧ (a.2 = q.2 ∨ a.2 = q.2 + 1) := by
  obtain ⟨hx, hy⟩ := hq
  obtain ⟨hx', hy'⟩ := hr
  have hne : ¬ (a.1 = q.1 ∧ a.2 = q.2) := fun h => haq (Prod.ext h.1 h.2)
  have hne' : ¬ (a.1 = q.1 ∧ a.2 = q.2 + 1) :=
    fun h => har (Prod.ext (by simpa using h.1) (by simpa using h.2))
  simp only [Prod.fst_add, Prod.snd_add, add_zero] at hx' hy'
  have := abs_le.mp hx
  have := abs_le.mp hy
  have := abs_le.mp hx'
  have := abs_le.mp hy'
  constructor <;> omega

private theorem forbidden_horizontal (R : Finset X) (q a : ℤ × ℤ)
    (ha : intVertex a ∈ R)
    (hx : a.1 = q.1 ∨ a.1 = q.1 + 1) (hy : a.2 = q.2 - 1 ∨ a.2 = q.2 + 1) :
    intVertex q ∈ torusIncidentDualPlaquettes R ∨
      ((intVertex q).1, (intVertex q).2 - 1) ∈ torusIncidentDualPlaquettes R := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  all_goals
    have hm := ha
    simp [intVertex, hx, hy] at hm
    simp only [intVertex, torusIncidentDualPlaquettes, Finset.mem_filter,
      Finset.mem_univ, true_and, sub_add_cancel]
    tauto

private theorem forbidden_vertical (R : Finset X) (q a : ℤ × ℤ)
    (ha : intVertex a ∈ R)
    (hx : a.1 = q.1 - 1 ∨ a.1 = q.1 + 1) (hy : a.2 = q.2 ∨ a.2 = q.2 + 1) :
    intVertex q ∈ torusIncidentDualPlaquettes R ∨
      ((intVertex q).1 - 1, (intVertex q).2) ∈ torusIncidentDualPlaquettes R := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  all_goals
    have hm := ha
    simp [intVertex, hx, hy] at hm
    simp only [intVertex, torusIncidentDualPlaquettes, Finset.mem_filter,
      Finset.mem_univ, true_and, sub_add_cancel]
    tauto

variable {G : Type*} [Group G]

private theorem right_transport (R : Finset X) (A : Finset (ℤ × ℤ))
    (hA : ∀ a ∈ A, intVertex a ∈ R) {s t : X} (p : TorusDualPath s t)
    (hp : ∀ v ∈ (torusDualPathGraphWalk p).support, v ∉ torusIncidentDualPlaquettes R)
    (g : G) (q a : ℤ × ℤ) (ha : a ∈ A) (hq : q ∉ A) (hr : q + (1, 0) ∉ A)
    (hnq : IsIntegerCellNear q a) (hnr : IsIntegerCellNear (q + (1, 0)) a)
    (hΓ : (Γₜ).Adj (intVertex q) (intVertex (q + (1, 0)))) :
    regularDirectedTransport
      (torusGraphRegularLabels (torusDualFluxLabels g p).1
        (torusDualFluxLabels g p).2) hΓ = 1 := by
  obtain ⟨hx, hy⟩ := near_horizontal q a hnq hnr (fun h => hq (h ▸ ha))
    (fun h => hr (h ▸ ha))
  have hz := (path_zero R p hp (intVertex q)).1 (forbidden_horizontal R q a (hA a ha) hx hy)
  have hu : (torusDualFluxLabels g p).1 (intVertex q) = 1 := by
    simp only [torusDualFluxLabels, torusFluxPowerLabels, hz, zpow_zero]
  simp only [intVertex, Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_one,
    Int.cast_zero, add_zero] at hΓ ⊢
  change torusNativeRightTransport _ (intVertex q) = 1
  rw [torusNativeRightTransport_torusGraphRegularLabels, hu]

private theorem up_transport (R : Finset X) (A : Finset (ℤ × ℤ))
    (hA : ∀ a ∈ A, intVertex a ∈ R) {s t : X} (p : TorusDualPath s t)
    (hp : ∀ v ∈ (torusDualPathGraphWalk p).support, v ∉ torusIncidentDualPlaquettes R)
    (g : G) (q a : ℤ × ℤ) (ha : a ∈ A) (hq : q ∉ A) (hr : q + (0, 1) ∉ A)
    (hnq : IsIntegerCellNear q a) (hnr : IsIntegerCellNear (q + (0, 1)) a)
    (hΓ : (Γₜ).Adj (intVertex q) (intVertex (q + (0, 1)))) :
    regularDirectedTransport
      (torusGraphRegularLabels (torusDualFluxLabels g p).1
        (torusDualFluxLabels g p).2) hΓ = 1 := by
  obtain ⟨hx, hy⟩ := near_vertical q a hnq hnr (fun h => hq (h ▸ ha))
    (fun h => hr (h ▸ ha))
  have hz := (path_zero R p hp (intVertex q)).2 (forbidden_vertical R q a (hA a ha) hx hy)
  have hu : (torusDualFluxLabels g p).2 (intVertex q) = 1 := by
    simp only [torusDualFluxLabels, torusFluxPowerLabels, hz, zpow_zero]
  simp only [intVertex, Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_one,
    Int.cast_zero, add_zero] at hΓ ⊢
  change torusNativeUpTransport _ (intVertex q) = 1
  rw [torusNativeUpTransport_torusGraphRegularLabels, hu, inv_one]

/-- A native dual path avoiding every plaquette with an observed corner has
identity group transport on every edge of a genuine exterior integer collar.
No centrality, gauge or desired transport equality is supplied. Local geometry
for SCP10, Theorem 6.9 and Lemma 6.14. -/
theorem torusDualFlux_transport_eq_one_on_integerExteriorCollar
    (R : Finset X) (A : Finset (ℤ × ℤ))
    (hA : ∀ a ∈ A, ((a.1 : ZMod width), (a.2 : ZMod height)) ∈ R)
    {s t : X} (p : TorusDualPath s t)
    (hp : ∀ v ∈ (torusDualPathGraphWalk p).support, v ∉ torusIncidentDualPlaquettes R)
    (g : G) {q r : integerExteriorBand A} (h : (integerExteriorCollarGraph A).Adj q r)
    (hΓ : (Γₜ).Adj ((q.1.1 : ZMod width), (q.1.2 : ZMod height))
      ((r.1.1 : ZMod width), (r.1.2 : ZMod height))) :
    regularDirectedTransport
      (torusGraphRegularLabels (torusDualFluxLabels g p).1
        (torusDualFluxLabels g p).2) hΓ = 1 := by
  rcases q with ⟨q, hq⟩
  rcases r with ⟨r, hr⟩
  obtain ⟨hstep, a, ha, hnq, hnr⟩ := h
  obtain ⟨_, d, hd, he⟩ := (SimpleGraph.addCayley_adj' _ q r).mp hstep
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hd with rfl | rfl
  · rcases he with he | he
    · subst r
      exact right_transport R A hA p hp g q a ha hq.1 hr.1 hnq hnr hΓ
    · subst q
      have ht := right_transport R A hA p hp g r a ha hr.1 hq.1 hnr hnq hΓ.symm
      simpa only [ht, inv_one] using regularDirectedTransport_symm _ hΓ.symm
  · rcases he with he | he
    · subst r
      exact up_transport R A hA p hp g q a ha hq.1 hr.1 hnq hnr hΓ
    · subst q
      have ht := up_transport R A hA p hp g r a ha hr.1 hq.1 hnr hnq hΓ.symm
      simpa only [ht, inv_one] using regularDirectedTransport_symm _ hΓ.symm

end TNLean.PEPS
