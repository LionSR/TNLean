/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusSimplyConnectedWalkAvoidance
import TNLean.PEPS.TorusDualFluxString

/-!
# Physical bonds avoided by a native dual detour

The forbidden dual plaquettes are computed from a physical observation region:
a plaquette is forbidden when at least one of its four corners is observed.
A dual path avoiding these plaquettes crosses no bond incident to the physical
region. When their actual closed-cell realization is simply connected and the
endpoints are outside them, such a path is constructed in the original lifted
displacement class. Its native group insertions are identity on every incident
physical bond.

Source: SCP10, arXiv:1001.3807v3, Definition 6.13 and Lemma 6.14,
local source lines 2180–2214.

**Scope restriction (simply connected dual corner collar):** Both periods are
at least three. Simple connectedness is required of the computed forbidden
plaquette set, rather than inferred from endpoint exclusion or from simple
connectedness of the physical region. This proves physical bond avoidance;
the open-pair vacuum-density comparison requires a separate contraction
argument. See `docs/paper-gaps/scp10_dual_physical_avoidance.tex`.
-/

noncomputable section
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
local notation "X" => TorusVertex width height
local instance physicalAvoidanceQuiver : Quiver X := torusDualQuiver width height

/-- Dual plaquettes whose four physical corners meet the observation region.
Source: SCP10, the native string incidence in Definition 6.13. -/
def torusIncidentDualPlaquettes (R : Finset X) : Finset X :=
  Finset.univ.filter fun v ↦ v ∈ R ∨ (v.1 + 1, v.2) ∈ R ∨
    (v.1, v.2 + 1) ∈ R ∨ (v.1 + 1, v.2 + 1) ∈ R

private theorem corners_outside (R : Finset X) {v : X}
    (hv : v ∉ torusIncidentDualPlaquettes R) :
    v ∉ R ∧ (v.1 + 1, v.2) ∉ R ∧ (v.1, v.2 + 1) ∉ R ∧
      (v.1 + 1, v.2 + 1) ∉ R := by
  simpa only [torusIncidentDualPlaquettes, Finset.mem_filter, Finset.mem_univ,
    true_and, not_or] using hv

omit [NeZero width] [NeZero height] in
private theorem step_crossings_zero (R : Finset X) {a b : X}
    (e : TorusDualStep a b)
    (ha : a ∉ R ∧ (a.1 + 1, a.2) ∉ R ∧ (a.1, a.2 + 1) ∉ R ∧
      (a.1 + 1, a.2 + 1) ∉ R)
    (hb : b ∉ R ∧ (b.1 + 1, b.2) ∉ R ∧ (b.1, b.2 + 1) ∉ R ∧
      (b.1 + 1, b.2 + 1) ∉ R) (v : X) :
    ((v ∈ R ∨ (v.1 + 1, v.2) ∈ R) → e.crossings.1 v = 0) ∧
      ((v ∈ R ∨ (v.1, v.2 + 1) ∈ R) → e.crossings.2 v = 0) := by
  cases e with
  | east x y =>
    constructor
    · intro _; rfl
    · intro hv
      have hne : v ≠ (x + 1, y) := by
        rintro rfl
        exact hv.elim ha.2.1 ha.2.2.2
      simp [TorusDualStep.crossings, torusPointMass, hne]
  | west x y =>
    constructor
    · intro _; rfl
    · intro hv
      have hne : v ≠ (x + 1, y) := by
        rintro rfl
        exact hv.elim hb.2.1 hb.2.2.2
      simp [TorusDualStep.crossings, torusPointMass, hne]
  | north x y =>
    constructor
    · intro hv
      have hne : v ≠ (x, y + 1) := by
        rintro rfl
        exact hv.elim ha.2.2.1 ha.2.2.2
      simp [TorusDualStep.crossings, torusPointMass, hne]
    · intro _; rfl
  | south x y =>
    constructor
    · intro hv
      have hne : v ≠ (x, y + 1) := by
        rintro rfl
        exact hv.elim hb.2.2.1 hb.2.2.2
      simp [TorusDualStep.crossings, torusPointMass, hne]
    · intro _; rfl

variable [Fact (2 < width)] [Fact (2 < height)]

private theorem path_crossings_zero (R : Finset X) {a b : X} (p : TorusDualPath a b)
    (h : ∀ v ∈ (torusDualPathGraphWalk p).support,
      v ∉ R ∧ (v.1 + 1, v.2) ∉ R ∧ (v.1, v.2 + 1) ∉ R ∧
        (v.1 + 1, v.2 + 1) ∉ R) :
    ∀ v : X,
      ((v ∈ R ∨ (v.1 + 1, v.2) ∈ R) → (torusDualPathCrossings p).1 v = 0) ∧
        ((v ∈ R ∨ (v.1, v.2 + 1) ∈ R) → (torusDualPathCrossings p).2 v = 0) := by
  revert h
  induction p with
  | nil => intro _ v; exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  | @cons b c p e ih =>
    intro h v
    have hp : ∀ w ∈ (torusDualPathGraphWalk p).support,
        w ∉ R ∧ (w.1 + 1, w.2) ∉ R ∧ (w.1, w.2 + 1) ∉ R ∧
          (w.1 + 1, w.2 + 1) ∉ R := by
      intro w hw
      apply h w
      simp only [torusDualPathGraphWalk, SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl hw
    have hb := hp b (torusDualPathGraphWalk p).end_mem_support
    have hc := h c (torusDualPathGraphWalk (p.cons e)).end_mem_support
    obtain ⟨hph, hpv⟩ := ih hp v
    obtain ⟨heh, hev⟩ := step_crossings_zero R e hb hc v
    constructor
    · intro hv
      change (torusDualPathCrossings p).1 v + e.crossings.1 v = 0
      rw [hph hv, heh hv, zero_add]
    · intro hv
      change (torusDualPathCrossings p).2 v + e.crossings.2 v = 0
      rw [hpv hv, hev hv, zero_add]

/-- Construct a native dual detour in the original displacement class whose
signed crossing count vanishes on every bond incident to the physical region.
The forbidden dual set is computed from the physical corners. No detour or
bond-avoidance premise is supplied. Source: SCP10, Lemma 6.14. -/
theorem exists_torusDualPath_zero_crossings_on_incident
    (R : Finset X)
    (hSC : IsSimplyConnected (torusRegionRealization (torusIncidentDualPlaquettes R)))
    {a b : X} (p : TorusDualPath a b)
    (ha : a ∉ torusIncidentDualPlaquettes R) (hb : b ∉ torusIncidentDualPlaquettes R) :
    ∃ q : TorusDualPath a b,
      torusDualPathDisplacement q = torusDualPathDisplacement p ∧
        ∀ v : X,
          ((v ∈ R ∨ (v.1 + 1, v.2) ∈ R) → (torusDualPathCrossings q).1 v = 0) ∧
            ((v ∈ R ∨ (v.1, v.2 + 1) ∈ R) → (torusDualPathCrossings q).2 v = 0) := by
  obtain ⟨q, hd, hq⟩ := exists_torusDualPath_avoiding_of_isSimplyConnected
    (torusIncidentDualPlaquettes R) hSC p ha hb
  exact ⟨q, hd, path_crossings_zero R q (fun v hv ↦ corners_outside R (hq v hv))⟩

/-- The actual inserted group labels of a constructed dual detour are identity
on every physical bond incident to the observation region. The group need not
be abelian. Source: SCP10, Definition 6.13 and Lemma 6.14. -/
theorem exists_torusDualPath_trivial_on_incident {G : Type*} [Group G]
    (R : Finset X)
    (hSC : IsSimplyConnected (torusRegionRealization (torusIncidentDualPlaquettes R)))
    {a b : X} (p : TorusDualPath a b)
    (ha : a ∉ torusIncidentDualPlaquettes R) (hb : b ∉ torusIncidentDualPlaquettes R)
    (g : G) :
    ∃ q : TorusDualPath a b,
      torusDualPathDisplacement q = torusDualPathDisplacement p ∧
        ∀ v : X,
          ((v ∈ R ∨ (v.1 + 1, v.2) ∈ R) → (torusDualFluxLabels g q).1 v = 1) ∧
            ((v ∈ R ∨ (v.1, v.2 + 1) ∈ R) → (torusDualFluxLabels g q).2 v = 1) := by
  obtain ⟨q, hd, hq⟩ := exists_torusDualPath_zero_crossings_on_incident R hSC p ha hb
  refine ⟨q, hd, fun v ↦ ⟨?_, ?_⟩⟩
  · intro hv
    simp only [torusDualFluxLabels, torusFluxPowerLabels, (hq v).1 hv, zpow_zero]
  · intro hv
    simp only [torusDualFluxLabels, torusFluxPowerLabels, (hq v).2 hv, zpow_zero]

end TNLean.PEPS
