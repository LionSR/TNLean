/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularOpenRegion
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Synchronization of regular group labels in a connected region

In a connected region, equality of group labels at the two ends of every internal
edge implies that all vertex labels agree. If two incident-edge configurations
are related at each vertex by left multiplication, cancellation of the common
edge label gives precisely these endpoint equalities. Thus all local translations
are one simultaneous translation of the incident-edge configuration.

This is an auxiliary step in the finite-region contraction of Schuch, Cirac, and
Pérez-García, arXiv:1001.3807, lines 1935–1957. The connectedness hypothesis is
explicit. No region isometry or entropy assertion is made here.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS

variable {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}
variable {G : Type*}

/-- Source: SCP10, finite-region contraction, lines 1935–1957. Labels equal at
the endpoints of every internal edge agree throughout a connected region. -/
theorem regionLabels_eq_of_internalEdge_eq (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected) (q : {v : V // v ∈ R} → G)
    (hq : ∀ (e : Edge Γ) (h₁ : e.1.1 ∈ R) (h₂ : e.1.2 ∈ R),
      q ⟨e.1.1, h₁⟩ = q ⟨e.1.2, h₂⟩) (u v : {v : V // v ∈ R}) :
    q u = q v := by
  have hAdj (u v : {v : V // v ∈ R}) (h : Γ.Adj u.1 v.1) : q u = q v := by
    let e := Edge.ofAdj h
    rcases Edge.ofAdj_endpoints h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have hu : e.1.1 ∈ R := by rw [show e.1.1 = u.1 from h₁]; exact u.2
      have hv : e.1.2 ∈ R := by rw [show e.1.2 = v.1 from h₂]; exact v.2
      have hu' : (⟨e.1.1, hu⟩ : {v : V // v ∈ R}) = u := Subtype.ext h₁
      have hv' : (⟨e.1.2, hv⟩ : {v : V // v ∈ R}) = v := Subtype.ext h₂
      simpa only [hu', hv'] using hq e hu hv
    · have hv : e.1.1 ∈ R := by rw [show e.1.1 = v.1 from h₁]; exact v.2
      have hu : e.1.2 ∈ R := by rw [show e.1.2 = u.1 from h₂]; exact u.2
      have hu' : (⟨e.1.2, hu⟩ : {v : V // v ∈ R}) = u := Subtype.ext h₂
      have hv' : (⟨e.1.1, hv⟩ : {v : V // v ∈ R}) = v := Subtype.ext h₁
      simpa only [hu', hv'] using (hq e hv hu).symm
  obtain ⟨p⟩ := hR u v
  induction p with
  | nil => rfl
  | cons h _ ih => exact (hAdj _ _ h).trans ih

/-- Source: SCP10, finite-region contraction, lines 1935–1957. A group-valued
vertex labelling of a nonempty connected region is constant exactly when it
agrees at both endpoints of every internal edge. -/
theorem regionLabels_constant_iff_internalEdge_eq (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected) (q : {v : V // v ∈ R} → G) :
    (∃ g : G, ∀ v, q v = g) ↔
      ∀ (e : Edge Γ) (h₁ : e.1.1 ∈ R) (h₂ : e.1.2 ∈ R),
        q ⟨e.1.1, h₁⟩ = q ⟨e.1.2, h₂⟩ := by
  constructor
  · rintro ⟨g, hg⟩ e h₁ h₂
    rw [hg, hg]
  · intro hq
    obtain ⟨v⟩ := hR.nonempty
    exact ⟨q v, fun w => regionLabels_eq_of_internalEdge_eq R hR q hq w v⟩

variable [Group G]

/-- The local compatibility equations for two configurations of all edges
incident to a region. At vertex `v`, the second configuration is translated
by `q v`. Source: SCP10, regular-basis contraction, lines 1935–1957. -/
def IsRegionLabelCompatible (R : Finset V) (q : {v : V // v ∈ R} → G)
    (η θ : {e : Edge Γ // IsRegionIncidentEdge R e} → G) : Prop :=
  ∀ (v : {v : V // v ∈ R}) (e : IncidentEdge Γ v.1),
    η ⟨e.1, isRegionIncidentEdge_of_regionVertex R v e⟩ =
      q v * θ ⟨e.1, isRegionIncidentEdge_of_regionVertex R v e⟩

instance [Fintype V] [DecidableRel Γ.Adj] [DecidableEq G] (R : Finset V)
    (q : {v : V // v ∈ R} → G)
    (η θ : {e : Edge Γ // IsRegionIncidentEdge R e} → G) :
    Decidable (IsRegionLabelCompatible R q η θ) :=
  inferInstanceAs (Decidable (∀ (v : {v : V // v ∈ R}) (e : IncidentEdge Γ v.1),
    η ⟨e.1, isRegionIncidentEdge_of_regionVertex R v e⟩ =
      q v * θ ⟨e.1, isRegionIncidentEdge_of_regionVertex R v e⟩))

/-- Cancellation on an internal edge equates its two local group translations.
Source: SCP10, regular-basis contraction, lines 1935–1957. -/
theorem IsRegionLabelCompatible.internalEdge_eq {R : Finset V}
    {q : {v : V // v ∈ R} → G}
    {η θ : {e : Edge Γ // IsRegionIncidentEdge R e} → G}
    (h : IsRegionLabelCompatible R q η θ)
    (e : Edge Γ) (h₁ : e.1.1 ∈ R) (h₂ : e.1.2 ∈ R) :
    q ⟨e.1.1, h₁⟩ = q ⟨e.1.2, h₂⟩ := by
  have hleft := h ⟨e.1.1, h₁⟩ ⟨e, Or.inl rfl⟩
  have hright := h ⟨e.1.2, h₂⟩ ⟨e, Or.inr rfl⟩
  exact mul_right_cancel (hleft.symm.trans hright)

/-- Source: SCP10, finite-region contraction, lines 1935–1957. Compatible
local translations in a connected region are one common translation. -/
theorem IsRegionLabelCompatible.exists_common_label {R : Finset V}
    (hR : (Γ.induce (R : Set V)).Connected) {q : {v : V // v ∈ R} → G}
    {η θ : {e : Edge Γ // IsRegionIncidentEdge R e} → G}
    (h : IsRegionLabelCompatible R q η θ) : ∃ g : G, ∀ v, q v = g :=
  (regionLabels_constant_iff_internalEdge_eq R hR q).mpr h.internalEdge_eq

/-- Every incident-edge label is translated by the common vertex label.
Source: SCP10, finite-region contraction, lines 1935–1957. -/
theorem IsRegionLabelCompatible.exists_translation {R : Finset V}
    (hR : (Γ.induce (R : Set V)).Connected) {q : {v : V // v ∈ R} → G}
    {η θ : {e : Edge Γ // IsRegionIncidentEdge R e} → G}
    (h : IsRegionLabelCompatible R q η θ) :
    ∃ g : G, (∀ v, q v = g) ∧ η = fun e => g * θ e := by
  obtain ⟨g, hg⟩ := h.exists_common_label hR
  refine ⟨g, hg, funext fun e => ?_⟩
  rcases e.2 with he | he
  · simpa only [hg] using h ⟨e.1.1.1, he⟩ ⟨e.1, Or.inl rfl⟩
  · simpa only [hg] using h ⟨e.1.1.2, he⟩ ⟨e.1, Or.inr rfl⟩

/-- Compatibility on a connected region is exactly a constant vertex label
and the corresponding simultaneous translation of incident labels.
Source: SCP10, finite-region contraction, lines 1935–1957. -/
theorem isRegionLabelCompatible_iff_exists_translation (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected) (q : {v : V // v ∈ R} → G)
    (η θ : {e : Edge Γ // IsRegionIncidentEdge R e} → G) :
    IsRegionLabelCompatible R q η θ ↔
      ∃ g : G, (∀ v, q v = g) ∧ η = fun e => g * θ e := by
  refine ⟨fun h => h.exists_translation hR, ?_⟩
  rintro ⟨g, hg, rfl⟩ v e
  rw [hg]

open scoped BigOperators in
/-- Source: SCP10, finite-region contraction, lines 1935–1957. The sum over
compatible local translations reduces to one sum over simultaneous translations.
This also covers an isolated singleton region: both sides then count all `|G|`
translations, without requiring uniqueness from an incident edge. -/
theorem sum_regionLabelCompatible_eq_sum_translation [Fintype V] [DecidableRel Γ.Adj]
    [Fintype G] [DecidableEq G]
    (R : Finset V) (hR : (Γ.induce (R : Set V)).Connected)
    (η θ : {e : Edge Γ // IsRegionIncidentEdge R e} → G) :
    (∑ q : {v : V // v ∈ R} → G,
      if IsRegionLabelCompatible R q η θ then (1 : ℂ) else 0) =
      ∑ g : G, if η = (fun e => g * θ e) then (1 : ℂ) else 0 := by
  classical
  obtain ⟨v⟩ := hR.nonempty
  refine (Fintype.sum_of_injective (fun g : G => fun _ : {v : V // v ∈ R} => g)
    (fun g h hgh => congrFun hgh v) _ _ ?_ ?_).symm
  · intro q hq
    split_ifs with hc
    · obtain ⟨g, hg⟩ := hc.exists_common_label hR
      exact (hq ⟨g, (funext hg).symm⟩).elim
    · rfl
  · intro g
    have hcompat : IsRegionLabelCompatible R (fun _ => g) η θ ↔
        η = fun e => g * θ e := by
      constructor
      · intro hc
        obtain ⟨g', hg', ht⟩ := hc.exists_translation hR
        simpa only [← hg' v] using ht
      · intro ht
        exact (isRegionLabelCompatible_iff_exists_translation R hR _ η θ).mpr
          ⟨g, fun _ => rfl, ht⟩
    simp only [hcompat]

end TNLean.PEPS
