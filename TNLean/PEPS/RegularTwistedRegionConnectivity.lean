/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularRegionConnectivity
import TNLean.PEPS.RegularTwistedRegion

/-!
# Synchronization through a common untwisted subgraph

Group operators on internal bonds constrain the local translations by
intertwining equations. If a connected spanning subgraph of the region has
identity operators in both configurations, its constraints equate the vertex
translations. The remaining internal bonds then test a single common group
element. This is the synchronization step for twisted regular contractions.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, the regular contraction
and boundary separation in the proof of Theorem 6.9, source lines 1935–1990.
Connectedness of the common untwisted subgraph is stated explicitly. Its
geometric construction and the physical entropy assertion are separate results.
-/

namespace TNLean.PEPS

variable {V : Type*} [LinearOrder V] {Γ Δ : SimpleGraph V} {G : Type*}

/-- Labels agreeing on a connected spanning subgraph agree throughout the
region. Source: SCP10, regular contraction, lines 1935–1957. -/
theorem regionLabels_eq_of_subgraph_internalEdge_eq (R : Finset V)
    (hΔ : Δ ≤ Γ) (hR : (Δ.induce (R : Set V)).Connected)
    (q : {v : V // v ∈ R} → G)
    (hq : ∀ (e : Edge Γ), Δ.Adj e.1.1 e.1.2 →
      ∀ (h₁ : e.1.1 ∈ R) (h₂ : e.1.2 ∈ R), q ⟨e.1.1, h₁⟩ = q ⟨e.1.2, h₂⟩)
    (u v : {v : V // v ∈ R}) : q u = q v := by
  apply regionLabels_eq_of_internalEdge_eq R hR q
  intro e h₁ h₂
  exact hq ⟨e.1, e.2.1, hΔ e.2.2⟩ e.2.2 h₁ h₂


variable [Group G]

/-- Compatibility at a tail leaves its group label unchanged by the bond
operator. Source: SCP10, oriented regular bonds, lines 1935–1957. -/
theorem IsTwistedRegionLabelCompatible.tail_eq {R : Finset V} {u w : Edge Γ → G}
    {q : {v : V // v ∈ R} → G}
    {η θ : {f : Edge Γ // IsRegionIncidentEdge R f} → G}
    (hc : IsTwistedRegionLabelCompatible R u w q η θ) (e : Edge Γ) (h₁ : e.1.1 ∈ R) :
    η ⟨e, Or.inl h₁⟩ = q ⟨e.1.1, h₁⟩ * θ ⟨e, Or.inl h₁⟩ := by
  have h := congrFun (hc ⟨e.1.1, h₁⟩) ⟨e, Or.inl rfl⟩
  simpa only [regularTwistedLabels, ne_of_lt e.2.1, ite_false] using h

/-- Compatibility at a head includes the inserted regular group elements.
Source: SCP10, oriented regular bonds, lines 1935–1957. -/
theorem IsTwistedRegionLabelCompatible.head_eq {R : Finset V} {u w : Edge Γ → G}
    {q : {v : V // v ∈ R} → G}
    {η θ : {f : Edge Γ // IsRegionIncidentEdge R f} → G}
    (hc : IsTwistedRegionLabelCompatible R u w q η θ) (e : Edge Γ) (h₂ : e.1.2 ∈ R) :
    u e * η ⟨e, Or.inr h₂⟩ = q ⟨e.1.2, h₂⟩ * (w e * θ ⟨e, Or.inr h₂⟩) := by
  have h := congrFun (hc ⟨e.1.2, h₂⟩) ⟨e, Or.inr rfl⟩
  simpa only [regularTwistedLabels, ite_true] using h

/-- The two local translations on an internal bond intertwine its group
operators. Source: SCP10, twisted regular contraction, lines 1935–1990. -/
theorem IsTwistedRegionLabelCompatible.internalEdge_intertwining
    {R : Finset V} {u w : Edge Γ → G} {q : {v : V // v ∈ R} → G}
    {η θ : {f : Edge Γ // IsRegionIncidentEdge R f} → G}
    (hc : IsTwistedRegionLabelCompatible R u w q η θ)
    (e : Edge Γ) (h₁ : e.1.1 ∈ R) (h₂ : e.1.2 ∈ R) :
    u e * q ⟨e.1.1, h₁⟩ = q ⟨e.1.2, h₂⟩ * w e := by
  apply mul_right_cancel (b := θ ⟨e, Or.inl h₁⟩)
  simpa only [hc.tail_eq e h₁, mul_assoc] using hc.head_eq e h₂

/-- A connected common untwisted subgraph synchronizes all vertex translations.
Source: SCP10, twisted regular contraction, lines 1935–1990. -/
theorem IsTwistedRegionLabelCompatible.exists_common_label
    {R : Finset V} {u w : Edge Γ → G} {q : {v : V // v ∈ R} → G}
    {η θ : {f : Edge Γ // IsRegionIncidentEdge R f} → G}
    (hc : IsTwistedRegionLabelCompatible R u w q η θ)
    (hΔ : Δ ≤ Γ) (hR : (Δ.induce (R : Set V)).Connected)
    (hUntwisted : ∀ e : Edge Γ, Δ.Adj e.1.1 e.1.2 → u e = 1 ∧ w e = 1) :
    ∃ x : G, ∀ v, q v = x := by
  obtain ⟨v⟩ := hR.nonempty
  refine ⟨q v, fun z => regionLabels_eq_of_subgraph_internalEdge_eq R hΔ hR q ?_ z v⟩
  intro e he h₁ h₂
  simpa only [(hUntwisted e he).1, (hUntwisted e he).2, one_mul, mul_one] using
    hc.internalEdge_intertwining e h₁ h₂

/-- With identity bond operators at the boundary, compatibility is exactly a
common translation and one intertwining equation for each internal bond.
Source: SCP10, twisted-region contraction, lines 1935–1990. -/
theorem isTwistedRegionLabelCompatible_iff_exists_translation
    (R : Finset V) (u w : Edge Γ → G) (q : {v : V // v ∈ R} → G)
    (η θ : {f : Edge Γ // IsRegionIncidentEdge R f} → G)
    (hΔ : Δ ≤ Γ) (hR : (Δ.induce (R : Set V)).Connected)
    (hUntwisted : ∀ e : Edge Γ, Δ.Adj e.1.1 e.1.2 → u e = 1 ∧ w e = 1)
    (hBoundary : ∀ e : Edge Γ, IsRegionBoundaryEdge R e → u e = 1 ∧ w e = 1) :
    IsTwistedRegionLabelCompatible R u w q η θ ↔
      ∃ x : G, (∀ v, q v = x) ∧ η = (fun e => x * θ e) ∧
        ∀ (e : Edge Γ), e.1.1 ∈ R → e.1.2 ∈ R → u e * x = x * w e := by
  constructor
  · intro hc
    obtain ⟨x, hx⟩ := hc.exists_common_label hΔ hR hUntwisted
    refine ⟨x, hx, funext fun e => ?_, fun e h₁ h₂ => ?_⟩
    · by_cases h₁ : e.1.1.1 ∈ R
      · simpa only [hx] using hc.tail_eq e.1 h₁
      · have h₂ : e.1.1.2 ∈ R := e.2.resolve_left h₁
        have hb := hBoundary e.1 (Or.inr ⟨h₁, h₂⟩)
        simpa only [hb.1, hb.2, one_mul, hx] using hc.head_eq e.1 h₂
    · simpa only [hx] using hc.internalEdge_intertwining e h₁ h₂
  · rintro ⟨x, hx, rfl, hi⟩ v
    funext f
    change (if v.1 = f.1.1.2 then u f.1 * (x * θ _) else x * θ _) =
      q v * (if v.1 = f.1.1.2 then w f.1 * θ _ else θ _)
    rw [hx]
    split_ifs with hv
    · have h₂ : f.1.1.2 ∈ R := by rw [← hv]; exact v.2
      by_cases h₁ : f.1.1.1 ∈ R
      · rw [← mul_assoc, hi f.1 h₁ h₂, mul_assoc]
      · have hb := hBoundary f.1 (Or.inr ⟨h₁, h₂⟩)
        simp only [hb.1, hb.2, one_mul]
    · rfl


open scoped BigOperators in
/-- The finite sum over compatible vertex translations reduces to a sum over
common internal-bond intertwiners. Source: SCP10, lines 1935–1990. -/
theorem sum_twistedRegionLabelCompatible_eq_sum_translation
    [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G]
    (R : Finset V) (u w : Edge Γ → G)
    (η θ : {f : Edge Γ // IsRegionIncidentEdge R f} → G)
    (hΔ : Δ ≤ Γ) (hR : (Δ.induce (R : Set V)).Connected)
    (hUntwisted : ∀ e : Edge Γ, Δ.Adj e.1.1 e.1.2 → u e = 1 ∧ w e = 1)
    (hBoundary : ∀ e : Edge Γ, IsRegionBoundaryEdge R e → u e = 1 ∧ w e = 1) :
    (∑ q : {v : V // v ∈ R} → G,
      if IsTwistedRegionLabelCompatible R u w q η θ then (1 : ℂ) else 0) =
      ∑ x : G, if η = (fun e => x * θ e) ∧
        (∀ e : Edge Γ, e.1.1 ∈ R → e.1.2 ∈ R → u e * x = x * w e)
        then (1 : ℂ) else 0 := by
  classical
  obtain ⟨v⟩ := hR.nonempty
  refine (Fintype.sum_of_injective (fun x : G => fun _ : {v : V // v ∈ R} => x)
    (fun x y hxy => congrFun hxy v) _ _ ?_ ?_).symm
  · intro q hq
    split_ifs with hc
    · obtain ⟨x, hx⟩ := hc.exists_common_label hΔ hR hUntwisted
      exact (hq ⟨x, (funext hx).symm⟩).elim
    · rfl
  · intro x
    have hc : IsTwistedRegionLabelCompatible R u w (fun _ => x) η θ ↔
        η = (fun e => x * θ e) ∧
          (∀ e : Edge Γ, e.1.1 ∈ R → e.1.2 ∈ R → u e * x = x * w e) := by
      rw [isTwistedRegionLabelCompatible_iff_exists_translation
        R u w _ η θ hΔ hR hUntwisted hBoundary]
      constructor
      · rintro ⟨y, hy, ht, hi⟩
        simpa only [← hy v] using And.intro ht hi
      · rintro ⟨ht, hi⟩
        exact ⟨x, fun _ => rfl, ht, hi⟩
    simp only [hc]

end TNLean.PEPS
