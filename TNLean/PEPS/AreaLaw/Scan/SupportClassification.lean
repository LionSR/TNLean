/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SideSeparation
import TNLean.PEPS.AreaLaw.Scan.TerminalSplits

/-!
# Classification of actual terminal supports

At every actual status a designated support either lies in one physical part
or is a terminal split: it meets the middle and exactly one receiving side,
and lies in one part of each other band. In particular, this classification
covers supports that were not initially given a middle-side incidence.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Lemma 9.1(1), and `06-transport.tex`, lines 336–352,
at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

omit [Fintype I] [LinearOrder I] in
/-- In a three-part physical partition, a support that cannot meet both receiving
sides either lies in one part or meets the middle and a receiving side. -/
theorem contained_or_middle_side (σ : PhysicalPartition V) (B : Finset V)
    (hsep : ¬ ((B ∩ receiving σ false).Nonempty ∧
      (B ∩ receiving σ true).Nonempty)) :
    (∃ part : Option Bool, ∀ x ∈ B, σ x = part) ∨
      ∃ side : Bool, (B ∩ receiving σ side).Nonempty ∧ (B ∩ middle σ).Nonempty := by
  classical
  by_cases hc : ∃ part : Option Bool, ∀ x ∈ B, σ x = part
  · exact Or.inl hc
  right
  have hn (part : Option Bool) : ∃ x ∈ B, σ x ≠ part := by
    have hnot : ¬ ∀ x ∈ B, σ x = part := fun h ↦ hc ⟨part, h⟩
    push Not at hnot
    exact hnot
  by_cases hm : (B ∩ middle σ).Nonempty
  · obtain ⟨x, hxB, hx⟩ := hn none
    cases hs : σ x with
    | none => exact (hx hs).elim
    | some side =>
      exact ⟨side, ⟨x, Finset.mem_inter.mpr
        ⟨hxB, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩⟩, hm⟩
  · have hnotmiddle (x : V) (hxB : x ∈ B) : σ x ≠ none := by
      intro hx
      exact hm ⟨x, Finset.mem_inter.mpr
        ⟨hxB, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩⟩
    obtain ⟨x, hxB, hx⟩ := hn (some false)
    obtain ⟨y, hyB, hy⟩ := hn (some true)
    have hxF : σ x = some true := by
      cases hs : σ x with
      | none => exact (hnotmiddle x hxB hs).elim
      | some side => cases side <;> simp_all
    have hyP : σ y = some false := by
      cases hs : σ y with
      | none => exact (hnotmiddle y hyB hs).elim
      | some side => cases side <;> simp_all
    exact (hsep ⟨⟨y, Finset.mem_inter.mpr
      ⟨hyB, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyP⟩⟩⟩,
      ⟨x, Finset.mem_inter.mpr
        ⟨hxB, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxF⟩⟩⟩⟩).elim

namespace CollarScan

/-- Every actual completed status satisfies the physical terminal-support
classification of the transport estimate, derived from scanner geometry. -/
theorem state_designatedSupport_classification_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (h : History S.K S.m S.M k) (hn : 0 < S.n) (hk : k ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (g : Fin S.K) (i : I) :
    (∃ part : Option Bool, ∀ x ∈
      designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i), S.state h g x = part) ∨
      ∃ side, IsTerminalSplit (S.state h)
        (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)) g side := by
  rcases contained_or_middle_side (S.state h g) _
    (state_designatedSupport_not_near_far_domainGraph hT S hgraph hdepth h
      hn hk hr hDpos hD hL hclear g i) with hc | ⟨side, hs⟩
  · exact Or.inl hc
  · exact Or.inr ⟨side,
      state_designatedSplitIncidence_isTerminalSplit_domainGraph hT S hgraph hdepth h
        hn hk hr hDpos hD hL hrows hclear g side i hs⟩

/-- Every actual pre-charge status satisfies the physical terminal-support
classification, without a good-history or a support-classification assumption. -/
theorem old_designatedSupport_classification_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L : ℕ}
    (h : History S.K S.m S.M k) (hn : 0 < S.n) (hk : k + 1 ≤ S.n * S.m)
    (hr : S.r₀ ≤ S.D) (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (g : Fin S.K) (i : I) :
    (∃ part : Option Bool, ∀ x ∈
      designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i),
        S.oldChargeState h g x = part) ∨
      ∃ side, IsTerminalSplit (S.oldChargeState h)
        (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)) g side := by
  rcases contained_or_middle_side (S.oldChargeState h g) _
    (old_designatedSupport_not_near_far_domainGraph hT S hgraph hdepth h
      hn hk hr hDpos hD hL hclear g i) with hc | ⟨side, hs⟩
  · exact Or.inl hc
  · exact Or.inr ⟨side,
      old_designatedSplitIncidence_isTerminalSplit_domainGraph hT S hgraph hdepth h
        hn hk hr hDpos hD hL hrows hclear g side i hs⟩

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
