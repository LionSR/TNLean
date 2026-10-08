/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicLevelSchedule
import TNLean.PEPS.Approximation.DyadicPointTreatment

/-!
# True vertices and tags of the large-scale dyadic repainting

A true vertex of a guide is a point in the closures of the regions of three distinct labels. Each
true vertex carries an encoded hole and a tag, held by one of its incident labels other than the
placeholder. This file proves that the bulk operations of a large-scale repainting create and
destroy no true vertex and keep the incident labels, hence the tags, of every existing one:

* the incident labels of a guide at a point, and their invariance under a change of the guide
  away from the point;
* for an elementary birth or death after the point treatment, the closure of the remaining
  changed region has the open neighborhood of radius `a₀ t` on which the surrounding guide is
  `P∘` and the other guide takes at most one further label; hence the two guides have the same
  true vertices, each at distance at least `a₀ t` from the closed change and with the same
  incident labels;
* for a lens exchange after the point treatment, both sheets are `C` on the open neighborhood of
  radius `a₀ t` of the lens boundary; hence each exchanged guide has, inside the lens, the true
  vertices and incident labels of the sheet it takes there, and outside the lens those of the
  other sheet;
* the true vertices of a homogenized guide: either true vertices of the guide off the closed
  treated squares, or points of a treated rim where two labels other than `P∘` meet;
* the tag part of the invariant on active labels: a tag holder is an incident label other than
  the placeholder, so at the end of a level only new labels hold tags.

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: true vertices and tags
  (lines 109–125), the point treatment (lines 341–351), the bulk recoloring without changed true
  vertices (lines 375–387), the exchange (lines 389–419), and the active labels and tags
  (lines 597–631).
-/

namespace TNLean.PEPS.Approximation

open Set Metric Filter Topology SquareEdge

/-! ### Incident labels -/

/-- The labels incident at a point `c` of a guide `f`: those whose region has `c` in its closure.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:109–111, 119–122`. -/
def incidentLabels {X ι : Type*} [TopologicalSpace X] (f : X → ι) (c : X) : Set ι :=
  {l | c ∈ closure (f ⁻¹' {l})}

section Incident

variable {X ι : Type*} [TopologicalSpace X] {f g : X → ι} {c : X}

/-- A true vertex is a point with three distinct incident labels. -/
theorem isTrueVertex_iff_incidentLabels :
    IsTrueVertex f c ↔ ∃ l₁ l₂ l₃ : ι, l₁ ≠ l₂ ∧ l₁ ≠ l₃ ∧ l₂ ≠ l₃ ∧ l₁ ∈ incidentLabels f c ∧
      l₂ ∈ incidentLabels f c ∧ l₃ ∈ incidentLabels f c :=
  Iff.rfl

/-- Guides with the same incident labels at `c` have the same true-vertex status there. -/
theorem isTrueVertex_congr (h : incidentLabels f c = incidentLabels g c) :
    IsTrueVertex f c ↔ IsTrueVertex g c := by
  rw [isTrueVertex_iff_incidentLabels, isTrueVertex_iff_incidentLabels, h]

/-- A point with at most two incident labels is not a true vertex. -/
theorem not_isTrueVertex_of_subset_pair {P Q : ι} (h : incidentLabels f c ⊆ {P, Q}) :
    ¬ IsTrueVertex f c := by
  rintro ⟨l₁, l₂, l₃, h12, h13, h23, h1, h2, h3⟩
  rcases h h1 with rfl | rfl <;> rcases h h2 with rfl | rfl <;> rcases h h3 with rfl | rfl <;>
    simp_all

/-- Two guides that agree near `c` have the same incident labels at `c`. -/
theorem incidentLabels_congr (h : f =ᶠ[𝓝 c] g) : incidentLabels f c = incidentLabels g c := by
  ext l
  simp only [incidentLabels, mem_ofPred_eq, mem_closure_iff_nhdsWithin_neBot]
  rw [nhdsWithin_eq_iff_eventuallyEqSet.2]
  rw [eventuallyEqSet_iff]
  filter_upwards [h] with p hp
  simp only [mem_preimage, mem_singleton_iff, hp]

/-- If a guide takes values in `s` near `c`, its incident labels at `c` lie in `s`. -/
theorem incidentLabels_subset {V : Set X} (hV : V ∈ 𝓝 c) {s : Set ι}
    (h : ∀ p ∈ V, f p ∈ s) : incidentLabels f c ⊆ s := by
  intro l hl
  obtain ⟨p, hpV, hp⟩ := mem_closure_iff_nhds.1 hl V hV
  rw [mem_preimage, mem_singleton_iff] at hp
  exact hp ▸ h p hpV

/-- An incident label is a value of the guide. -/
theorem mem_range_of_mem_incidentLabels {l : ι} (hl : l ∈ incidentLabels f c) : l ∈ range f := by
  by_contra h
  have : f ⁻¹' {l} = ∅ := eq_empty_of_forall_notMem fun p hp => h ⟨p, hp⟩
  rw [incidentLabels, mem_ofPred_eq, this, closure_empty] at hl
  exact hl

/-- **No changed true vertex, abstract form.** Let the closure of the set where two guides differ
lie in an open set `U` on which both guides take only the two values `P`, `Q`. Then at every
point either the two guides have the same incident labels, or the point lies in `U` and both have
at most the incident labels `P`, `Q`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:375–382`. -/
theorem incidentLabels_eq_or_subset_pair {U : Set X} (hU : IsOpen U)
    (hR : closure {p | f p ≠ g p} ⊆ U) {P Q : ι} (hf : ∀ p ∈ U, f p ∈ ({P, Q} : Set ι))
    (hg : ∀ p ∈ U, g p ∈ ({P, Q} : Set ι)) (c : X) :
    incidentLabels f c = incidentLabels g c ∨
      (c ∈ U ∧ incidentLabels f c ⊆ {P, Q} ∧ incidentLabels g c ⊆ {P, Q}) := by
  by_cases hc : c ∈ U
  · exact Or.inr ⟨hc, incidentLabels_subset (hU.mem_nhds hc) hf,
      incidentLabels_subset (hU.mem_nhds hc) hg⟩
  · refine Or.inl (incidentLabels_congr ?_)
    have hc' : c ∉ closure {p | f p ≠ g p} := fun h => hc (hR h)
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc'] with p hp
    by_contra h
    exact hp (subset_closure h)

/-- In the setting of `incidentLabels_eq_or_subset_pair`, the two guides have the same true
vertices, and each of them lies outside `U` with the same incident labels in both guides. -/
theorem isTrueVertex_iff_of_two_labels {U : Set X} (hU : IsOpen U)
    (hR : closure {p | f p ≠ g p} ⊆ U) {P Q : ι} (hf : ∀ p ∈ U, f p ∈ ({P, Q} : Set ι))
    (hg : ∀ p ∈ U, g p ∈ ({P, Q} : Set ι)) (c : X) :
    (IsTrueVertex f c ↔ IsTrueVertex g c) ∧
      (IsTrueVertex f c → c ∉ U ∧ incidentLabels f c = incidentLabels g c) := by
  rcases incidentLabels_eq_or_subset_pair hU hR hf hg c with h | ⟨hc, h1, h2⟩
  · refine ⟨isTrueVertex_congr h, fun hv => ⟨fun hc => ?_, h⟩⟩
    rcases incidentLabels_eq_or_subset_pair hU hR hf hg c with - | ⟨-, h1, -⟩
    · exact not_isTrueVertex_of_subset_pair
        (incidentLabels_subset (hU.mem_nhds hc) hf) hv
    · exact not_isTrueVertex_of_subset_pair h1 hv
  · exact ⟨iff_of_false (not_isTrueVertex_of_subset_pair h1) (not_isTrueVertex_of_subset_pair h2),
      fun hv => absurd hv (not_isTrueVertex_of_subset_pair h1)⟩

/-- **Exchanging two guides along a common corridor, abstract form.** Let two guides `h₁`, `h₂`
both take the value `C` on an open set `U` containing the boundary of `Y`, and let `h` be `h₂` on
`Y` and `h₁` off it. At every point of `U` all three guides have at most the incident label `C`;
at a point of the interior of `Y` the guide `h` has the incident labels of `h₂`, and at a point of
the interior of the complement those of `h₁`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:393–398, 415–419`. -/
theorem incidentLabels_piecewise {Y U : Set X} [DecidablePred (· ∈ Y)] {h₁ h₂ : X → ι} {C : ι}
    (hU : IsOpen U) (hYU : frontier Y ⊆ U) (h₁U : ∀ p ∈ U, h₁ p = C) (h₂U : ∀ p ∈ U, h₂ p = C)
    (c : X) :
    (c ∈ U ∧ incidentLabels (fun p => if p ∈ Y then h₂ p else h₁ p) c ⊆ {C} ∧
        incidentLabels h₁ c ⊆ {C} ∧ incidentLabels h₂ c ⊆ {C}) ∨
      (c ∈ interior Y ∧
        incidentLabels (fun p => if p ∈ Y then h₂ p else h₁ p) c = incidentLabels h₂ c) ∨
      (c ∈ interior Yᶜ ∧
        incidentLabels (fun p => if p ∈ Y then h₂ p else h₁ p) c = incidentLabels h₁ c) := by
  by_cases hc : c ∈ U
  · refine Or.inl ⟨hc, incidentLabels_subset (hU.mem_nhds hc) fun p hp => ?_,
      incidentLabels_subset (hU.mem_nhds hc) fun p hp => h₁U p hp,
      incidentLabels_subset (hU.mem_nhds hc) fun p hp => h₂U p hp⟩
    split_ifs
    · exact h₂U p hp
    · exact h₁U p hp
  · have hcY : c ∉ frontier Y := fun h => hc (hYU h)
    by_cases hi : c ∈ interior Y
    · refine Or.inr (Or.inl ⟨hi, incidentLabels_congr ?_⟩)
      filter_upwards [isOpen_interior.mem_nhds hi] with p hp
      simp only [interior_subset hp, ↓reduceIte]
    · have hi' : c ∈ interior Yᶜ := by
        rw [interior_compl]
        intro hcl
        exact hcY ⟨hcl, hi⟩
      refine Or.inr (Or.inr ⟨hi', incidentLabels_congr ?_⟩)
      filter_upwards [isOpen_interior.mem_nhds hi'] with p hp
      simp only [show p ∉ Y from interior_subset hp, ↓reduceIte]

/-- In the setting of `incidentLabels_piecewise`, the exchanged guide has a true vertex at `c` if
and only if `c ∈ Y` and `h₂` has one there or `c ∉ Y` and `h₁` has one there; it then has the
incident labels of that guide at `c`. -/
theorem isTrueVertex_piecewise_iff {Y U : Set X} [DecidablePred (· ∈ Y)] {h₁ h₂ : X → ι}
    {C : ι} (hU : IsOpen U) (hYU : frontier Y ⊆ U) (h₁U : ∀ p ∈ U, h₁ p = C)
    (h₂U : ∀ p ∈ U, h₂ p = C) (c : X) :
    (IsTrueVertex (fun p => if p ∈ Y then h₂ p else h₁ p) c ↔
        (c ∈ Y ∧ IsTrueVertex h₂ c) ∨ (c ∉ Y ∧ IsTrueVertex h₁ c)) ∧
      (c ∈ Y → IsTrueVertex h₂ c →
        incidentLabels (fun p => if p ∈ Y then h₂ p else h₁ p) c = incidentLabels h₂ c) ∧
      (c ∉ Y → IsTrueVertex h₁ c →
        incidentLabels (fun p => if p ∈ Y then h₂ p else h₁ p) c = incidentLabels h₁ c) := by
  have hC (s : Set ι) (h : s ⊆ {C}) : s ⊆ {C, C} := by simpa using h
  rcases incidentLabels_piecewise hU hYU h₁U h₂U c with ⟨-, h, h1, h2⟩ | ⟨hi, h⟩ | ⟨hi, h⟩
  · have n0 := not_isTrueVertex_of_subset_pair (hC _ h)
    have n1 := not_isTrueVertex_of_subset_pair (hC _ h1)
    have n2 := not_isTrueVertex_of_subset_pair (hC _ h2)
    exact ⟨by tauto, fun _ h => absurd h n2, fun _ h => absurd h n1⟩
  · have hY : c ∈ Y := interior_subset hi
    rw [isTrueVertex_congr h]
    exact ⟨by tauto, fun _ _ => h, fun h' => absurd hY h'⟩
  · have hY : c ∉ Y := interior_subset hi
    rw [isTrueVertex_congr h]
    exact ⟨by tauto, fun h' => absurd h' hY, fun _ _ => h⟩

end Incident

/-! ### True vertices of a homogenized guide -/

section Homogenize

variable {X ι : Type*} [TopologicalSpace X] {U : Set X} {P : ι} {f : X → ι} {c : X}

/-- Homogenization adds at most the label `P` to the incident labels. -/
theorem incidentLabels_homogenize_subset :
    incidentLabels (homogenize U P f) c ⊆ insert P (incidentLabels f c) := by
  intro l hl
  by_cases hlP : l = P
  · exact hlP ▸ mem_insert _ _
  · refine mem_insert_of_mem _ (closure_mono (fun p hp => ?_) hl)
    rw [mem_preimage, mem_singleton_iff] at hp ⊢
    by_cases hpU : p ∈ U
    · exact absurd (hp ▸ homogenize_of_mem hpU) hlP
    · rwa [homogenize_of_notMem hpU] at hp

/-- **True vertices of a homogenized guide.** A true vertex of the guide homogenized to `P` on the
open set `U` is either a true vertex of the guide off the closure of `U`, or a point of the
boundary of `U` at which two distinct labels other than `P` of the guide meet.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:341–346, 353–355`. -/
theorem IsTrueVertex.of_homogenize (hU : IsOpen U) (h : IsTrueVertex (homogenize U P f) c) :
    (c ∉ closure U ∧ IsTrueVertex f c) ∨
      (c ∈ frontier U ∧ ∃ l₁ l₂ : ι, l₁ ≠ l₂ ∧ l₁ ≠ P ∧ l₂ ≠ P ∧ l₁ ∈ incidentLabels f c ∧
        l₂ ∈ incidentLabels f c) := by
  by_cases hcU : c ∈ closure U
  · right
    have hc : c ∉ U := fun hc => not_isTrueVertex_of_subset_pair (P := P) (Q := P)
      (incidentLabels_subset (hU.mem_nhds hc) fun p hp => by
        rw [homogenize_of_mem hp]; exact mem_insert _ _) h
    refine ⟨by rw [hU.frontier_eq]; exact ⟨hcU, hc⟩, ?_⟩
    obtain ⟨l₁, l₂, l₃, h12, h13, h23, h1, h2, h3⟩ := h
    have m1 := incidentLabels_homogenize_subset h1
    have m2 := incidentLabels_homogenize_subset h2
    have m3 := incidentLabels_homogenize_subset h3
    by_cases hP1 : l₁ = P
    · subst hP1
      exact ⟨l₂, l₃, h23, Ne.symm h12, Ne.symm h13, m2.resolve_left (Ne.symm h12),
        m3.resolve_left (Ne.symm h13)⟩
    · by_cases hP2 : l₂ = P
      · subst hP2
        exact ⟨l₁, l₃, h13, hP1, Ne.symm h23, m1.resolve_left hP1, m3.resolve_left (Ne.symm h23)⟩
      · exact ⟨l₁, l₂, h12, hP1, hP2, m1.resolve_left hP1, m2.resolve_left hP2⟩
  · left
    refine ⟨hcU, (isTrueVertex_congr (incidentLabels_congr ?_)).1 h⟩
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hcU] with p hp
    exact homogenize_of_notMem fun h => hp (subset_closure h)

end Homogenize

/-! ### Births and deaths after the point treatment -/

section BandOperations

variable {ι : Type*}

/-- An elementary birth or death introduces the single label `Q`: its surrounding word is its
before or its after word, and at every changed normal ratio the before and after words take only
the values `P∘` and `Q`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:378–379`. -/
structure BandOperation.InsertsOne (op : BandOperation ι) (Q : ι) : Prop where
  surrounding_eq : op.surrounding = op.before ∨ op.surrounding = op.after
  changed_mem : ∀ x, op.before x ≠ op.after x →
    op.before x ∈ ({op.label, Q} : Set ι) ∧ op.after x ∈ ({op.label, Q} : Set ι)

/-- Each of the seven births and deaths of an edge construction introduces a single label.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:185–221, 378–379`. -/
theorem edgeOperations_insertsOne (A B C : ι) :
    ∀ op ∈ edgeOperations A B C, ∃ Q, op.InsertsOne Q := by
  intro op hop
  simp only [edgeOperations, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨B, Or.inl rfl, fun x h => ?_⟩
    simp only [auxBirthB, auxWordOne, bandWord] at h ⊢
    split_ifs at h ⊢ <;> simp_all
  · refine ⟨A, Or.inl rfl, fun x h => ?_⟩
    simp only [auxBirthA, auxWordOne, auxWordTwo, bandWord] at h ⊢
    split_ifs at h ⊢ <;> first | (exfalso; linarith) | simp_all
  · refine ⟨C, Or.inl rfl, fun x h => ?_⟩
    simp only [auxBirthC, auxWordTwo, auxWord, bandWord] at h ⊢
    split_ifs at h ⊢ <;> first | (exfalso; linarith) | simp_all
  · refine ⟨C, Or.inr rfl, fun x h => ?_⟩
    simp only [mainDeathC, mainWordOne, mainWordTwo, bandWord] at h ⊢
    split_ifs at h ⊢ <;> first | (exfalso; linarith) | simp_all
  · refine ⟨A, Or.inr rfl, fun x h => ?_⟩
    simp only [mainDeathA, mainWordTwo, mainWordThree, bandWord] at h ⊢
    split_ifs at h ⊢ <;> simp_all
  · refine ⟨C, Or.inl rfl, fun x h => ?_⟩
    simp only [mainBirthC, mainWordThree, mainWordFour, bandWord] at h ⊢
    split_ifs at h ⊢ <;> simp_all
  · refine ⟨B, Or.inr rfl, fun x h => ?_⟩
    simp only [mainDeathB, mainWordFour, mainWordFive, bandWord] at h ⊢
    split_ifs at h ⊢ <;> first | (exfalso; linarith) | simp_all

/-- The open neighborhood of radius `a₀ t` of the closure of the remaining changed region of a
treated birth or death: on it the treated surrounding guide is `P∘`, by the logarithmic floor. -/
theorem BandOperation.treated_surrounding_eq (op : BandOperation ι) {n t : ℝ} (htn : t ≤ n)
    (e : SquareEdge) (g : ℝ × ℝ → ι) {p : ℝ × ℝ}
    (hp : p ∈ thickening (angularConstant * t)
      {p | homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g) p ≠
        homogenize (edgeTreated n e t) op.label (bandUpdate n e op.after g) p}) :
    homogenize (edgeTreated n e t) op.label (bandUpdate n e op.surrounding g) p = op.label := by
  obtain ⟨y, hy, hpy⟩ := mem_thickening_iff.1 hp
  by_contra hne
  have h := op.floor_bandUpdate htn e g (subset_closure hy) hne
  have : angularConstant * t ≤ angularConstant * max t (min n (edgeMarkDist n e y)) :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) angularConstant_pos.le
  rw [dist_comm] at h
  linarith

/-- **No changed true vertex in a treated birth or death.** Homogenize the before and after guides
of an elementary birth or death that introduces a single label to the surrounding label on the
treated squares of radius `0 < t ≤ n`. The two homogenized guides have the same true vertices.
Each of them lies at distance at least `a₀ t` from the closure of the remaining changed region,
and has the same incident labels in both guides, so it keeps its hole and its tag holder.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:375–387`. -/
theorem BandOperation.isTrueVertex_treated {op : BandOperation ι} {Q : ι} (hop : op.InsertsOne Q)
    {n t : ℝ} (ht : 0 < t) (htn : t ≤ n) (e : SquareEdge) (g : ℝ × ℝ → ι) (c : ℝ × ℝ) :
    (IsTrueVertex (homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g)) c ↔
        IsTrueVertex (homogenize (edgeTreated n e t) op.label (bandUpdate n e op.after g)) c) ∧
      (IsTrueVertex (homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g)) c →
        incidentLabels (homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g)) c =
          incidentLabels (homogenize (edgeTreated n e t) op.label (bandUpdate n e op.after g)) c ∧
        ∀ y ∈ closure {p |
          homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g) p ≠
            homogenize (edgeTreated n e t) op.label (bandUpdate n e op.after g) p},
          angularConstant * t ≤ dist c y) := by
  set Ut := edgeTreated n e t
  set fb := homogenize Ut op.label (bandUpdate n e op.before g)
  set fa := homogenize Ut op.label (bandUpdate n e op.after g)
  set R := {p | fb p ≠ fa p}
  set U := thickening (angularConstant * t) R
  have hδ : 0 < angularConstant * t := mul_pos angularConstant_pos ht
  have hRU : closure R ⊆ U := closure_subset_thickening hδ R
  -- on `U`, both guides take only the values `P∘` and `Q`
  have hmem : ∀ p ∈ U, fb p ∈ ({op.label, Q} : Set ι) ∧ fa p ∈ ({op.label, Q} : Set ι) := by
    intro p hp
    have hs := op.treated_surrounding_eq htn e g hp
    by_cases hpR : p ∈ R
    · have hpU : p ∉ Ut := fun h => hpR (show fb p = fa p by
        simp only [fb, fa, homogenize_of_mem h])
      have hpB : p ∈ edgeBand n e (-8) 2 := by
        by_contra hb
        exact hpR (show fb p = fa p by
          simp only [fb, fa, homogenize_of_notMem hpU, bandUpdate_of_notMem hb])
      have hne : op.before (bandCoord n e p) ≠ op.after (bandCoord n e p) := by
        have h' : fb p ≠ fa p := hpR
        simpa only [fb, fa, homogenize_of_notMem hpU, bandUpdate_of_mem hpB] using h'
      simp only [fb, fa, homogenize_of_notMem hpU, bandUpdate_of_mem hpB]
      exact hop.changed_mem _ hne
    · have heq : fb p = fa p := not_not.1 hpR
      have hP : fb p = op.label := by
        rcases hop.surrounding_eq with h | h
        · rw [h] at hs; exact hs
        · rw [h] at hs; exact heq.trans hs
      exact ⟨Or.inl hP, Or.inl (heq ▸ hP)⟩
  obtain ⟨hiff, hinc⟩ := isTrueVertex_iff_of_two_labels isOpen_thickening hRU
    (fun p hp => (hmem p hp).1) (fun p hp => (hmem p hp).2) c
  refine ⟨hiff, fun hv => ⟨(hinc hv).2, fun y hy => ?_⟩⟩
  have hcU := (hinc hv).1
  refine le_dist_of_mem_closure (fun z hz => ?_) hy
  by_contra hlt
  exact hcU (mem_thickening_iff.2 ⟨z, hz, not_le.1 hlt⟩)

end BandOperations

/-! ### The central birth after the point treatment -/

namespace RepaintingBaseline

variable {ι : Type*} (R : RepaintingBaseline ι)

/-- **No changed true vertex in the treated central birth.** Homogenize the starting guide and the
guide after the central birth to `A` on the treated squares of radius `0 < t ≤ n` about the four
corners. The two homogenized guides have the same true vertices, each at distance at least `a₀ t`
from the closure of the remaining changed region and with the same incident labels in both
guides.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:375–387`. -/
theorem isTrueVertex_central_treated {t : ℝ} (ht : 0 < t) (htn : t ≤ R.n) (c : ℝ × ℝ) :
    (IsTrueVertex (homogenize (cornerTreated R.n t) R.oldLabel R.guide) c ↔
        IsTrueVertex (homogenize (cornerTreated R.n t) R.oldLabel R.centralGuide) c) ∧
      (IsTrueVertex (homogenize (cornerTreated R.n t) R.oldLabel R.guide) c →
        incidentLabels (homogenize (cornerTreated R.n t) R.oldLabel R.guide) c =
          incidentLabels (homogenize (cornerTreated R.n t) R.oldLabel R.centralGuide) c ∧
        ∀ y ∈ closure {p | homogenize (cornerTreated R.n t) R.oldLabel R.guide p ≠
            homogenize (cornerTreated R.n t) R.oldLabel R.centralGuide p},
          angularConstant * t ≤ dist c y) := by
  set Ut := cornerTreated R.n t
  set fb := homogenize Ut R.oldLabel R.guide
  set fa := homogenize Ut R.oldLabel R.centralGuide
  set S := {p | fb p ≠ fa p}
  set U := thickening (angularConstant * t) S
  have hδ : 0 < angularConstant * t := mul_pos angularConstant_pos ht
  have hfb : ∀ p ∈ U, fb p = R.oldLabel := by
    intro p hp
    obtain ⟨y, hy, hpy⟩ := mem_thickening_iff.1 hp
    by_contra hne
    have h := R.floor_central htn (subset_closure hy) hne
    have : angularConstant * t ≤ angularConstant * max t (min R.n (cornerMarkDist R.n y)) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) angularConstant_pos.le
    rw [dist_comm] at h
    linarith
  have hmem : ∀ p ∈ U, fb p ∈ ({R.oldLabel, R.finalLabel} : Set ι) ∧
      fa p ∈ ({R.oldLabel, R.finalLabel} : Set ι) := by
    intro p hp
    refine ⟨Or.inl (hfb p hp), ?_⟩
    by_cases hpS : p ∈ S
    · have hpU : p ∉ Ut := fun h => hpS (show fb p = fa p by
        simp only [fb, fa, homogenize_of_mem h])
      have hc : p ∈ centralRegion R.n := by
        by_contra hc
        exact hpS (show fb p = fa p by
          simp only [fb, fa, homogenize_of_notMem hpU, R.centralGuide_of_notMem hc])
      simp only [fa, homogenize_of_notMem hpU, R.centralGuide_of_mem hc]
      exact Or.inr rfl
    · exact Or.inl ((not_not.1 hpS).symm.trans (hfb p hp))
  obtain ⟨hiff, hinc⟩ := isTrueVertex_iff_of_two_labels isOpen_thickening
    (closure_subset_thickening hδ S) (fun p hp => (hmem p hp).1) (fun p hp => (hmem p hp).2) c
  refine ⟨hiff, fun hv => ⟨(hinc hv).2, fun y hy => ?_⟩⟩
  refine le_dist_of_mem_closure (fun z hz => ?_) hy
  by_contra hlt
  exact (hinc hv).1 (mem_thickening_iff.2 ⟨z, hz, not_le.1 hlt⟩)

/-! ### The lens exchange after the point treatment -/

/-- The main guide with the starting word of the construction along `e`, homogenized to `C_e` on
the treated squares of radius `t` about the endpoints of `e`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:334–336`. -/
noncomputable def treatedStartMain (t : ℝ) (E : List SquareEdge) (e : SquareEdge) :
    ℝ × ℝ → ι :=
  homogenize (edgeTreated R.n e t) (R.nbrLabel e)
    (R.mainGuide E e (edgeStartWord R.oldLabel R.finalLabel (R.nbrLabel e)))

/-- The auxiliary guide with the auxiliary word `eq:geometry-aux-word` along `e`, homogenized to
`C_e` on the treated squares of radius `t` about the endpoints of `e`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:334–336`. -/
noncomputable def treatedAux (t : ℝ) (e : SquareEdge) : ℝ × ℝ → ι :=
  homogenize (edgeTreated R.n e t) (R.nbrLabel e)
    (R.auxGuide e (auxWord R.oldLabel R.finalLabel (R.nbrLabel e)))

/-- **The common corridor of the treated exchange.** On the open neighborhood of radius `a₀ t` of
the lens boundary both treated sheets are `C_e`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:389–397`. -/
theorem exchange_corridor {t : ℝ} (htn : t ≤ R.n) (E : List SquareEdge) (e : SquareEdge)
    {p : ℝ × ℝ} (hp : p ∈ thickening (angularConstant * t) (frontier (edgeLens R.n e))) :
    R.treatedStartMain t E e p = R.nbrLabel e ∧ R.treatedAux t e p = R.nbrLabel e := by
  obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.1 hp
  by_contra hne
  have hmem : p ∈ {p | R.treatedStartMain t E e p ≠ R.nbrLabel e ∨
      R.treatedAux t e p ≠ R.nbrLabel e} := not_and_or.1 hne
  have h := R.floor_exchange htn E e (subset_closure hmem) hz
  have : angularConstant * t ≤ angularConstant * max t (min R.n (edgeMarkDist R.n e p)) :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) angularConstant_pos.le
  linarith

open Classical in
/-- **No new true vertex in the treated exchange.** Exchange the two treated sheets of the
construction along `e` on the lens `Y`. Inside `Y` the new main guide has exactly the true
vertices of the auxiliary sheet, and outside `Y` those of the main sheet, with the same incident
labels there; symmetrically for the new auxiliary guide. So the exchange carries each true vertex
with its whole hole and tag, and splices no sectors of the two sheets.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:389–398, 415–419`. -/
theorem isTrueVertex_exchange_treated {t : ℝ} (ht : 0 < t) (htn : t ≤ R.n)
    (E : List SquareEdge) (e : SquareEdge) (c : ℝ × ℝ) :
    ((IsTrueVertex (fun p => if p ∈ edgeLens R.n e then R.treatedAux t e p
          else R.treatedStartMain t E e p) c ↔
        (c ∈ edgeLens R.n e ∧ IsTrueVertex (R.treatedAux t e) c) ∨
          (c ∉ edgeLens R.n e ∧ IsTrueVertex (R.treatedStartMain t E e) c)) ∧
      (c ∈ edgeLens R.n e → IsTrueVertex (R.treatedAux t e) c →
        incidentLabels (fun p => if p ∈ edgeLens R.n e then R.treatedAux t e p
          else R.treatedStartMain t E e p) c = incidentLabels (R.treatedAux t e) c) ∧
      (c ∉ edgeLens R.n e → IsTrueVertex (R.treatedStartMain t E e) c →
        incidentLabels (fun p => if p ∈ edgeLens R.n e then R.treatedAux t e p
          else R.treatedStartMain t E e p) c = incidentLabels (R.treatedStartMain t E e) c)) ∧
    ((IsTrueVertex (fun p => if p ∈ edgeLens R.n e then R.treatedStartMain t E e p
          else R.treatedAux t e p) c ↔
        (c ∈ edgeLens R.n e ∧ IsTrueVertex (R.treatedStartMain t E e) c) ∨
          (c ∉ edgeLens R.n e ∧ IsTrueVertex (R.treatedAux t e) c)) ∧
      (c ∈ edgeLens R.n e → IsTrueVertex (R.treatedStartMain t E e) c →
        incidentLabels (fun p => if p ∈ edgeLens R.n e then R.treatedStartMain t E e p
          else R.treatedAux t e p) c = incidentLabels (R.treatedStartMain t E e) c) ∧
      (c ∉ edgeLens R.n e → IsTrueVertex (R.treatedAux t e) c →
        incidentLabels (fun p => if p ∈ edgeLens R.n e then R.treatedStartMain t E e p
          else R.treatedAux t e p) c = incidentLabels (R.treatedAux t e) c)) := by
  have hδ : 0 < angularConstant * t := mul_pos angularConstant_pos ht
  have hU := self_subset_thickening hδ (frontier (edgeLens R.n e))
  exact ⟨isTrueVertex_piecewise_iff isOpen_thickening hU
      (fun p hp => (R.exchange_corridor htn E e hp).1)
      (fun p hp => (R.exchange_corridor htn E e hp).2) c,
    isTrueVertex_piecewise_iff isOpen_thickening hU
      (fun p hp => (R.exchange_corridor htn E e hp).2)
      (fun p hp => (R.exchange_corridor htn E e hp).1) c⟩

end RepaintingBaseline

/-! ### Tags -/

section Tags

variable {X ι : Type*} [TopologicalSpace X] {f g : X → ι} {c : X} {ph l : ι}

/-- A label `l` may hold the tag of the true vertex `c` of a guide `f`: it is an incident label
other than the placeholder `ph`. A tag rule chooses one such label at every true vertex, for
example by a fixed order on the block parties.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:119–125, 610`. -/
def IsTagHolder (f : X → ι) (ph : ι) (c : X) (l : ι) : Prop :=
  l ∈ incidentLabels f c ∧ l ≠ ph

/-- **A tag holder exists.** A true vertex has at least two incident labels other than the
placeholder.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:119–123`. -/
theorem IsTrueVertex.exists_isTagHolder (h : IsTrueVertex f c) (ph : ι) :
    ∃ l₁ l₂ : ι, l₁ ≠ l₂ ∧ IsTagHolder f ph c l₁ ∧ IsTagHolder f ph c l₂ := by
  obtain ⟨l₁, l₂, l₃, h12, h13, h23, h1, h2, h3⟩ := h
  by_cases hp1 : l₁ = ph
  · subst hp1
    exact ⟨l₂, l₃, h23, ⟨h2, Ne.symm h12⟩, h3, Ne.symm h13⟩
  · by_cases hp2 : l₂ = ph
    · subst hp2
      exact ⟨l₁, l₃, h13, ⟨h1, hp1⟩, h3, Ne.symm h23⟩
    · exact ⟨l₁, l₂, h12, ⟨h1, hp1⟩, h2, hp2⟩

/-- Guides with the same incident labels at `c` have the same tag holders there; in particular
the bulk operations keep the tag holders (`BandOperation.isTrueVertex_treated`,
`RepaintingBaseline.isTrueVertex_central_treated`,
`RepaintingBaseline.isTrueVertex_exchange_treated`).

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:381–382, 417–419`. -/
theorem isTagHolder_congr (h : incidentLabels f c = incidentLabels g c) :
    IsTagHolder f ph c l ↔ IsTagHolder g ph c l := by
  rw [IsTagHolder, IsTagHolder, h]

/-- If every value of a guide is the placeholder or lies in `s`, so does every tag holder. -/
theorem IsTagHolder.mem_of_forall {s : Set ι} (hf : ∀ p, f p ∈ insert ph s)
    (h : IsTagHolder f ph c l) : l ∈ s := by
  obtain ⟨p, rfl⟩ := mem_range_of_mem_incidentLabels h.1
  exact (hf p).resolve_left h.2

end Tags

section LevelTags

variable {ι : Type*} (M : ℤ) (old new : ℤ × ℤ → ι) (ph : ι)

/-- **Tags at the start of a level.** At the start of the pass to level `n` only old labels, of
the `2n`-blocks, hold tags.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-active-labels`,
`06-geometry.tex:601–610`. -/
theorem isTagHolder_levelStart {n : ℝ} {c : ℝ × ℝ} {l : ι}
    (h : IsTagHolder (blockGuide n (levelLabels M old new ph ∅)) ph c l) : l ∈ range old :=
  h.mem_of_forall fun _ => levelLabels_empty_mem M old new ph _

/-- **Tags during a level.** During the pass to level `n` only old and new labels hold tags.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-active-labels`,
`06-geometry.tex:601–610`. -/
theorem isTagHolder_level {n : ℝ} (done : Set (ℤ × ℤ)) {c : ℝ × ℝ} {l : ι}
    (h : IsTagHolder (blockGuide n (levelLabels M old new ph done)) ph c l) :
    l ∈ range old ∪ range new :=
  h.mem_of_forall fun _ => levelLabels_mem M old new ph done _

/-- **Tags at the end of a level.** Once every block of the root square is repainted, only new
labels, of the `n`-blocks, hold tags: a party of side `2n` has disappeared from every main tag as
well as from every main guide region.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-active-labels`,
`06-geometry.tex:601–614`. -/
theorem isTagHolder_levelEnd {n : ℝ} {done : Set (ℤ × ℤ)} (hd : {Q | InRoot M Q} ⊆ done)
    {c : ℝ × ℝ} {l : ι}
    (h : IsTagHolder (blockGuide n (levelLabels M old new ph done)) ph c l) : l ∈ range new :=
  h.mem_of_forall fun _ => levelLabels_mem_of_subset M old new ph hd _

end LevelTags

end TNLean.PEPS.Approximation
