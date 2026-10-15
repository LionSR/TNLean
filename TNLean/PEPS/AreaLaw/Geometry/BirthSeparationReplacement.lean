/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.BirthSeparationFan

/-!
# Birth separation of a replacement from its local comparison regions

Normalize the removal square of a replacement to `Q = [-1, 1]²`. A same-label
region compared with its closed birth `B` near the parent mark lies either in
the exterior trapezoid of a wedge of the opposite exterior label, or in the
birth of a distinct run with the same exterior label at the same parent.

*Compactness away from marks.* For each of the finitely many pairs of a
triangle of `B` and one such comparison piece, the two compact sets meet only
at integer marks. Pairs of points not lying together in an open quarter-square
about one mark therefore stay at distance at least a positive `η`, uniformly
over the finitely many pairs.

*Angular estimate at marks.* Inside a quarter-square about a mark `q` the two
sets are quarter-sectorial and meet only at `q`, so their points satisfy
`‖x - y‖ ≥ ‖y - q‖ / 2`.

*The following trim.* Every one of the nine marks is a mark of the next
generation. Its removal square, of half-side `d(u) ≥ u^ρ₀ / 2`, is cut from
every compared region. A remaining point near a mark is hence at distance at
least `u^ρ₀ / 2` from it, which with the angular estimate gives `u^ρ₀ / 4`.

The resulting statement fixes one constant `c₁ > 0` before any repair data and
gives `dist(B, Y) ≥ c₁ u^ρ₀` for every set `Y` satisfying the local bound near
the parent and avoiding the nine following removal squares. These two
properties of the final actual regions are supplied by the repair induction.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:birth-separation`, lines 573–659.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-! ### Compactness away from integer marks -/

private theorem eq_of_norm_sub_intPoint_le {i j i' j' : ℤ}
    (h : ‖((i : ℝ), (j : ℝ)) - ((i' : ℝ), (j' : ℝ))‖ ≤ 1 / 4) : i = i' ∧ j = j' := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff] at h
  simp only [Prod.fst_sub, Prod.snd_sub] at h
  obtain ⟨h₁, h₂⟩ := h
  have a₁ : |((i - i' : ℤ) : ℝ)| < 1 := by push_cast; linarith
  have a₂ : |((j - j' : ℤ) : ℝ)| < 1 := by push_cast; linarith
  rw [← Int.cast_abs] at a₁ a₂
  have b₁ : |i - i'| < 1 := by exact_mod_cast a₁
  have b₂ : |j - j'| < 1 := by exact_mod_cast a₂
  constructor <;> [skip; skip] <;>
    first | (have := abs_lt.mp b₁; omega) | (have := abs_lt.mp b₂; omega)

/-- **Separation of two compact contact patterns away from marks.** Let two
compact sets meet only in integer points. Then pairs of their points not lying
together in one open quarter-square about an integer point are at distance at
least some `η > 0`.
Source: area-law Section 11, `geometry:birth-separation`, lines 616–625. -/
theorem exists_pos_le_norm_sub_away_from_intPoints {X Y : Set (ℝ × ℝ)}
    (hX : IsCompact X) (hY : IsCompact Y)
    (hXY : ∀ z ∈ X, z ∈ Y → ∃ i j : ℤ, z = ((i : ℝ), (j : ℝ))) :
    ∃ η > 0, ∀ x ∈ X, ∀ y ∈ Y, (∀ i j : ℤ, ¬ (‖x - ((i : ℝ), (j : ℝ))‖ < 1 / 4 ∧
      ‖y - ((i : ℝ), (j : ℝ))‖ < 1 / 4)) → η ≤ ‖x - y‖ := by
  set K : Set ((ℝ × ℝ) × (ℝ × ℝ)) := (X ×ˢ Y) ∩ ⋂ i : ℤ, ⋂ j : ℤ,
    {p | ¬ (‖p.1 - ((i : ℝ), (j : ℝ))‖ < 1 / 4 ∧ ‖p.2 - ((i : ℝ), (j : ℝ))‖ < 1 / 4)}
  have hKc : IsCompact K := by
    refine (hX.prod hY).inter_right (isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ ?_)
    refine (IsOpen.isClosed_compl ?_)
    exact (isOpen_lt (continuous_norm.comp (continuous_fst.sub continuous_const))
      continuous_const).inter
      (isOpen_lt (continuous_norm.comp (continuous_snd.sub continuous_const)) continuous_const)
  rcases K.eq_empty_or_nonempty with hK | hK
  · refine ⟨1, one_pos, fun x hx y hy h ↦ ?_⟩
    have : (x, y) ∈ K :=
      ⟨⟨hx, hy⟩, Set.mem_iInter.mpr fun i ↦ Set.mem_iInter.mpr fun j ↦ (h i j : _)⟩
    rw [hK] at this; exact this.elim
  obtain ⟨p, hp, hmin⟩ := hKc.exists_isMinOn hK
    (continuous_norm.comp (continuous_fst.sub continuous_snd)).continuousOn
  refine ⟨‖p.1 - p.2‖, ?_, fun x hx y hy h ↦ ?_⟩
  · refine norm_pos_iff.mpr fun h0 ↦ ?_
    have he : p.1 = p.2 := sub_eq_zero.mp h0
    obtain ⟨i, j, hij⟩ := hXY p.1 hp.1.1 (he ▸ hp.1.2)
    have := Set.mem_iInter.mp (Set.mem_iInter.mp hp.2 i) j
    apply this
    rw [← he, hij]; simp
  · have hxy : (x, y) ∈ K := ⟨⟨hx, hy⟩, Set.mem_iInter.mpr fun i ↦ Set.mem_iInter.mpr
      fun j ↦ (h i j : _)⟩
    exact hmin hxy

/-- **Local dichotomy for one contact pattern.** Two compact sets, quarter-sectorial
at every integer point and meeting only in integer points, have a constant
`η > 0` such that each pair of their points is at distance at least `η` or lies
in an open quarter-square about an integer point `q`, where the angular estimate
`‖x - y‖ ≥ ‖y - q‖ / 2` holds.
Source: area-law Section 11, `geometry:birth-separation`, lines 616–645. -/
theorem exists_pos_contact_dichotomy {X Y : Set (ℝ × ℝ)}
    (hX : IsCompact X) (hY : IsCompact Y)
    (hXs : ∀ i j : ℤ, IsQuarterSectorial ((i : ℝ), (j : ℝ)) X)
    (hYs : ∀ i j : ℤ, IsQuarterSectorial ((i : ℝ), (j : ℝ)) Y)
    (hXY : ∀ z ∈ X, z ∈ Y → ∃ i j : ℤ, z = ((i : ℝ), (j : ℝ))) :
    ∃ η > 0, ∀ x ∈ X, ∀ y ∈ Y, η ≤ ‖x - y‖ ∨ ∃ i j : ℤ,
      ‖x - ((i : ℝ), (j : ℝ))‖ < 1 / 4 ∧ ‖y - ((i : ℝ), (j : ℝ))‖ < 1 / 4 ∧
        ‖y - ((i : ℝ), (j : ℝ))‖ / 2 ≤ ‖x - y‖ := by
  obtain ⟨η, hη, h⟩ := exists_pos_le_norm_sub_away_from_intPoints hX hY hXY
  refine ⟨η, hη, fun x hx y hy ↦ ?_⟩
  by_cases hnear : ∀ i j : ℤ, ¬ (‖x - ((i : ℝ), (j : ℝ))‖ < 1 / 4 ∧
      ‖y - ((i : ℝ), (j : ℝ))‖ < 1 / 4)
  · exact Or.inl (h x hx y hy hnear)
  push Not at hnear
  obtain ⟨i, j, hxq, hyq⟩ := hnear
  refine Or.inr ⟨i, j, hxq, hyq, ?_⟩
  have hcontact : ∀ z ∈ X, z ∈ Y → ‖z - ((i : ℝ), (j : ℝ))‖ ≤ 1 / 4 →
      z = ((i : ℝ), (j : ℝ)) := by
    intro z hzX hzY hz
    obtain ⟨i', j', rfl⟩ := hXY z hzX hzY
    obtain ⟨rfl, rfl⟩ := eq_of_norm_sub_intPoint_le hz
    rfl
  have := half_max_le_norm_sub_of_isQuarterSectorial (hXs i j) (hYs i j) hcontact hx hy
    hxq.le hyq.le
  linarith [le_max_right ‖x - ((i : ℝ), (j : ℝ))‖ ‖y - ((i : ℝ), (j : ℝ))‖]

/-- A positive constant for each member of a finite family, valid also for every
smaller positive constant, gives one common positive constant. -/
theorem exists_pos_forall_of_finite {ι : Type*} [Finite ι] {P : ι → ℝ → Prop}
    (hP : ∀ i, ∃ η > 0, ∀ η' > 0, η' ≤ η → P i η') :
    ∃ η > 0, η ≤ 1 ∧ ∀ i, P i η := by
  choose f hf hP using hP
  have := Fintype.ofFinite ι
  set η := (insert 1 (Finset.univ.image f)).min' (Finset.insert_nonempty _ _)
  have hle : ∀ i, η ≤ f i := fun i ↦
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f (Finset.mem_univ i)))
  have hpos : 0 < η := by
    obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image _ id (Finset.insert_nonempty 1
      (Finset.univ.image f))
    rw [show η = a from le_antisymm (Finset.min'_le _ _ ha)
      (Finset.le_min' _ _ _ fun b hb ↦ hmin b hb)]
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact one_pos
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha; exact hf i
  exact ⟨η, hpos, Finset.min'_le _ _ (Finset.mem_insert_self _ _),
    fun i ↦ hP i η hpos (hle i)⟩

/-! ### The normalized replacement comparison -/

/-- The normalized closed birth of a replacement run: the union of its closed
fan triangles in `[-1, 1]²`.
Source: area-law Section 11, lines 404–417 and 558–561. -/
abbrev repairNormRunRegion {ι : Type*} (ξ : ι → Fin 2) (σ : RepairFanSlot → ι)
    (C : RepairFanRun ξ σ) : Set (ℝ × ℝ) :=
  cellFanRunRegion (-1, -1) 1 (0, 0) repairFanSplit (repairExteriorColor ξ σ) C

/-- The normalized local bound for the same-label regions compared with the
birth of the run `C`, inside the doubled square `[-2, 2]²`: the exterior
trapezoids of the wedges of the opposite exterior label, which contain the old
remnants after the removal of `Q`, and the births of the other runs with the
same exterior label at the same parent, which contain the peer replacements.
Source: area-law Section 11, `geometry:birth-separation`, lines 584–591 and
606–615. -/
def repairSameLabelBound {ι : Type*} (ξ : ι → Fin 2) (σ : RepairFanSlot → ι)
    (C : RepairFanRun ξ σ) : Set (ℝ × ℝ) :=
  (⋃ t, ⋃ (_ : repairExteriorColor ξ σ t ≠ repairFanRunExteriorColor ξ σ C),
      repairExteriorTrapezoid t) ∪
    ⋃ C', ⋃ (_ : C' ≠ C ∧ repairFanRunExteriorColor ξ σ C' = repairFanRunExteriorColor ξ σ C),
      repairNormRunRegion ξ σ C'

theorem repairExteriorColor_eq_of_mem_supp {ι : Type*} {ξ : ι → Fin 2}
    {σ : RepairFanSlot → ι} {C : RepairFanRun ξ σ} {s : RepairFanSlot} (hs : s ∈ C.supp) :
    repairExteriorColor ξ σ s = repairFanRunExteriorColor ξ σ C := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hs
  subst hs
  rfl

/-- **Normalized replacement dichotomy.** There is a fixed `η ∈ (0, 1]` such
that for every exterior labelling, every run `C` and every point `y` of the
same-label bound, each point `x` of the normalized birth of `C` is at distance
at least `η` from `y`, or both lie in an open quarter-square about an integer
point `q` with `‖x - y‖ ≥ ‖y - q‖ / 2`.
Source: area-law Section 11, `geometry:birth-separation`, lines 606–645. -/
theorem exists_repairSameLabel_dichotomy :
    ∃ η > 0, η ≤ 1 ∧ ∀ {ι : Type*} (ξ : ι → Fin 2) (σ : RepairFanSlot → ι)
      (C : RepairFanRun ξ σ), ∀ x ∈ repairNormRunRegion ξ σ C,
      ∀ y ∈ repairSameLabelBound ξ σ C, η ≤ ‖x - y‖ ∨ ∃ i j : ℤ,
        ‖x - ((i : ℝ), (j : ℝ))‖ < 1 / 4 ∧ ‖y - ((i : ℝ), (j : ℝ))‖ < 1 / 4 ∧
          ‖y - ((i : ℝ), (j : ℝ))‖ / 2 ≤ ‖x - y‖ := by
  let Y : RepairFanSlot × RepairFanSlot × Bool → Set (ℝ × ℝ) := fun p ↦
    if p.2.2 then repairExteriorTrapezoid p.2.1 else repairNormTriangle 1 p.2.1
  let V : RepairFanSlot × RepairFanSlot × Bool → Prop := fun p ↦
    if p.2.2 then p.1 ≠ p.2.1 else p.1 ≠ p.2.1 ∧ ¬ RepairSlotConsecutive p.1 p.2.1
  let P : RepairFanSlot × RepairFanSlot × Bool → ℝ → Prop := fun p η ↦ V p →
    ∀ x ∈ repairNormTriangle 1 p.1, ∀ y ∈ Y p, η ≤ ‖x - y‖ ∨ ∃ i j : ℤ,
      ‖x - ((i : ℝ), (j : ℝ))‖ < 1 / 4 ∧ ‖y - ((i : ℝ), (j : ℝ))‖ < 1 / 4 ∧
        ‖y - ((i : ℝ), (j : ℝ))‖ / 2 ≤ ‖x - y‖
  have hP : ∀ p, ∃ η > 0, ∀ η' > 0, η' ≤ η → P p η' := by
    rintro ⟨s, t, b⟩
    by_cases hV : V (s, t, b)
    · have hYc : IsCompact (Y (s, t, b)) := by
        cases b
        · exact isCompact_repairNormTriangle 1 t
        · exact isCompact_repairExteriorTrapezoid t
      have hYs : ∀ i j : ℤ, IsQuarterSectorial ((i : ℝ), (j : ℝ)) (Y (s, t, b)) := by
        cases b
        · exact isQuarterSectorial_repairNormTriangle 1 t
        · exact isQuarterSectorial_repairExteriorTrapezoid t
      have hXY : ∀ z ∈ repairNormTriangle 1 s, z ∈ Y (s, t, b) →
          ∃ i j : ℤ, z = ((i : ℝ), (j : ℝ)) := by
        intro z hz hz'
        cases b
        · exact ⟨0, 0, by rw [repairNormTriangle_inter_eq_zero hV.1 hV.2 hz hz']; ext <;> simp⟩
        · exact repairNormTriangle_inter_exteriorTrapezoid hV hz hz'
      obtain ⟨η, hη, h⟩ := exists_pos_contact_dichotomy (isCompact_repairNormTriangle 1 s)
        hYc (isQuarterSectorial_repairNormTriangle 1 s) hYs hXY
      refine ⟨η, hη, fun η' _ hη' _ x hx y hy ↦ ?_⟩
      rcases h x hx y hy with h | h
      · exact Or.inl (hη'.trans h)
      · exact Or.inr h
    · exact ⟨1, one_pos, fun _ _ _ hV' ↦ (hV hV').elim⟩
  obtain ⟨η, hη, hη1, h⟩ := exists_pos_forall_of_finite hP
  refine ⟨η, hη, hη1, fun ξ σ C x hx y hy ↦ ?_⟩
  obtain ⟨s, hs, hxs⟩ : ∃ s ∈ C.supp, x ∈ repairNormTriangle 1 s := by
    simp only [repairNormRunRegion, cellFanRunRegion, Set.mem_iUnion] at hx
    obtain ⟨s, hs, hx⟩ := hx
    exact ⟨s, hs, cellFanPolygon_region_subset_repairNormTriangle s hx⟩
  have hcs := repairExteriorColor_eq_of_mem_supp hs
  rcases hy with hy | hy
  · simp only [Set.mem_iUnion] at hy
    obtain ⟨t, ht, hy⟩ := hy
    have hst : s ≠ t := by rintro rfl; exact ht hcs
    exact h (s, t, true) hst x hxs y hy
  · simp only [Set.mem_iUnion] at hy
    obtain ⟨C', ⟨hC', hcol⟩, hy⟩ := hy
    simp only [repairNormRunRegion, cellFanRunRegion, Set.mem_iUnion] at hy
    obtain ⟨t, ht, hyt⟩ := hy
    have hct := repairExteriorColor_eq_of_mem_supp ht
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hs ht
    have hst : s ≠ t := by rintro rfl; exact hC' (ht.symm.trans hs)
    have hcons : ¬ RepairSlotConsecutive s t := by
      intro hadj
      refine cellFanRun_adjacent_colors_ne (-1, -1) 1 (0, 0) repairFanSplit _ s t hadj
        (fun he ↦ hC' (ht.symm.trans (he.symm.trans hs))) ?_
      rw [hcs, hct, hcol]
    exact h (s, t, false) ⟨hst, hcons⟩ x hxs y
      (cellFanPolygon_region_subset_repairNormTriangle t hyt)

end TNLean.PEPS.AreaLaw.Geometry
