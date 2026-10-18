/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.BeltFacetSeparation
import TNLean.PEPS.AreaLaw.Geometry.BirthSeparationFan

/-!
# Birth separation of a replacement from its local comparison regions

Normalize the removal square of a replacement to `Q = [-1, 1]²`. A same-label
region compared with its closed birth `B` near the parent mark lies either in
the exterior trapezoid of a wedge of the opposite exterior label, or in the
birth of a distinct run with the same exterior label at the same parent.

*Separation away from marks.* For each pair of a triangle of `B` and one such
comparison piece, the two compact sets meet only at integer marks. Pairs of
points not lying together in an open quarter-square about one mark therefore
stay at distance at least a positive `η`. The manuscript takes `η` as a minimum
over the finitely many pairs; since all these sets are cut out by belt facets,
`η = birthSeparationConstant = 1/28` works for every pair.

*Angular estimate at marks.* Inside a quarter-square about a mark `q` the two
sets are quarter-sectorial and meet only at `q`, so their points satisfy
`‖x - y‖ ≥ ‖y - q‖ / 2`.

*The following trim.* Every one of the nine marks is a mark of the next
generation. Its removal square, of half-side `d(u) ≥ u^ρ₀ / 2`, is cut from
every compared region. A remaining point near a mark is hence at distance at
least `u^ρ₀ / 2` from it, which with the angular estimate gives `u^ρ₀ / 4`.

The resulting statement fixes the constant `c₁ = 1/28` before any repair data
and gives `dist(B, Y) ≥ c₁ u^ρ₀` for every set `Y` satisfying the local bound near
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
    obtain ⟨rfl, rfl⟩ := eq_of_norm_sub_intPoint_le_quarter hz
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

/-- The outer facet at level `L` and the two radial facets of the triangle of
slot `s`.
Source: area-law Section 11, lines 404–417 and 573–659. -/
def repairTriangleFacets (L : ℤ) (s : RepairFanSlot) : Set (ℤ × ℤ × ℤ) :=
  {((repairSlotFacets s).1.1, (repairSlotFacets s).1.2, L),
    ((repairSlotFacets s).2.1.1, (repairSlotFacets s).2.1.2, 0),
    ((repairSlotFacets s).2.2.1, (repairSlotFacets s).2.2.2, 0)}

theorem repairNormTriangle_eq_facetPolygon (L : ℤ) (s : RepairFanSlot) :
    repairNormTriangle L s = facetPolygon (repairTriangleFacets L s) := by
  ext x
  simp [repairNormTriangle, mem_facetPolygon, repairTriangleFacets, intHalfPlane, and_assoc]

theorem repairExteriorTrapezoid_eq_facetPolygon (s : RepairFanSlot) :
    repairExteriorTrapezoid s = facetPolygon (insert
      (-(repairSlotFacets s).1.1, -(repairSlotFacets s).1.2, -1) (repairTriangleFacets 2 s)) := by
  ext x
  simp [repairExteriorTrapezoid, repairNormTriangle, mem_facetPolygon, repairTriangleFacets,
    intHalfPlane]
  tauto

/-- The facets of the normalized fan triangles and exterior trapezoids are belt
facets: axis outer normals at integer levels and radial facets at level `0`.
Source: area-law Section 11, lines 404–417, with `geometry:initial-stars`,
lines 352–359. -/
theorem isBeltFacet_of_mem_repairTriangleFacets {L : ℤ} {s : RepairFanSlot}
    {f : ℤ × ℤ × ℤ} (hf : f ∈ repairTriangleFacets L s) : IsBeltFacet f := by
  rcases s with ⟨k, j⟩
  rcases hf with rfl | rfl | rfl <;> fin_cases k <;> fin_cases j <;>
    simp [repairSlotFacets, IsBeltFacet]

theorem isBeltFacet_of_mem_repairTrapezoidFacets {s : RepairFanSlot} {f : ℤ × ℤ × ℤ}
    (hf : f ∈ insert (-(repairSlotFacets s).1.1, -(repairSlotFacets s).1.2, -1)
      (repairTriangleFacets 2 s)) : IsBeltFacet f := by
  rcases hf with rfl | hf
  · rcases s with ⟨k, j⟩
    fin_cases k <;> fin_cases j <;> simp [repairSlotFacets, IsBeltFacet]
  · exact isBeltFacet_of_mem_repairTriangleFacets hf

/-- **Explicit normalized replacement dichotomy.** For every exterior labelling,
every run `C` and every point `y` of the same-label bound, each point `x` of the
normalized birth of `C` is at distance at least `birthSeparationConstant = 1/28`
from `y`, or both lie in an open quarter-square about an integer point `q` with
`‖x - y‖ ≥ ‖y - q‖ / 2`.
Source: area-law Section 11, `geometry:birth-separation`, lines 606–645. -/
theorem repairSameLabel_dichotomy {ι : Type*} (ξ : ι → Fin 2) (σ : RepairFanSlot → ι)
    (C : RepairFanRun ξ σ) : ∀ x ∈ repairNormRunRegion ξ σ C,
      ∀ y ∈ repairSameLabelBound ξ σ C, birthSeparationConstant ≤ ‖x - y‖ ∨ ∃ i j : ℤ,
        ‖x - ((i : ℝ), (j : ℝ))‖ < 1 / 4 ∧ ‖y - ((i : ℝ), (j : ℝ))‖ < 1 / 4 ∧
          ‖y - ((i : ℝ), (j : ℝ))‖ / 2 ≤ ‖x - y‖ := by
  have h (s : RepairFanSlot) (T : Set (ℤ × ℤ × ℤ)) (hT : ∀ f ∈ T, IsBeltFacet f)
      (hXY : ∀ z ∈ repairNormTriangle 1 s, z ∈ facetPolygon T → ∃ i j : ℤ, z = ((i : ℝ), (j : ℝ)))
      (x : ℝ × ℝ) (hx : x ∈ repairNormTriangle 1 s) (y : ℝ × ℝ) (hy : y ∈ facetPolygon T) :
      birthSeparationConstant ≤ ‖x - y‖ ∨ ∃ i j : ℤ,
        ‖x - ((i : ℝ), (j : ℝ))‖ < 1 / 4 ∧ ‖y - ((i : ℝ), (j : ℝ))‖ < 1 / 4 ∧
          ‖y - ((i : ℝ), (j : ℝ))‖ / 2 ≤ ‖x - y‖ := by
    rw [repairNormTriangle_eq_facetPolygon] at hx hXY
    rcases facetPolygon_contact_dichotomy (fun _ ↦ isBeltFacet_of_mem_repairTriangleFacets) hT
      hXY hx hy with hd | ⟨q, hq, hxq, hyq, hang⟩
    · exact .inl hd
    · obtain ⟨i, j, rfl⟩ := hXY q hq.1 hq.2
      exact .inr ⟨i, j, hxq, hyq, hang⟩
  intro x hx y hy
  obtain ⟨s, hs, hxs⟩ : ∃ s ∈ C.supp, x ∈ repairNormTriangle 1 s := by
    simp only [repairNormRunRegion, cellFanRunRegion, Set.mem_iUnion] at hx
    obtain ⟨s, hs, hx⟩ := hx
    exact ⟨s, hs, cellFanPolygon_region_subset_repairNormTriangle s hx⟩
  have hcs := repairExteriorColor_eq_of_mem_supp hs
  rcases hy with hy | hy
  · simp only [Set.mem_iUnion] at hy
    obtain ⟨t, ht, hy⟩ := hy
    have hst : s ≠ t := by rintro rfl; exact ht hcs
    rw [repairExteriorTrapezoid_eq_facetPolygon] at hy
    refine h s _ (fun _ ↦ isBeltFacet_of_mem_repairTrapezoidFacets) (fun z hz hz' ↦ ?_) x hxs y hy
    rw [← repairExteriorTrapezoid_eq_facetPolygon] at hz'
    exact repairNormTriangle_inter_exteriorTrapezoid hst hz hz'
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
    have hyt' := cellFanPolygon_region_subset_repairNormTriangle t hyt
    rw [repairNormTriangle_eq_facetPolygon] at hyt'
    refine h s _ (fun _ ↦ isBeltFacet_of_mem_repairTriangleFacets) (fun z hz hz' ↦ ?_) x hxs y hyt'
    rw [← repairNormTriangle_eq_facetPolygon] at hz'
    exact ⟨0, 0, by rw [repairNormTriangle_inter_eq_zero hst hcons hz hz']; ext <;> simp⟩

/-- **Normalized replacement dichotomy.** There is a fixed `η ∈ (0, 1]` such
that for every exterior labelling, every run `C` and every point `y` of the
same-label bound, each point `x` of the normalized birth of `C` is at distance
at least `η` from `y`, or both lie in an open quarter-square about an integer
point `q` with `‖x - y‖ ≥ ‖y - q‖ / 2`. One may take `η = 1/28`
(`repairSameLabel_dichotomy`).
Source: area-law Section 11, `geometry:birth-separation`, lines 606–645. -/
theorem exists_repairSameLabel_dichotomy :
    ∃ η > 0, η ≤ 1 ∧ ∀ {ι : Type*} (ξ : ι → Fin 2) (σ : RepairFanSlot → ι)
      (C : RepairFanRun ξ σ), ∀ x ∈ repairNormRunRegion ξ σ C,
      ∀ y ∈ repairSameLabelBound ξ σ C, η ≤ ‖x - y‖ ∨ ∃ i j : ℤ,
        ‖x - ((i : ℝ), (j : ℝ))‖ < 1 / 4 ∧ ‖y - ((i : ℝ), (j : ℝ))‖ < 1 / 4 ∧
          ‖y - ((i : ℝ), (j : ℝ))‖ / 2 ≤ ‖x - y‖ :=
  ⟨birthSeparationConstant, birthSeparationConstant_pos, birthSeparationConstant_le_one,
    repairSameLabel_dichotomy⟩

/-! ### Separation after the following trim -/

private theorem intPoint_mem_childOffsets {x : ℝ × ℝ} (hx : ‖x‖ ≤ 1) {i j : ℤ}
    (h : ‖x - ((i : ℝ), (j : ℝ))‖ < 1 / 4) :
    ∃ p : Fin 3 × Fin 3, repairChildOffset p = ((i : ℝ), (j : ℝ)) := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff] at hx
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_lt_iff] at h
  simp only [Prod.fst_sub, Prod.snd_sub] at h
  obtain ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ := And.intro (abs_le.mp hx.1) (abs_le.mp hx.2)
  obtain ⟨⟨c₁, c₂⟩, ⟨d₁, d₂⟩⟩ := And.intro (abs_lt.mp h.1) (abs_lt.mp h.2)
  have hi₁ : (-2 : ℝ) < i := by linarith
  have hi₂ : (i : ℝ) < 2 := by linarith
  have hj₁ : (-2 : ℝ) < j := by linarith
  have hj₂ : (j : ℝ) < 2 := by linarith
  have ei₁ : -2 < i := by exact_mod_cast hi₁
  have ei₂ : i < 2 := by exact_mod_cast hi₂
  have ej₁ : -2 < j := by exact_mod_cast hj₁
  have ej₂ : j < 2 := by exact_mod_cast hj₂
  refine ⟨(⟨(i + 1).toNat, by omega⟩, ⟨(j + 1).toNat, by omega⟩), ?_⟩
  simp only [repairChildOffset]
  ext
  · simp only
    have h := Int.toNat_of_nonneg (show 0 ≤ i + 1 by omega)
    have : (((i + 1).toNat : ℕ) : ℝ) = i + 1 := by exact_mod_cast h
    linarith
  · simp only
    have h := Int.toNat_of_nonneg (show 0 ≤ j + 1 by omega)
    have : (((j + 1).toNat : ℕ) : ℝ) = j + 1 := by exact_mod_cast h
    linarith

/-- **Birth separation of a replacement from its local comparison regions,
with the explicit constant.** Let a replacement run `C` be born in the removal
square of half-side `u ≥ 1` about `v`, and let `Y` be any set satisfying the two
properties of a final actual region of an older or peer identifier of the same
label: near the parent, in the open square of half-side `2u`, its rescaled
points lie in the same-label bound; and it avoids the removal squares of the
nine following marks `v + u q`, each of half-side `d(u)`. Then every point of the
closed birth is at distance at least `c₁ u^ρ₀` from `Y`, with
`c₁ = birthSeparationConstant = 1/28`.
Source: area-law Section 11, `geometry:birth-separation`, lines 573–659. -/
theorem repairBirth_separation {ι : Type*} (ξ : ι → Fin 2) (σ : RepairFanSlot → ι)
    (C : RepairFanRun ξ σ) (v : ℝ × ℝ) {u : ℝ} (hu : 1 ≤ u) (Y : Set (ℝ × ℝ))
    (hloc : ∀ y ∈ Y, ‖y - v‖ < 2 * u → u⁻¹ • (y - v) ∈ repairSameLabelBound ξ σ C)
    (htrim : ∀ y ∈ Y, ∀ p : Fin 3 × Fin 3, y ∉ repairSquare (v + u • repairChildOffset p) u) :
    ∀ x ∈ (fun z ↦ v + u • z) '' repairNormRunRegion ξ σ C, ∀ y ∈ Y,
      birthSeparationConstant * u ^ (Exponents.rho : ℝ) ≤ ‖x - y‖ := by
  have h := repairSameLabel_dichotomy ξ σ C
  have hη := birthSeparationConstant_pos
  have hη4 := birthSeparationConstant_le_quarter
  intro x hx y hy
  obtain ⟨x', hx', rfl⟩ := hx
  have hu0 : 0 < u := by linarith
  have hρ : u ^ (Exponents.rho : ℝ) ≤ u := by
    calc u ^ (Exponents.rho : ℝ) ≤ u ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hu rho_pos_lt_one.2.le
      _ = u := Real.rpow_one u
  have hρ0 : 0 ≤ u ^ (Exponents.rho : ℝ) := Real.rpow_nonneg hu0.le _
  have hc := birthSeparationConstant_le_one
  have hx'n : ‖x'‖ ≤ 1 := by
    simp only [repairNormRunRegion, cellFanRunRegion, Set.mem_iUnion] at hx'
    obtain ⟨s, -, hs⟩ := hx'
    simpa using norm_le_of_mem_repairNormTriangle
      (cellFanPolygon_region_subset_repairNormTriangle s hs)
  have hux : ‖u • x'‖ ≤ u := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hu0]; nlinarith [norm_nonneg x']
  by_cases hfar : 2 * u ≤ ‖y - v‖
  · have : u ≤ ‖v + u • x' - y‖ := by
      have := norm_sub_norm_le (y - v) (u • x')
      rw [show y - v - u • x' = -(v + u • x' - y) by abel, norm_neg] at this
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hc hρ0]
  push Not at hfar
  set y' := u⁻¹ • (y - v)
  have hyy : y = v + u • y' := by
    simp only [y', smul_smul, mul_inv_cancel₀ hu0.ne', one_smul]; abel
  have hxy : v + u • x' - y = u • (x' - y') := by rw [hyy, smul_sub]; abel
  have hnorm : ‖v + u • x' - y‖ = u * ‖x' - y'‖ := by
    rw [hxy, norm_smul, Real.norm_eq_abs, abs_of_pos hu0]
  rcases h x' hx' y' (hloc y hy hfar) with hd | ⟨i, j, hxq, hyq, hang⟩
  · rw [hnorm]
    calc birthSeparationConstant * u ^ (Exponents.rho : ℝ) ≤ birthSeparationConstant * u :=
          mul_le_mul_of_nonneg_left hρ hη.le
      _ ≤ ‖x' - y'‖ * u := mul_le_mul_of_nonneg_right hd hu0.le
      _ = u * ‖x' - y'‖ := mul_comm _ _
  · obtain ⟨p, hp⟩ := intPoint_mem_childOffsets hx'n hxq
    have hout := htrim y hy p
    simp only [repairSquare, Metric.mem_closedBall, dist_eq_norm, not_le] at hout
    have hyq' : y - (v + u • repairChildOffset p) = u • (y' - ((i : ℝ), (j : ℝ))) := by
      rw [hp, hyy, smul_sub]; abel
    rw [hyq', norm_smul, Real.norm_eq_abs, abs_of_pos hu0] at hout
    have hd := half_rpow_le_repairHalfSide hu0
    rw [hnorm]
    have : u * (‖y' - ((i : ℝ), (j : ℝ))‖ / 2) ≤ u * ‖x' - y'‖ :=
      mul_le_mul_of_nonneg_left hang hu0.le
    nlinarith

/-- **Birth separation of a replacement from its local comparison regions.**
There is one fixed `c₁ > 0` with the following property. Let a replacement run
`C` be born in the removal square of half-side `u ≥ 1` about `v`, and let `Y`
be any set satisfying the two properties of a final actual region of an older
or peer identifier of the same label: near the parent, in the open square of
half-side `2u`, its rescaled points lie in the same-label bound; and it avoids
the removal squares of the nine following marks `v + u q`, each of half-side
`d(u)`. Then every point of the closed birth is at distance at least
`c₁ u^ρ₀` from `Y`. One may take `c₁ = 1/28` (`repairBirth_separation`).
Source: area-law Section 11, `geometry:birth-separation`, lines 573–659. -/
theorem exists_repairBirth_separation :
    ∃ c₁ > 0, ∀ {ι : Type*} (ξ : ι → Fin 2) (σ : RepairFanSlot → ι)
      (C : RepairFanRun ξ σ) (v : ℝ × ℝ) {u : ℝ}, 1 ≤ u → ∀ Y : Set (ℝ × ℝ),
      (∀ y ∈ Y, ‖y - v‖ < 2 * u → u⁻¹ • (y - v) ∈ repairSameLabelBound ξ σ C) →
      (∀ y ∈ Y, ∀ p : Fin 3 × Fin 3, y ∉ repairSquare (v + u • repairChildOffset p) u) →
      ∀ x ∈ (fun z ↦ v + u • z) '' repairNormRunRegion ξ σ C, ∀ y ∈ Y,
        c₁ * u ^ (Exponents.rho : ℝ) ≤ ‖x - y‖ :=
  ⟨birthSeparationConstant, birthSeparationConstant_pos, repairBirth_separation⟩

end TNLean.PEPS.AreaLaw.Geometry
