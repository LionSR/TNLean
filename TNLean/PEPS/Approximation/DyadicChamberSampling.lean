/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicSampledGuides

/-!
# The sampled guides of the source are the readings of the formal guides

A guide of the source is a finite polygonal partition of the plane specified by its open
chambers. A label on a boundary is read by one tie convention: the sampled point is moved by an
arbitrarily small generic vector `v` into an incident chamber, and the label of that chamber is
taken. The formal guides of the schedule are labellings of the whole plane, built from the same
descriptions. This file identifies the two:

* the open chamber of a label of a labelling `f` is the interior of its label region, and the
  guide sampled from the chambers of `f` after `v` takes at `p` the label of the chamber that
  contains `p + ε v` for all small `ε > 0`; a sampled guide is a reading of `f` after `v`;
* every guide of the schedule, the block guide, the unmodified guides of the repainting of a
  block, and these homogenized on finitely many open squares, is constant near every point off a
  set lying in a locally finite family of lines, whose normals belong to an explicit finite set
  `wallNormals`; so its open chambers are the open sets on which it is constant, off a locally
  finite family of segments;
* a displacement `v` parallel to none of these lines leaves them at once along every ray
  `p + ε v`, so the sampled guide of every guide of the schedule after `v` exists, is unique, and
  equals its reading after `v`; the generic displacements are those off finitely many lines
  through the origin, and `(1, 1)` is one of them;
* hence Lemma 7.2 holds for the source's sampled guides, with the same constant `a₀ = 1/5000`.

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: guides, their open polygonal
  chambers and the tie convention (lines 69–80), the edge construction (lines 142–241), and
  Lemma 7.2 `lem:geometry-angular` (lines 243–319).
-/

namespace TNLean.PEPS.Approximation

open Set Metric Filter Topology SquareEdge

/-! ### Guides sampled from open chambers -/

section Sampling

variable {X ι : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]

/-- The guide `g` is sampled from the open chambers of `f` after the displacement `v`: at every
point `p`, for all small `ε > 0`, the point `p + ε v` lies in the open chamber of label `g p`, the
interior of the region of `f` with that label.

The source's open polygonal chambers are modelled as the interiors of the label regions of the
formal labelling `f`. The formal guides agree with the source's descriptions on every open chamber,
merging adjacent chambers with one label does not change the sampled label, and a label confined
to boundaries is never sampled, as the source requires (`06-geometry.tex:77`). What is proved about
the chambers is `HasLineWalls`: the formal guides are constant off a locally finite family of lines.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–77`: "All guides below are
specified by their open polygonal chambers. … move a sampled point by an arbitrarily small generic
vector into an incident chamber … and take the resulting label". -/
def IsChamberSampling (g f : X → ι) (v : X) : Prop :=
  ∀ p, ∀ᶠ ε in 𝓝[>] (0 : ℝ), p + ε • v ∈ interior (f ⁻¹' {g p})

/-- **A sampled guide is a reading.** -/
theorem IsChamberSampling.isDisplacedReading {g f : X → ι} {v : X}
    (h : IsChamberSampling g f v) : IsDisplacedReading g f v :=
  fun p => (h p).mono fun _ hε => (mem_singleton_iff.1 (mem_preimage.1 (interior_subset hε))).symm

/-- Two guides sampled from the chambers of one labelling after one displacement agree. -/
theorem IsChamberSampling.unique {g₁ g₂ f : X → ι} {v : X} (h₁ : IsChamberSampling g₁ f v)
    (h₂ : IsChamberSampling g₂ f v) : g₁ = g₂ :=
  h₁.isDisplacedReading.unique h₂.isDisplacedReading

end Sampling

/-! ### Walls on lines -/

/-- The line `{q | N₁ q₁ + N₂ q₂ = c}` with normal `N`. -/
def normalLine (N : ℝ × ℝ) (c : ℝ) : Set (ℝ × ℝ) := {q | N.1 * q.1 + N.2 * q.2 = c}

/-- The set `Z` lies near every point in finitely many lines with normals in `𝒩`: it lies in a
locally finite family of such lines. -/
def IsLocallyInLines (𝒩 : Set (ℝ × ℝ)) (Z : Set (ℝ × ℝ)) : Prop :=
  ∀ p, ∃ U ∈ 𝓝 p, ∃ F : Set ((ℝ × ℝ) × ℝ), F.Finite ∧ (∀ L ∈ F, L.1 ∈ 𝒩) ∧
    Z ∩ U ⊆ ⋃ L ∈ F, normalLine L.1 L.2

/-- The labelling `f` is constant near every point off a set lying in a locally finite family of
lines with normals in `𝒩`. Every point off these walls lies in an open chamber of `f`, so the
open chambers of `f` are the open sets on which `f` is constant, off a locally finite family of
segments.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–72`: "A guide is a finite
polygonal partition of the ambient plane … specified by their open polygonal chambers". -/
def HasLineWalls {ι : Sort*} (𝒩 : Set (ℝ × ℝ)) (f : ℝ × ℝ → ι) : Prop :=
  ∃ Z, IsLocallyInLines 𝒩 Z ∧ ∀ q ∉ Z, ∀ᶠ y in 𝓝 q, f y = f q

section Lines

variable {𝒩 : Set (ℝ × ℝ)} {Z Z' : Set (ℝ × ℝ)}

theorem IsLocallyInLines.mono (h : IsLocallyInLines 𝒩 Z) (hZ : Z' ⊆ Z) :
    IsLocallyInLines 𝒩 Z' := fun p => by
  obtain ⟨U, hU, F, hF, h𝒩, hs⟩ := h p
  exact ⟨U, hU, F, hF, h𝒩, (inter_subset_inter_left U hZ).trans hs⟩

/-- Lying locally in lines is a local property. -/
theorem IsLocallyInLines.of_local
    (h : ∀ p, ∃ U ∈ 𝓝 p, ∃ Z', IsLocallyInLines 𝒩 Z' ∧ Z ∩ U ⊆ Z') :
    IsLocallyInLines 𝒩 Z := fun p => by
  obtain ⟨U, hU, Z', hZ', hs⟩ := h p
  obtain ⟨U', hU', F, hF, h𝒩, hs'⟩ := hZ' p
  refine ⟨U ∩ U', inter_mem hU hU', F, hF, h𝒩, fun q hq => hs' ⟨hs ⟨hq.1, hq.2.1⟩, hq.2.2⟩⟩

theorem isLocallyInLines_empty : IsLocallyInLines 𝒩 ∅ :=
  fun _ => ⟨univ, univ_mem, ∅, finite_empty, by simp, by simp⟩

theorem isLocallyInLines_normalLine {N : ℝ × ℝ} (hN : N ∈ 𝒩) (c : ℝ) :
    IsLocallyInLines 𝒩 (normalLine N c) := fun _ =>
  ⟨univ, univ_mem, {(N, c)}, finite_singleton _,
    fun L hL => by rw [mem_singleton_iff.1 hL]; exact hN,
    fun _ hq => mem_biUnion (mem_singleton _) hq.1⟩

theorem IsLocallyInLines.union {Z₁ Z₂ : Set (ℝ × ℝ)} (h₁ : IsLocallyInLines 𝒩 Z₁)
    (h₂ : IsLocallyInLines 𝒩 Z₂) : IsLocallyInLines 𝒩 (Z₁ ∪ Z₂) := fun p => by
  obtain ⟨U₁, hU₁, F₁, hF₁, h𝒩₁, hs₁⟩ := h₁ p
  obtain ⟨U₂, hU₂, F₂, hF₂, h𝒩₂, hs₂⟩ := h₂ p
  refine ⟨U₁ ∩ U₂, inter_mem hU₁ hU₂, F₁ ∪ F₂, hF₁.union hF₂,
    fun L hL => hL.elim (h𝒩₁ L) (h𝒩₂ L), ?_⟩
  rintro q ⟨hq | hq, hq₁, hq₂⟩
  · exact biUnion_subset_biUnion_left subset_union_left (hs₁ ⟨hq, hq₁⟩)
  · exact biUnion_subset_biUnion_left subset_union_right (hs₂ ⟨hq, hq₂⟩)

theorem isLocallyInLines_iUnion {α : Type*} [Finite α] {Z : α → Set (ℝ × ℝ)}
    (h : ∀ a, IsLocallyInLines 𝒩 (Z a)) : IsLocallyInLines 𝒩 (⋃ a, Z a) := fun p => by
  choose U hU F hF h𝒩 hs using fun a => h a p
  refine ⟨⋂ a, U a, iInter_mem.2 hU, ⋃ a, F a, finite_iUnion hF, fun L hL => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := mem_iUnion.1 hL
    exact h𝒩 a L ha
  · rintro q ⟨hq, hqU⟩
    obtain ⟨a, ha⟩ := mem_iUnion.1 hq
    exact biUnion_subset_biUnion_left (subset_iUnion F a) (hs a ⟨ha, mem_iInter.1 hqU a⟩)

/-- Translating a set lying locally in lines keeps it so, with the same normals. -/
theorem IsLocallyInLines.preimage_add (h : IsLocallyInLines 𝒩 Z) (o : ℝ × ℝ) :
    IsLocallyInLines 𝒩 ((· + o) ⁻¹' Z) := fun p => by
  obtain ⟨U, hU, F, hF, h𝒩, hs⟩ := h (p + o)
  refine ⟨(· + o) ⁻¹' U, (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds hU,
    (fun L => (L.1, L.2 - (L.1.1 * o.1 + L.1.2 * o.2))) '' F, hF.image _, ?_, ?_⟩
  · rintro _ ⟨L, hL, rfl⟩
    exact h𝒩 L hL
  · rintro q ⟨hqZ, hqU⟩
    obtain ⟨L, hL, hm⟩ := mem_iUnion₂.1 (hs ⟨hqZ, hqU⟩)
    refine mem_iUnion₂.2 ⟨_, mem_image_of_mem _ hL, ?_⟩
    simp only [normalLine, mem_ofPred_eq, Prod.fst_add, Prod.snd_add] at hm ⊢
    linear_combination hm

/-- A positive small parameter eventually avoids any given value. -/
private theorem eventually_ne_nhdsGT_zero (a : ℝ) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≠ a := by
  rcases eq_or_ne a 0 with rfl | ha
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε) using hε.ne'
  · exact nhdsWithin_le_nhds (eventually_ne_nhds ha.symm)

/-- **The ray leaves the walls at once.** If `v` is parallel to none of the lines with normals in
`𝒩`, then for every point `p` the point `p + ε v` avoids a set lying locally in such lines for
all small `ε > 0`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:73–75`. -/
theorem IsLocallyInLines.eventually_notMem (hZ : IsLocallyInLines 𝒩 Z) {v : ℝ × ℝ}
    (hv : ∀ N ∈ 𝒩, N.1 * v.1 + N.2 * v.2 ≠ 0) (p : ℝ × ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), p + ε • v ∉ Z := by
  obtain ⟨U, hU, F, hF, h𝒩, hs⟩ := hZ p
  have hline : ∀ L ∈ F, ∀ᶠ ε in 𝓝[>] (0 : ℝ), p + ε • v ∉ normalLine L.1 L.2 := by
    intro L hL
    have hN := hv L.1 (h𝒩 L hL)
    filter_upwards [eventually_ne_nhdsGT_zero
      ((L.2 - (L.1.1 * p.1 + L.1.2 * p.2)) / (L.1.1 * v.1 + L.1.2 * v.2))] with ε hε hm
    refine hε ((eq_div_iff hN).2 ?_)
    simp only [normalLine, mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] at hm
    linear_combination hm
  filter_upwards [tendsto_add_smul_nhdsGT p v hU, (hF.eventually_all).2 hline] with ε hεU hε hεZ
  obtain ⟨L, hL, hm⟩ := mem_iUnion₂.1 (hs ⟨hεZ, hεU⟩)
  exact hε L hL hm

end Lines

/-! ### Sampled guides are readings -/

section Readings

variable {𝒩 : Set (ℝ × ℝ)} {ι : Type*} {f g : ℝ × ℝ → ι} {v : ℝ × ℝ}

/-- **The sampled guide is the reading.** For a labelling constant off walls on lines with
normals in `𝒩`, and a displacement parallel to none of these lines, a guide is sampled from the
open chambers of `f` after `v` exactly when it reads `f` after `v`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80`. -/
theorem HasLineWalls.isChamberSampling_iff (hf : HasLineWalls 𝒩 f)
    (hv : ∀ N ∈ 𝒩, N.1 * v.1 + N.2 * v.2 ≠ 0) :
    IsChamberSampling g f v ↔ IsDisplacedReading g f v := by
  refine ⟨IsChamberSampling.isDisplacedReading, fun h p => ?_⟩
  obtain ⟨Z, hZ, hloc⟩ := hf
  filter_upwards [h p, hZ.eventually_notMem hv p] with ε e hε
  rw [e]
  exact mem_interior_iff_mem_nhds.2 (hloc _ hε)

/-- **The sampled guide exists.** A labelling constant off walls on lines with normals in `𝒩`
and eventually constant along rays has a guide sampled from its open chambers after every
displacement parallel to none of these lines.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80`. -/
theorem HasLineWalls.exists_isChamberSampling (hf : HasLineWalls 𝒩 f) (hr : IsRayConstant f)
    (hv : ∀ N ∈ 𝒩, N.1 * v.1 + N.2 * v.2 ≠ 0) : ∃ g, IsChamberSampling g f v := by
  obtain ⟨g, hg⟩ := hr.exists_isDisplacedReading v
  exact ⟨g, (hf.isChamberSampling_iff hv).2 hg⟩

end Readings

/-! ### Labellings with walls on lines -/

section Walls

variable {𝒩 : Set (ℝ × ℝ)} {ι κ μ : Sort*}

theorem hasLineWalls_const (c : ι) : HasLineWalls 𝒩 fun _ => c :=
  ⟨∅, isLocallyInLines_empty, fun _ _ => Eventually.of_forall fun _ => rfl⟩

theorem HasLineWalls.comp {f : ℝ × ℝ → ι} (h : HasLineWalls 𝒩 f) (F : ι → κ) :
    HasLineWalls 𝒩 fun q => F (f q) := by
  obtain ⟨Z, hZ, hl⟩ := h
  exact ⟨Z, hZ, fun q hq => (hl q hq).mono fun y hy => by dsimp only; rw [hy]⟩

theorem HasLineWalls.comp₂ {f : ℝ × ℝ → ι} {g : ℝ × ℝ → κ} (hf : HasLineWalls 𝒩 f)
    (hg : HasLineWalls 𝒩 g) (F : ι → κ → μ) : HasLineWalls 𝒩 fun q => F (f q) (g q) := by
  obtain ⟨Z₁, h₁, l₁⟩ := hf
  obtain ⟨Z₂, h₂, l₂⟩ := hg
  refine ⟨Z₁ ∪ Z₂, h₁.union h₂, fun q hq => ?_⟩
  rw [mem_union, not_or] at hq
  filter_upwards [l₁ q hq.1, l₂ q hq.2] with y e₁ e₂
  rw [e₁, e₂]

theorem HasLineWalls.and {P Q : ℝ × ℝ → Prop} (hP : HasLineWalls 𝒩 P) (hQ : HasLineWalls 𝒩 Q) :
    HasLineWalls 𝒩 fun q => P q ∧ Q q :=
  hP.comp₂ hQ And

theorem HasLineWalls.forall {α : Type*} [Finite α] {P : α → ℝ × ℝ → Prop}
    (h : ∀ k, HasLineWalls 𝒩 (P k)) : HasLineWalls 𝒩 fun q => ∀ k, P k q := by
  choose Z hZ hl using h
  refine ⟨⋃ k, Z k, isLocallyInLines_iUnion hZ, fun q hq => ?_⟩
  simp only [mem_iUnion, not_exists] at hq
  filter_upwards [eventually_all.2 fun k => hl k q (hq k)] with y hy
  exact propext (forall_congr' fun k => by rw [hy k])

theorem HasLineWalls.ite {P : ℝ × ℝ → Prop} {inst : DecidablePred P} (hP : HasLineWalls 𝒩 P)
    {f g : ℝ × ℝ → ι} (hf : HasLineWalls 𝒩 f) (hg : HasLineWalls 𝒩 g) :
    HasLineWalls 𝒩 fun q => if P q then f q else g q := by
  obtain ⟨Z₁, h₁, l₁⟩ := hP
  obtain ⟨Z₂, h₂, l₂⟩ := hf
  obtain ⟨Z₃, h₃, l₃⟩ := hg
  refine ⟨Z₁ ∪ Z₂ ∪ Z₃, (h₁.union h₂).union h₃, fun q hq => ?_⟩
  simp only [mem_union, not_or] at hq
  filter_upwards [l₁ q hq.1.1, l₂ q hq.1.2, l₃ q hq.2] with y e₁ e₂ e₃
  by_cases h : P q
  · rw [ite_eq_left (by rw [e₁]; exact h), ite_eq_left h, e₂]
  · rw [ite_eq_right (by rw [e₁]; exact h), ite_eq_right h, e₃]

/-- Translating the argument keeps the walls on lines with the same normals. -/
theorem HasLineWalls.comp_add {f : ℝ × ℝ → ι} (h : HasLineWalls 𝒩 f) (o : ℝ × ℝ) :
    HasLineWalls 𝒩 fun q => f (q + o) := by
  obtain ⟨Z, hZ, hl⟩ := h
  exact ⟨_, hZ.preimage_add o, fun q hq =>
    ((continuous_id.add continuous_const).tendsto q).eventually (hl (q + o) hq)⟩

/-- Moving a guide keeps its walls on lines with the same normals. -/
theorem HasLineWalls.shiftGuide {ι : Type*} {f : ℝ × ℝ → ι} (h : HasLineWalls 𝒩 f)
    (o : ℝ × ℝ) : HasLineWalls 𝒩 (shiftGuide o f) := by
  unfold Approximation.shiftGuide
  simpa only [sub_eq_add_neg] using h.comp_add (-o)

/-- A strict inequality between continuous functions is constant off the set where they agree. -/
theorem hasLineWalls_lt {φ ψ : ℝ × ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hZ : IsLocallyInLines 𝒩 {q | φ q = ψ q}) : HasLineWalls 𝒩 fun q => φ q < ψ q := by
  refine ⟨_, hZ, fun q hq => ?_⟩
  rcases lt_or_gt_of_ne hq with h | h
  · filter_upwards [(hφ.tendsto q).eventually_lt (hψ.tendsto q) h] with y hy
    exact propext ⟨fun _ => h, fun _ => hy⟩
  · filter_upwards [(hψ.tendsto q).eventually_lt (hφ.tendsto q) h] with y hy
    exact propext ⟨fun h' => absurd h' (not_lt.2 hy.le), fun h' => absurd h' (not_lt.2 h.le)⟩

/-- The integer part of a continuous function is constant off the set where it is an integer. -/
theorem hasLineWalls_floor {φ : ℝ × ℝ → ℝ} (hφ : Continuous φ)
    (hZ : IsLocallyInLines 𝒩 {q | ∃ k : ℤ, φ q = k}) : HasLineWalls 𝒩 fun q => ⌊φ q⌋ := by
  refine ⟨_, hZ, fun q hq => ?_⟩
  have hlt : (⌊φ q⌋ : ℝ) < φ q :=
    (Int.floor_le _).lt_of_ne fun h => hq ⟨⌊φ q⌋, h.symm⟩
  filter_upwards [(hφ.tendsto q).eventually (Ioo_mem_nhds hlt (Int.lt_floor_add_one (φ q)))]
    with y hy
  exact Int.floor_eq_iff.2 ⟨hy.1.le, hy.2⟩

end Walls

/-! ### The walls of the schedule -/

/-- The thresholds of the normal ratio at which a guide of the schedule or a band-update region
can have a boundary: the boundaries `-8` and `2` of the band-update region, the interfaces
`-6, …, -1, 0, 1` of the normal words, and `0` for the edges themselves and the grid lines.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:142–221`. -/
def wallThresholds : Set ℝ := {-8, -6, -5, -4, -3, -2, -1, 0, 1, 2}

/-- The normals `(±t, 1000)` and `(1000, ±t)`, `t` a threshold, of the lines that carry the walls
of the guides of the schedule: in the edge coordinates `(s, d)` of a square of side `n` the
interface curve `x = t` of a band is `1000 d = t min(s, n - s)`, a union of two segments, and the
edges, the grid lines and the sides of the treated squares are the lines with `t = 0`. -/
def wallNormals : Set (ℝ × ℝ) :=
  {N | ∃ t ∈ wallThresholds, N = (t, 1000) ∨ N = (-t, 1000) ∨ N = (1000, t) ∨ N = (1000, -t)}

/-- A displacement is generic if it is parallel to none of the walls of the guides of the schedule:
it avoids finitely many lines through the origin.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:73–77`: "move a sampled point
by an arbitrarily small generic vector … choose a sufficiently small generic displacement after
all the finitely many guides are specified". -/
def IsGenericDisplacement (v : ℝ × ℝ) : Prop := ∀ N ∈ wallNormals, N.1 * v.1 + N.2 * v.2 ≠ 0

theorem mem_wallNormals {t : ℝ} (ht : t ∈ wallThresholds) :
    (t, (1000 : ℝ)) ∈ wallNormals ∧ (-t, (1000 : ℝ)) ∈ wallNormals ∧
      ((1000 : ℝ), t) ∈ wallNormals ∧ ((1000 : ℝ), -t) ∈ wallNormals :=
  ⟨⟨t, ht, Or.inl rfl⟩, ⟨t, ht, Or.inr (Or.inl rfl)⟩, ⟨t, ht, Or.inr (Or.inr (Or.inl rfl))⟩,
    ⟨t, ht, Or.inr (Or.inr (Or.inr rfl))⟩⟩

theorem zero_mem_wallThresholds : (0 : ℝ) ∈ wallThresholds := by simp [wallThresholds]

/-- **Generic displacements exist.** The diagonal `(1, 1)` is parallel to none of the walls. -/
theorem isGenericDisplacement_one_one : IsGenericDisplacement (1, 1) := by
  rintro _ ⟨t, ht, rfl | rfl | rfl | rfl⟩ <;>
  · simp only [wallThresholds, mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- Rescaling keeps a displacement generic, so generic displacements are arbitrarily small. -/
theorem IsGenericDisplacement.smul {v : ℝ × ℝ} (hv : IsGenericDisplacement v) {a : ℝ}
    (ha : a ≠ 0) : IsGenericDisplacement (a • v) := fun N hN => by
  have := hv N hN
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  intro h
  exact this (by
    have : a * (N.1 * v.1 + N.2 * v.2) = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left ha)

theorem isLocallyInLines_fst_eq (c : ℝ) : IsLocallyInLines wallNormals {q | q.1 = c} :=
  (isLocallyInLines_normalLine (mem_wallNormals zero_mem_wallThresholds).2.2.1 (1000 * c)).mono
    fun q (hq : q.1 = c) => by simp only [normalLine, mem_ofPred_eq, hq]; ring

theorem isLocallyInLines_snd_eq (c : ℝ) : IsLocallyInLines wallNormals {q | q.2 = c} :=
  (isLocallyInLines_normalLine (mem_wallNormals zero_mem_wallThresholds).1 (1000 * c)).mono
    fun q (hq : q.2 = c) => by simp only [normalLine, mem_ofPred_eq, hq]; ring

theorem isLocallyInLines_par_eq (e : SquareEdge) (c : ℝ) :
    IsLocallyInLines wallNormals {q | e.par q = c} := by
  cases e
  exacts [isLocallyInLines_fst_eq c, isLocallyInLines_snd_eq c, isLocallyInLines_fst_eq c,
    isLocallyInLines_snd_eq c]

/-- The edge band width vanishes only on the lines `s = 0` and `s = n`. -/
theorem isLocallyInLines_bandWidth_eq_zero (n : ℝ) (e : SquareEdge) :
    IsLocallyInLines wallNormals {q | bandWidth n (e.par q) = 0} :=
  ((isLocallyInLines_par_eq e 0).union (isLocallyInLines_par_eq e n)).mono fun q hq => by
    simp only [mem_ofPred_eq, bandWidth] at hq
    rcases min_choice (e.par q) (n - e.par q) with h | h
    · left; simp only [mem_ofPred_eq]; rw [h] at hq; linarith
    · right; simp only [mem_ofPred_eq]; rw [h] at hq; linarith

/-- **The interface curves are polygonal.** For a threshold `t`, the curve `x = t` of the band of
an edge, `1000 d = t min(s, n - s)`, lies in two lines with normals in `wallNormals`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:142–158`. -/
theorem isLocallyInLines_bandWidth_eq {t : ℝ} (ht : t ∈ wallThresholds) (n : ℝ) (e : SquareEdge) :
    IsLocallyInLines wallNormals {q | t * bandWidth n (e.par q) = e.nor n q} := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_wallNormals ht
  have key (q : ℝ × ℝ) (hq : t * bandWidth n (e.par q) = e.nor n q) :
      1000 * e.nor n q = t * e.par q ∨ 1000 * e.nor n q = t * (n - e.par q) := by
    unfold bandWidth at hq
    rcases min_choice (e.par q) (n - e.par q) with h | h <;> rw [h] at hq
    · exact Or.inl (by linear_combination (-1000 : ℝ) * hq)
    · exact Or.inr (by linear_combination (-1000 : ℝ) * hq)
  cases e
  · refine ((isLocallyInLines_normalLine h2 0).union
      (isLocallyInLines_normalLine h1 (t * n))).mono fun q hq => ?_
    rcases key q hq with h | h <;> simp only [par, nor] at h
    · left; simp only [normalLine, mem_ofPred_eq]; linear_combination h
    · right; simp only [normalLine, mem_ofPred_eq]; linear_combination h
  · refine ((isLocallyInLines_normalLine h3 (1000 * n)).union
      (isLocallyInLines_normalLine h4 (1000 * n - t * n))).mono fun q hq => ?_
    rcases key q hq with h | h <;> simp only [par, nor] at h
    · left; simp only [normalLine, mem_ofPred_eq]; linear_combination -h
    · right; simp only [normalLine, mem_ofPred_eq]; linear_combination -h
  · refine ((isLocallyInLines_normalLine h1 (1000 * n)).union
      (isLocallyInLines_normalLine h2 (1000 * n - t * n))).mono fun q hq => ?_
    rcases key q hq with h | h <;> simp only [par, nor] at h
    · left; simp only [normalLine, mem_ofPred_eq]; linear_combination -h
    · right; simp only [normalLine, mem_ofPred_eq]; linear_combination -h
  · refine ((isLocallyInLines_normalLine h4 0).union
      (isLocallyInLines_normalLine h3 (t * n))).mono fun q hq => ?_
    rcases key q hq with h | h <;> simp only [par, nor] at h
    · left; simp only [normalLine, mem_ofPred_eq]; linear_combination h
    · right; simp only [normalLine, mem_ofPred_eq]; linear_combination h

/-- The integer points of `q₁ / n` or of `q₂ / n` form a locally finite family of grid lines. -/
theorem isLocallyInLines_div_eq_int {φ : ℝ × ℝ → ℝ} (hφ : φ = Prod.fst ∨ φ = Prod.snd) {n : ℝ}
    (hn : n ≠ 0) : IsLocallyInLines wallNormals {q | ∃ k : ℤ, φ q / n = k} := by
  have hc : Continuous fun q => φ q / n := by
    rcases hφ with rfl | rfl
    exacts [continuous_fst.div_const n, continuous_snd.div_const n]
  have hline (k : ℤ) : IsLocallyInLines wallNormals {q | φ q / n = k} := by
    rcases hφ with rfl | rfl
    · exact (isLocallyInLines_fst_eq (k * n)).mono fun q (hq : q.1 / n = k) => by
        simp only [mem_ofPred_eq]; rw [← hq, div_mul_cancel₀ _ hn]
    · exact (isLocallyInLines_snd_eq (k * n)).mono fun q (hq : q.2 / n = k) => by
        simp only [mem_ofPred_eq]; rw [← hq, div_mul_cancel₀ _ hn]
  refine IsLocallyInLines.of_local fun p => ?_
  set m := ⌊φ p / n⌋
  refine ⟨(fun q => φ q / n) ⁻¹' Ioo ((m : ℝ) - 1) (m + 2),
    (isOpen_Ioo.preimage hc).mem_nhds ⟨by linarith [Int.floor_le (φ p / n)],
      by linarith [Int.lt_floor_add_one (φ p / n)]⟩,
    _, (hline m).union (hline (m + 1)), fun q ⟨⟨k, hk⟩, hq⟩ => ?_⟩
  simp only [mem_preimage, mem_Ioo, hk] at hq
  have h1 : m - 1 < k := by exact_mod_cast hq.1
  have h2 : k < m + 2 := by exact_mod_cast hq.2
  rcases (show k = m ∨ k = m + 1 by omega) with rfl | rfl
  · exact Or.inl hk
  · exact Or.inr hk

/-! ### The pieces of the guides -/

/-- Membership in a band with threshold boundaries is constant off walls on lines. -/
theorem hasLineWalls_mem_edgeBand (n : ℝ) (e : SquareEdge) {α β : ℝ} (hα : α ∈ wallThresholds)
    (hβ : β ∈ wallThresholds) : HasLineWalls wallNormals fun q => q ∈ edgeBand n e α β := by
  have hw : Continuous fun q => bandWidth n (e.par q) :=
    (continuous_bandWidth n).comp (continuous_par e)
  refine (hasLineWalls_lt continuous_const (continuous_par e) ?_).and
    ((hasLineWalls_lt (continuous_par e) continuous_const ?_).and
    ((hasLineWalls_lt (continuous_const.mul hw) (continuous_nor n e) ?_).and
    (hasLineWalls_lt (continuous_nor n e) (continuous_const.mul hw) ?_)))
  · exact (isLocallyInLines_par_eq e 0).mono fun q (hq : 0 = e.par q) => hq.symm
  · exact isLocallyInLines_par_eq e n
  · exact isLocallyInLines_bandWidth_eq hα n e
  · exact (isLocallyInLines_bandWidth_eq hβ n e).mono fun q (hq : _ = _) => hq.symm

/-- Membership in the central region is constant off walls on lines. -/
theorem hasLineWalls_mem_centralRegion (n : ℝ) :
    HasLineWalls wallNormals fun q => q ∈ centralRegion n := by
  have h1 : (1 : ℝ) ∈ wallThresholds := by simp [wallThresholds]
  refine (hasLineWalls_lt continuous_const continuous_fst ?_).and
    ((hasLineWalls_lt continuous_fst continuous_const ?_).and
    ((hasLineWalls_lt continuous_const continuous_snd ?_).and
    ((hasLineWalls_lt continuous_snd continuous_const ?_).and
    (HasLineWalls.forall fun e => hasLineWalls_lt
      ((continuous_bandWidth n).comp (continuous_par e)) (continuous_nor n e) ?_))))
  · exact (isLocallyInLines_fst_eq 0).mono fun q (hq : 0 = q.1) => hq.symm
  · exact isLocallyInLines_fst_eq n
  · exact (isLocallyInLines_snd_eq 0).mono fun q (hq : 0 = q.2) => hq.symm
  · exact isLocallyInLines_snd_eq n
  · exact (isLocallyInLines_bandWidth_eq h1 n e).mono fun q (hq : _ = _) => by
      simp only [mem_ofPred_eq, one_mul]; exact hq

/-- The open sup square about a point is constant off walls on lines. -/
theorem hasLineWalls_mem_ball (c : ℝ × ℝ) (r : ℝ) :
    HasLineWalls wallNormals fun q => q ∈ ball c r := by
  have key : (fun q : ℝ × ℝ => q ∈ ball c r) = fun q =>
      ((-r < q.1 - c.1 ∧ q.1 - c.1 < r) ∧ (-r < q.2 - c.2 ∧ q.2 - c.2 < r)) := by
    funext q
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt]
  have h1 : Continuous fun q : ℝ × ℝ => q.1 - c.1 := continuous_fst.sub continuous_const
  have h2 : Continuous fun q : ℝ × ℝ => q.2 - c.2 := continuous_snd.sub continuous_const
  rw [key]
  refine ((hasLineWalls_lt continuous_const h1 ?_).and (hasLineWalls_lt h1 continuous_const ?_)).and
    ((hasLineWalls_lt continuous_const h2 ?_).and (hasLineWalls_lt h2 continuous_const ?_))
  · exact (isLocallyInLines_fst_eq (c.1 - r)).mono fun q (hq : -r = q.1 - c.1) => by
      simp only [mem_ofPred_eq]; linarith
  · exact (isLocallyInLines_fst_eq (c.1 + r)).mono fun q (hq : q.1 - c.1 = r) => by
      simp only [mem_ofPred_eq]; linarith
  · exact (isLocallyInLines_snd_eq (c.2 - r)).mono fun q (hq : -r = q.2 - c.2) => by
      simp only [mem_ofPred_eq]; linarith
  · exact (isLocallyInLines_snd_eq (c.2 + r)).mono fun q (hq : q.2 - c.2 = r) => by
      simp only [mem_ofPred_eq]; linarith

/-- A bound `x < t` on the normal ratio, `t` a threshold, is constant off walls on lines. -/
theorem hasLineWalls_bandCoord_lt (n : ℝ) (e : SquareEdge) {t : ℝ} (ht : t ∈ wallThresholds) :
    HasLineWalls wallNormals fun q => bandCoord n e q < t := by
  refine ⟨_, (isLocallyInLines_bandWidth_eq_zero n e).union (isLocallyInLines_bandWidth_eq ht n e),
    fun q hq => ?_⟩
  simp only [mem_union, mem_ofPred_eq, not_or] at hq
  have hc : ContinuousAt (bandCoord n e) q :=
    (continuous_nor n e).continuousAt.div
      ((continuous_bandWidth n).comp (continuous_par e)).continuousAt hq.1
  have hne : bandCoord n e q ≠ t := fun h => hq.2 (by
    rw [bandCoord, div_eq_iff hq.1] at h
    linarith)
  rcases lt_or_gt_of_ne hne with h | h
  · filter_upwards [hc.eventually (gt_mem_nhds h)] with y hy
    exact propext ⟨fun _ => h, fun _ => hy⟩
  · filter_upwards [hc.eventually (lt_mem_nhds h)] with y hy
    exact propext ⟨fun h' => absurd h' (not_lt.2 hy.le), fun h' => absurd h' (not_lt.2 h.le)⟩

/-- A normal word with threshold interfaces, read through the normal ratio of an edge, is constant
off walls on lines. -/
theorem hasLineWalls_bandWord {ι : Type*} (n : ℝ) (e : SquareEdge) (c : ι) {l : List (ℝ × ι)}
    (hl : ∀ x ∈ l, x.1 ∈ wallThresholds) :
    HasLineWalls wallNormals fun q => bandWord c l (bandCoord n e q) := by
  induction l generalizing c with
  | nil => exact hasLineWalls_const c
  | cons q rest ih =>
    obtain ⟨t, l'⟩ := q
    simp only [bandWord]
    exact (hasLineWalls_bandCoord_lt n e (hl _ List.mem_cons_self)).ite (hasLineWalls_const c)
      (ih l' fun x hx => hl x (List.mem_cons_of_mem _ hx))

theorem neg_eight_mem_wallThresholds : (-8 : ℝ) ∈ wallThresholds := by simp [wallThresholds]

theorem two_mem_wallThresholds : (2 : ℝ) ∈ wallThresholds := by simp [wallThresholds]

/-- Replacing a band by a normal word with threshold interfaces keeps the walls on lines. -/
theorem HasLineWalls.bandUpdate {ι : Type*} {g : ℝ × ℝ → ι} (hg : HasLineWalls wallNormals g)
    (n : ℝ) (e : SquareEdge) (c : ι) {l : List (ℝ × ι)} (hl : ∀ x ∈ l, x.1 ∈ wallThresholds) :
    HasLineWalls wallNormals (bandUpdate n e (bandWord c l) g) :=
  (hasLineWalls_mem_edgeBand n e neg_eight_mem_wallThresholds two_mem_wallThresholds).ite
    (hasLineWalls_bandWord n e c hl) hg

/-- Homogenizing on finitely many open squares about grid corners keeps the walls on lines. -/
theorem HasLineWalls.homogenize {ι : Type*} {g : ℝ × ℝ → ι} (hg : HasLineWalls wallNormals g)
    (M : Finset (ℤ × ℤ)) (n t : ℝ) (P : ι) :
    HasLineWalls wallNormals (homogenize (⋃ Q ∈ M, ball (blockCorner n Q) t) P g) := by
  have hU : HasLineWalls wallNormals fun q => q ∈ ⋃ Q ∈ M, ball (blockCorner n Q) t := by
    have key : (fun q => q ∈ ⋃ Q ∈ M, ball (blockCorner n Q) t) =
        fun q => ¬ ∀ Q : M, ¬ q ∈ ball (blockCorner n Q.1) t := by
      funext q
      simp only [mem_iUnion, exists_prop, Subtype.forall, not_forall, not_not]
    rw [key]
    exact (HasLineWalls.forall fun Q : M =>
      (hasLineWalls_mem_ball (blockCorner n Q.1) t).comp Not).comp Not
  exact hU.ite (hasLineWalls_const P) hg

/-- **The block guide has its walls on the grid lines.** -/
theorem hasLineWalls_blockGuide {ι : Type*} (n : ℝ) (lab : ℤ × ℤ → ι) :
    HasLineWalls wallNormals (blockGuide n lab) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have h0 : blockGuide 0 lab = fun _ => lab (0, 0) := by
      funext p
      simp [blockGuide, blockIndex]
    rw [h0]
    exact hasLineWalls_const _
  exact (hasLineWalls_floor (continuous_fst.div_const n)
    (isLocallyInLines_div_eq_int (Or.inl rfl) hn)).comp₂
    (hasLineWalls_floor (continuous_snd.div_const n)
      (isLocallyInLines_div_eq_int (Or.inr rfl) hn)) fun a b => lab (a, b)

/-! ### The guides of the schedule -/

/-- The interfaces of the normal words are thresholds. -/
theorem word_subset_wallThresholds :
    ({-6, -5, -4, -3, -2, -1, 0, 1} : Set ℝ) ⊆ wallThresholds := by
  intro x hx
  simp only [mem_insert_iff, mem_singleton_iff] at hx
  simp only [wallThresholds, mem_insert_iff, mem_singleton_iff]
  tauto

namespace RepaintingBaseline

variable {ι : Type*} (R : RepaintingBaseline ι)

/-- **The unmodified guides have their walls on lines.** If the starting guide is constant off
walls on lines with normals in `wallNormals`, so is every unmodified guide of the repainting.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–72, 142–241`. -/
theorem IsUnmodifiedGuide.hasLineWalls (hR : HasLineWalls wallNormals R.guide)
    {g : ℝ × ℝ → ι} (hg : R.IsUnmodifiedGuide g) : HasLineWalls wallNormals g := by
  have central : HasLineWalls wallNormals R.centralGuide :=
    (hasLineWalls_mem_centralRegion R.n).ite (hasLineWalls_const _) hR
  have completed (E : List SquareEdge) : HasLineWalls wallNormals (R.completedGuide E) := by
    induction E with
    | nil => exact central
    | cons e E ih =>
      exact ih.bandUpdate R.n e _ (by simp [wallThresholds])
  rcases hg with rfl | rfl | ⟨E, rfl⟩ | ⟨E, e, W, hW, rfl⟩ | ⟨e, W, hW, rfl⟩
  · exact hR
  · exact central
  · exact completed E
  · obtain ⟨c, l, rfl, hl⟩ := exists_eq_bandWord_of_mem_mainWords hW
    exact (completed E).bandUpdate R.n e c fun x hx => word_subset_wallThresholds (hl x hx)
  · obtain ⟨c, l, rfl, hl⟩ := exists_eq_bandWord_of_mem_auxWords hW
    exact (hasLineWalls_const _).bandUpdate R.n e c fun x hx => word_subset_wallThresholds (hl x hx)

end RepaintingBaseline

section Schedule

variable {ι : Type*} {n : ℝ} (hn : 0 < n) {lab : ℤ × ℤ → ι} {S : ℤ × ℤ} {B : ι}

/-- **The guides of the schedule have their walls on lines.** The block guide, every unmodified
guide of the repainting of the block `S` placed on the block, and each of these homogenized on the
open squares of radius `t` about finitely many grid corners, are constant off walls on lines with
normals in `wallNormals`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–72, 142–241, 330–338`. -/
theorem hasLineWalls_schedule {g : ℝ × ℝ → ι}
    (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g) (M : Finset (ℤ × ℤ)) (t : ℝ) (P : ι) :
    HasLineWalls wallNormals (blockGuide n lab) ∧
      HasLineWalls wallNormals (shiftGuide (blockCorner n S) g) ∧
      HasLineWalls wallNormals
        (homogenize (⋃ Q ∈ M, ball (blockCorner n Q) t) P (shiftGuide (blockCorner n S) g)) := by
  have hR : HasLineWalls wallNormals (blockBaseline hn lab S B).guide :=
    (hasLineWalls_blockGuide n lab).comp_add _
  have h := (hg.hasLineWalls _ hR).shiftGuide (blockCorner n S)
  exact ⟨hasLineWalls_blockGuide n lab, h, h.homogenize M n t P⟩

/-- **The sampled guides of the schedule are its readings.** Let `v` be generic. The block guide,
every unmodified guide of the repainting of the block `S` placed on the block, and each of these
homogenized on the open squares of radius `t` about finitely many grid corners, have exactly one
guide sampled from their open chambers after `v`, and a guide is sampled from their chambers after
`v` exactly when it reads them after `v`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 142–241, 330–338`. -/
theorem isChamberSampling_schedule {v : ℝ × ℝ} (hv : IsGenericDisplacement v) {g : ℝ × ℝ → ι}
    (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g) (M : Finset (ℤ × ℤ)) (t : ℝ) (P : ι) :
    ∀ f ∈ ({blockGuide n lab, shiftGuide (blockCorner n S) g,
      homogenize (⋃ Q ∈ M, ball (blockCorner n Q) t) P (shiftGuide (blockCorner n S) g)} :
        Set (ℝ × ℝ → ι)),
      (∃ g', IsChamberSampling g' f v) ∧ ∀ g', IsChamberSampling g' f v ↔ IsDisplacedReading g' f v
    := by
  obtain ⟨hb, hs, hh⟩ := hasLineWalls_schedule hn hg M t P
  have rb := isRayConstant_blockGuide n lab
  have rs : IsRayConstant (shiftGuide (blockCorner n S) g) :=
    (hg.isRayConstant _ (rb.comp_add _)).shiftGuide _
  have key {f : ℝ × ℝ → ι} (hw : HasLineWalls wallNormals f) (hr : IsRayConstant f) :
      (∃ g', IsChamberSampling g' f v) ∧
        ∀ g', IsChamberSampling g' f v ↔ IsDisplacedReading g' f v :=
    ⟨hw.exists_isChamberSampling hr hv, fun _ => hw.isChamberSampling_iff hv⟩
  intro f hf
  simp only [mem_insert_iff, mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl
  · exact key hb rb
  · exact key hs rs
  · exact key hh (rs.homogenize M n t P)

end Schedule

/-! ### Lemma 7.2 for the source's sampled guides -/

section Lemma72

variable {ι : Type*} {n : ℝ} (hn : 0 < n) (lab : ℤ × ℤ → ι) (S : ℤ × ℤ) (B : ι) {v : ℝ × ℝ}

local notation "R" => blockBaseline hn lab S B
local notation "o" => blockCorner n S

/-- **The sampled guides of the repainting exist.** For a generic displacement `v`, the block
guide, the guide after the central birth of the block `S`, and every main or auxiliary guide along
an edge whose band carries a main or an auxiliary word, placed on the block, have a guide sampled
from their open chambers after `v`. These include all the guides of
`blockRepainting_central_of_chamberSampling`, `blockRepainting_auxStep_of_chamberSampling`,
`blockRepainting_mainStep_of_chamberSampling` and `blockRepainting_exchange_of_chamberSampling`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 155–241`. -/
theorem exists_isChamberSampling_blockRepainting (hv : IsGenericDisplacement v) :
    (∃ g, IsChamberSampling g (blockGuide n lab) v) ∧
    (∃ g, IsChamberSampling g (shiftGuide o (R).centralGuide) v) ∧
    (∀ (E : List SquareEdge) (e : SquareEdge), ∀ W ∈ mainWords (lab S) B (lab (e.nbrBlock S)),
      ∃ g, IsChamberSampling g (shiftGuide o ((R).mainGuide E e W)) v) ∧
    ∀ e : SquareEdge, ∀ W ∈ auxWords (lab S) B (lab (e.nbrBlock S)),
      ∃ g, IsChamberSampling g (shiftGuide o ((R).auxGuide e W)) v := by
  have key {g : ℝ × ℝ → ι} (hg : (R).IsUnmodifiedGuide g) :
      ∃ g', IsChamberSampling g' (shiftGuide o g) v :=
    (isChamberSampling_schedule hn hv hg ∅ 0 B _ (mem_insert_of_mem _ (mem_insert _ _))).1
  refine ⟨(hasLineWalls_blockGuide n lab).exists_isChamberSampling (isRayConstant_blockGuide n lab)
    hv, key (Or.inr (Or.inl rfl)), fun E e W hW => key (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨E, e, W, hW, rfl⟩)))), fun e W hW => key (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨e, W, hW, rfl⟩))))⟩

/-- **Lemma 7.2 for the source's sampled guides, central birth.** For the guides `g₀`, `g₁`
sampled after one displacement `v` from the open chambers of the block guide and of the guide
after the central birth of the block `S`, the changed region has closure of diameter at most `n`,
and each of its points `y` lies at sup distance at least `a₀ min(n, d_V(y))` from the closure of
the positions where `g₀` is not the old label. For generic `v` these sampled guides exist
(`exists_isChamberSampling_blockRepainting`).

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`, equation
`eq:geometry-birth-clearance`, `06-geometry.tex:69–80, 254–264, 276–281`. -/
theorem blockRepainting_central_of_chamberSampling {g₀ g₁ : ℝ × ℝ → ι}
    (h₀ : IsChamberSampling g₀ (blockGuide n lab) v)
    (h₁ : IsChamberSampling g₁ (shiftGuide o (R).centralGuide) v) :
    (∀ y ∈ closure {p | g₀ p ≠ g₁ p}, ∀ z ∈ closure {p | g₀ p ≠ g₁ p}, dist y z ≤ n) ∧
    ∀ y ∈ closure {p | g₀ p ≠ g₁ p}, ∀ z ∈ closure {p | g₀ p ≠ lab S},
      angularConstant * min n (cornerMarkDist n (y - o)) ≤ dist y z :=
  blockRepainting_central_of_reading hn lab S B h₀.isDisplacedReading h₁.isDisplacedReading

/-- **Lemma 7.2 for the source's sampled guides, auxiliary births.** For the guides sampled after
one displacement from the open chambers of the auxiliary guides before, after and surrounding an
elementary birth on the auxiliary sheet of the edge `e`, the estimates of
`blockRepainting_auxStep` hold.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`, equation
`eq:geometry-birth-clearance`, `06-geometry.tex:69–80, 254–264, 283–286`. -/
theorem blockRepainting_auxStep_of_chamberSampling (e : SquareEdge) {op : BandOperation ι}
    (hop : op ∈ auxSteps (lab S) B (lab (e.nbrBlock S))) {gb ga gs : ℝ × ℝ → ι}
    (hb : IsChamberSampling gb (shiftGuide o ((R).auxGuide e op.before)) v)
    (ha : IsChamberSampling ga (shiftGuide o ((R).auxGuide e op.after)) v)
    (hs : IsChamberSampling gs (shiftGuide o ((R).auxGuide e op.surrounding)) v) :
    (∀ y ∈ closure {p | gb p ≠ ga p}, ∀ z ∈ closure {p | gb p ≠ ga p}, dist y z ≤ n) ∧
    ∀ y ∈ closure {p | gb p ≠ ga p}, ∀ z ∈ closure {p | gs p ≠ op.label},
      angularConstant * min n (edgeMarkDist n e (y - o)) ≤ dist y z :=
  blockRepainting_auxStep_of_reading hn lab S B e hop hb.isDisplacedReading ha.isDisplacedReading
    hs.isDisplacedReading

/-- **Lemma 7.2 for the source's sampled guides, main births and deaths.** For the guides sampled
after one displacement from the open chambers of the main guides before, after and surrounding an
elementary birth or death on the main sheet along the edge `e`, after the edges of `E`, the
estimates of `blockRepainting_mainStep` hold.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`, equation
`eq:geometry-birth-clearance`, `06-geometry.tex:69–80, 254–264, 286–293`. -/
theorem blockRepainting_mainStep_of_chamberSampling (E : List SquareEdge) (e : SquareEdge)
    {op : BandOperation ι} (hop : op ∈ mainSteps (lab S) B (lab (e.nbrBlock S)))
    {gb ga gs : ℝ × ℝ → ι}
    (hb : IsChamberSampling gb (shiftGuide o ((R).mainGuide E e op.before)) v)
    (ha : IsChamberSampling ga (shiftGuide o ((R).mainGuide E e op.after)) v)
    (hs : IsChamberSampling gs (shiftGuide o ((R).mainGuide E e op.surrounding)) v) :
    (∀ y ∈ closure {p | gb p ≠ ga p}, ∀ z ∈ closure {p | gb p ≠ ga p}, dist y z ≤ n) ∧
    ∀ y ∈ closure {p | gb p ≠ ga p}, ∀ z ∈ closure {p | gs p ≠ op.label},
      angularConstant * min n (edgeMarkDist n e (y - o)) ≤ dist y z :=
  blockRepainting_mainStep_of_reading hn lab S B E e hop hb.isDisplacedReading
    ha.isDisplacedReading hs.isDisplacedReading

/-- **Lemma 7.2 for the source's sampled guides, lens exchange.** For the guides `gm`, `gx`
sampled after one displacement from the open chambers of the main guide with the starting word and
of the auxiliary guide with the auxiliary word along the edge `e`, every point `y` in the closure
of the positions that are not common `C_e` on `gm` and `gx` lies at sup distance at least
`a₀ min(n, d_V(y))` from the boundary of the translated lens, and the closure of those positions
inside the translated lens has diameter at most `n`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`, equation
`eq:geometry-exchange-clearance`, `06-geometry.tex:69–80, 265–272, 295–299`, and the diameter of
the exchange, `06-geometry.tex:421–424`. -/
theorem blockRepainting_exchange_of_chamberSampling (E : List SquareEdge) (e : SquareEdge)
    {gm gx : ℝ × ℝ → ι}
    (hm : IsChamberSampling gm
      (shiftGuide o ((R).mainGuide E e (edgeStartWord (lab S) B (lab (e.nbrBlock S))))) v)
    (hx : IsChamberSampling gx
      (shiftGuide o ((R).auxGuide e (auxWord (lab S) B (lab (e.nbrBlock S))))) v) :
    (∀ y ∈ closure {p | p - o ∈ edgeLens n e ∧ (gm p ≠ lab (e.nbrBlock S) ∨
        gx p ≠ lab (e.nbrBlock S))},
      ∀ z ∈ closure {p | p - o ∈ edgeLens n e ∧ (gm p ≠ lab (e.nbrBlock S) ∨
        gx p ≠ lab (e.nbrBlock S))}, dist y z ≤ n) ∧
    ∀ y ∈ closure {p | gm p ≠ lab (e.nbrBlock S) ∨ gx p ≠ lab (e.nbrBlock S)},
      ∀ z ∈ frontier ((fun p => p - o) ⁻¹' edgeLens n e),
        angularConstant * min n (edgeMarkDist n e (y - o)) ≤ dist y z :=
  blockRepainting_exchange_of_reading hn lab S B E e hm.isDisplacedReading hx.isDisplacedReading

end Lemma72

end TNLean.PEPS.Approximation
