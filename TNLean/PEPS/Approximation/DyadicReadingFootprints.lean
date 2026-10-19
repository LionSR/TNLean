/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicBlockFootprints
import TNLean.PEPS.Approximation.DyadicConicalFootprints

/-!
# Footprint ratios of the sampled guides

The small-patch covers of the source are applied to its sampled guides. The footprint ratios of
`TNLean.PEPS.Approximation.DyadicFootprintTemplates` and
`TNLean.PEPS.Approximation.DyadicBlockFootprints` are proved for the formal labellings, with holes
at their true vertices. This file proves them for the readings of these labellings after a
generic displacement `v`, with holes at the true vertices of the readings, and with one ratio `ν`
for all generic `v`. For generic `v` these readings are the source's sampled guides, by
`isChamberSampling_schedule` for the block guides and the homogenized guides and by
`isChamberSampling_pointTreated` for the point-treated guides. As in the source, `ν` is chosen
before the displacement, which is chosen only after all the guides are specified
(`06-geometry.tex:73–77, 559–563`).

The argument:

* a reading takes only values of the labelling, and reading commutes with relabellings and with
  the similarities `u ↦ c + s u`, `s > 0`: if `f` agrees on an open square with a relabelled
  similar image of a template `T`, every reading of `f` agrees there with the same image of the
  reading of `T`;
* the templates of the point treatment and of the block guides are eventually constant along rays,
  so they have readings after `v`, and the readings of the templates are templates for the
  readings of the guides;
* the templates are constant off walls on lines with normals in the finite set `wallNormals`, and
  two displacements on the same side of every wall direction give the same labels just after
  every point, since the segment between the two displaced points crosses no wall; so each
  template has only finitely many readings after generic displacements;
* hence one ratio `ν > 0` serves the readings after every generic `v` of all the point-treated
  guides near a mark, of the guides homogenized about several marks at once, and of the block
  guides at direct repaintings and resizings, at every scale.

Near a mark the ratio is explicit: every `ν ≤ pointTreatmentRatio ε₀ = min(ε₀, 1) / 20000`
serves the readings of the templates (`template_footprintRatio_reading_of_le`), by the slope
argument of `TNLean.PEPS.Approximation.DyadicConicalFootprints`.

For the block guides there is also an explicit ratio: three distinct labels of a reading of a
block guide in a footprint of radius `δ < s / 2` come from three blocks about one grid corner, which
is then a true vertex within `2 δ` of a footprint point, so every `δ` with `2 δ` below the hole
radius works (`IsDisplacedReading.hasTwoOwnerFootprints_blockGuide`). For the resizings this gives
every ratio `ν ≤ resizeRatio ε₀ = min(ε₀, 1) / 8` (`resizing_footprintRatio_mixed_reading_of_le`).

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: the tie convention (lines
  69–80), the compactness observation and its uniformity (lines 447–479), the point covers (lines
  481–505), the direct repainting (lines 507–527), the resizing (lines 529–541) and the order of
  the constants (lines 559–563).
-/

namespace TNLean.PEPS.Approximation

open Set Metric Filter Topology

universe u

/-! ### Readings of relabelled similar images -/

/-- A reading takes only values of the labelling. -/
theorem IsDisplacedReading.range_subset {X ι : Type*} [AddCommGroup X] [Module ℝ X]
    {f f' : X → ι} {v : X} (h : IsDisplacedReading f' f v) : range f' ⊆ range f := by
  rintro _ ⟨p, rfl⟩
  obtain ⟨ε, hε⟩ := (h p).exists
  exact ⟨_, hε.symm⟩

/-- **Readings of relabelled similar images.** If `f` agrees on the open square of radius `ρ`
about `c` with the relabelling by `σ` of a template `T` read through the similarity
`u ↦ c + s u`, `s > 0`, then every reading of `f` after `v` agrees there with the relabelling of a
reading `T'` of `T` after `v`, read through the same similarity.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 469–471`. -/
theorem IsDisplacedReading.eq_on_ball {ι κ : Type*} {f g' : ℝ × ℝ → ι} {T T' : ℝ × ℝ → κ}
    {σ : κ → ι} {c : ℝ × ℝ} {s ρ : ℝ} (hs : 0 < s) {v : ℝ × ℝ}
    (hf : ∀ q ∈ ball c ρ, f q = σ (T (s⁻¹ • (q - c)))) (hT : IsDisplacedReading T' T v)
    (hg : IsDisplacedReading g' f v) : ∀ q ∈ ball c ρ, g' q = σ (T' (s⁻¹ • (q - c))) := by
  intro q hq
  have hball : ∀ᶠ ε in 𝓝[>] (0 : ℝ), q + ε • v ∈ ball c ρ :=
    tendsto_add_smul_nhdsGT q v (isOpen_ball.mem_nhds hq)
  have hscale : Tendsto (fun ε : ℝ => s⁻¹ * ε) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h : Tendsto (fun ε : ℝ => s⁻¹ * ε) (𝓝 0) (𝓝 (s⁻¹ * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact mul_pos (inv_pos.2 hs) hε
  obtain ⟨ε, e₁, e₂, e₃⟩ :=
    ((hg q).and (hball.and (hscale.eventually (hT (s⁻¹ • (q - c)))))).exists
  rw [e₁, hf _ e₂, e₃, add_sub_right_comm, smul_add, smul_smul]

/-- Composing with an affine map keeps a labelling eventually constant along rays. -/
theorem IsRayConstant.comp_affine {ι : Sort*} {f : ℝ × ℝ → ι} (h : IsRayConstant f)
    (c : ℝ × ℝ) (a : ℝ) : IsRayConstant fun u => f (c + a • u) := fun p v => by
  obtain ⟨k, hk⟩ := h (c + a • p) (a • v)
  refine ⟨k, hk.mono fun ε hε => ?_⟩
  have e : c + a • (p + ε • v) = c + a • p + ε • (a • v) := by
    rw [smul_add, smul_comm a ε v, add_assoc]
  simp only [e, hε]

/-- The point treatment keeps a labelling eventually constant along rays. -/
theorem IsRayConstant.pointTreated {ι : Type*} {f : ℝ × ℝ → ι} (h : IsRayConstant f)
    (c : ℝ × ℝ) (t : ℝ) (P : Option ι) : IsRayConstant (pointTreated c t P f) := by
  cases P with
  | none => exact h
  | some P₀ => exact (isRayConstant_mem_ball c t).ite (isRayConstant_const P₀) h

/-- The point treatment keeps the walls on lines. -/
theorem HasLineWalls.pointTreated {ι : Type*} {f : ℝ × ℝ → ι} (h : HasLineWalls wallNormals f)
    (c : ℝ × ℝ) (t : ℝ) (P : Option ι) : HasLineWalls wallNormals (pointTreated c t P f) := by
  cases P with
  | none => exact h
  | some P₀ => exact (hasLineWalls_mem_ball c t).ite (hasLineWalls_const P₀) h

/-- **The sampled point-treated guides are the readings.** Let `v` be generic. Every unmodified
guide of the repainting of the block `S`, placed on the block and point treated about a grid
corner, has exactly one guide sampled from its open chambers after `v`, and a guide is sampled
from its chambers after `v` exactly when it reads it after `v`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 330–338, 481–505`. -/
theorem isChamberSampling_pointTreated {ι : Type*} {n : ℝ} (hn : 0 < n) {v : ℝ × ℝ}
    (hv : IsGenericDisplacement v) {lab : ℤ × ℤ → ι} {S : ℤ × ℤ} {B : ι} {g : ℝ × ℝ → ι}
    (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g) (Q : ℤ × ℤ) (t : ℝ) (P : Option ι) :
    (∃ g', IsChamberSampling g'
      (pointTreated (blockCorner n Q) t P (shiftGuide (blockCorner n S) g)) v) ∧
    ∀ g', IsChamberSampling g'
      (pointTreated (blockCorner n Q) t P (shiftGuide (blockCorner n S) g)) v ↔
      IsDisplacedReading g'
        (pointTreated (blockCorner n Q) t P (shiftGuide (blockCorner n S) g)) v := by
  have hw := ((hasLineWalls_schedule hn hg ∅ 0 B).2.1).pointTreated (blockCorner n Q) t P
  have hr : IsRayConstant
      (pointTreated (blockCorner n Q) t P (shiftGuide (blockCorner n S) g)) :=
    ((hg.isRayConstant _ ((isRayConstant_blockGuide n lab).comp_add _)).shiftGuide _).pointTreated
      _ t P
  exact ⟨hw.exists_isChamberSampling hr hv, fun _ => hw.isChamberSampling_iff hv⟩

/-- The templates of the point treatment are eventually constant along rays. -/
theorem isRayConstant_footprintTemplate (i : TemplateIndex) :
    IsRayConstant (footprintTemplate i) := by
  have h0 : IsRayConstant i.1.1 :=
    i.1.2.isRayConstant _ ((isRayConstant_blockGuide 1 (blockSlot 1)).comp_add _)
  exact ((h0.comp_affine _ _).pointTreated 0 1 i.2.2.1).comp i.2.2.2

/-! ### Readings after generic displacements -/

/-- **Displacements on the same side of every wall give the same labels.** Let `f` be constant
off walls on lines with normals in `𝒩`, and let `v` and `w` lie strictly on the same side of each
line through the origin with normal in `𝒩`. Then at every point `p` the labels at `p + ε v` and
`p + ε w` agree for all small `ε > 0`: the segment between these points crosses no wall, since the
walls through `p` separate neither `v` from `w` and the others stay away from `p`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–77`. -/
theorem HasLineWalls.eventually_eq_of_sameSide {𝒩 : Set (ℝ × ℝ)} {ι : Type*} {f : ℝ × ℝ → ι}
    (hf : HasLineWalls 𝒩 f) {v w : ℝ × ℝ}
    (hvw : ∀ N ∈ 𝒩, 0 < (N.1 * v.1 + N.2 * v.2) * (N.1 * w.1 + N.2 * w.2)) (p : ℝ × ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), f (p + ε • v) = f (p + ε • w) := by
  obtain ⟨Z, hZ, hloc⟩ := hf
  obtain ⟨U, hU, F, hF, h𝒩, hs⟩ := hZ p
  set Φ : ℝ × ℝ → ℝ × ℝ := fun z => p + z.1 • ((1 - z.2) • v + z.2 • w) with hΦ
  have hΦc : Continuous Φ := by fun_prop
  have hnear : ∀ᶠ y in 𝓝 p, y ∈ U ∧ ∀ L ∈ F,
      L.1.1 * p.1 + L.1.2 * p.2 ≠ L.2 → L.1.1 * y.1 + L.1.2 * y.2 ≠ L.2 := by
    refine (show ∀ᶠ y in 𝓝 p, y ∈ U from hU).and ((hF.eventually_all).2 fun L _ => ?_)
    by_cases h : L.1.1 * p.1 + L.1.2 * p.2 = L.2
    · exact Eventually.of_forall fun _ h' => absurd h h'
    · filter_upwards [(by fun_prop : Continuous fun y : ℝ × ℝ =>
        L.1.1 * y.1 + L.1.2 * y.2).continuousAt.eventually_ne h] with y hy _ using hy
  have hseg : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ a ∈ Icc (0 : ℝ) 1, Φ (ε, a) ∈ U ∧ ∀ L ∈ F,
      L.1.1 * p.1 + L.1.2 * p.2 ≠ L.2 → L.1.1 * (Φ (ε, a)).1 + L.1.2 * (Φ (ε, a)).2 ≠ L.2 := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun a _ => ?_
    have h0 : Φ (0, a) = p := by simp [hΦ]
    have : Tendsto Φ (𝓝 (0, a)) (𝓝 p) := h0 ▸ hΦc.tendsto (0, a)
    exact this.eventually hnear
  filter_upwards [nhdsWithin_le_nhds hseg, self_mem_nhdsWithin] with ε hε (hε0 : 0 < ε)
  have hoff (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) : Φ (ε, a) ∉ Z := by
    intro hZa
    obtain ⟨L, hL, hm⟩ := mem_iUnion₂.1 (hs ⟨hZa, (hε a ha).1⟩)
    simp only [normalLine, mem_ofPred_eq] at hm
    by_cases hp : L.1.1 * p.1 + L.1.2 * p.2 = L.2
    · have hαβ := hvw L.1 (h𝒩 L hL)
      set α := L.1.1 * v.1 + L.1.2 * v.2
      set β := L.1.1 * w.1 + L.1.2 * w.2
      have key : ε * ((1 - a) * α + a * β) = 0 := by
        simp only [hΦ, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul] at hm
        linear_combination hm - hp
      obtain ⟨h0, h1⟩ := ha
      have hX : (1 - a) * α + a * β = 0 := (mul_eq_zero.1 key).resolve_left hε0.ne'
      have hsq : (1 - a) * α ^ 2 + a * (α * β) = 0 := by linear_combination α * hX
      have hα : 0 < α ^ 2 := by
        have : α ≠ 0 := by rintro h; rw [h, zero_mul] at hαβ; exact lt_irrefl _ hαβ
        positivity
      rcases le_total (α * β) (α ^ 2) with h | h
      · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h)]
      · nlinarith [mul_nonneg h0 (sub_nonneg.2 h)]
    · exact (hε a ha).2 L hL hp hm
  let _ : TopologicalSpace ι := ⊥
  have _ : DiscreteTopology ι := ⟨rfl⟩
  have hcont : ContinuousOn (fun a => f (Φ (ε, a))) (Icc 0 1) := fun a ha => by
    refine ContinuousAt.continuousWithinAt ?_
    rw [ContinuousAt, nhds_discrete ι, tendsto_pure]
    exact ((by fun_prop : Continuous fun b : ℝ => Φ (ε, b)).tendsto a).eventually
      (hloc _ (hoff a ha))
  have := isPreconnected_Icc.constant hcont (left_mem_Icc.2 zero_le_one)
    (right_mem_Icc.2 zero_le_one)
  simpa [hΦ] using this

/-- A reading after `v` of a labelling with walls on lines is also its reading after every `w` on
the same side of each wall direction as `v`. -/
theorem IsDisplacedReading.of_sameSide {𝒩 : Set (ℝ × ℝ)} {ι : Type*} {f g : ℝ × ℝ → ι}
    (hf : HasLineWalls 𝒩 f) {v w : ℝ × ℝ}
    (hvw : ∀ N ∈ 𝒩, 0 < (N.1 * v.1 + N.2 * v.2) * (N.1 * w.1 + N.2 * w.2))
    (hg : IsDisplacedReading g f v) : IsDisplacedReading g f w :=
  fun p => ((hg p).and (hf.eventually_eq_of_sameSide hvw p)).mono fun _ h => h.1.trans h.2

/-- **Finitely many generic readings.** A labelling with walls on lines with normals in
`wallNormals` has only finitely many readings after generic displacements: the reading after a
generic `v` depends only on the side of each of the finitely many wall directions on which `v`
lies.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–77`. -/
theorem HasLineWalls.finite_genericReadings {ι : Type*} {f : ℝ × ℝ → ι}
    (hf : HasLineWalls wallNormals f) :
    {g | ∃ v, IsGenericDisplacement v ∧ IsDisplacedReading g f v}.Finite := by
  have : Finite wallNormals := finite_wallNormals.to_subtype
  let side (v : ℝ × ℝ) : wallNormals → Prop := fun N => 0 < N.1.1 * v.1 + N.1.2 * v.2
  refine (finite_iUnion fun s : wallNormals → Prop => Set.Subsingleton.finite
    (s := {g | ∃ v, IsGenericDisplacement v ∧ side v = s ∧ IsDisplacedReading g f v}) ?_).subset ?_
  · rintro g₁ ⟨v₁, hv₁, rfl, h₁⟩ g₂ ⟨v₂, hv₂, hs, h₂⟩
    refine h₁.unique (h₂.of_sameSide hf fun N hN => ?_)
    have e : 0 < N.1 * v₂.1 + N.2 * v₂.2 ↔ 0 < N.1 * v₁.1 + N.2 * v₁.2 :=
      Iff.of_eq (congrFun hs ⟨N, hN⟩)
    rcases lt_or_gt_of_ne (hv₂ N hN) with h | h
    · exact mul_pos_of_neg_of_neg h ((hv₁ N hN).lt_of_le (not_lt.1 (mt e.2 (not_lt.2 h.le))))
    · exact mul_pos h (e.1 h)
  · rintro g ⟨v, hv, hg⟩
    exact mem_iUnion.2 ⟨side v, v, hv, rfl, hg⟩

/-- The templates of the point treatment have their walls on lines with normals in
`wallNormals`. -/
theorem hasLineWalls_footprintTemplate (i : TemplateIndex) :
    HasLineWalls wallNormals (footprintTemplate i) := by
  have h0 : HasLineWalls wallNormals i.1.1 :=
    i.1.2.hasLineWalls _ ((hasLineWalls_blockGuide 1 (blockSlot 1)).comp_add _)
  exact ((h0.comp_affine _ (by norm_num)).pointTreated 0 1 i.2.2.1).comp i.2.2.2

/-! ### The point treatment -/

/-- **The footprint ratio of the readings of the templates.** Fix `ε₀ > 0` and
`ν ≤ pointTreatmentRatio ε₀`. For every generic displacement `v`, whenever a guide `f` agrees on
the open square of radius `4 t` about `c` with the image of a template of the point treatment,
relabelled by a map injective on its values and read through `u ↦ c + t u`, every reading of `f`
after `v` has the two-owner condition with working set the closed square of radius `2 t` about
`c`, holes at its own true vertices within `3 t` of `c`, inner radius `ε₀ t` and footprint radius
`ν t`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 447–479, 481–505,
559–563`. -/
theorem template_footprintRatio_reading_of_le {ε₀ : ℝ} (hε : 0 < ε₀) {ν : ℝ}
    (hν : ν ≤ pointTreatmentRatio ε₀) : ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
      ∀ {ι : Type u} {t : ℝ}, 0 < t → ∀ (i : TemplateIndex) (σ : BlockSlot 1 → ι),
      InjOn σ (range (footprintTemplate i)) → ∀ (c : ℝ × ℝ) (f g' : ℝ × ℝ → ι),
      (∀ q ∈ ball c (4 * t), f q = σ (footprintTemplate i (t⁻¹ • (q - c)))) →
      IsDisplacedReading g' f v →
      HasTwoOwnerFootprints g' (closedBall c (2 * t))
        {x | x ∈ closedBall c (3 * t) ∧ IsTrueVertex g' x} (ε₀ * t) (ν * t) := by
  intro v hv ι t ht i σ hσ c f g' hf hg'
  obtain ⟨T, hT⟩ := (isRayConstant_footprintTemplate i).exists_isDisplacedReading v
  have key := HasTwoOwnerFootprints.of_template (ρ₁ := 2) (ρ₂ := 3) (ρ₃ := 4)
    (hσ.mono hT.range_subset) ht (by norm_num) (by norm_num)
    (hT.eq_on_ball ht (fun q hq => hf q (by rwa [mul_comm] at hq)) hg')
    (((hasTwoOwnerFootprints_reading_footprintTemplate i hv hT hε hν).image_similarity c
      ht).relabel σ)
  rwa [mul_comm t 2, mul_comm t 3, mul_comm t ε₀, mul_comm t ν] at key

/-- **One footprint ratio for the readings of the templates.** Fix `ε₀ > 0`. There is a ratio
`ν > 0` such that, for every generic displacement `v`, whenever a guide `f` agrees on the open
square of radius `4 t` about `c` with the image of a template of the point treatment, relabelled
by a map injective on its values and read through `u ↦ c + t u`, every reading of `f` after `v`
has the two-owner condition with working set the closed square of radius `2 t` about `c`, holes at
its own true vertices within `3 t` of `c`, inner radius `ε₀ t` and footprint radius `ν t`. The
ratio is chosen before `v`; the ratio `pointTreatmentRatio ε₀` serves
(`template_footprintRatio_reading_of_le`).

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 464–479, 481–505,
559–563`. -/
theorem exists_template_footprintRatio_reading {ε₀ : ℝ} (hε : 0 < ε₀) :
    ∃ ν > 0, ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
      ∀ {ι : Type u} {t : ℝ}, 0 < t → ∀ (i : TemplateIndex) (σ : BlockSlot 1 → ι),
      InjOn σ (range (footprintTemplate i)) → ∀ (c : ℝ × ℝ) (f g' : ℝ × ℝ → ι),
      (∀ q ∈ ball c (4 * t), f q = σ (footprintTemplate i (t⁻¹ • (q - c)))) →
      IsDisplacedReading g' f v →
      HasTwoOwnerFootprints g' (closedBall c (2 * t))
        {x | x ∈ closedBall c (3 * t) ∧ IsTrueVertex g' x} (ε₀ * t) (ν * t) :=
  ⟨pointTreatmentRatio ε₀, pointTreatmentRatio_pos hε,
    template_footprintRatio_reading_of_le hε le_rfl⟩

/-- **One footprint ratio for the readings of the point treatment.** Fix `ε₀ > 0`. There is a
ratio `ν > 0` such that, for every generic displacement `v`, the conclusion of
`exists_pointTreatment_footprintRatio` holds for every reading after `v` of every point-treated
unmodified guide, with holes at the true vertices of the reading.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 464–479, 481–505,
559–563`. -/
theorem exists_pointTreatment_footprintRatio_reading {ε₀ : ℝ} (hε : 0 < ε₀) :
    ∃ ν > 0, ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
      ∀ {ι : Type u} {n t : ℝ} (hn : 0 < n), 0 < t → 8 * t < n →
      ∀ {lab : ℤ × ℤ → ι} {S : ℤ × ℤ} {B : ι} {g : ℝ × ℝ → ι},
      (blockBaseline hn lab S B).IsUnmodifiedGuide g → ∀ {Q : ℤ × ℤ}, IsBlockCornerOf S Q →
      ∀ P : Option ι, (∀ x ∈ P, x = B ∨ ∃ R ∈ blockWindow 1, x = lab (R + S)) →
      ∀ g' : ℝ × ℝ → ι, IsDisplacedReading g'
        (pointTreated (blockCorner n Q) t P (shiftGuide (blockCorner n S) g)) v →
      HasTwoOwnerFootprints g' (closedBall (blockCorner n Q) (2 * t))
        {c | c ∈ closedBall (blockCorner n Q) (3 * t) ∧ IsTrueVertex g' c} (ε₀ * t) (ν * t) := by
  obtain ⟨ν, hν, H⟩ := exists_template_footprintRatio_reading.{u} hε
  refine ⟨ν, hν, fun {v} hv {ι n t} hn ht htn {lab S B g} hg {Q} hQ P hP g' hg' => ?_⟩
  obtain ⟨i, hinj, heq⟩ := exists_template_injOn hn hg hQ ht htn P hP
  exact H hv ht i _ hinj _ _ g' heq hg'

/-- **One footprint ratio for the readings of the simultaneous point treatment.** With one ratio
`ν > 0` for all generic displacements `v`, the conclusion of
`exists_pointTreatment_footprintRatio_iUnion` holds for every reading after `v` of every
unmodified guide homogenized about the corners of a finite set `M`, with holes at the true
vertices of the reading.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 330–333, 464–479,
481–505, 559–563`. -/
theorem exists_pointTreatment_footprintRatio_iUnion_reading {ε₀ : ℝ} (hε : 0 < ε₀) :
    ∃ ν > 0, ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
      ∀ {ι : Type u} {n t : ℝ} (hn : 0 < n), 0 < t → 8 * t < n →
      ∀ {lab : ℤ × ℤ → ι} {S : ℤ × ℤ} {B : ι} {g : ℝ × ℝ → ι},
      (blockBaseline hn lab S B).IsUnmodifiedGuide g → ∀ (M : Finset (ℤ × ℤ)) {Q : ℤ × ℤ},
      Q ∈ M → IsBlockCornerOf S Q → ∀ P : ι, (P = B ∨ ∃ R ∈ blockWindow 1, P = lab (R + S)) →
      ∀ g' : ℝ × ℝ → ι, IsDisplacedReading g'
        (homogenize (⋃ Q' ∈ M, ball (blockCorner n Q') t) P (shiftGuide (blockCorner n S) g)) v →
      HasTwoOwnerFootprints g' (closedBall (blockCorner n Q) (2 * t))
        {c | c ∈ closedBall (blockCorner n Q) (3 * t) ∧ IsTrueVertex g' c} (ε₀ * t) (ν * t) := by
  obtain ⟨ν, hν, H⟩ := exists_template_footprintRatio_reading.{u} hε
  refine ⟨ν, hν, fun {v} hv {ι n t} hn ht htn {lab S B g} hg M {Q} hQM hQ P hP g' hg' => ?_⟩
  obtain ⟨i, hinj, heq⟩ :=
    exists_template_injOn hn hg hQ ht htn (some P) fun x hx => Option.mem_some_iff.1 hx ▸ hP
  refine H hv ht i _ hinj _ _ g' (fun q hq => ?_) hg'
  rw [homogenize_iUnion_eq_of_mem_ball hn htn M hQM P _ hq]
  exact heq q hq

/-! ### Block guides -/

/-- Block indices of two points closer than the side differ by at most one.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:82–90`. -/
theorem floor_div_le_floor_div_add_one {s x y : ℝ} (hs : 0 < s) (h : x - y < s) :
    ⌊x / s⌋ ≤ ⌊y / s⌋ + 1 := by
  by_contra hlt
  have h2 : (⌊y / s⌋ : ℝ) + 2 ≤ ⌊x / s⌋ := by exact_mod_cast (by omega : ⌊y / s⌋ + 2 ≤ ⌊x / s⌋)
  have hx := Int.floor_le (x / s)
  have hy := Int.lt_floor_add_one (y / s)
  rw [le_div_iff₀ hs] at hx
  rw [div_lt_iff₀ hs] at hy
  nlinarith

/-- For two points in adjacent block columns, the distance of the first to the grid line between
them is at most their distance.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:82–90`. -/
theorem abs_sub_max_floor_mul_le {s x y : ℝ} (hs : 0 < s) (hne : ⌊x / s⌋ ≠ ⌊y / s⌋)
    (h₁ : ⌊x / s⌋ ≤ ⌊y / s⌋ + 1) (h₂ : ⌊y / s⌋ ≤ ⌊x / s⌋ + 1) :
    |x - s * (max ⌊x / s⌋ ⌊y / s⌋ : ℤ)| ≤ |x - y| := by
  have hx := Int.floor_le (x / s)
  have hx' := Int.lt_floor_add_one (x / s)
  have hy := Int.floor_le (y / s)
  have hy' := Int.lt_floor_add_one (y / s)
  rw [le_div_iff₀ hs] at hx hy
  rw [div_lt_iff₀ hs] at hx' hy'
  have hxy := le_abs_self (x - y)
  have hyx := neg_abs_le (x - y)
  rcases (by omega : ⌊x / s⌋ = ⌊y / s⌋ + 1 ∨ ⌊y / s⌋ = ⌊x / s⌋ + 1) with e | e
  · rw [max_eq_left (by omega), abs_le]
    have e' : (⌊x / s⌋ : ℝ) = ⌊y / s⌋ + 1 := by exact_mod_cast e
    constructor <;> nlinarith
  · rw [max_eq_right (by omega), abs_le]
    have e' : (⌊y / s⌋ : ℝ) = ⌊x / s⌋ + 1 := by exact_mod_cast e
    constructor <;> nlinarith

/-- A reading of a block guide carries the label of a block on its open interior.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–90`. -/
theorem IsDisplacedReading.blockGuide_eq_of_mem {ι : Type*} {s : ℝ} (hs : 0 < s)
    {lab : ℤ × ℤ → ι} {v : ℝ × ℝ} {g' : ℝ × ℝ → ι}
    (hg' : IsDisplacedReading g' (blockGuide s lab) v) {a b : ℤ} {y : ℝ × ℝ}
    (hy : y ∈ Ioo (s * a) (s * (a + 1)) ×ˢ Ioo (s * b) (s * (b + 1))) : g' y = lab (a, b) := by
  have hU : Ioo (s * a) (s * (a + 1)) ×ˢ Ioo (s * b) (s * (b + 1)) ∈ 𝓝 y :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds hy
  obtain ⟨ε, e₁, ⟨h1, h2⟩, h3, h4⟩ := ((hg' y).and (tendsto_add_smul_nhdsGT y v hU)).exists
  rw [e₁]
  simp only [blockGuide, blockIndex]
  congr 1
  refine Prod.ext ?_ ?_ <;> simp only [] <;> rw [Int.floor_eq_iff, le_div_iff₀ hs, div_lt_iff₀ hs]
  · constructor <;> linarith
  · constructor <;> linarith

/-- A grid corner lies in the closure of the label of each of its four blocks in a reading of a
block guide.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–90, 109–111`. -/
theorem IsDisplacedReading.blockCorner_mem_closure {ι : Type*} {s : ℝ} (hs : 0 < s)
    {lab : ℤ × ℤ → ι} {v : ℝ × ℝ} {g' : ℝ × ℝ → ι}
    (hg' : IsDisplacedReading g' (blockGuide s lab) v) {A B a b : ℤ} (ha₁ : A - 1 ≤ a)
    (ha₂ : a ≤ A) (hb₁ : B - 1 ≤ b) (hb₂ : b ≤ B) :
    blockCorner s (A, B) ∈ closure (g' ⁻¹' {lab (a, b)}) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set τ := min ε s / 2 with hτ
  have hτ0 : 0 < τ := by positivity
  have hτε : τ < ε := by have := min_le_left ε s; linarith
  have hτs : τ < s := by have := min_le_right ε s; linarith
  have ha : a = A - 1 ∨ a = A := by omega
  have hb : b = B - 1 ∨ b = B := by omega
  set y : ℝ × ℝ := (s * A + ((a - A : ℤ) + 1 / 2) * τ, s * B + ((b - B : ℤ) + 1 / 2) * τ)
  refine ⟨y, hg'.blockGuide_eq_of_mem hs ?_, ?_⟩
  · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [y] <;> push_cast <;> nlinarith
  · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [blockCorner, y]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> push_cast <;>
      refine max_lt ?_ ?_ <;> rw [abs_lt] <;> constructor <;> nlinarith


/-- The block indices of two points closer than the side differ by at most one in each
coordinate.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:82–90`. -/
theorem floor_div_adjacent {s : ℝ} (hs : 0 < s) {a b : ℝ × ℝ} (h : dist a b < s) :
    ⌊a.1 / s⌋ ≤ ⌊b.1 / s⌋ + 1 ∧ ⌊b.1 / s⌋ ≤ ⌊a.1 / s⌋ + 1 ∧
      ⌊a.2 / s⌋ ≤ ⌊b.2 / s⌋ + 1 ∧ ⌊b.2 / s⌋ ≤ ⌊a.2 / s⌋ + 1 := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at h
  obtain ⟨h1, h2⟩ := abs_lt.1 ((le_max_left _ _).trans_lt h)
  obtain ⟨h3, h4⟩ := abs_lt.1 ((le_max_right _ _).trans_lt h)
  exact ⟨floor_div_le_floor_div_add_one hs h2, floor_div_le_floor_div_add_one hs (by linarith),
    floor_div_le_floor_div_add_one hs h4, floor_div_le_floor_div_add_one hs (by linarith)⟩

/-- The core of the explicit two-owner condition of a block guide: three points of a reading with
pairwise distinct labels, the first two in diagonally adjacent blocks, force a hole at the grid
corner between those two.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:109–111, 453–462`. -/
private theorem blockReading_diagonal_false {ι : Type*} {s r : ℝ} (hs : 0 < s)
    {lab : ℤ × ℤ → ι} {v : ℝ × ℝ} {g' : ℝ × ℝ → ι}
    (hg' : IsDisplacedReading g' (blockGuide s lab) v) {H : Set (ℝ × ℝ)} {p q₁ q₂ q₃ : ℝ × ℝ}
    (hH : ∀ c, dist c p ≤ s → IsTrueVertex g' c → c ∈ H) (hp : p ∉ ⋃ h ∈ H, ball h r)
    (h12 : dist q₁ q₂ < s) (h13 : dist q₁ q₃ < s) (h23 : dist q₂ q₃ < s)
    (hx : ⌊q₁.1 / s⌋ ≠ ⌊q₂.1 / s⌋) (hy : ⌊q₁.2 / s⌋ ≠ ⌊q₂.2 / s⌋)
    (l12 : lab (blockIndex s q₁) ≠ lab (blockIndex s q₂))
    (l13 : lab (blockIndex s q₁) ≠ lab (blockIndex s q₃))
    (l23 : lab (blockIndex s q₂) ≠ lab (blockIndex s q₃))
    (hr : dist p q₁ + dist q₁ q₂ < r) (hps : dist p q₁ + dist q₁ q₂ ≤ s) : False := by
  obtain ⟨f12x, f12x', f12y, f12y'⟩ := floor_div_adjacent hs h12
  obtain ⟨f13x, f13x', f13y, f13y'⟩ := floor_div_adjacent hs h13
  obtain ⟨f23x, f23x', f23y, f23y'⟩ := floor_div_adjacent hs h23
  set A := max ⌊q₁.1 / s⌋ ⌊q₂.1 / s⌋
  set B := max ⌊q₁.2 / s⌋ ⌊q₂.2 / s⌋
  set z := blockCorner s (A, B)
  have hz : dist q₁ z ≤ dist q₁ q₂ := by
    rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_le_max (abs_sub_max_floor_mul_le hs hx f12x f12x')
      (abs_sub_max_floor_mul_le hs hy f12y f12y')
  have hpz : dist z p < r ∧ dist z p ≤ s := by
    have := dist_triangle p q₁ z
    rw [dist_comm z p]
    constructor <;> linarith
  have hmem (q : ℝ × ℝ) (h₁ : A - 1 ≤ ⌊q.1 / s⌋) (h₂ : ⌊q.1 / s⌋ ≤ A) (h₃ : B - 1 ≤ ⌊q.2 / s⌋)
      (h₄ : ⌊q.2 / s⌋ ≤ B) : z ∈ closure (g' ⁻¹' {lab (blockIndex s q)}) :=
    hg'.blockCorner_mem_closure hs h₁ h₂ h₃ h₄
  have htv : IsTrueVertex g' z :=
    ⟨_, _, _, l12, l13, l23, hmem q₁ (by omega) (by omega) (by omega) (by omega),
      hmem q₂ (by omega) (by omega) (by omega) (by omega),
      hmem q₃ (by omega) (by omega) (by omega) (by omega)⟩
  exact hp (mem_biUnion (hH z hpz.2 htv) (by rw [mem_ball, dist_comm]; exact hpz.1))

/-- **The two-owner condition of a block guide at an explicit footprint radius.** Let `g'` be a
reading, after any displacement, of the guide uniform on the blocks of side `s > 0`, and let every
true vertex of `g'` within `s` of the working set `W` be a hole center. Then every footprint
radius `δ` with `2 δ < r` and `2 δ < s` gives the two-owner condition with inner radius `r`.
Indeed three distinct labels in a footprint come from three blocks around one grid corner, two of
them diagonal to each other, so the corner is a true vertex within `2 δ` of a footprint point.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:447–479, 507–527, 529–541`.
-/
theorem IsDisplacedReading.hasTwoOwnerFootprints_blockGuide {ι : Type*} {s : ℝ} (hs : 0 < s)
    {lab : ℤ × ℤ → ι} {v : ℝ × ℝ} {g' : ℝ × ℝ → ι}
    (hg' : IsDisplacedReading g' (blockGuide s lab) v) {W H : Set (ℝ × ℝ)}
    (hH : ∀ c, ∀ w ∈ W, dist c w ≤ s → IsTrueVertex g' c → c ∈ H) {r δ : ℝ} (hδr : 2 * δ < r)
    (hδs : 2 * δ < s) : HasTwoOwnerFootprints g' W H r δ := by
  intro x p₁ p₂ p₃ h₁ h₂ h₃
  by_contra hne
  push Not at hne
  obtain ⟨n12, n13, n23⟩ := hne
  set η := min (r - 2 * δ) (s - 2 * δ) / 4 with hη
  have hη0 : 0 < η := by have := lt_min (sub_pos.2 hδr) (sub_pos.2 hδs); positivity
  have hηr : 3 * η < r - 2 * δ := by have := min_le_left (r - 2 * δ) (s - 2 * δ); linarith
  have hηs : 3 * η < s - 2 * δ := by have := min_le_right (r - 2 * δ) (s - 2 * δ); linarith
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (0 : ℝ × ℝ) + ε • v ∈ ball 0 η :=
    tendsto_add_smul_nhdsGT 0 v (ball_mem_nhds 0 hη0)
  obtain ⟨ε, e₁, e₂, e₃, e₄⟩ := ((hg' p₁).and ((hg' p₂).and ((hg' p₃).and hsmall))).exists
  rw [zero_add, mem_ball, dist_zero_right] at e₄
  have hq (p : ℝ × ℝ) : dist p (p + ε • v) < η := by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left]; exact e₄
  have hd {p p' : ℝ × ℝ} (hp : p ∈ (closedBall x δ ∩ W) \ ⋃ h ∈ H, ball h r)
      (hp' : p' ∈ (closedBall x δ ∩ W) \ ⋃ h ∈ H, ball h r) :
      dist (p + ε • v) (p' + ε • v) ≤ 2 * δ := by
    rw [dist_add_right]
    linarith [dist_triangle p x p', dist_comm x p', mem_closedBall.1 hp.1.1,
      mem_closedBall.1 hp'.1.1]
  have hW {p : ℝ × ℝ} (hp : p ∈ (closedBall x δ ∩ W) \ ⋃ h ∈ H, ball h r) :
      ∀ c, dist c p ≤ s → IsTrueVertex g' c → c ∈ H := fun c hc => hH c p hp.1.2 hc
  rw [e₁, e₂] at n12; rw [e₁, e₃] at n13; rw [e₂, e₃] at n23
  have hne {a b : ℝ × ℝ} (h : blockGuide s lab a ≠ blockGuide s lab b) :
      ⌊a.1 / s⌋ ≠ ⌊b.1 / s⌋ ∨ ⌊a.2 / s⌋ ≠ ⌊b.2 / s⌋ := by
    by_contra hc
    push Not at hc
    exact h (by simp only [blockGuide, blockIndex, hc.1, hc.2])
  have d12 := hd h₁ h₂
  have d13 := hd h₁ h₃
  have d23 := hd h₂ h₃
  have s12 : dist (p₁ + ε • v) (p₂ + ε • v) < s := by linarith
  have s13 : dist (p₁ + ε • v) (p₃ + ε • v) < s := by linarith
  have s23 : dist (p₂ + ε • v) (p₃ + ε • v) < s := by linarith
  obtain ⟨f12x, f12x', f12y, f12y'⟩ := floor_div_adjacent hs s12
  obtain ⟨f13x, f13x', f13y, f13y'⟩ := floor_div_adjacent hs s13
  obtain ⟨f23x, f23x', f23y, f23y'⟩ := floor_div_adjacent hs s23
  have m12 := hne n12
  have m13 := hne n13
  have m23 := hne n23
  have q₁ := hq p₁
  have q₂ := hq p₂
  have q₃ := hq p₃
  rcases (by omega : (⌊(p₁ + ε • v).1 / s⌋ ≠ ⌊(p₂ + ε • v).1 / s⌋ ∧
      ⌊(p₁ + ε • v).2 / s⌋ ≠ ⌊(p₂ + ε • v).2 / s⌋) ∨
    (⌊(p₁ + ε • v).1 / s⌋ ≠ ⌊(p₃ + ε • v).1 / s⌋ ∧
      ⌊(p₁ + ε • v).2 / s⌋ ≠ ⌊(p₃ + ε • v).2 / s⌋) ∨
    (⌊(p₂ + ε • v).1 / s⌋ ≠ ⌊(p₃ + ε • v).1 / s⌋ ∧
      ⌊(p₂ + ε • v).2 / s⌋ ≠ ⌊(p₃ + ε • v).2 / s⌋)) with h | h | h
  · exact blockReading_diagonal_false hs hg' (hW h₁) h₁.2 s12 s13 s23 h.1 h.2 n12 n13 n23
      (by linarith) (by linarith)
  · rw [dist_comm] at s23
    exact blockReading_diagonal_false hs hg' (hW h₁) h₁.2 s13 s12 s23 h.1 h.2 n13 n12
      (Ne.symm n23) (by linarith) (by linarith)
  · rw [dist_comm] at s12 s13
    exact blockReading_diagonal_false hs hg' (hW h₂) h₂.2 s23 s12 s13 h.1 h.2 n23 (Ne.symm n12)
      (Ne.symm n13) (by linarith) (by linarith)

/-- **One footprint ratio for the readings of block guides.** Fix `ρ` and `0 < r₀`. There is a
ratio `ν > 0` such that, for every generic displacement `v`, the conclusion of
`exists_blockGuide_footprintRatio` holds for every reading after `v` of every guide uniform on the
blocks of side `s > 0`, with holes at the true vertices of the reading.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 464–479, 515–520,
534–538, 559–563`. -/
theorem exists_blockGuide_footprintRatio_reading {ρ r₀ r₁ : ℝ} (hr₀ : 0 < r₀) :
    ∃ ν > 0, ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
      ∀ {ι : Type u} {s : ℝ}, 0 < s → ∀ (lab : ℤ × ℤ → ι) (Q : ℤ × ℤ),
      ∀ r ∈ Icc (r₀ * s) (r₁ * s), ∀ g' : ℝ × ℝ → ι, IsDisplacedReading g' (blockGuide s lab) v →
      HasTwoOwnerFootprints g' (closedBall (blockCorner s Q) (s * ρ))
        {c | c ∈ closedBall (blockCorner s Q) (s * (ρ + 1)) ∧ IsTrueVertex g' c} r (ν * s) := by
  set M : ℕ := ⌈ρ⌉₊ + 2
  have hM : ρ + 2 ≤ M := by push_cast [M]; linarith [Nat.le_ceil ρ]
  let T : (BlockSlot M → BlockSlot M) → ℝ × ℝ → BlockSlot M := fun π u =>
    π (blockGuide 1 (blockSlot M) u)
  let R (π : BlockSlot M → BlockSlot M) : Set (ℝ × ℝ → BlockSlot M) :=
    {T' | ∃ v, IsGenericDisplacement v ∧ IsDisplacedReading T' (T π) v}
  have (π : BlockSlot M → BlockSlot M) : Finite (R π) :=
    ((hasLineWalls_blockGuide 1 (blockSlot M)).comp π).finite_genericReadings.to_subtype
  obtain ⟨ν, hν, H⟩ := exists_footprintRatio.{0, 0, u} (I := Σ π, R π) (g := fun j => j.2.1)
    (fun _ => Set.toFinite _) (W := fun _ => closedBall 0 ρ) (fun _ => isCompact_closedBall 0 ρ)
    (H := fun j => {w | w ∈ closedBall (0 : ℝ × ℝ) (ρ + 1) ∧ IsTrueVertex j.2.1 w})
    (r₀ := r₀) (r₁ := r₁) (fun _ c hc htv =>
      ⟨c, ⟨closedBall_subset_closedBall (by linarith) hc, htv⟩, mem_ball_self hr₀⟩)
  refine ⟨ν, hν, fun {v} hv {ι s} hs lab Q r hr g' hg' => ?_⟩
  set σ : BlockSlot M → ι := blockSlotLabel (fun R => lab (Q + R)) (lab Q)
  obtain ⟨T', hT'⟩ :=
    ((isRayConstant_blockGuide 1 (blockSlot M)).comp (classRep σ)).exists_isDisplacedReading v
  have hinj : InjOn σ (range T') :=
    (injOn_range_classRep σ).mono (hT'.range_subset.trans
      (by rintro _ ⟨w, rfl⟩; exact mem_range_self _))
  have hf (q : ℝ × ℝ) (hq : q ∈ ball (blockCorner s Q) (s * (ρ + 2))) :
      blockGuide s lab q = σ (T (classRep σ) (s⁻¹ • (q - blockCorner s Q))) :=
    blockGuide_eq_classRep hs lab Q M (ball_subset_ball (mul_le_mul_of_nonneg_left hM hs.le) hq)
  have hrs : r / s ∈ Icc r₀ r₁ := ⟨(le_div_iff₀ hs).2 hr.1, (div_le_iff₀ hs).2 hr.2⟩
  have key := HasTwoOwnerFootprints.of_template (ρ₁ := ρ) (ρ₂ := ρ + 1) (ρ₃ := ρ + 2) hinj hs
    (by linarith) (by linarith) (hT'.eq_on_ball hs hf hg')
    (H ⟨classRep σ, T', v, hv, hT'⟩ σ (blockCorner s Q) hs (r / s) hrs)
  rwa [mul_div_cancel₀ r hs.ne'] at key

/-- **One footprint ratio for the readings of the direct repaintings.** Fix `ε₀ > 0` and `K₀`.
There is a ratio `ν > 0` such that, for every generic displacement `v`, the conclusion of
`exists_directRepainting_footprintRatio` holds for every reading after `v` of every guide uniform
on the `n`-blocks, with holes at the true vertices of the reading.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 507–527, 559–563`. -/
theorem exists_directRepainting_footprintRatio_reading {ε₀ K₀ : ℝ} (hε : 0 < ε₀) :
    ∃ ν > 0, ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
      ∀ {ι : Type u} {n t : ℝ}, 0 < n → 0 < t → n ≤ K₀ * t →
      ∀ (lab : ℤ × ℤ → ι) (Q : ℤ × ℤ) (g' : ℝ × ℝ → ι),
      IsDisplacedReading g' (blockGuide n lab) v →
      HasTwoOwnerFootprints g' (closedBall (blockCorner n Q) (n * 2))
        {c | c ∈ closedBall (blockCorner n Q) (n * (2 + 1)) ∧ IsTrueVertex g' c}
        (holeRadius ε₀ n t) (ν * n) := by
  obtain ⟨ν, hν, H⟩ := exists_blockGuide_footprintRatio_reading.{u} (ρ := 2)
    (r₀ := ε₀ / max K₀ 1) (r₁ := ε₀) (div_pos hε (lt_of_lt_of_le one_pos (le_max_right _ _)))
  refine ⟨ν, hν, fun {v} hv {ι n t} hn ht hK lab Q g' hg' => H hv hn lab Q _ ?_ g' hg'⟩
  have h := holeRadius_div_mem_Icc hε.le hn ht hK
  exact ⟨(le_div_iff₀ hn).1 h.1, (div_le_iff₀ hn).1 h.2⟩

/-- **One footprint ratio for the readings of the resizings.** Fix `ε₀ > 0`. There is a ratio
`ν > 0` such that, for every generic displacement `v`, the conclusion of
`exists_resizing_footprintRatio` holds for every reading after `v` of every guide uniform on the
`2n`-blocks, with holes at the true vertices of the reading.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 529–541, 559–563`. -/
theorem exists_resizing_footprintRatio_reading {ε₀ : ℝ} (hε : 0 < ε₀) :
    ∃ ν > 0, ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
      ∀ {ι : Type u} {n t : ℝ}, 0 < n → n < t → ∀ (lab : ℤ × ℤ → ι) (Q : ℤ × ℤ),
      ∀ r ∈ ({holeRadius ε₀ n t, holeRadius ε₀ (2 * n) t} : Set ℝ), ∀ g' : ℝ × ℝ → ι,
      IsDisplacedReading g' (blockGuide (2 * n) lab) v →
      HasTwoOwnerFootprints g' (closedBall (blockCorner (2 * n) Q) (2 * n * 1))
        {c | c ∈ closedBall (blockCorner (2 * n) Q) (2 * n * (1 + 1)) ∧ IsTrueVertex g' c} r
        (ν * (2 * n)) := by
  obtain ⟨ν, hν, H⟩ := exists_blockGuide_footprintRatio_reading.{u} (ρ := 1) (r₀ := ε₀ / 2)
    (r₁ := ε₀) (by positivity)
  exact ⟨ν, hν, fun {v} hv {ι n t} hn hnt lab Q r hr g' hg' =>
    H hv (by positivity) lab Q r (mem_Icc_of_mem_holeRadius_pair hε hn hnt hr) g' hg'⟩

/-- **Intermediate configurations of a resizing, for the readings.** With one ratio `ν > 0` for
all generic displacements `v`, the conclusion of `exists_resizing_footprintRatio_mixed` holds for
every reading after `v` of every guide uniform on the `2n`-blocks, with holes at the true vertices
of the reading, each of its own radius `h_n` or `h_{2n}`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 529–541, 559–563`. -/
theorem exists_resizing_footprintRatio_mixed_reading {ε₀ : ℝ} (hε : 0 < ε₀) :
    ∃ ν > 0, ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
      ∀ {ι : Type u} {n t : ℝ}, 0 < n → n < t → ∀ (lab : ℤ × ℤ → ι) (Q : ℤ × ℤ)
      (g' : ℝ × ℝ → ι), IsDisplacedReading g' (blockGuide (2 * n) lab) v →
      ∀ ρ : ℝ × ℝ → ℝ, (∀ c, ρ c = holeRadius ε₀ n t ∨ ρ c = holeRadius ε₀ (2 * n) t) →
      ∀ x p₁ p₂ p₃ : ℝ × ℝ, (∀ p ∈ ({p₁, p₂, p₃} : Set (ℝ × ℝ)),
        p ∈ (closedBall x (ν * (2 * n)) ∩ closedBall (blockCorner (2 * n) Q) (2 * n * 1)) \
          ⋃ c ∈ {c | c ∈ closedBall (blockCorner (2 * n) Q) (2 * n * (1 + 1)) ∧
            IsTrueVertex g' c}, ball c (ρ c)) →
      g' p₁ = g' p₂ ∨ g' p₁ = g' p₃ ∨ g' p₂ = g' p₃ := by
  obtain ⟨ν, hν, H⟩ := exists_resizing_footprintRatio_reading.{u} hε
  refine ⟨ν, hν, fun {v} hv {ι n t} hn hnt lab Q g' hg' ρ hρ x p₁ p₂ p₃ hp => ?_⟩
  have hle : holeRadius ε₀ n t ≤ holeRadius ε₀ (2 * n) t :=
    mul_le_mul_of_nonneg_left (min_le_min (by linarith) le_rfl) hε.le
  exact (H hv hn hnt lab Q _ (Or.inl rfl) g' hg').of_le_radii
    (fun c _ => (hρ c).elim (fun h => h.ge) fun h => h ▸ hle) x p₁ p₂ p₃
    (hp p₁ (by simp)) (hp p₂ (by simp)) (hp p₃ (by simp))

/-! ### An explicit ratio for the resizings -/

/-- **The mesh ratio of the resizings**, `ν₁ = min(ε₀, 1) / 8`. A footprint of radius
`ν₁ (2 n)` on the guide uniform on the `2n`-blocks has `2 · ν₁ (2 n) ≤ ε₀ n / 2 < h_n` and
`2 · ν₁ (2 n) ≤ n / 2 < 2 n` when `n < t`, which is what the explicit two-owner condition of a
block guide needs (`IsDisplacedReading.hasTwoOwnerFootprints_blockGuide`). It replaces the
minimum given by the compactness observation; the bound is crude, since it uses only that three
labels meet at grid corners.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:447–479, 529–541`. -/
noncomputable def resizeRatio (ε₀ : ℝ) : ℝ := min ε₀ 1 / 8

/-- The mesh ratio of the resizings is positive (`06-geometry.tex:559–563`). -/
theorem resizeRatio_pos {ε₀ : ℝ} (hε : 0 < ε₀) : 0 < resizeRatio ε₀ := by
  unfold resizeRatio; have := lt_min hε one_pos; positivity

/-- The mesh ratio of the resizings is at most `1 / 8` (`06-geometry.tex:559–563`). -/
theorem resizeRatio_le (ε₀ : ℝ) : resizeRatio ε₀ ≤ 1 / 8 := by
  unfold resizeRatio; have := min_le_right ε₀ 1; linarith

/-- The mesh ratio of the resizings is at most `ε₀ / 8` (`06-geometry.tex:529–541`). -/
theorem resizeRatio_le_div (ε₀ : ℝ) : resizeRatio ε₀ ≤ ε₀ / 8 := by
  unfold resizeRatio; have := min_le_left ε₀ 1; linarith

/-- **Intermediate configurations of a resizing at the explicit ratio.** Fix `ε₀ > 0` and
`ν ≤ resizeRatio ε₀ = min(ε₀, 1) / 8`. For every displacement `v`, every `0 < n < t` and every
reading `g'` after `v` of a guide uniform on the `2n`-blocks, with holes at the true vertices of
`g'` within `4 n` of a grid corner, each of its own radius `h_n` or `h_{2n}`, every footprint of
radius `ν (2 n)` in the closed square of radius `2 n` about the corner meets at most two labels
outside the holes. No genericity of `v` is used.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:447–479, 529–541`. -/
theorem resizing_footprintRatio_mixed_reading_of_le {ε₀ ν : ℝ} (hε : 0 < ε₀)
    (hν : ν ≤ resizeRatio ε₀) {v : ℝ × ℝ} {ι : Type u} {n t : ℝ} (hn : 0 < n) (hnt : n < t)
    (lab : ℤ × ℤ → ι) (Q : ℤ × ℤ) (g' : ℝ × ℝ → ι)
    (hg' : IsDisplacedReading g' (blockGuide (2 * n) lab) v) (ρ : ℝ × ℝ → ℝ)
    (hρ : ∀ c, ρ c = holeRadius ε₀ n t ∨ ρ c = holeRadius ε₀ (2 * n) t)
    (x p₁ p₂ p₃ : ℝ × ℝ) (hp : ∀ p ∈ ({p₁, p₂, p₃} : Set (ℝ × ℝ)),
      p ∈ (closedBall x (ν * (2 * n)) ∩ closedBall (blockCorner (2 * n) Q) (2 * n * 1)) \
        ⋃ c ∈ {c | c ∈ closedBall (blockCorner (2 * n) Q) (2 * n * (1 + 1)) ∧
          IsTrueVertex g' c}, ball c (ρ c)) :
    g' p₁ = g' p₂ ∨ g' p₁ = g' p₃ ∨ g' p₂ = g' p₃ := by
  have hle : holeRadius ε₀ n t ≤ holeRadius ε₀ (2 * n) t :=
    mul_le_mul_of_nonneg_left (min_le_min (by linarith) le_rfl) hε.le
  have hh : holeRadius ε₀ n t = ε₀ * n := by rw [holeRadius, min_eq_left hnt.le]
  have hν8 : ν * n ≤ ε₀ / 8 * n :=
    mul_le_mul_of_nonneg_right (hν.trans (resizeRatio_le_div ε₀)) hn.le
  have hν1 : ν * n ≤ 1 / 8 * n := mul_le_mul_of_nonneg_right (hν.trans (resizeRatio_le ε₀)) hn.le
  have hεn : 0 < ε₀ * n := mul_pos hε hn
  have key : HasTwoOwnerFootprints g' (closedBall (blockCorner (2 * n) Q) (2 * n * 1))
      {c | c ∈ closedBall (blockCorner (2 * n) Q) (2 * n * (1 + 1)) ∧ IsTrueVertex g' c}
      (holeRadius ε₀ n t) (ν * (2 * n)) := by
    refine hg'.hasTwoOwnerFootprints_blockGuide (by positivity) ?_ ?_ ?_
    · intro c w hw hcw htv
      refine ⟨?_, htv⟩
      rw [mem_closedBall] at hw ⊢
      linarith [dist_triangle c w (blockCorner (2 * n) Q)]
    · rw [hh]; linarith
    · linarith
  exact key.of_le_radii (fun c _ => (hρ c).elim (fun h => h.ge) fun h => h ▸ hle) x p₁ p₂ p₃
    (hp p₁ (by simp)) (hp p₂ (by simp)) (hp p₃ (by simp))

end TNLean.PEPS.Approximation
