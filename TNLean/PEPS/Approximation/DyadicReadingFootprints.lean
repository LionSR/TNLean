/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicBlockFootprints
import TNLean.PEPS.Approximation.DyadicChamberSampling
import TNLean.PEPS.Approximation.DyadicFootprintTemplates

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

/-- Rescaling the argument about a point keeps a set lying locally in lines so, with the same
normals. -/
theorem IsLocallyInLines.preimage_affine {𝒩 Z : Set (ℝ × ℝ)} (h : IsLocallyInLines 𝒩 Z)
    (c : ℝ × ℝ) {a : ℝ} (ha : a ≠ 0) : IsLocallyInLines 𝒩 ((fun u => c + a • u) ⁻¹' Z) :=
  fun p => by
  obtain ⟨U, hU, F, hF, h𝒩, hs⟩ := h (c + a • p)
  refine ⟨(fun u => c + a • u) ⁻¹' U,
    (by fun_prop : Continuous fun u : ℝ × ℝ => c + a • u).continuousAt.preimage_mem_nhds hU,
    (fun L => (L.1, (L.2 - (L.1.1 * c.1 + L.1.2 * c.2)) / a)) '' F, hF.image _, ?_, ?_⟩
  · rintro _ ⟨L, hL, rfl⟩
    exact h𝒩 L hL
  · rintro q ⟨hqZ, hqU⟩
    obtain ⟨L, hL, hm⟩ := mem_iUnion₂.1 (hs ⟨hqZ, hqU⟩)
    refine mem_iUnion₂.2 ⟨_, mem_image_of_mem _ hL, ?_⟩
    simp only [normalLine, mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] at hm ⊢
    rw [eq_div_iff ha]
    linear_combination hm

/-- Composing with an affine map of nonzero ratio keeps the walls on lines with the same
normals. -/
theorem HasLineWalls.comp_affine {𝒩 : Set (ℝ × ℝ)} {ι : Sort*} {f : ℝ × ℝ → ι}
    (h : HasLineWalls 𝒩 f) (c : ℝ × ℝ) {a : ℝ} (ha : a ≠ 0) :
    HasLineWalls 𝒩 fun u => f (c + a • u) := by
  obtain ⟨Z, hZ, hl⟩ := h
  exact ⟨_, hZ.preimage_affine c ha, fun q hq =>
    ((by fun_prop : Continuous fun u : ℝ × ℝ => c + a • u).tendsto q).eventually (hl _ hq)⟩

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

/-- There are finitely many wall normals. -/
theorem finite_wallNormals : wallNormals.Finite := by
  have hT : wallThresholds.Finite := by simp [wallThresholds]
  refine (hT.biUnion fun t _ =>
    Set.toFinite ({(t, 1000), (-t, 1000), (1000, t), (1000, -t)} : Set (ℝ × ℝ))).subset ?_
  rintro N ⟨t, ht, h⟩
  exact mem_biUnion ht (by rcases h with rfl | rfl | rfl | rfl <;> simp)

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

/-- **One footprint ratio for the readings of the templates.** Fix `ε₀ > 0`. There is a ratio
`ν > 0` such that, for every generic displacement `v`, whenever a guide `f` agrees on the open
square of radius `4 t` about `c` with the image of a template of the point treatment, relabelled
by a map injective on its values and read through `u ↦ c + t u`, every reading of `f` after `v`
has the two-owner condition with working set the closed square of radius `2 t` about `c`, holes at
its own true vertices within `3 t` of `c`, inner radius `ε₀ t` and footprint radius `ν t`. The
ratio is chosen before `v`: the templates have finitely many readings after generic
displacements.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 464–479, 481–505,
559–563`. -/
theorem exists_template_footprintRatio_reading {ε₀ : ℝ} (hε : 0 < ε₀) :
    ∃ ν > 0, ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
      ∀ {ι : Type u} {t : ℝ}, 0 < t → ∀ (i : TemplateIndex) (σ : BlockSlot 1 → ι),
      InjOn σ (range (footprintTemplate i)) → ∀ (c : ℝ × ℝ) (f g' : ℝ × ℝ → ι),
      (∀ q ∈ ball c (4 * t), f q = σ (footprintTemplate i (t⁻¹ • (q - c)))) →
      IsDisplacedReading g' f v →
      HasTwoOwnerFootprints g' (closedBall c (2 * t))
        {x | x ∈ closedBall c (3 * t) ∧ IsTrueVertex g' x} (ε₀ * t) (ν * t) := by
  let R (i : TemplateIndex) : Set (ℝ × ℝ → BlockSlot 1) :=
    {T | ∃ v, IsGenericDisplacement v ∧ IsDisplacedReading T (footprintTemplate i) v}
  have (i : TemplateIndex) : Finite (R i) :=
    (hasLineWalls_footprintTemplate i).finite_genericReadings.to_subtype
  obtain ⟨ν, hν, H⟩ := exists_footprintRatio.{0, 0, u} (I := Σ i, R i) (g := fun j => j.2.1)
    (fun _ => Set.toFinite _) (W := fun _ => closedBall 0 2) (fun _ => isCompact_closedBall 0 2)
    (H := fun j => {u | u ∈ closedBall (0 : ℝ × ℝ) 3 ∧ IsTrueVertex j.2.1 u})
    (r₀ := ε₀) (r₁ := ε₀) (fun _ c hc htv =>
      ⟨c, ⟨closedBall_subset_closedBall (by norm_num) hc, htv⟩, mem_ball_self hε⟩)
  refine ⟨ν, hν, fun {v} hv {ι t} ht i σ hσ c f g' hf hg' => ?_⟩
  obtain ⟨T, hT⟩ := (isRayConstant_footprintTemplate i).exists_isDisplacedReading v
  have key := HasTwoOwnerFootprints.of_template (ρ₁ := 2) (ρ₂ := 3) (ρ₃ := 4)
    (hσ.mono hT.range_subset) ht (by norm_num) (by norm_num)
    (hT.eq_on_ball ht (fun q hq => hf q (by rwa [mul_comm] at hq)) hg')
    (H ⟨i, T, v, hv, hT⟩ σ c ht ε₀ ⟨le_rfl, le_rfl⟩)
  rwa [mul_comm t 2, mul_comm t 3, mul_comm t ε₀] at key

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

end TNLean.PEPS.Approximation
