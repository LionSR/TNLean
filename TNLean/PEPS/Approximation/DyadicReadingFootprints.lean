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
at their true vertices. This file proves them for the readings of these labellings after one
displacement `v`, with holes at the true vertices of the readings. For generic `v` these readings
are the source's sampled guides, by `isChamberSampling_schedule` for the block guides and the
homogenized guides and by `isChamberSampling_pointTreated` for the point-treated guides.

**Scope restriction (one displacement):** the ratio `ν` is proved for each displacement `v`, and
may depend on it. The source chooses the patch ratio before the information scale `D`, and the
displacement only after all the guides, which depend on `D`, are specified (`06-geometry.tex:73–77,
559–563`); its ratio serves every generic displacement. Here genericity does not depend on `L`,
`D`, `n` or `t` (`IsGenericDisplacement`), so one generic direction, such as `(1, 1)`
(`isGenericDisplacement_one_one`), can be fixed before every constant, and the ratio for it is
then a fixed constant. Documented in
`docs/paper-gaps/openai26_dyadic_geometry_guide_properties.tex`.

The argument:

* a reading takes only values of the labelling, and reading commutes with relabellings and with
  the similarities `u ↦ c + s u`, `s > 0`: if `f` agrees on an open square with a relabelled
  similar image of a template `T`, every reading of `f` agrees there with the same image of the
  reading of `T`;
* the templates of the point treatment and of the block guides are eventually constant along rays,
  so they have readings after `v`, and the finitely many readings of the templates are templates
  for the readings of the guides;
* hence one ratio `ν > 0` serves the readings after `v` of all the point-treated guides near a
  mark, of the guides homogenized about several marks at once, and of the block guides at direct
  repaintings and resizings, at every scale.

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: the tie convention (lines
  69–80), the compactness observation and its uniformity (lines 447–479), the point covers (lines
  481–505), the direct repainting (lines 507–527) and the resizing (lines 529–541).
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

/-! ### The point treatment -/

/-- **One footprint ratio for the readings of the templates.** Fix `ε₀ > 0` and a displacement
`v`. There is a ratio `ν > 0` such that, whenever a guide `f` agrees on the open square of radius
`4 t` about `c` with the image of a template of the point treatment, relabelled by a map injective
on its values and read through `u ↦ c + t u`, every reading of `f` after `v` has the two-owner
condition with working set the closed square of radius `2 t` about `c`, holes at its own true
vertices within `3 t` of `c`, inner radius `ε₀ t` and footprint radius `ν t`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 464–479, 481–505`. -/
theorem exists_template_footprintRatio_reading {ε₀ : ℝ} (hε : 0 < ε₀) (v : ℝ × ℝ) :
    ∃ ν > 0, ∀ {ι : Type u} {t : ℝ}, 0 < t → ∀ (i : TemplateIndex) (σ : BlockSlot 1 → ι),
      InjOn σ (range (footprintTemplate i)) → ∀ (c : ℝ × ℝ) (f g' : ℝ × ℝ → ι),
      (∀ q ∈ ball c (4 * t), f q = σ (footprintTemplate i (t⁻¹ • (q - c)))) →
      IsDisplacedReading g' f v →
      HasTwoOwnerFootprints g' (closedBall c (2 * t))
        {x | x ∈ closedBall c (3 * t) ∧ IsTrueVertex g' x} (ε₀ * t) (ν * t) := by
  choose T hT using fun i : TemplateIndex =>
    (isRayConstant_footprintTemplate i).exists_isDisplacedReading v
  obtain ⟨ν, hν, H⟩ := exists_footprintRatio.{0, 0, u} (I := TemplateIndex) (g := T)
    (fun _ => Set.toFinite _) (W := fun _ => closedBall 0 2) (fun _ => isCompact_closedBall 0 2)
    (H := fun i => {u | u ∈ closedBall (0 : ℝ × ℝ) 3 ∧ IsTrueVertex (T i) u})
    (r₀ := ε₀) (r₁ := ε₀) (fun _ c hc htv =>
      ⟨c, ⟨closedBall_subset_closedBall (by norm_num) hc, htv⟩, mem_ball_self hε⟩)
  refine ⟨ν, hν, fun {ι t} ht i σ hσ c f g' hf hg' => ?_⟩
  have key := HasTwoOwnerFootprints.of_template (ρ₁ := 2) (ρ₂ := 3) (ρ₃ := 4)
    (hσ.mono (hT i).range_subset) ht (by norm_num) (by norm_num)
    ((hT i).eq_on_ball ht (fun q hq => hf q (by rwa [mul_comm] at hq)) hg')
    (H i σ c ht ε₀ ⟨le_rfl, le_rfl⟩)
  rwa [mul_comm t 2, mul_comm t 3, mul_comm t ε₀] at key

/-- **One footprint ratio for the readings of the point treatment.** Fix `ε₀ > 0` and a
displacement `v`. There is a ratio `ν > 0` such that the conclusion of
`exists_pointTreatment_footprintRatio` holds for every reading after `v` of every point-treated
unmodified guide, with holes at the true vertices of the reading.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 464–479, 481–505`. -/
theorem exists_pointTreatment_footprintRatio_reading {ε₀ : ℝ} (hε : 0 < ε₀) (v : ℝ × ℝ) :
    ∃ ν > 0, ∀ {ι : Type u} {n t : ℝ} (hn : 0 < n), 0 < t → 8 * t < n →
      ∀ {lab : ℤ × ℤ → ι} {S : ℤ × ℤ} {B : ι} {g : ℝ × ℝ → ι},
      (blockBaseline hn lab S B).IsUnmodifiedGuide g → ∀ {Q : ℤ × ℤ}, IsBlockCornerOf S Q →
      ∀ P : Option ι, (∀ x ∈ P, x = B ∨ ∃ R ∈ blockWindow 1, x = lab (R + S)) →
      ∀ g' : ℝ × ℝ → ι, IsDisplacedReading g'
        (pointTreated (blockCorner n Q) t P (shiftGuide (blockCorner n S) g)) v →
      HasTwoOwnerFootprints g' (closedBall (blockCorner n Q) (2 * t))
        {c | c ∈ closedBall (blockCorner n Q) (3 * t) ∧ IsTrueVertex g' c} (ε₀ * t) (ν * t) := by
  obtain ⟨ν, hν, H⟩ := exists_template_footprintRatio_reading.{u} hε v
  refine ⟨ν, hν, fun {ι n t} hn ht htn {lab S B g} hg {Q} hQ P hP g' hg' => ?_⟩
  set σ := blockSlotLabel (fun R => lab (R + S)) B
  obtain ⟨Pκ, rfl⟩ : ∃ Pκ : Option (BlockSlot 1), P = Pκ.map σ := by
    cases P with
    | none => exact ⟨none, rfl⟩
    | some x =>
      rcases hP x rfl with rfl | ⟨R, hR, rfl⟩
      · exact ⟨some none, rfl⟩
      · exact ⟨some (some ⟨R, hR⟩), rfl⟩
  obtain ⟨i, -, -, hπ, heq⟩ := exists_template_eq hn hg hQ ht htn Pκ
  have hinj : InjOn σ (range (footprintTemplate i)) := (injOn_range_classRep σ).mono (by
    rintro _ ⟨w, rfl⟩
    simp only [footprintTemplate, hπ]
    exact mem_range_self _)
  exact H ht i σ hinj _ _ g' heq hg'

/-- **One footprint ratio for the readings of the simultaneous point treatment.** With one ratio
`ν > 0` for the displacement `v`, the conclusion of `exists_pointTreatment_footprintRatio_iUnion`
holds for every reading after `v` of every unmodified guide homogenized about the corners of a
finite set `M`, with holes at the true vertices of the reading.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 330–333, 464–479,
481–505`. -/
theorem exists_pointTreatment_footprintRatio_iUnion_reading {ε₀ : ℝ} (hε : 0 < ε₀)
    (v : ℝ × ℝ) :
    ∃ ν > 0, ∀ {ι : Type u} {n t : ℝ} (hn : 0 < n), 0 < t → 8 * t < n →
      ∀ {lab : ℤ × ℤ → ι} {S : ℤ × ℤ} {B : ι} {g : ℝ × ℝ → ι},
      (blockBaseline hn lab S B).IsUnmodifiedGuide g → ∀ (M : Finset (ℤ × ℤ)) {Q : ℤ × ℤ},
      Q ∈ M → IsBlockCornerOf S Q → ∀ P : ι, (P = B ∨ ∃ R ∈ blockWindow 1, P = lab (R + S)) →
      ∀ g' : ℝ × ℝ → ι, IsDisplacedReading g'
        (homogenize (⋃ Q' ∈ M, ball (blockCorner n Q') t) P (shiftGuide (blockCorner n S) g)) v →
      HasTwoOwnerFootprints g' (closedBall (blockCorner n Q) (2 * t))
        {c | c ∈ closedBall (blockCorner n Q) (3 * t) ∧ IsTrueVertex g' c} (ε₀ * t) (ν * t) := by
  obtain ⟨ν, hν, H⟩ := exists_template_footprintRatio_reading.{u} hε v
  refine ⟨ν, hν, fun {ι n t} hn ht htn {lab S B g} hg M {Q} hQM hQ P hP g' hg' => ?_⟩
  set σ := blockSlotLabel (fun R => lab (R + S)) B
  obtain ⟨Pκ, hPκ⟩ : ∃ Pκ : Option (BlockSlot 1), some P = Pκ.map σ := by
    rcases hP with rfl | ⟨R, hR, rfl⟩
    · exact ⟨some none, rfl⟩
    · exact ⟨some (some ⟨R, hR⟩), rfl⟩
  obtain ⟨i, -, -, hπ, heq⟩ := exists_template_eq hn hg hQ ht htn Pκ
  have hinj : InjOn σ (range (footprintTemplate i)) := (injOn_range_classRep σ).mono (by
    rintro _ ⟨w, rfl⟩
    simp only [footprintTemplate, hπ]
    exact mem_range_self _)
  refine H ht i σ hinj _ _ g' (fun q hq => ?_) hg'
  have h := heq q hq
  rw [← hPκ] at h
  rw [homogenize_iUnion_eq_of_mem_ball hn htn M hQM P _ hq]
  exact h

/-! ### Block guides -/

/-- **One footprint ratio for the readings of block guides.** Fix `ρ`, `0 < r₀` and a
displacement `v`. There is a ratio `ν > 0` such that the conclusion of
`exists_blockGuide_footprintRatio` holds for every reading after `v` of every guide uniform on the
blocks of side `s > 0`, with holes at the true vertices of the reading.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 464–479, 515–520,
534–538`. -/
theorem exists_blockGuide_footprintRatio_reading {ρ r₀ r₁ : ℝ} (hr₀ : 0 < r₀) (v : ℝ × ℝ) :
    ∃ ν > 0, ∀ {ι : Type u} {s : ℝ}, 0 < s → ∀ (lab : ℤ × ℤ → ι) (Q : ℤ × ℤ),
      ∀ r ∈ Icc (r₀ * s) (r₁ * s), ∀ g' : ℝ × ℝ → ι, IsDisplacedReading g' (blockGuide s lab) v →
      HasTwoOwnerFootprints g' (closedBall (blockCorner s Q) (s * ρ))
        {c | c ∈ closedBall (blockCorner s Q) (s * (ρ + 1)) ∧ IsTrueVertex g' c} r (ν * s) := by
  set M : ℕ := ⌈ρ⌉₊ + 2
  have hM : ρ + 2 ≤ M := by
    have := Nat.le_ceil ρ
    simp only [M, Nat.cast_add, Nat.cast_ofNat]
    linarith
  let T : (BlockSlot M → BlockSlot M) → ℝ × ℝ → BlockSlot M := fun π u =>
    π (blockGuide 1 (blockSlot M) u)
  choose T' hT' using fun π : BlockSlot M → BlockSlot M =>
    ((isRayConstant_blockGuide 1 (blockSlot M)).comp π).exists_isDisplacedReading v
  obtain ⟨ν, hν, H⟩ := exists_footprintRatio.{0, 0, u} (I := BlockSlot M → BlockSlot M) (g := T')
    (fun _ => Set.toFinite _) (W := fun _ => closedBall 0 ρ) (fun _ => isCompact_closedBall 0 ρ)
    (H := fun π => {w | w ∈ closedBall (0 : ℝ × ℝ) (ρ + 1) ∧ IsTrueVertex (T' π) w})
    (r₀ := r₀) (r₁ := r₁) (fun _ c hc htv =>
      ⟨c, ⟨closedBall_subset_closedBall (by linarith) hc, htv⟩, mem_ball_self hr₀⟩)
  refine ⟨ν, hν, fun {ι s} hs lab Q r hr g' hg' => ?_⟩
  set σ : BlockSlot M → ι := blockSlotLabel (fun R => lab (Q + R)) (lab Q)
  have hinj : InjOn σ (range (T' (classRep σ))) :=
    (injOn_range_classRep σ).mono ((hT' _).range_subset.trans
      (by rintro _ ⟨w, rfl⟩; exact mem_range_self _))
  have hf (q : ℝ × ℝ) (hq : q ∈ ball (blockCorner s Q) (s * (ρ + 2))) :
      blockGuide s lab q = σ (T (classRep σ) (s⁻¹ • (q - blockCorner s Q))) := by
    have hu : ‖s⁻¹ • (q - blockCorner s Q)‖ < M := by
      rw [mem_ball, dist_eq_norm] at hq
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, inv_mul_lt_iff₀ hs]
      nlinarith
    have hq' : q = blockCorner s Q + s • (s⁻¹ • (q - blockCorner s Q)) := by
      rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul, add_sub_cancel]
    conv_lhs => rw [hq']
    rw [blockGuide_eq_blockSlot hs lab Q M hu]
    simp only [T, σ, classRep_spec]
  have hrs : r / s ∈ Icc r₀ r₁ := ⟨(le_div_iff₀ hs).2 hr.1, (div_le_iff₀ hs).2 hr.2⟩
  have key := HasTwoOwnerFootprints.of_template (ρ₁ := ρ) (ρ₂ := ρ + 1) (ρ₃ := ρ + 2) hinj hs
    (by linarith) (by linarith) ((hT' (classRep σ)).eq_on_ball hs hf hg')
    (H (classRep σ) σ (blockCorner s Q) hs (r / s) hrs)
  rwa [mul_div_cancel₀ r hs.ne'] at key

/-- **One footprint ratio for the readings of the direct repaintings.** Fix `ε₀ > 0`, `K₀` and a
displacement `v`. There is a ratio `ν > 0` such that the conclusion of
`exists_directRepainting_footprintRatio` holds for every reading after `v` of every guide uniform
on the `n`-blocks, with holes at the true vertices of the reading.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 507–527`. -/
theorem exists_directRepainting_footprintRatio_reading {ε₀ K₀ : ℝ} (hε : 0 < ε₀) (v : ℝ × ℝ) :
    ∃ ν > 0, ∀ {ι : Type u} {n t : ℝ}, 0 < n → 0 < t → n ≤ K₀ * t →
      ∀ (lab : ℤ × ℤ → ι) (Q : ℤ × ℤ) (g' : ℝ × ℝ → ι),
      IsDisplacedReading g' (blockGuide n lab) v →
      HasTwoOwnerFootprints g' (closedBall (blockCorner n Q) (n * 2))
        {c | c ∈ closedBall (blockCorner n Q) (n * (2 + 1)) ∧ IsTrueVertex g' c}
        (holeRadius ε₀ n t) (ν * n) := by
  obtain ⟨ν, hν, H⟩ := exists_blockGuide_footprintRatio_reading.{u} (ρ := 2)
    (r₀ := ε₀ / max K₀ 1) (r₁ := ε₀) (div_pos hε (lt_of_lt_of_le one_pos (le_max_right _ _))) v
  refine ⟨ν, hν, fun {ι n t} hn ht hK lab Q g' hg' => H hn lab Q _ ?_ g' hg'⟩
  have h := holeRadius_div_mem_Icc hε.le hn ht hK
  exact ⟨(le_div_iff₀ hn).1 h.1, (div_le_iff₀ hn).1 h.2⟩

/-- **One footprint ratio for the readings of the resizings.** Fix `ε₀ > 0` and a displacement
`v`. There is a ratio `ν > 0` such that the conclusion of `exists_resizing_footprintRatio` holds
for every reading after `v` of every guide uniform on the `2n`-blocks, with holes at the true
vertices of the reading.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 529–541`. -/
theorem exists_resizing_footprintRatio_reading {ε₀ : ℝ} (hε : 0 < ε₀) (v : ℝ × ℝ) :
    ∃ ν > 0, ∀ {ι : Type u} {n t : ℝ}, 0 < n → n < t → ∀ (lab : ℤ × ℤ → ι) (Q : ℤ × ℤ),
      ∀ r ∈ ({holeRadius ε₀ n t, holeRadius ε₀ (2 * n) t} : Set ℝ), ∀ g' : ℝ × ℝ → ι,
      IsDisplacedReading g' (blockGuide (2 * n) lab) v →
      HasTwoOwnerFootprints g' (closedBall (blockCorner (2 * n) Q) (2 * n * 1))
        {c | c ∈ closedBall (blockCorner (2 * n) Q) (2 * n * (1 + 1)) ∧ IsTrueVertex g' c} r
        (ν * (2 * n)) := by
  obtain ⟨ν, hν, H⟩ := exists_blockGuide_footprintRatio_reading.{u} (ρ := 1) (r₀ := ε₀ / 2)
    (r₁ := ε₀) (by positivity) v
  refine ⟨ν, hν, fun {ι n t} hn hnt lab Q r hr g' hg' => H (by positivity) lab Q r ?_ g' hg'⟩
  rcases hr with rfl | rfl
  · rw [holeRadius, min_eq_left hnt.le]
    exact ⟨by linarith, by nlinarith⟩
  · rw [holeRadius]
    refine ⟨?_, ?_⟩
    · have : n ≤ min (2 * n) t := le_min (by linarith) hnt.le
      nlinarith
    · have : min (2 * n) t ≤ 2 * n := min_le_left _ _
      nlinarith

/-- **Intermediate configurations of a resizing, for the readings.** With one ratio `ν > 0` for
the displacement `v`, the conclusion of `exists_resizing_footprintRatio_mixed` holds for every
reading after `v` of every guide uniform on the `2n`-blocks, with holes at the true vertices of
the reading, each of its own radius `h_n` or `h_{2n}`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 529–541`. -/
theorem exists_resizing_footprintRatio_mixed_reading {ε₀ : ℝ} (hε : 0 < ε₀) (v : ℝ × ℝ) :
    ∃ ν > 0, ∀ {ι : Type u} {n t : ℝ}, 0 < n → n < t → ∀ (lab : ℤ × ℤ → ι) (Q : ℤ × ℤ)
      (g' : ℝ × ℝ → ι), IsDisplacedReading g' (blockGuide (2 * n) lab) v →
      ∀ ρ : ℝ × ℝ → ℝ, (∀ c, ρ c = holeRadius ε₀ n t ∨ ρ c = holeRadius ε₀ (2 * n) t) →
      ∀ x p₁ p₂ p₃ : ℝ × ℝ, (∀ p ∈ ({p₁, p₂, p₃} : Set (ℝ × ℝ)),
        p ∈ (closedBall x (ν * (2 * n)) ∩ closedBall (blockCorner (2 * n) Q) (2 * n * 1)) \
          ⋃ c ∈ {c | c ∈ closedBall (blockCorner (2 * n) Q) (2 * n * (1 + 1)) ∧
            IsTrueVertex g' c}, ball c (ρ c)) →
      g' p₁ = g' p₂ ∨ g' p₁ = g' p₃ ∨ g' p₂ = g' p₃ := by
  obtain ⟨ν, hν, H⟩ := exists_resizing_footprintRatio_reading.{u} hε v
  refine ⟨ν, hν, fun {ι n t} hn hnt lab Q g' hg' ρ hρ x p₁ p₂ p₃ hp => ?_⟩
  have hle : holeRadius ε₀ n t ≤ holeRadius ε₀ (2 * n) t :=
    mul_le_mul_of_nonneg_left (min_le_min (by linarith) le_rfl) hε.le
  exact (H hn hnt lab Q _ (Or.inl rfl) g' hg').of_le_radii
    (fun c _ => (hρ c).elim (fun h => h.ge) fun h => h ▸ hle) x p₁ p₂ p₃
    (hp p₁ (by simp)) (hp p₂ (by simp)) (hp p₃ (by simp))

end TNLean.PEPS.Approximation
