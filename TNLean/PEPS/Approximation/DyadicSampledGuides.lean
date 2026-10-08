/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicGuideReadings
import TNLean.PEPS.Approximation.DyadicRimPatterns

/-!
# Readings of the guides of the schedule exist

The source samples each of its guides after one small generic displacement `v`. The estimates of
Lemma 7.2 pass to every reading after `v` of the formal guides of the schedule
(`TNLean.PEPS.Approximation.DyadicGuideReadings`). This file proves that such readings exist and
are unique, and that the separation of the true vertices of the temporary guides passes to them:

* a labelling that is eventually constant along every ray from every point has exactly one
  reading after every displacement;
* the labellings built from strict inequalities and floors of functions that are eventually
  affine along every ray are eventually constant along every ray. The sup-distance balls, the
  bands and their normal ratios, the central region and the grid blocks are of this kind;
* so the block guide, every guide of the repainting of a block with normal words on its bands,
  and these guides homogenized on finitely many open squares have readings after every
  displacement;
* the label regions of a reading lie in the closures of those of the labelling, so a true vertex
  of a reading is a true vertex of the labelling, and the outer holes of the readings of the
  temporary guides of the point treatment are disjoint.

That the source's sampled guides are these readings, for a generic displacement, is proved in
`TNLean.PEPS.Approximation.DyadicChamberSampling`.

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: guides and the tie convention
  (lines 69–80), the edge construction (lines 142–241), and the choice of `K₀` and `ε₀` (lines
  341–351).
-/

namespace TNLean.PEPS.Approximation

open Set Metric Filter Topology SquareEdge

/-! ### Labellings constant along rays -/

/-- A labelling is eventually constant along every ray: for every point `p` and direction `v`,
the label `f (p + ε v)` is the same for all small `ε > 0`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:71–77`. -/
def IsRayConstant {ι : Sort*} (f : ℝ × ℝ → ι) : Prop :=
  ∀ p v : ℝ × ℝ, ∃ c : ι, ∀ᶠ ε in 𝓝[>] (0 : ℝ), f (p + ε • v) = c

/-- A real function on the plane is eventually affine along every ray. -/
def IsRayAffine (φ : ℝ × ℝ → ℝ) : Prop :=
  ∀ p v : ℝ × ℝ, ∃ a b : ℝ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), φ (p + ε • v) = a + b * ε

/-- **Readings exist.** A labelling eventually constant along every ray has a reading after every
displacement.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:71–77`. -/
theorem IsRayConstant.exists_isDisplacedReading {ι : Type*} {f : ℝ × ℝ → ι}
    (h : IsRayConstant f) (v : ℝ × ℝ) : ∃ f', IsDisplacedReading f' f v := by
  choose c hc using fun p => h p v
  exact ⟨c, fun p => (hc p).mono fun _ hε => hε.symm⟩

/-- **Readings are unique.** Two readings of one labelling after one displacement agree. -/
theorem IsDisplacedReading.unique {X ι : Type*} [AddCommGroup X] [Module ℝ X] {f f₁ f₂ : X → ι}
    {v : X} (h₁ : IsDisplacedReading f₁ f v) (h₂ : IsDisplacedReading f₂ f v) : f₁ = f₂ :=
  funext fun p => by
    obtain ⟨ε, e₁, e₂⟩ := ((h₁ p).and (h₂ p)).exists
    rw [e₁, e₂]

section RayConstant

variable {ι κ μ : Sort*}

/-- A constant labelling is constant along rays. -/
theorem isRayConstant_const (c : ι) : IsRayConstant fun _ : ℝ × ℝ => c :=
  fun _ _ => ⟨c, Eventually.of_forall fun _ => rfl⟩

/-- Relabelling keeps a labelling eventually constant along rays. -/
theorem IsRayConstant.comp {f : ℝ × ℝ → ι} (h : IsRayConstant f) (F : ι → κ) :
    IsRayConstant fun q => F (f q) := fun p v => by
  obtain ⟨c, hc⟩ := h p v
  exact ⟨F c, hc.mono fun _ hε => by dsimp only; rw [hε]⟩

/-- Combining two labellings eventually constant along rays. -/
theorem IsRayConstant.comp₂ {f : ℝ × ℝ → ι} {g : ℝ × ℝ → κ} (hf : IsRayConstant f)
    (hg : IsRayConstant g) (F : ι → κ → μ) : IsRayConstant fun q => F (f q) (g q) := fun p v => by
  obtain ⟨a, ha⟩ := hf p v
  obtain ⟨b, hb⟩ := hg p v
  exact ⟨F a b, by filter_upwards [ha, hb] with ε e₁ e₂; rw [e₁, e₂]⟩

/-- A conjunction of conditions eventually decided along rays is eventually decided. -/
theorem IsRayConstant.and {P Q : ℝ × ℝ → Prop} (hP : IsRayConstant P) (hQ : IsRayConstant Q) :
    IsRayConstant fun q => P q ∧ Q q :=
  hP.comp₂ hQ And

/-- A finite conjunction of conditions eventually decided along rays is eventually decided. -/
theorem IsRayConstant.forall {α : Type*} [Finite α] {P : α → ℝ × ℝ → Prop}
    (h : ∀ k, IsRayConstant (P k)) : IsRayConstant fun q => ∀ k, P k q := fun p v => by
  choose c hc using fun k => h k p v
  refine ⟨∀ k, c k, ?_⟩
  filter_upwards [eventually_all.2 hc] with ε hε
  exact propext (forall_congr' fun k => by rw [hε k])

/-- A choice by a condition eventually decided along rays between two labellings eventually
constant along rays is eventually constant along rays. -/
theorem IsRayConstant.ite {P : ℝ × ℝ → Prop} {inst : DecidablePred P} (hP : IsRayConstant P)
    {f g : ℝ × ℝ → ι} (hf : IsRayConstant f) (hg : IsRayConstant g) :
    IsRayConstant fun q => if P q then f q else g q := fun p v => by
  obtain ⟨c, hc⟩ := hP p v
  obtain ⟨a, ha⟩ := hf p v
  obtain ⟨b, hb⟩ := hg p v
  by_cases h : c
  · refine ⟨a, ?_⟩
    filter_upwards [hc, ha] with ε e₁ e₂
    rw [ite_eq_left (by rw [e₁]; exact h), e₂]
  · refine ⟨b, ?_⟩
    filter_upwards [hc, hb] with ε e₁ e₂
    rw [ite_eq_right (by rw [e₁]; exact h), e₂]

/-- Translating the argument keeps a labelling eventually constant along rays. -/
theorem IsRayConstant.comp_add {f : ℝ × ℝ → ι} (h : IsRayConstant f) (o : ℝ × ℝ) :
    IsRayConstant fun q => f (q + o) := fun p v => by
  obtain ⟨c, hc⟩ := h (p + o) v
  exact ⟨c, hc.mono fun ε hε => by dsimp only; rw [add_right_comm]; exact hε⟩

/-- Moving a guide keeps it eventually constant along rays. -/
theorem IsRayConstant.shiftGuide {ι : Type*} {f : ℝ × ℝ → ι} (h : IsRayConstant f)
    (o : ℝ × ℝ) : IsRayConstant (shiftGuide o f) := fun p v => by
  simpa only [Approximation.shiftGuide, sub_eq_add_neg] using h.comp_add (-o) p v

end RayConstant

/-! ### Functions eventually affine along rays -/

/-- An affine function of `ε` tends to its value at zero. -/
theorem tendsto_affine_nhdsGT (a b : ℝ) :
    Tendsto (fun ε : ℝ => a + b * ε) (𝓝[>] 0) (𝓝 a) := by
  have h : Tendsto (fun ε : ℝ => a + b * ε) (𝓝 0) (𝓝 (a + b * 0)) :=
    (continuous_const.add (continuous_const.mul continuous_id)).tendsto 0
  rw [mul_zero, add_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- An affine function of `ε` has eventually constant sign as `ε` decreases to zero. -/
theorem eventually_affine_trichotomy (a b : ℝ) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), a + b * ε < 0) ∨ (∀ᶠ ε in 𝓝[>] (0 : ℝ), a + b * ε = 0) ∨
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < a + b * ε := by
  have hT := tendsto_affine_nhdsGT a b
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · exact Or.inl (hT.eventually_lt_const ha)
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · exact Or.inl (hpos.mono fun ε hε => by nlinarith)
    · exact Or.inr (Or.inl (Eventually.of_forall fun ε => by ring))
    · exact Or.inr (Or.inr (hpos.mono fun ε hε => by nlinarith))
  · exact Or.inr (Or.inr (hT.eventually_const_lt ha))

/-- Constants are affine along rays. -/
theorem isRayAffine_const (c : ℝ) : IsRayAffine fun _ => c :=
  fun _ _ => ⟨c, 0, Eventually.of_forall fun _ => by ring⟩

/-- The first coordinate is affine along rays. -/
theorem isRayAffine_fst : IsRayAffine Prod.fst :=
  fun p v => ⟨p.1, v.1, Eventually.of_forall fun ε => by simp [mul_comm]⟩

/-- The second coordinate is affine along rays. -/
theorem isRayAffine_snd : IsRayAffine Prod.snd :=
  fun p v => ⟨p.2, v.2, Eventually.of_forall fun ε => by simp [mul_comm]⟩

section Affine

variable {φ ψ : ℝ × ℝ → ℝ}

/-- Subtracting from a constant keeps a function eventually affine along rays. -/
theorem IsRayAffine.const_sub (hφ : IsRayAffine φ) (c : ℝ) : IsRayAffine fun q => c - φ q :=
  fun p v => by
    obtain ⟨a, b, h⟩ := hφ p v
    exact ⟨c - a, -b, h.mono fun ε e => by dsimp only; rw [e]; ring⟩

/-- Differences of functions eventually affine along rays are eventually affine along rays. -/
theorem IsRayAffine.sub (hφ : IsRayAffine φ) (hψ : IsRayAffine ψ) :
    IsRayAffine fun q => φ q - ψ q := fun p v => by
  obtain ⟨a₁, b₁, h₁⟩ := hφ p v
  obtain ⟨a₂, b₂, h₂⟩ := hψ p v
  exact ⟨a₁ - a₂, b₁ - b₂, by filter_upwards [h₁, h₂] with ε e₁ e₂; rw [e₁, e₂]; ring⟩

/-- Constant multiples keep a function eventually affine along rays. -/
theorem IsRayAffine.const_mul (hφ : IsRayAffine φ) (c : ℝ) : IsRayAffine fun q => c * φ q :=
  fun p v => by
    obtain ⟨a, b, h⟩ := hφ p v
    exact ⟨c * a, c * b, h.mono fun ε e => by dsimp only; rw [e]; ring⟩

/-- Dividing by a constant keeps a function eventually affine along rays. -/
theorem IsRayAffine.div_const (hφ : IsRayAffine φ) (c : ℝ) : IsRayAffine fun q => φ q / c :=
  fun p v => by
    obtain ⟨a, b, h⟩ := hφ p v
    exact ⟨a / c, b / c, h.mono fun ε e => by dsimp only; rw [e]; ring⟩

/-- The minimum of two functions eventually affine along rays is eventually affine along rays. -/
theorem IsRayAffine.min (hφ : IsRayAffine φ) (hψ : IsRayAffine ψ) :
    IsRayAffine fun q => min (φ q) (ψ q) := fun p v => by
  obtain ⟨a₁, b₁, h₁⟩ := hφ p v
  obtain ⟨a₂, b₂, h₂⟩ := hψ p v
  rcases eventually_affine_trichotomy (a₂ - a₁) (b₂ - b₁) with h | h | h
  · refine ⟨a₂, b₂, ?_⟩
    filter_upwards [h₁, h₂, h] with ε e₁ e₂ e
    rw [e₁, e₂, min_eq_right (by nlinarith)]
  · refine ⟨a₁, b₁, ?_⟩
    filter_upwards [h₁, h₂, h] with ε e₁ e₂ e
    rw [e₁, e₂, min_eq_left (by nlinarith)]
  · refine ⟨a₁, b₁, ?_⟩
    filter_upwards [h₁, h₂, h] with ε e₁ e₂ e
    rw [e₁, e₂, min_eq_left (by nlinarith)]

/-- A strict inequality between functions eventually affine along rays is eventually decided
along rays. -/
theorem IsRayAffine.isRayConstant_lt (hφ : IsRayAffine φ) (hψ : IsRayAffine ψ) :
    IsRayConstant fun q => φ q < ψ q := fun p v => by
  obtain ⟨a₁, b₁, h₁⟩ := hφ p v
  obtain ⟨a₂, b₂, h₂⟩ := hψ p v
  rcases eventually_affine_trichotomy (a₂ - a₁) (b₂ - b₁) with h | h | h
  · refine ⟨False, ?_⟩
    filter_upwards [h₁, h₂, h] with ε e₁ e₂ e
    exact eq_false (by rw [e₁, e₂]; exact not_lt.2 (by nlinarith))
  · refine ⟨False, ?_⟩
    filter_upwards [h₁, h₂, h] with ε e₁ e₂ e
    exact eq_false (by rw [e₁, e₂]; exact not_lt.2 (by nlinarith))
  · refine ⟨True, ?_⟩
    filter_upwards [h₁, h₂, h] with ε e₁ e₂ e
    exact eq_true (by rw [e₁, e₂]; nlinarith)

/-- A strict upper bound on a quotient of functions eventually affine along rays is eventually
decided along rays, with the convention `x / 0 = 0`. -/
theorem IsRayAffine.isRayConstant_div_lt (hφ : IsRayAffine φ) (hψ : IsRayAffine ψ) (t : ℝ) :
    IsRayConstant fun q => φ q / ψ q < t := fun p v => by
  obtain ⟨a, b, hb⟩ := hψ p v
  rcases eventually_affine_trichotomy a b with h | h | h
  · obtain ⟨c, hc⟩ := (hψ.const_mul t).isRayConstant_lt hφ p v
    refine ⟨c, ?_⟩
    filter_upwards [hb, h, hc] with ε e₁ e₂ e₃
    rw [← e₃]
    exact propext (div_lt_iff_of_neg (e₁ ▸ e₂))
  · refine ⟨0 < t, ?_⟩
    filter_upwards [hb, h] with ε e₁ e₂
    rw [e₁, e₂, div_zero]
  · obtain ⟨c, hc⟩ := hφ.isRayConstant_lt (hψ.const_mul t) p v
    refine ⟨c, ?_⟩
    filter_upwards [hb, h, hc] with ε e₁ e₂ e₃
    rw [← e₃]
    exact propext (div_lt_iff₀ (e₁ ▸ e₂))

/-- The integer part of a function eventually affine along rays is eventually constant along
rays. -/
theorem IsRayAffine.isRayConstant_floor (hφ : IsRayAffine φ) : IsRayConstant fun q => ⌊φ q⌋ :=
  fun p v => by
    obtain ⟨a, b, h⟩ := hφ p v
    have hT := tendsto_affine_nhdsGT a b
    have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    rcases le_or_gt 0 b with hb | hb
    · refine ⟨⌊a⌋, ?_⟩
      filter_upwards [h, hpos, hT.eventually_lt_const (Int.lt_floor_add_one a)] with ε e hε hlt
      rw [e, Int.floor_eq_iff]
      exact ⟨(Int.floor_le a).trans (by nlinarith), hlt⟩
    · have hc : ((⌈a⌉ - 1 : ℤ) : ℝ) < a := by push_cast; linarith [Int.ceil_lt_add_one a]
      refine ⟨⌈a⌉ - 1, ?_⟩
      filter_upwards [h, hpos, hT.eventually_const_lt hc] with ε e hε hlt
      rw [e, Int.floor_eq_iff]
      refine ⟨hlt.le, ?_⟩
      push_cast
      nlinarith [Int.le_ceil a]

end Affine

/-! ### The pieces of the guides -/

/-- The parallel coordinate of an edge is affine along rays. -/
theorem isRayAffine_par (e : SquareEdge) : IsRayAffine e.par := by
  cases e
  exacts [isRayAffine_fst, isRayAffine_snd, isRayAffine_fst, isRayAffine_snd]

/-- The normal coordinate of an edge is affine along rays. -/
theorem isRayAffine_nor (n : ℝ) (e : SquareEdge) : IsRayAffine (e.nor n) := by
  cases e
  exacts [isRayAffine_snd, isRayAffine_fst.const_sub n, isRayAffine_snd.const_sub n,
    isRayAffine_fst]

/-- The band width `w(s)` is eventually affine along rays. -/
theorem isRayAffine_bandWidth (n : ℝ) (e : SquareEdge) :
    IsRayAffine fun q => bandWidth n (e.par q) :=
  ((isRayAffine_par e).min ((isRayAffine_par e).const_sub n)).div_const 1000

/-- Membership in a band is eventually decided along rays. -/
theorem isRayConstant_mem_edgeBand (n : ℝ) (e : SquareEdge) (α β : ℝ) :
    IsRayConstant fun q => q ∈ edgeBand n e α β :=
  ((isRayAffine_const 0).isRayConstant_lt (isRayAffine_par e)).and
    (((isRayAffine_par e).isRayConstant_lt (isRayAffine_const n)).and
    ((((isRayAffine_bandWidth n e).const_mul α).isRayConstant_lt (isRayAffine_nor n e)).and
    ((isRayAffine_nor n e).isRayConstant_lt ((isRayAffine_bandWidth n e).const_mul β))))

/-- Membership in the central region is eventually decided along rays. -/
theorem isRayConstant_mem_centralRegion (n : ℝ) :
    IsRayConstant fun q => q ∈ centralRegion n :=
  ((isRayAffine_const 0).isRayConstant_lt isRayAffine_fst).and
    ((isRayAffine_fst.isRayConstant_lt (isRayAffine_const n)).and
    (((isRayAffine_const 0).isRayConstant_lt isRayAffine_snd).and
    ((isRayAffine_snd.isRayConstant_lt (isRayAffine_const n)).and
    (IsRayConstant.forall fun e =>
      (isRayAffine_bandWidth n e).isRayConstant_lt (isRayAffine_nor n e)))))

/-- The open sup square about a point is eventually decided along rays. -/
theorem isRayConstant_mem_ball (c : ℝ × ℝ) (r : ℝ) : IsRayConstant fun q => q ∈ ball c r := by
  have h1 := isRayAffine_fst.sub (isRayAffine_const c.1)
  have h2 := isRayAffine_snd.sub (isRayAffine_const c.2)
  have key : (fun q : ℝ × ℝ => q ∈ ball c r) = fun q =>
      ((-r < q.1 - c.1 ∧ q.1 - c.1 < r) ∧ (-r < q.2 - c.2 ∧ q.2 - c.2 < r)) := by
    funext q
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt]
  rw [key]
  exact (((isRayAffine_const (-r)).isRayConstant_lt h1).and
    (h1.isRayConstant_lt (isRayAffine_const r))).and
    (((isRayAffine_const (-r)).isRayConstant_lt h2).and (h2.isRayConstant_lt (isRayAffine_const r)))

/-- A normal word read through the normal ratio of an edge is eventually constant along rays. -/
theorem isRayConstant_bandWord {ι : Type*} (n : ℝ) (e : SquareEdge) (c : ι)
    (l : List (ℝ × ι)) : IsRayConstant fun q => bandWord c l (bandCoord n e q) := by
  induction l generalizing c with
  | nil => exact isRayConstant_const c
  | cons q rest ih =>
    obtain ⟨t, l'⟩ := q
    simp only [bandWord]
    exact ((isRayAffine_nor n e).isRayConstant_div_lt (isRayAffine_bandWidth n e) t).ite
      (isRayConstant_const c) (ih l')

/-- Replacing a band by a normal word keeps a guide eventually constant along rays. -/
theorem IsRayConstant.bandUpdate {ι : Type*} {g : ℝ × ℝ → ι} (hg : IsRayConstant g) (n : ℝ)
    (e : SquareEdge) (c : ι) (l : List (ℝ × ι)) :
    IsRayConstant (bandUpdate n e (bandWord c l) g) :=
  (isRayConstant_mem_edgeBand n e (-8) 2).ite (isRayConstant_bandWord n e c l) hg

/-- Homogenizing on finitely many open squares about grid corners keeps a guide eventually
constant along rays. -/
theorem IsRayConstant.homogenize {ι : Type*} {g : ℝ × ℝ → ι} (hg : IsRayConstant g)
    (M : Finset (ℤ × ℤ)) (n t : ℝ) (P : ι) :
    IsRayConstant (homogenize (⋃ Q ∈ M, ball (blockCorner n Q) t) P g) := by
  have hU : IsRayConstant fun q => q ∈ ⋃ Q ∈ M, ball (blockCorner n Q) t := by
    have key : (fun q => q ∈ ⋃ Q ∈ M, ball (blockCorner n Q) t) =
        fun q => ¬ ∀ Q : M, ¬ q ∈ ball (blockCorner n Q.1) t := by
      funext q
      simp only [mem_iUnion, exists_prop, Subtype.forall, not_forall, not_not]
    rw [key]
    exact (IsRayConstant.forall fun Q : M =>
      (isRayConstant_mem_ball (blockCorner n Q.1) t).comp Not).comp Not
  exact hU.ite (isRayConstant_const P) hg

/-- A block guide is eventually constant along rays. -/
theorem isRayConstant_blockGuide {ι : Type*} (n : ℝ) (lab : ℤ × ℤ → ι) :
    IsRayConstant (blockGuide n lab) :=
  ((isRayAffine_fst.div_const n).isRayConstant_floor.comp₂
    (isRayAffine_snd.div_const n).isRayConstant_floor fun a b => lab (a, b))

/-! ### The guides of the schedule -/

namespace RepaintingBaseline

variable {ι : Type*} (R : RepaintingBaseline ι)

/-- The auxiliary guides with a normal word are eventually constant along rays. -/
theorem isRayConstant_auxGuide (e : SquareEdge) (c : ι) (l : List (ℝ × ι)) :
    IsRayConstant (R.auxGuide e (bandWord c l)) :=
  (isRayConstant_const _).bandUpdate R.n e c l

variable (hR : IsRayConstant R.guide)
include hR

/-- The guide after the central birth is eventually constant along rays. -/
theorem isRayConstant_centralGuide : IsRayConstant R.centralGuide :=
  (isRayConstant_mem_centralRegion R.n).ite (isRayConstant_const _) hR

/-- The guides after completed edges are eventually constant along rays. -/
theorem isRayConstant_completedGuide (E : List SquareEdge) :
    IsRayConstant (R.completedGuide E) := by
  induction E with
  | nil => exact R.isRayConstant_centralGuide hR
  | cons e E ih => exact ih.bandUpdate R.n e _ _

/-- The main guides with a normal word are eventually constant along rays. -/
theorem isRayConstant_mainGuide (E : List SquareEdge) (e : SquareEdge) (c : ι)
    (l : List (ℝ × ι)) : IsRayConstant (R.mainGuide E e (bandWord c l)) :=
  (R.isRayConstant_completedGuide hR E).bandUpdate R.n e c l

/-- **The unmodified guides are eventually constant along rays.** -/
theorem IsUnmodifiedGuide.isRayConstant {g : ℝ × ℝ → ι} (hg : R.IsUnmodifiedGuide g) :
    IsRayConstant g := by
  rcases hg with rfl | rfl | ⟨E, rfl⟩ | ⟨E, e, W, hW, rfl⟩ | ⟨e, W, hW, rfl⟩
  · exact hR
  · exact R.isRayConstant_centralGuide hR
  · exact R.isRayConstant_completedGuide hR E
  · obtain ⟨c, l, rfl, -⟩ := exists_eq_bandWord_of_mem_mainWords hW
    exact R.isRayConstant_mainGuide hR E e c l
  · obtain ⟨c, l, rfl, -⟩ := exists_eq_bandWord_of_mem_auxWords hW
    exact R.isRayConstant_auxGuide e c l

end RepaintingBaseline

/-- Every normal word of the construction along an edge is a normal word `bandWord c l`. -/
theorem exists_eq_bandWord_of_mem_edgeWords {ι : Type*} {A B C : ι} {W : ℝ → ι}
    (hW : W ∈ edgeWords A B C) : ∃ c l, W = bandWord c l := by
  rcases hW with rfl | ⟨op, hop, rfl | rfl | rfl⟩
  · exact ⟨_, _, rfl⟩
  all_goals
    simp only [edgeOperations, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩

section Schedule

variable {ι : Type*} {n : ℝ} (hn : 0 < n) (lab : ℤ × ℤ → ι) (S : ℤ × ℤ) (B : ι)

local notation "R" => blockBaseline hn lab S B
local notation "o" => blockCorner n S

/-- **The guides of the schedule have readings.** The block guide, the guides of the repainting
of the block `S` after the central birth and after completed edges, and the main and auxiliary
guides along an edge with any normal word on its band, all placed on the block, have readings
after every displacement `v`, and these readings are unique.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 142–241`. -/
theorem isRayConstant_blockSchedule :
    IsRayConstant (blockGuide n lab) ∧ IsRayConstant (shiftGuide o (R).centralGuide) ∧
      (∀ E, IsRayConstant (shiftGuide o ((R).completedGuide E))) ∧
      (∀ E e (c : ι) l, IsRayConstant (shiftGuide o ((R).mainGuide E e (bandWord c l)))) ∧
      ∀ e (c : ι) l, IsRayConstant (shiftGuide o ((R).auxGuide e (bandWord c l))) := by
  have hR : IsRayConstant (R).guide := (isRayConstant_blockGuide n lab).comp_add o
  exact ⟨isRayConstant_blockGuide n lab, ((R).isRayConstant_centralGuide hR).shiftGuide o,
    fun E => ((R).isRayConstant_completedGuide hR E).shiftGuide o,
    fun E e c l => ((R).isRayConstant_mainGuide hR E e c l).shiftGuide o,
    fun e c l => ((R).isRayConstant_auxGuide e c l).shiftGuide o⟩

/-- **The guides of one lens exchange have readings.** After every displacement `v` there are
readings of the main guide with the starting word and of the auxiliary guide with the auxiliary
word along every edge, so `blockRepainting_exchange_of_reading` applies to them.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 199–214`. -/
theorem exists_readings_exchange (E : List SquareEdge) (e : SquareEdge) (v : ℝ × ℝ) :
    (∃ gm, IsDisplacedReading gm
      (shiftGuide o ((R).mainGuide E e (edgeStartWord (lab S) B (lab (e.nbrBlock S))))) v) ∧
    ∃ gx, IsDisplacedReading gx
      (shiftGuide o ((R).auxGuide e (auxWord (lab S) B (lab (e.nbrBlock S))))) v :=
  ⟨((isRayConstant_blockSchedule hn lab S B).2.2.2.1 E e _ _).exists_isDisplacedReading v,
    ((isRayConstant_blockSchedule hn lab S B).2.2.2.2 e _ _).exists_isDisplacedReading v⟩

end Schedule

/-! ### True vertices of readings -/

/-- The region of a label in a reading lies in the closure of its region in the labelling. -/
theorem IsDisplacedReading.preimage_subset_closure {ι : Type*} {f f' : ℝ × ℝ → ι} {v : ℝ × ℝ}
    (h : IsDisplacedReading f' f v) (l : ι) : f' ⁻¹' {l} ⊆ closure (f ⁻¹' {l}) := fun p hp =>
  mem_closure_of_tendsto (tendsto_add_smul_nhdsGT p v)
    ((h p).mono fun ε hε => by rw [mem_preimage, ← hε]; exact hp)

/-- **A true vertex of a reading is a true vertex of the labelling.** -/
theorem IsDisplacedReading.isTrueVertex {ι : Type*} {f f' : ℝ × ℝ → ι} {v : ℝ × ℝ}
    (h : IsDisplacedReading f' f v) {c : ℝ × ℝ} (hc : IsTrueVertex f' c) : IsTrueVertex f c := by
  have key (l : ι) : closure (f' ⁻¹' {l}) ⊆ closure (f ⁻¹' {l}) :=
    closure_minimal (h.preimage_subset_closure l) isClosed_closure
  obtain ⟨l₁, l₂, l₃, h12, h13, h23, h1, h2, h3⟩ := hc
  exact ⟨l₁, l₂, l₃, h12, h13, h23, key _ h1, key _ h2, key _ h3⟩

/-- **Disjoint outer holes in the readings of the temporary guides.** Let `20 t < n` and
`ε₀ < 1/4000`. Every unmodified guide of the repainting of a block, homogenized on the open
squares of radius `t` about finitely many grid corners, has a reading after every displacement,
and the closed outer hole squares of radius `2 ε₀ t` about distinct true vertices of any such
reading are disjoint.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 341–351`. -/
theorem homogenize_reading_outerHoles_disjoint {ι : Type*} {n t ε₀ : ℝ} (hn : 0 < n)
    (ht : 0 < t) (htn : 20 * t < n) (hε : ε₀ < 1 / 4000) {lab : ℤ × ℤ → ι} {S : ℤ × ℤ}
    {B : ι} {g : ℝ × ℝ → ι} (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g)
    (M : Finset (ℤ × ℤ)) (P : ι) (v : ℝ × ℝ) :
    (∃ g', IsDisplacedReading g'
      (homogenize (⋃ Q ∈ M, ball (blockCorner n Q) t) P (shiftGuide (blockCorner n S) g)) v) ∧
    ∀ g', IsDisplacedReading g'
      (homogenize (⋃ Q ∈ M, ball (blockCorner n Q) t) P (shiftGuide (blockCorner n S) g)) v →
      ∀ c₁ c₂, IsTrueVertex g' c₁ → IsTrueVertex g' c₂ → c₁ ≠ c₂ →
        Disjoint (closedBall c₁ (2 * ε₀ * t)) (closedBall c₂ (2 * ε₀ * t)) := by
  refine ⟨?_, fun g' hg' c₁ c₂ h₁ h₂ hne =>
    homogenize_outerHoles_disjoint hn ht htn hε hg M P (hg'.isTrueVertex h₁)
      (hg'.isTrueVertex h₂) hne⟩
  have hgr : IsRayConstant (shiftGuide (blockCorner n S) g) :=
    (hg.isRayConstant _ ((isRayConstant_blockGuide n lab).comp_add _)).shiftGuide _
  exact (hgr.homogenize M n t P).exists_isDisplacedReading v

end TNLean.PEPS.Approximation
