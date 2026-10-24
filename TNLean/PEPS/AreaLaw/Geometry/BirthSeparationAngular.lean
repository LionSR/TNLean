/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic.IntervalCases

/-!
# Angular separation at an integer contact mark

In coordinates normalized so that a removal square is `[-1, 1]²`, every mark is
an integer point `q`. The local regions compared in the birth-separation lemma
are built from closed half-planes `a x₁ + b x₂ ≤ n` with integers `a, b, n`
satisfying `|a| + |b| ≤ 2`: axis and diagonal lines with integer levels.

Near `q`, within sup distance `1/4`, such a set is described by its section
`{d : ‖d‖ = 1, q + d/4 ∈ P}` of the unit sphere of the maximum norm.

* *Radial extension.* A level not passing through `q` has integer discrepancy
  at least one at `q`, whereas its variation over the quarter-square is at most
  one half. A level through `q` is homogeneous along rays from `q`. Hence
  membership is unchanged along the punctured radial segments of length `1/4`.
* *Box saturation.* For a unit direction `d`, the box with corners `⌊d⌋` and
  `⌈d⌉` is the closed elementary half-side of the sphere containing `d`, or the
  vertex `d` itself. Membership of `d` in a section forces the whole box.
* *Integer gap.* Two disjoint boxes with integer endpoints are at sup distance at
  least one. Hence two sections without common directions are at distance one.
* *Angular estimate.* For unit directions with `‖d - e‖ ≥ 1` and radii
  `r, s ≥ 0`, `‖r d - s e‖ ≥ max r s / 2`.

All of these properties are preserved by arbitrary unions and intersections.
The final statement says that two such sets which meet in the closed
quarter-square only at `q` satisfy `‖x - y‖ ≥ max ‖x - q‖ ‖y - q‖ / 2` there.
This is the angular constant `1/2` of the contact estimate, valid for closed
endpoints and zero displacements, without enumerating colorings.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:birth-separation`, lines 573–659,
especially the angular estimate `geometry:angular-gap`, lines 627–645.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Manuscript file:
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
`build/sections/10-geometry.tex`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-! ### The angular estimate -/

/-- **Sup-norm angular estimate.** Unit directions at sup distance at least one,
scaled by nonnegative radii, are at distance at least half the larger radius.
Source: area-law Section 11, `geometry:angular-gap`, lines 627–645. -/
theorem half_max_le_norm_smul_sub_smul {d e : ℝ × ℝ} (hd : ‖d‖ = 1) (he : ‖e‖ = 1)
    (hde : 1 ≤ ‖d - e‖) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    max r s / 2 ≤ ‖r • d - s • e‖ := by
  -- The case `s ≤ r`, for arbitrary unit directions at distance one.
  have key : ∀ {d e : ℝ × ℝ} {r s : ℝ}, ‖d‖ = 1 → ‖e‖ = 1 → 1 ≤ ‖d - e‖ →
      0 ≤ s → s ≤ r → r / 2 ≤ ‖r • d - s • e‖ := by
    intro d e r s hd he hde hs hsr
    have hr : 0 ≤ r := hs.trans hsr
    have h₁ : r - s ≤ ‖r • d - s • e‖ := by
      have := norm_sub_norm_le (r • d) (s • e)
      simpa [norm_smul, hd, he, Real.norm_eq_abs, abs_of_nonneg hr,
        abs_of_nonneg hs] using this
    have h₂ : r ≤ ‖r • d - s • e‖ + (r - s) := by
      have hsplit : r • d - r • e = (r • d - s • e) + (s - r) • e := by
        rw [sub_smul]; abel
      have h := norm_add_le (r • d - s • e) ((s - r) • e)
      rw [← hsplit, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr,
        norm_smul, he, Real.norm_eq_abs, abs_of_nonpos (by linarith), mul_one] at h
      nlinarith
    linarith
  rcases le_total s r with hsr | hrs
  · rw [max_eq_left hsr]; exact key hd he hde hs hsr
  · rw [max_eq_right hrs, norm_sub_rev]
    exact key he hd (by rwa [norm_sub_rev]) hr hrs

/-! ### Integer boxes on the unit sphere -/

/-- The box with corners `⌊d⌋` and `⌈d⌉`. For a unit direction of the maximum
norm it is the closed elementary half-side containing `d`, or the vertex `d`.
Source: area-law Section 11, `geometry:birth-separation`, lines 627–645. -/
def unitBox (d : ℝ × ℝ) : Set (ℝ × ℝ) :=
  Set.Icc (⌊d.1⌋ : ℝ) ⌈d.1⌉ ×ˢ Set.Icc (⌊d.2⌋ : ℝ) ⌈d.2⌉

private theorem floor_le_ceil_of_abs_sub_lt {s t : ℝ} (h : |s - t| < 1) :
    ⌊s⌋ ≤ ⌈t⌉ := by
  have h1 : (⌊s⌋ : ℝ) < ⌈t⌉ + 1 := by
    have := Int.floor_le s; have := Int.le_ceil t
    linarith [(abs_lt.mp h).2]
  exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast h1)

/-- **Integer gap.** Two points whose integer boxes are disjoint are at sup
distance at least one.
Source: area-law Section 11, `geometry:birth-separation`, lines 627–645. -/
theorem one_le_norm_sub_of_disjoint_unitBox {d e : ℝ × ℝ}
    (h : Disjoint (unitBox d) (unitBox e)) : 1 ≤ ‖d - e‖ := by
  by_contra hlt
  push Not at hlt
  have h1 : |d.1 - e.1| < 1 := by
    have := norm_fst_le (d - e); rw [Real.norm_eq_abs] at this
    simp only [Prod.fst_sub] at this; linarith
  have h2 : |d.2 - e.2| < 1 := by
    have := norm_snd_le (d - e); rw [Real.norm_eq_abs] at this
    simp only [Prod.snd_sub] at this; linarith
  have h1' : |e.1 - d.1| < 1 := by rwa [abs_sub_comm]
  have h2' : |e.2 - d.2| < 1 := by rwa [abs_sub_comm]
  have k1 : ⌊d.1⌋ ≤ ⌈e.1⌉ := floor_le_ceil_of_abs_sub_lt h1
  have k2 : ⌊d.2⌋ ≤ ⌈e.2⌉ := floor_le_ceil_of_abs_sub_lt h2
  have k1' : ⌊e.1⌋ ≤ ⌈d.1⌉ := floor_le_ceil_of_abs_sub_lt h1'
  have k2' : ⌊e.2⌋ ≤ ⌈d.2⌉ := floor_le_ceil_of_abs_sub_lt h2'
  have l1 := Int.floor_le_ceil d.1
  have l2 := Int.floor_le_ceil d.2
  have l1' := Int.floor_le_ceil e.1
  have l2' := Int.floor_le_ceil e.2
  let p : ℝ × ℝ := (((max ⌊d.1⌋ ⌊e.1⌋ : ℤ) : ℝ), ((max ⌊d.2⌋ ⌊e.2⌋ : ℤ) : ℝ))
  have hpd : p ∈ unitBox d := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [p] <;> norm_cast <;> omega
  have hpe : p ∈ unitBox e := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [p] <;> norm_cast <;> omega
  exact Set.disjoint_left.mp h hpd hpe

/-- A coordinate of a unit direction has absolute value at most one, and some
coordinate has absolute value one. -/
private theorem unit_cases {d : ℝ × ℝ} (hd : ‖d‖ = 1) :
    |d.1| ≤ 1 ∧ |d.2| ≤ 1 ∧ (|d.1| = 1 ∨ |d.2| = 1) := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at hd
  refine ⟨hd ▸ le_max_left _ _, hd ▸ le_max_right _ _, ?_⟩
  rcases max_choice |d.1| |d.2| with h | h <;> rw [h] at hd <;> simp [hd]

private theorem icc_floor_ceil_of_abs_eq_one {t s : ℝ} (ht : |t| = 1)
    (hs : s ∈ Set.Icc (⌊t⌋ : ℝ) ⌈t⌉) : s = t := by
  rcases abs_eq (zero_le_one) |>.mp ht with h | h <;> subst h <;>
    · norm_num at hs; exact hs

private theorem abs_le_one_of_icc_floor_ceil {t s : ℝ} (ht : |t| ≤ 1)
    (hs : s ∈ Set.Icc (⌊t⌋ : ℝ) ⌈t⌉) : |s| ≤ 1 := by
  obtain ⟨h1, h2⟩ := abs_le.mp ht
  have hf : (-1 : ℤ) ≤ ⌊t⌋ := Int.le_floor.mpr (by push_cast; linarith)
  have hc : ⌈t⌉ ≤ (1 : ℤ) := Int.ceil_le.mpr (by push_cast; linarith)
  have hf' : (-1 : ℝ) ≤ ⌊t⌋ := by exact_mod_cast hf
  have hc' : (⌈t⌉ : ℝ) ≤ 1 := by exact_mod_cast hc
  exact abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- The integer box of a unit direction lies on the unit sphere.
Source: area-law Section 11, `geometry:birth-separation`, lines 627–645. -/
theorem norm_eq_one_of_mem_unitBox {d e : ℝ × ℝ} (hd : ‖d‖ = 1)
    (he : e ∈ unitBox d) : ‖e‖ = 1 := by
  obtain ⟨h1, h2, h12⟩ := unit_cases hd
  have e1 := abs_le_one_of_icc_floor_ceil h1 he.1
  have e2 := abs_le_one_of_icc_floor_ceil h2 he.2
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  rcases h12 with h | h
  · rw [icc_floor_ceil_of_abs_eq_one h he.1, h]; exact max_eq_left e2
  · rw [icc_floor_ceil_of_abs_eq_one h he.2, h]; exact max_eq_right e1

/-! ### Quarter sections and sectorial sets -/

/-- The point at sup distance `1/4` from `q` on the ray through `x`.
Source: area-law Section 11, `geometry:birth-separation`, lines 627–645. -/
def quarterRadialPoint (q x : ℝ × ℝ) : ℝ × ℝ :=
  q + (4 * ‖x - q‖)⁻¹ • (x - q)

/-- A set is *quarter-sectorial* at `q` if membership is unchanged along the
punctured radial segments of length `1/4` from `q`, and membership of
`q + d/4` for a unit direction `d` forces membership of `q + e/4` for every
`e` in the integer box of `d`. Closed axis-and-diagonal polygonal sets with
integer levels have this property at every integer point.
Source: area-law Section 11, `geometry:birth-separation`, lines 627–645. -/
structure IsQuarterSectorial (q : ℝ × ℝ) (P : Set (ℝ × ℝ)) : Prop where
  /-- Radial extension of membership. -/
  radial : ∀ x, 0 < ‖x - q‖ → ‖x - q‖ ≤ 1 / 4 → (x ∈ P ↔ quarterRadialPoint q x ∈ P)
  /-- Saturation of the quarter section along integer boxes. -/
  box : ∀ d, ‖d‖ = 1 → q + (1 / 4 : ℝ) • d ∈ P →
    ∀ e ∈ unitBox d, q + (1 / 4 : ℝ) • e ∈ P

theorem IsQuarterSectorial.iUnion {ι : Sort*} {q : ℝ × ℝ} {P : ι → Set (ℝ × ℝ)}
    (h : ∀ i, IsQuarterSectorial q (P i)) : IsQuarterSectorial q (⋃ i, P i) where
  radial x h0 h1 := by simp only [Set.mem_iUnion]; exact exists_congr fun i ↦ (h i).radial x h0 h1
  box d hd hm e he := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hm
    exact Set.mem_iUnion.mpr ⟨i, (h i).box d hd hi e he⟩

theorem IsQuarterSectorial.iInter {ι : Sort*} {q : ℝ × ℝ} {P : ι → Set (ℝ × ℝ)}
    (h : ∀ i, IsQuarterSectorial q (P i)) : IsQuarterSectorial q (⋂ i, P i) where
  radial x h0 h1 := by simp only [Set.mem_iInter]; exact forall_congr' fun i ↦ (h i).radial x h0 h1
  box d hd hm e he := Set.mem_iInter.mpr fun i ↦ (h i).box d hd (Set.mem_iInter.mp hm i) e he

theorem IsQuarterSectorial.union {q : ℝ × ℝ} {P P' : Set (ℝ × ℝ)}
    (h : IsQuarterSectorial q P) (h' : IsQuarterSectorial q P') :
    IsQuarterSectorial q (P ∪ P') := by
  rw [Set.union_eq_iUnion]; exact .iUnion fun b ↦ by cases b <;> assumption

theorem IsQuarterSectorial.inter {q : ℝ × ℝ} {P P' : Set (ℝ × ℝ)}
    (h : IsQuarterSectorial q P) (h' : IsQuarterSectorial q P') :
    IsQuarterSectorial q (P ∩ P') := by
  rw [Set.inter_eq_iInter]; exact .iInter fun b ↦ by cases b <;> assumption

/-! ### Integer half-planes -/

/-- The closed half-plane `a x₁ + b x₂ ≤ n`.
Source: area-law Section 11, lines 393–417 and 573–659. -/
def intHalfPlane (a b n : ℤ) : Set (ℝ × ℝ) :=
  {x | (a : ℝ) * x.1 + b * x.2 ≤ n}

/-- On a closed elementary half-side, a homogeneous inequality with
`|α| + |β| ≤ 2` holding at an interior parameter holds at both endpoints. -/
private theorem homogeneous_endpoints {α β m : ℤ} (hαβ : |α| + |β| ≤ 2)
    (hm : m = -1 ∨ m = 0) {t : ℝ} (ht₀ : (m : ℝ) < t) (ht₁ : t < m + 1)
    (h : (α : ℝ) + β * t ≤ 0) :
    (α : ℝ) + β * m ≤ 0 ∧ (α : ℝ) + β * (m + 1) ≤ 0 := by
  have hα : -2 ≤ α ∧ α ≤ 2 := by
    constructor <;> linarith [abs_nonneg β, neg_abs_le α, le_abs_self α]
  have hβ : -2 ≤ β ∧ β ≤ 2 := by
    constructor <;> linarith [abs_nonneg α, neg_abs_le β, le_abs_self β]
  obtain ⟨hα₁, hα₂⟩ := hα
  obtain ⟨hβ₁, hβ₂⟩ := hβ
  rcases hm with rfl | rfl <;> interval_cases α <;> interval_cases β
  all_goals first
    | (exfalso; revert hαβ; decide)
    | (push_cast at h ht₀ ht₁ ⊢; constructor <;> linarith)

/-- Along one closed elementary half-side, a homogeneous inequality with
`|α| + |β| ≤ 2` at a point `t` of the free coordinate holds on its whole box. -/
private theorem homogeneous_side {α β : ℤ} (hαβ : |α| + |β| ≤ 2) {t s : ℝ}
    (ht : |t| ≤ 1) (hs : s ∈ Set.Icc (⌊t⌋ : ℝ) ⌈t⌉) (h : (α : ℝ) + β * t ≤ 0) :
    (α : ℝ) + β * s ≤ 0 := by
  have hft := Int.floor_le t
  have hct := Int.le_ceil t
  rcases eq_or_lt_of_le (Int.floor_le_ceil t) with hfc | hfc
  · have hfc' : (⌊t⌋ : ℝ) = ⌈t⌉ := by exact_mod_cast hfc
    have : s = t := by linarith [hs.1, hs.2]
    rwa [this]
  · have hc : ⌈t⌉ = ⌊t⌋ + 1 := le_antisymm (Int.ceil_le_floor_add_one t) hfc
    have hc' : (⌈t⌉ : ℝ) = ⌊t⌋ + 1 := by exact_mod_cast hc
    have hne : (⌊t⌋ : ℝ) ≠ t := by
      intro he
      have : ⌈t⌉ ≤ ⌊t⌋ := Int.ceil_le.mpr he.ge
      omega
    have hlt : (⌊t⌋ : ℝ) < t := lt_of_le_of_ne hft hne
    have hlt' : t < ⌊t⌋ + 1 := Int.lt_floor_add_one t
    obtain ⟨h1, h2⟩ := abs_le.mp ht
    have hm : ⌊t⌋ = -1 ∨ ⌊t⌋ = 0 := by
      have a1 : (-2 : ℝ) < ⌊t⌋ := by linarith
      have a2 : (⌊t⌋ : ℝ) < 1 := by linarith
      have b1 : (-2 : ℤ) < ⌊t⌋ := by exact_mod_cast a1
      have b2 : ⌊t⌋ < (1 : ℤ) := by exact_mod_cast a2
      omega
    obtain ⟨e₀, e₁⟩ := homogeneous_endpoints hαβ hm hlt hlt' h
    have hs₁ := hs.1
    have hs₂ : s ≤ ⌊t⌋ + 1 := hc' ▸ hs.2
    nlinarith [mul_nonneg (sub_nonneg.mpr hs₁) (neg_nonneg.mpr e₁),
      mul_nonneg (sub_nonneg.mpr hs₂) (neg_nonneg.mpr e₀)]

/-- A homogeneous axis-and-diagonal inequality valid at a unit direction is
valid on its whole integer box. -/
private theorem homogeneous_unitBox {a b : ℤ} (hab : |a| + |b| ≤ 2) {d e : ℝ × ℝ}
    (hd : ‖d‖ = 1) (he : e ∈ unitBox d) (h : (a : ℝ) * d.1 + b * d.2 ≤ 0) :
    (a : ℝ) * e.1 + b * e.2 ≤ 0 := by
  obtain ⟨h1, h2, h12⟩ := unit_cases hd
  rcases h12 with h' | h'
  · rw [icc_floor_ceil_of_abs_eq_one h' he.1]
    rcases abs_eq zero_le_one |>.mp h' with hv | hv <;> rw [hv] at h ⊢
    · simpa using homogeneous_side (α := a) (β := b) hab h2 he.2 (by simpa using h)
    · have := homogeneous_side (α := -a) (β := b) (by rwa [abs_neg]) h2 he.2
        (by push_cast; linarith)
      push_cast at this; linarith
  · rw [icc_floor_ceil_of_abs_eq_one h' he.2]
    rcases abs_eq zero_le_one |>.mp h' with hv | hv <;> rw [hv] at h ⊢
    · have := homogeneous_side (α := b) (β := a) (by rwa [add_comm]) h1 he.1
        (by linarith)
      linarith
    · have := homogeneous_side (α := -b) (β := a) (by rwa [abs_neg, add_comm]) h1 he.1
        (by push_cast; linarith)
      push_cast at this; linarith

private theorem abs_linear_le (a b : ℤ) (w : ℝ × ℝ) :
    |(a : ℝ) * w.1 + b * w.2| ≤ ((|a| + |b| : ℤ) : ℝ) * ‖w‖ := by
  have h1 : |w.1| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using norm_fst_le w
  have h2 : |w.2| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using norm_snd_le w
  push_cast
  calc |(a : ℝ) * w.1 + b * w.2| ≤ |(a : ℝ)| * |w.1| + |(b : ℝ)| * |w.2| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |(a : ℝ)| * ‖w‖ + |(b : ℝ)| * ‖w‖ := by gcongr
    _ = _ := by ring

/-- Near an integer point, membership in an integer half-plane is decided by
the integer discrepancy at that point and, when it vanishes, by the
homogeneous inequality. -/
private theorem mem_intHalfPlane_iff_near {a b n i j : ℤ} (hab : |a| + |b| ≤ 2)
    {y : ℝ × ℝ} (hy : ‖y - ((i : ℝ), (j : ℝ))‖ ≤ 1 / 4) :
    y ∈ intHalfPlane a b n ↔ (a * i + b * j - n ≤ -1 ∨
      (a * i + b * j - n = 0 ∧
        (a : ℝ) * (y - ((i : ℝ), (j : ℝ))).1 + b * (y - ((i : ℝ), (j : ℝ))).2 ≤ 0)) := by
  set w := y - ((i : ℝ), (j : ℝ))
  have hg := abs_linear_le a b w
  have hab' : ((|a| + |b| : ℤ) : ℝ) ≤ 2 := by exact_mod_cast hab
  have hg' : |(a : ℝ) * w.1 + b * w.2| ≤ 1 / 2 := by
    nlinarith [norm_nonneg w, abs_nonneg ((a : ℝ) * w.1 + b * w.2)]
  obtain ⟨g1, g2⟩ := abs_le.mp hg'
  have hy' : (a : ℝ) * y.1 + b * y.2 - n =
      ((a * i + b * j - n : ℤ) : ℝ) + ((a : ℝ) * w.1 + b * w.2) := by
    simp only [w, Prod.fst_sub, Prod.snd_sub]; push_cast; ring
  simp only [intHalfPlane, Set.mem_ofPred_eq]
  rw [← sub_nonpos, hy']
  rcases lt_trichotomy (a * i + b * j - n) 0 with hk | hk | hk
  · have hk' : ((a * i + b * j - n : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : _ ≤ (-1 : ℤ))
    exact ⟨fun _ ↦ Or.inl (by omega), fun _ ↦ by linarith⟩
  · rw [hk]; simp
  · have hk' : (1 : ℝ) ≤ ((a * i + b * j - n : ℤ) : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ _)
    constructor
    · intro h; linarith
    · rintro (h | ⟨h, _⟩) <;> omega

/-- **Integer half-planes are quarter-sectorial at integer points.** This covers
the closed half-planes bounded by horizontal, vertical and diagonal lines with
integer levels, the facets of the normalized fan triangles and of the
complement of the open removal square.
Source: area-law Section 11, `geometry:birth-separation`, lines 573–659. -/
theorem isQuarterSectorial_intHalfPlane {a b n : ℤ} (hab : |a| + |b| ≤ 2) (i j : ℤ) :
    IsQuarterSectorial ((i : ℝ), (j : ℝ)) (intHalfPlane a b n) where
  radial x h0 h1 := by
    set q : ℝ × ℝ := ((i : ℝ), (j : ℝ))
    have hpt : quarterRadialPoint q x - q = (4 * ‖x - q‖)⁻¹ • (x - q) := by
      simp [quarterRadialPoint]
    have hpos : 0 < (4 * ‖x - q‖)⁻¹ := by positivity
    have hn : ‖quarterRadialPoint q x - q‖ ≤ 1 / 4 := by
      rw [hpt, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
      field_simp; norm_num
    rw [mem_intHalfPlane_iff_near hab h1, mem_intHalfPlane_iff_near hab hn, hpt]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have : (a : ℝ) * ((4 * ‖x - q‖)⁻¹ * (x - q).1) + b * ((4 * ‖x - q‖)⁻¹ * (x - q).2) =
        (4 * ‖x - q‖)⁻¹ * ((a : ℝ) * (x - q).1 + b * (x - q).2) := by ring
    rw [this]
    constructor
    · rintro (h | ⟨h, h'⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h, mul_nonpos_of_nonneg_of_nonpos hpos.le h'⟩
    · rintro (h | ⟨h, h'⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h, nonpos_of_mul_nonpos_right h' hpos⟩
  box d hd hm e he := by
    have hq (f : ℝ × ℝ) (hf : ‖f‖ = 1) :
        ‖(((i : ℝ), (j : ℝ)) + (1 / 4 : ℝ) • f) - ((i : ℝ), (j : ℝ))‖ ≤ 1 / 4 := by
      simp [norm_smul, hf]
    have he1 := norm_eq_one_of_mem_unitBox hd he
    rw [mem_intHalfPlane_iff_near hab (hq d hd)] at hm
    rw [mem_intHalfPlane_iff_near hab (hq e he1)]
    rcases hm with h | ⟨h, h'⟩
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      simp only [add_sub_cancel_left, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h' ⊢
      have := homogeneous_unitBox hab hd he (by nlinarith)
      nlinarith

/-! ### The contact estimate -/

/-- **Angular estimate at a contact mark.** Two quarter-sectorial sets meeting in
the closed quarter-square about `q` at most at `q` satisfy
`‖x - y‖ ≥ max ‖x - q‖ ‖y - q‖ / 2` for their points in that square. The
constant `1/2` includes closed endpoints and zero displacements.
Source: area-law Section 11, `geometry:angular-gap`, lines 627–645. -/
theorem half_max_le_norm_sub_of_isQuarterSectorial {q : ℝ × ℝ} {P P' : Set (ℝ × ℝ)}
    (hP : IsQuarterSectorial q P) (hP' : IsQuarterSectorial q P')
    (hcontact : ∀ z ∈ P, z ∈ P' → ‖z - q‖ ≤ 1 / 4 → z = q)
    {x y : ℝ × ℝ} (hx : x ∈ P) (hy : y ∈ P') (hxq : ‖x - q‖ ≤ 1 / 4)
    (hyq : ‖y - q‖ ≤ 1 / 4) :
    max ‖x - q‖ ‖y - q‖ / 2 ≤ ‖x - y‖ := by
  rcases eq_or_lt_of_le (norm_nonneg (x - q)) with hx0 | hx0
  · have : x = q := sub_eq_zero.mp (norm_eq_zero.mp hx0.symm)
    subst this
    rw [← hx0, max_eq_right (norm_nonneg _), norm_sub_rev]; linarith [norm_nonneg (x - y)]
  rcases eq_or_lt_of_le (norm_nonneg (y - q)) with hy0 | hy0
  · have : y = q := sub_eq_zero.mp (norm_eq_zero.mp hy0.symm)
    subst this
    rw [← hy0, max_eq_left (norm_nonneg _)]; linarith
  set r := ‖x - q‖
  set s := ‖y - q‖
  set d := r⁻¹ • (x - q)
  set e := s⁻¹ • (y - q)
  have hd : ‖d‖ = 1 := by simp [d, norm_smul, r, hx0.ne']
  have he : ‖e‖ = 1 := by simp [e, norm_smul, s, hy0.ne']
  have hxd : quarterRadialPoint q x = q + (1 / 4 : ℝ) • d := by
    simp only [quarterRadialPoint, d, smul_smul, r]; congr 2; field_simp
  have hye : quarterRadialPoint q y = q + (1 / 4 : ℝ) • e := by
    simp only [quarterRadialPoint, e, smul_smul, s]; congr 2; field_simp
  have hxP : q + (1 / 4 : ℝ) • d ∈ P := hxd ▸ (hP.radial x hx0 hxq).mp hx
  have hyP : q + (1 / 4 : ℝ) • e ∈ P' := hye ▸ (hP'.radial y hy0 hyq).mp hy
  have hde : 1 ≤ ‖d - e‖ := by
    refine one_le_norm_sub_of_disjoint_unitBox (Set.disjoint_left.mpr fun f hfd hfe ↦ ?_)
    have hf := norm_eq_one_of_mem_unitBox hd hfd
    have h := hcontact _ (hP.box d hd hxP f hfd) (hP'.box e he hyP f hfe)
      (by simp [norm_smul, hf])
    have : (1 / 4 : ℝ) • f = 0 := by simpa using h
    rw [smul_eq_zero] at this
    rcases this with h4 | h0
    · norm_num at h4
    · simp [h0] at hf
  have hxy : x - y = r • d - s • e := by
    simp only [d, e, smul_smul, mul_inv_cancel₀ hx0.ne', mul_inv_cancel₀ hy0.ne', one_smul]
    abel
  rw [hxy]
  exact half_max_le_norm_smul_sub_smul hd he hde hx0.le hy0.le

end TNLean.PEPS.AreaLaw.Geometry
