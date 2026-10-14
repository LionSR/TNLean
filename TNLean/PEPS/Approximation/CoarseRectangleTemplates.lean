/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.Templates
import TNLean.PEPS.AreaLaw.Scan.AmbientDepth
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Bounded unions of lattice rectangles as templates

Proposition 3.1 of the polynomial-PEPS paper concerns the full ambient lattice
sample `T` of a union of at most `N₀` axis-parallel rectangles. Its proof reads
such a set as a template of the area-law companion. This module supplies that
geometric step.

* The lattice sample of a rectangle is an integer box `[lo, hi]`, possibly empty.
  This holds for every assignment of open or closed sides, and more generally
  for any product of two real intervals.
* A finite nonempty union of `k` integer boxes is the point set of a template whose
  pieces are closed rectangles. An empty box is sampled from a small rectangle that
  contains no lattice point. The piece diameters are bounded by the diameter of the
  union plus one, and the scale inequality is the only remaining condition.

## Main definitions

* `IsBoxUnion N₀ T`: `T` is a union of at most `N₀` integer boxes.

## Main statements

* `isBoxUnion_of_ordConnected`: the lattice sample of a union of at most `N₀`
  products of real intervals is a union of at most `N₀` integer boxes.
* `IsBoxUnion.translate`: a common translation preserves the box-union form.
* `IsBoxUnion.exists_template`: a nonempty union of boxes is the point set of a
  template with prescribed scale parameters.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Proposition 3.1 (`prop:coarse`), `02-information.tex`
  lines 91–108, and the first and last paragraphs of its proof, lines 111–117 and
  136–144.
* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
  2026, Definition 9.3 (`scanner:template`).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscripts; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.Approximation

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Geometry

/-- An ambient lattice set is a union of at most `N₀` integer boxes `[lo a, hi a]`,
each possibly empty. This is the full lattice sample of a union of at most `N₀`
axis-parallel rectangles; see `isBoxUnion_of_ordConnected`.
Source: polynomial-PEPS Proposition 3.1, `02-information.tex` lines 95–97. -/
def IsBoxUnion (N₀ : ℕ) (T : Finset (ℤ × ℤ)) : Prop :=
  ∃ k ≤ N₀, ∃ lo hi : Fin k → ℤ × ℤ,
    T = Finset.univ.biUnion fun a ↦ Finset.Icc (lo a) (hi a)

section Intervals

/-- The integers in a real interval form an interval of integers. -/
private theorem ordConnected_intCast_preimage {I : Set ℝ} (hI : I.OrdConnected) :
    (Int.cast ⁻¹' I : Set ℤ).OrdConnected :=
  ⟨fun _ hx _ hy _ hz ↦ hI.out hx hy
    ⟨Int.cast_le.mpr hz.1, Int.cast_le.mpr hz.2⟩⟩

/-- A nonempty bounded interval of integers is the closed interval between its
infimum and supremum. -/
private theorem mem_iff_of_ordConnected {P : Set ℤ} (hP : P.OrdConnected) (hne : P.Nonempty)
    (hbdd : BddBelow P) (hbdd' : BddAbove P) (m : ℤ) :
    m ∈ P ↔ sInf P ≤ m ∧ m ≤ sSup P := by
  refine ⟨fun hm ↦ ⟨csInf_le hbdd hm, le_csSup hbdd' hm⟩, fun hm ↦ ?_⟩
  exact hP.out (Int.csInf_mem hne hbdd) (Int.csSup_mem hne hbdd') hm

end Intervals

/-- **The lattice sample of a union of rectangles.** Let `T` be the set of lattice
points in a union of at most `N₀` products `I a × J a` of real intervals. The
intervals are arbitrary: each side may be open or closed, independently for every
rectangle. Then `T` is a union of at most `N₀` integer boxes.
Source: polynomial-PEPS proof of Proposition 3.1, `02-information.tex`
lines 136–140, where a rectangle with open sides has the sample of a closed
rectangle with shifted sides. -/
theorem isBoxUnion_of_ordConnected {N₀ k : ℕ} (hk : k ≤ N₀) (I J : Fin k → Set ℝ)
    (hI : ∀ a, (I a).OrdConnected) (hJ : ∀ a, (J a).OrdConnected) (T : Finset (ℤ × ℤ))
    (hT : ∀ t : ℤ × ℤ, t ∈ T ↔ ∃ a, ((t.1 : ℝ) ∈ I a ∧ (t.2 : ℝ) ∈ J a)) :
    IsBoxUnion N₀ T := by
  classical
  let P : Fin k → Set ℤ := fun a ↦ Int.cast ⁻¹' I a
  let Q : Fin k → Set ℤ := fun a ↦ Int.cast ⁻¹' J a
  have hfst : ∀ a, (Q a).Nonempty → ∀ m ∈ P a, m ∈ T.image Prod.fst := by
    intro a ⟨y, hy⟩ m hm
    exact Finset.mem_image.mpr ⟨(m, y), (hT _).mpr ⟨a, hm, hy⟩, rfl⟩
  have hsnd : ∀ a, (P a).Nonempty → ∀ m ∈ Q a, m ∈ T.image Prod.snd := by
    intro a ⟨x, hx⟩ m hm
    exact Finset.mem_image.mpr ⟨(x, m), (hT _).mpr ⟨a, hx, hm⟩, rfl⟩
  let good : Fin k → Prop := fun a ↦ (P a).Nonempty ∧ (Q a).Nonempty
  refine ⟨k, hk, fun a ↦ if good a then (sInf (P a), sInf (Q a)) else (1, 1),
    fun a ↦ if good a then (sSup (P a), sSup (Q a)) else (0, 0), ?_⟩
  ext t
  rw [hT, Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  refine exists_congr fun a ↦ ?_
  by_cases hg : good a
  · obtain ⟨hPn, hQn⟩ := hg
    have hPb := (T.image Prod.fst).finite_toSet.subset (hfst a hQn)
    have hQb := (T.image Prod.snd).finite_toSet.subset (hsnd a hPn)
    have hP := mem_iff_of_ordConnected (ordConnected_intCast_preimage (hI a)) hPn
      hPb.bddBelow hPb.bddAbove
    have hQ := mem_iff_of_ordConnected (ordConnected_intCast_preimage (hJ a)) hQn
      hQb.bddBelow hQb.bddAbove
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hPn, hQn⟩), ite_eq_left_of_eq_true _ _ (eq_true ⟨hPn, hQn⟩),
      Finset.mem_Icc, Prod.mk_le_mk, Prod.mk_le_mk]
    change t.1 ∈ P a ∧ t.2 ∈ Q a ↔ _
    rw [hP, hQ]
    tauto
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hg), ite_eq_right_of_eq_false _ _ (eq_false hg),
      Finset.mem_Icc]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact absurd ⟨⟨t.1, h₁⟩, ⟨t.2, h₂⟩⟩ hg
    · rintro ⟨h₁, h₂⟩
      exact absurd (le_trans h₁ h₂) (by decide)

/-- **Common translations.** Translating a union of at most `N₀` boxes gives a union
of at most `N₀` boxes. Source: polynomial-PEPS Proposition 3.1,
`02-information.tex` lines 107–108 and 141–142. -/
theorem IsBoxUnion.translate {N₀ : ℕ} {T : Finset (ℤ × ℤ)} (hT : IsBoxUnion N₀ T)
    (c : ℤ × ℤ) : IsBoxUnion N₀ (T.image fun t ↦ t + c) := by
  obtain ⟨k, hk, lo, hi, rfl⟩ := hT
  refine ⟨k, hk, fun a ↦ lo a + c, fun a ↦ hi a + c, ?_⟩
  ext t
  simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_Icc, Prod.le_def, Prod.fst_add, Prod.snd_add]
  constructor
  · rintro ⟨s, ⟨a, ⟨h₁, h₂⟩, h₃, h₄⟩, rfl⟩
    exact ⟨a, ⟨by simpa using h₁, by simpa using h₂⟩, by simpa using h₃, by simpa using h₄⟩
  · rintro ⟨a, ⟨h₁, h₂⟩, h₃, h₄⟩
    refine ⟨t - c, ⟨a, ⟨?_, ?_⟩, ?_, ?_⟩, sub_add_cancel t c⟩ <;>
      simp only [Prod.fst_sub, Prod.snd_sub] <;> omega

/-- An empty union of boxes is empty. -/
theorem IsBoxUnion.eq_empty_of_zero {T : Finset (ℤ × ℤ)} (hT : IsBoxUnion 0 T) : T = ∅ := by
  obtain ⟨k, hk, lo, hi, rfl⟩ := hT
  obtain rfl : k = 0 := Nat.le_zero.mp hk
  simp

section Template

/-- The closed axis-parallel rectangle `[a₁, a₁ + w₁] × [a₂, a₂ + w₂]` as a template
polygon. Source: area-law Definition 9.3, closed rectangles with sides of slope
`0` and `∞`. -/
noncomputable def axisRectangle (a : ℝ × ℝ) (w : ℝ × ℝ) (hw₁ : 0 < w.1) (hw₂ : 0 < w.2) :
    TemplatePolygon :=
  .rectangle a (w.1, 0) (0, w.2) (by simp [Prod.ext_iff, hw₁.ne'])
    (by simp [Prod.ext_iff, hw₂.ne']) (by simp) (Or.inr (Or.inl rfl)) (Or.inl rfl)

/-- The axis-parallel rectangle is the product of its two closed side intervals. -/
theorem axisRectangle_region (a w : ℝ × ℝ) (hw₁ : 0 < w.1) (hw₂ : 0 < w.2) :
    (axisRectangle a w hw₁ hw₂).region =
      Set.Icc a.1 (a.1 + w.1) ×ˢ Set.Icc a.2 (a.2 + w.2) := by
  have hset : ({a, a + (w.1, 0), a + (w.1, 0) + (0, w.2), a + (0, w.2)} : Set (ℝ × ℝ)) =
      ({a.1, a.1 + w.1} : Set ℝ) ×ˢ ({a.2, a.2 + w.2} : Set ℝ) := by
    ext ⟨x, y⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_prod, Prod.ext_iff,
      Prod.fst_add, Prod.snd_add, add_zero]
    tauto
  simp only [axisRectangle, TemplatePolygon.region]
  rw [hset, convexHull_prod, convexHull_pair, convexHull_pair,
    segment_eq_Icc (by linarith), segment_eq_Icc (by linarith)]

/-- The rectangle sampling a box: `[lo - 1/4, hi + 1/4]` in each coordinate for a
nonempty box, and a small square without lattice points for an empty box. -/
private noncomputable def boxPolygon (lo hi : ℤ × ℤ) : TemplatePolygon :=
  if h : lo ≤ hi then
    axisRectangle ((lo.1 : ℝ) - 1 / 4, (lo.2 : ℝ) - 1 / 4)
      ((hi.1 : ℝ) - lo.1 + 1 / 2, (hi.2 : ℝ) - lo.2 + 1 / 2)
      (by have : (lo.1 : ℝ) ≤ hi.1 := Int.cast_le.mpr h.1
          dsimp only; linarith)
      (by have : (lo.2 : ℝ) ≤ hi.2 := Int.cast_le.mpr h.2
          dsimp only; linarith)
  else axisRectangle (-1 / 4, -1 / 4) (1 / 8, 1 / 8) (by norm_num) (by norm_num)

private theorem intCast_mem_Icc_quarter_iff (m l h : ℤ) :
    (m : ℝ) ∈ Set.Icc ((l : ℝ) - 1 / 4) ((l : ℝ) - 1 / 4 + ((h : ℝ) - l + 1 / 2)) ↔
      l ≤ m ∧ m ≤ h := by
  rw [Set.mem_Icc]
  constructor
  · rintro ⟨h₁, h₂⟩
    have h₁' : (l : ℝ) < m + 1 := by linarith
    have h₂' : (m : ℝ) < h + 1 := by linarith
    exact ⟨Int.lt_add_one_iff.mp (by exact_mod_cast h₁'),
      Int.lt_add_one_iff.mp (by exact_mod_cast h₂')⟩
  · rintro ⟨h₁, h₂⟩
    have h₁' : (l : ℝ) ≤ m := Int.cast_le.mpr h₁
    have h₂' : (m : ℝ) ≤ h := Int.cast_le.mpr h₂
    constructor <;> linarith

private theorem mem_boxPolygon_region_iff (lo hi x : ℤ × ℤ) :
    integerPoint x ∈ (boxPolygon lo hi).region ↔ x ∈ Finset.Icc lo hi := by
  rw [Finset.mem_Icc]
  unfold boxPolygon
  split_ifs with h
  · rw [axisRectangle_region, Set.mem_prod]
    simp only [integerPoint]
    rw [intCast_mem_Icc_quarter_iff, intCast_mem_Icc_quarter_iff, Prod.le_def, Prod.le_def]
    tauto
  · rw [axisRectangle_region, Set.mem_prod]
    simp only [integerPoint, Set.mem_Icc]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, -⟩
      have h₁' : (-1 : ℝ) < x.1 := by linarith
      have h₂' : (x.1 : ℝ) < 0 := by linarith
      have : (-1 : ℤ) < x.1 := by exact_mod_cast h₁'
      have : x.1 < 0 := by exact_mod_cast h₂'
      omega
    · rintro ⟨h₁, h₂⟩
      exact absurd (le_trans h₁ h₂) h

/-- The side lengths of an axis rectangle bound its sup-norm diameter. -/
private theorem axisRectangle_diameter (a w : ℝ × ℝ) (hw₁ : 0 < w.1) (hw₂ : 0 < w.2)
    {s : ℝ} (h₁ : w.1 ≤ s) (h₂ : w.2 ≤ s) :
    ∀ x ∈ (axisRectangle a w hw₁ hw₂).region, ∀ y ∈ (axisRectangle a w hw₁ hw₂).region,
      max |x.1 - y.1| |x.2 - y.2| ≤ s := by
  intro x hx y hy
  rw [axisRectangle_region, Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hx hy
  refine max_le (abs_sub_le_iff.mpr ⟨?_, ?_⟩) (abs_sub_le_iff.mpr ⟨?_, ?_⟩) <;> linarith

/-- **A union of boxes is a template.** Let `T` be a nonempty union of `k ≤ N₀` integer
boxes whose sup-norm diameter is at most `D`. If `D + 1 ≤ s₀`, `D ≤ n` and
`Ctpl N₀ (s₀ + 1) ≤ n` with `Ctpl ≤ C'` for some `C' ≥ 0`, then `T` is the point set of
a template with parameters `(n, s₀)` whose pieces are closed rectangles.
Source: polynomial-PEPS proof of Proposition 3.1, `02-information.tex`
lines 111–117; area-law Definition 9.3. -/
theorem IsBoxUnion.exists_template {N₀ : ℕ} {T : Finset (ℤ × ℤ)} (hT : IsBoxUnion N₀ T)
    (hne : T.Nonempty) {Ctpl : ℝ} {n s₀ : ℕ} {D : ℝ}
    (hdiam : ∀ x ∈ T, ∀ y ∈ T, (Scan.ambientSupDistance x y : ℝ) ≤ D)
    (hs₀ : D + 1 ≤ s₀) (hn : D ≤ n) (hn₀ : 0 < n)
    (hscale : max Ctpl 0 * N₀ * (s₀ + 1 : ℝ) ≤ n) :
    ∃ T' : Template Ctpl n s₀, T'.points = T := by
  classical
  obtain ⟨k, hk, lo, hi, rfl⟩ := hT
  have hD : 0 ≤ D := by
    obtain ⟨x, hx⟩ := hne
    have := hdiam x hx x hx
    simp only [Scan.ambientSupDistance, sub_self, abs_zero, max_self, Int.cast_zero] at this
    exact this
  have hs₀pos : 0 < s₀ := by exact_mod_cast (show (0 : ℝ) < s₀ by linarith)
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · obtain ⟨x, hx⟩ := hne
      simp at hx
    · exact h
  refine ⟨{
    n_pos := hn₀
    s₀_pos := hs₀pos
    pieceCount := k
    pieceCount_pos := hkpos
    polygon := fun a ↦ boxPolygon (lo a) (hi a)
    sample := fun a ↦ Finset.Icc (lo a) (hi a)
    mem_sample := fun a x ↦ (mem_boxPolygon_region_iff (lo a) (hi a) x).symm
    piece_diameter := ?_
    points := Finset.univ.biUnion fun a ↦ Finset.Icc (lo a) (hi a)
    nonempty := hne
    cover := rfl
    scale := ?_
    diameter := ?_ }, rfl⟩
  · intro a
    unfold boxPolygon
    split_ifs with h
    · have hlo : lo a ∈ Finset.univ.biUnion fun a ↦ Finset.Icc (lo a) (hi a) :=
        Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, Finset.left_mem_Icc.mpr h⟩
      have hhi : hi a ∈ Finset.univ.biUnion fun a ↦ Finset.Icc (lo a) (hi a) :=
        Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, Finset.right_mem_Icc.mpr h⟩
      have hd := hdiam _ hhi _ hlo
      simp only [Scan.ambientSupDistance, Int.cast_max, Int.cast_abs, Int.cast_sub,
        max_le_iff] at hd
      apply axisRectangle_diameter
      · dsimp only
        linarith [le_abs_self ((hi a).1 - (lo a).1 : ℝ), hd.1]
      · dsimp only
        linarith [le_abs_self ((hi a).2 - (lo a).2 : ℝ), hd.2]
    · apply axisRectangle_diameter <;> dsimp only <;> linarith
  · have hk' : (k : ℝ) ≤ N₀ := by exact_mod_cast hk
    have h1 : Ctpl * k ≤ max Ctpl 0 * N₀ :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hk' (le_max_right _ _))
    nlinarith [show (0 : ℝ) < s₀ + 1 by positivity]
  · intro x hx y hy
    have := hdiam x hx y hy
    simp only [Scan.ambientSupDistance, Int.cast_max, Int.cast_abs, Int.cast_sub] at this
    linarith

end Template

end TNLean.PEPS.Approximation
