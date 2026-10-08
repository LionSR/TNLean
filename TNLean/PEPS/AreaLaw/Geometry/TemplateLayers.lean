/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.TemplateRowBounds

/-!
# Ambient dilation layers of templates

The argument uses the proved supporting-strip description of each
polygon. Windowed column intervals give horizontal intervals after integer
dilation. Comparing two consecutive radius windows changes old row endpoints
by at most two sites each.

Original formalization of manuscript Lemma 9.4; no upstream Lean proof text
is reused. The template model has no additional regularity fields.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

open scoped BigOperators

/-- Every horizontal row of a dilated polygon is an integer interval. -/
theorem Template.mem_latticeRow_dilation_of_between {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) (r : ℕ) {a b x y : ℤ}
    (ha : a ∈ latticeRow (ambientDilation (T.sample i) r) y)
    (hb : b ∈ latticeRow (ambientDilation (T.sample i) r) y)
    (hax : a ≤ x) (hxb : x ≤ b) :
    x ∈ latticeRow (ambientDilation (T.sample i) r) y := by
  obtain ⟨za, hza, aa, haa, ha'⟩ := mem_latticeRow_ambientDilation.mp ha
  obtain ⟨zb, hzb, bb, hbb, hb'⟩ := mem_latticeRow_ambientDilation.mp hb
  simp only [Finset.mem_Icc] at hza hzb ha' hb'
  let v := max (min aa bb) (min x (max aa bb))
  have hv : v - r ≤ x ∧ x ≤ v + r := by dsimp [v]; omega
  have hex : ∃ z : ℤ, (v, z) ∈ T.sample i ∧ y - r ≤ z ∧ z ≤ y + r := by
    by_cases hab : aa ≤ bb
    · exact T.exists_sample_in_window_between i (mem_latticeRow.mp haa)
        (mem_latticeRow.mp hbb) hza hzb (by dsimp [v]; omega) (by dsimp [v]; omega)
    · exact T.exists_sample_in_window_between i (mem_latticeRow.mp hbb)
        (mem_latticeRow.mp haa) hzb hza (by dsimp [v]; omega) (by dsimp [v]; omega)
  obtain ⟨z, hz, hz₀, hz₁⟩ := hex
  exact mem_latticeRow_ambientDilation.mpr
    ⟨z, Finset.mem_Icc.mpr ⟨hz₀, hz₁⟩, v, mem_latticeRow.mpr hz,
      Finset.mem_Icc.mpr hv⟩

/-- A nonempty dilated row is exactly the interval of its attained endpoints. -/
theorem Template.latticeRow_dilation_eq_Icc {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) (r : ℕ) (y : ℤ)
    (h : (latticeRow (ambientDilation (T.sample i) r) y).Nonempty) :
    latticeRow (ambientDilation (T.sample i) r) y =
      Finset.Icc ((latticeRow (ambientDilation (T.sample i) r) y).min' h)
        ((latticeRow (ambientDilation (T.sample i) r) y).max' h) := by
  ext x
  constructor
  · intro hx
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hx, Finset.le_max' _ _ hx⟩
  · intro hx
    obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hx
    exact T.mem_latticeRow_dilation_of_between i r
      (Finset.min'_mem _ h) (Finset.max'_mem _ h) hl hu

/-- On an old nonempty output row, increasing the radius by one extends each
endpoint by at most two. This compares the original row windows directly. -/
theorem Template.latticeRow_dilation_succ_bounds {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) (r : ℕ) (y : ℤ)
    (h : (latticeRow (ambientDilation (T.sample i) r) y).Nonempty) {x : ℤ}
    (hx : x ∈ latticeRow (ambientDilation (T.sample i) (r + 1)) y) :
    (latticeRow (ambientDilation (T.sample i) r) y).min' h - 2 ≤ x ∧
      x ≤ (latticeRow (ambientDilation (T.sample i) r) y).max' h + 2 := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨zo, hzo, ao, hao, _⟩ := mem_latticeRow_ambientDilation.mp hw
  obtain ⟨zn, hzn, an, han, hxn⟩ := mem_latticeRow_ambientDilation.mp hx
  simp only [Finset.mem_Icc] at hzo hzn hxn
  let z := max (y - r) (min zn (y + r))
  have hz : y - r ≤ z ∧ z ≤ y + r := by dsimp [z]; omega
  have hnear : zn - 1 ≤ z ∧ z ≤ zn + 1 := by dsimp [z]; omega
  have hbetween : (zn ≤ z ∧ z ≤ zo) ∨ (zo ≤ z ∧ z ≤ zn) := by dsimp [z]; omega
  have hzrow : (latticeRow (T.sample i) z).Nonempty := by
    rcases hbetween with hbetween | hbetween
    · exact T.latticeRow_nonempty_between i ⟨an, han⟩ ⟨ao, hao⟩
        hbetween.1 hbetween.2
    · exact T.latticeRow_nonempty_between i ⟨ao, hao⟩ ⟨an, han⟩
        hbetween.1 hbetween.2
  obtain ⟨a', ha', hna₀, hna₁⟩ :=
    T.exists_nearby_sample_in_row i (mem_latticeRow.mp han) hnear hzrow
  have hl : a' - r ∈ latticeRow (ambientDilation (T.sample i) r) y := by
    apply mem_latticeRow_ambientDilation.mpr
    exact ⟨z, Finset.mem_Icc.mpr hz, a', mem_latticeRow.mpr ha',
      Finset.mem_Icc.mpr (by omega)⟩
  have hu : a' + r ∈ latticeRow (ambientDilation (T.sample i) r) y := by
    apply mem_latticeRow_ambientDilation.mpr
    exact ⟨z, Finset.mem_Icc.mpr hz, a', mem_latticeRow.mpr ha',
      Finset.mem_Icc.mpr (by omega)⟩
  have hmin := Finset.min'_le _ _ hl
  have hmax := Finset.le_max' _ _ hu
  constructor <;> omega

/-- An old output row acquires at most four sites in the next radius layer. -/
theorem Template.card_latticeRow_layer_le_four {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) (r : ℕ) (y : ℤ)
    (h : (latticeRow (ambientDilation (T.sample i) r) y).Nonempty) :
    (latticeRow (ambientDilation (T.sample i) (r + 1) \
      ambientDilation (T.sample i) r) y).card ≤ 4 := by
  let l := (latticeRow (ambientDilation (T.sample i) r) y).min' h
  let u := (latticeRow (ambientDilation (T.sample i) r) y).max' h
  have hsub : latticeRow (ambientDilation (T.sample i) (r + 1) \
      ambientDilation (T.sample i) r) y ⊆
      Finset.Icc (l - 2) (l - 1) ∪ Finset.Icc (u + 1) (u + 2) := by
    intro x hx
    obtain ⟨hxnew, hxold⟩ := Finset.mem_sdiff.mp (mem_latticeRow.mp hx)
    have hb := T.latticeRow_dilation_succ_bounds i r y h (mem_latticeRow.mpr hxnew)
    have hn : x ∉ latticeRow (ambientDilation (T.sample i) r) y :=
      fun hh ↦ hxold (mem_latticeRow.mp hh)
    rw [T.latticeRow_dilation_eq_Icc i r y h] at hn
    change ¬x ∈ Finset.Icc l u at hn
    change l - 2 ≤ x ∧ x ≤ u + 2 at hb
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hl : (Finset.Icc (l - 2) (l - 1)).card = 2 := by
    simp only [Int.card_Icc]
    omega
  have hu : (Finset.Icc (u + 1) (u + 2)).card = 2 := by
    simp only [Int.card_Icc]
    omega
  calc
    (latticeRow (ambientDilation (T.sample i) (r + 1) \
        ambientDilation (T.sample i) r) y).card ≤
        (Finset.Icc (l - 2) (l - 1) ∪ Finset.Icc (u + 1) (u + 2)).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.Icc (l - 2) (l - 1)).card + (Finset.Icc (u + 1) (u + 2)).card :=
      Finset.card_union_le _ _
    _ = 4 := by rw [hl, hu]

/-- The piece diameter bounds the width of every dilated horizontal row. -/
theorem Template.card_latticeRow_dilation_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) {p : ℤ × ℤ}
    (hp : p ∈ T.sample i) (r : ℕ) (y : ℤ) :
    (latticeRow (ambientDilation (T.sample i) r) y).card ≤ 2 * s₀ + 2 * r + 1 := by
  have hsub : latticeRow (ambientDilation (T.sample i) r) y ⊆
      Finset.Icc (p.1 - s₀ - r) (p.1 + s₀ + r) := by
    intro x hx
    obtain ⟨q, hq, hxy⟩ := mem_ambientDilation_iff.mp (mem_latticeRow.mp hx)
    have hqbox := T.sample_subset_box i hp hq
    simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at hqbox
    apply Finset.mem_Icc.mpr
    omega
  calc
    (latticeRow (ambientDilation (T.sample i) r) y).card ≤
        (Finset.Icc (p.1 - s₀ - r) (p.1 + s₀ + r)).card := Finset.card_le_card hsub
    _ = 2 * s₀ + 2 * r + 1 := by
      simp only [Int.card_Icc]
      omega

/-- A nonempty sample has one interval of occupied rows, with a
diameter-controlled length. Every radius expands that interval by its radius. -/
theorem Template.exists_dilation_row_domain {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) (hne : (T.sample i).Nonempty) :
    ∃ a b : ℤ, a ≤ b ∧ b - a ≤ 2 * s₀ ∧ ∀ r : ℕ, ∀ y : ℤ,
      (latticeRow (ambientDilation (T.sample i) r) y).Nonempty ↔
        a - r ≤ y ∧ y ≤ b + r := by
  let Y := (T.sample i).image Prod.snd
  have hY : Y.Nonempty := hne.image Prod.snd
  let a := Y.min' hY
  let b := Y.max' hY
  obtain ⟨pa, hpa, hpaY⟩ := Finset.mem_image.mp (Finset.min'_mem Y hY)
  obtain ⟨pb, hpb, hpbY⟩ := Finset.mem_image.mp (Finset.max'_mem Y hY)
  change pa.2 = a at hpaY
  change pb.2 = b at hpbY
  have ha : (latticeRow (T.sample i) a).Nonempty := by
    refine ⟨pa.1, mem_latticeRow.mpr ?_⟩
    simpa only [← hpaY, Prod.mk.eta] using hpa
  have hb : (latticeRow (T.sample i) b).Nonempty := by
    refine ⟨pb.1, mem_latticeRow.mpr ?_⟩
    simpa only [← hpbY, Prod.mk.eta] using hpb
  have hab : a ≤ b := Finset.min'_le_max' Y hY
  have hbase (y : ℤ) : (latticeRow (T.sample i) y).Nonempty ↔ a ≤ y ∧ y ≤ b := by
    constructor
    · rintro ⟨x, hx⟩
      have hy : y ∈ Y := Finset.mem_image.mpr ⟨(x, y), mem_latticeRow.mp hx, rfl⟩
      exact ⟨Finset.min'_le _ _ hy, Finset.le_max' _ _ hy⟩
    · intro hy
      exact T.latticeRow_nonempty_between i ha hb hy.1 hy.2
  obtain ⟨p, hp⟩ := hne
  have hpaBox := T.sample_subset_box i hp hpa
  have hpbBox := T.sample_subset_box i hp hpb
  simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at hpaBox hpbBox
  have hdiam : b - a ≤ 2 * s₀ := by
    omega
  refine ⟨a, b, hab, hdiam, fun r y ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx⟩
    obtain ⟨z, hz, q, hq, _⟩ := mem_latticeRow_ambientDilation.mp hx
    have hz' := (hbase z).mp ⟨q, hq⟩
    simp only [Finset.mem_Icc] at hz
    omega
  · intro hy
    let z := max a (min y b)
    have hz : a ≤ z ∧ z ≤ b := by dsimp [z]; omega
    obtain ⟨x, hx⟩ := (hbase z).mpr hz
    refine ⟨x, mem_latticeRow_ambientDilation.mpr ?_⟩
    refine ⟨z, Finset.mem_Icc.mpr ?_, x, hx, Finset.mem_Icc.mpr ?_⟩
    · dsimp [z]
      omega
    · omega

private theorem card_le_rows_and_ends (S : Finset (ℤ × ℤ)) (a b : ℤ) (k w : ℕ)
    (hband : ∀ p ∈ S, a - 1 ≤ p.2 ∧ p.2 ≤ b + 1)
    (hmid : ∀ y ∈ Finset.Icc a b, (latticeRow S y).card ≤ k)
    (hlo : (latticeRow S (a - 1)).card ≤ w)
    (hhi : (latticeRow S (b + 1)).card ≤ w) :
    S.card ≤ (Finset.Icc a b).card * k + 2 * w := by
  let R (y : ℤ) := (latticeRow S y).image (fun x ↦ (x, y))
  have hR (y : ℤ) : (R y).card ≤ (latticeRow S y).card := Finset.card_image_le
  have hm : ((Finset.Icc a b).biUnion R).card ≤ (Finset.Icc a b).card * k :=
    Finset.card_biUnion_le_card_mul _ _ _ (fun y hy ↦ (hR y).trans (hmid y hy))
  have hpR {p : ℤ × ℤ} (hp : p ∈ S) : p ∈ R p.2 := by
    apply Finset.mem_image.mpr
    exact ⟨p.1, mem_latticeRow.mpr (by simpa only [Prod.mk.eta] using hp), Prod.mk.eta⟩
  have hsub : S ⊆ ((Finset.Icc a b).biUnion R ∪ R (a - 1)) ∪ R (b + 1) := by
    intro p hp
    have hbp := hband p hp
    simp only [Finset.mem_union, Finset.mem_biUnion]
    by_cases hy : a ≤ p.2 ∧ p.2 ≤ b
    · exact Or.inl (Or.inl ⟨p.2, Finset.mem_Icc.mpr hy, hpR hp⟩)
    · have he : p.2 = a - 1 ∨ p.2 = b + 1 := by omega
      rcases he with he | he
      · exact Or.inl (Or.inr (by simpa only [he] using hpR hp))
      · exact Or.inr (by simpa only [he] using hpR hp)
  calc
    S.card ≤ (((Finset.Icc a b).biUnion R ∪ R (a - 1)) ∪ R (b + 1)).card :=
      Finset.card_le_card hsub
    _ ≤ ((Finset.Icc a b).biUnion R ∪ R (a - 1)).card + (R (b + 1)).card :=
      Finset.card_union_le _ _
    _ ≤ ((Finset.Icc a b).biUnion R).card + (R (a - 1)).card + (R (b + 1)).card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (Finset.Icc a b).card * k + w + w :=
      Nat.add_le_add (Nat.add_le_add hm ((hR _).trans hlo)) ((hR _).trans hhi)
    _ = (Finset.Icc a b).card * k + 2 * w := by omega

/-- A single polygon contributes at most `24 * (s₀ + 1)` sites to a
depth layer at every radius from one through `s₀`, including empty samples. -/
theorem Template.card_dilation_layer_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) (j : ℕ)
    (hj : 1 ≤ j) (hjs : j ≤ s₀) :
    (ambientDilation (T.sample i) j \ ambientDilation (T.sample i) (j - 1)).card ≤
      24 * (s₀ + 1) := by
  obtain he | hne := (T.sample i).eq_empty_or_nonempty
  · simp [he, ambientDilation]
  obtain ⟨a, b, hab, hdiam, hdom⟩ := T.exists_dilation_row_domain i hne
  obtain ⟨p, hp⟩ := hne
  let r := j - 1
  have hjr : j = r + 1 := by dsimp [r]; omega
  let S := ambientDilation (T.sample i) (r + 1) \ ambientDilation (T.sample i) r
  change (ambientDilation (T.sample i) j \ ambientDilation (T.sample i) r).card ≤ _
  rw [hjr]
  change S.card ≤ _
  have hband : ∀ q ∈ S, (a - r) - 1 ≤ q.2 ∧ q.2 ≤ (b + r) + 1 := by
    intro q hq
    have hnew := (Finset.mem_sdiff.mp hq).1
    have hy : (latticeRow (ambientDilation (T.sample i) (r + 1)) q.2).Nonempty :=
      ⟨q.1, mem_latticeRow.mpr (by simpa only [Prod.mk.eta] using hnew)⟩
    have hy' := (hdom (r + 1) q.2).mp hy
    omega
  have hmid : ∀ y ∈ Finset.Icc (a - r) (b + r), (latticeRow S y).card ≤ 4 := by
    intro y hy
    exact T.card_latticeRow_layer_le_four i r y ((hdom r y).mpr (Finset.mem_Icc.mp hy))
  have hwidth (y : ℤ) : (latticeRow S y).card ≤ 2 * s₀ + 2 * (r + 1) + 1 := by
    apply (Finset.card_le_card ?_).trans (T.card_latticeRow_dilation_le i hp (r + 1) y)
    intro x hx
    exact mem_latticeRow.mpr ((Finset.mem_sdiff.mp (mem_latticeRow.mp hx)).1)
  have hc := card_le_rows_and_ends S (a - r) (b + r) 4 (2 * s₀ + 2 * (r + 1) + 1)
    hband hmid (hwidth _) (hwidth _)
  have hrows : (Finset.Icc (a - r) (b + r)).card ≤ 2 * s₀ + 2 * r + 1 := by
    simp only [Int.card_Icc]
    omega
  omega

/-- The geometric depth-layer estimate of Lemma 9.4, derived directly from
the template with the universal sufficient lower bound `Ctpl ≥ 24`. -/
theorem template_layer_card_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl) (j : ℕ) (hj : 1 ≤ j) (hjs : j ≤ s₀) :
    (ambientDilation T.points j \ ambientDilation T.points (j - 1)).card ≤ n := by
  have hscale : (24 : ℝ) * T.pieceCount * (s₀ + 1) ≤ n := by
    calc
      (24 : ℝ) * T.pieceCount * (s₀ + 1) ≤ Ctpl * T.pieceCount * (s₀ + 1) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hC)
          (show 0 ≤ (T.pieceCount : ℝ) * (s₀ + 1) by positivity)]
      _ ≤ n := T.scale
  have hn : T.pieceCount * (24 * (s₀ + 1)) ≤ n := by
    have hn' : 24 * T.pieceCount * (s₀ + 1) ≤ n := by exact_mod_cast hscale
    nlinarith
  rw [T.cover]
  calc
    (ambientDilation (Finset.univ.biUnion T.sample) j \
        ambientDilation (Finset.univ.biUnion T.sample) (j - 1)).card ≤
        ∑ i ∈ Finset.univ,
          (ambientDilation (T.sample i) j \ ambientDilation (T.sample i) (j - 1)).card :=
      card_ambientDilation_biUnion_sdiff_le _ _ _ _
    _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin T.pieceCount)), 24 * (s₀ + 1) :=
      Finset.sum_le_sum (fun i _ ↦ T.card_dilation_layer_le i j hj hjs)
    _ = T.pieceCount * (24 * (s₀ + 1)) := by simp
    _ ≤ n := hn

end TNLean.PEPS.AreaLaw.Geometry
