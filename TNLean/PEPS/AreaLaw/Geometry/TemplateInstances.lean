/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BufferedRectangles
import TNLean.PEPS.AreaLaw.Geometry.CellCounting
import TNLean.PEPS.AreaLaw.Geometry.Templates

/-!
# Instances of polygonal lattice templates

Three constructions show that Definition 9.3 admits the templates used later.

* `Template.ofIntRect`: an integer rectangle of size at most `s₀`, including a
  thin rectangle of one row or one column, is a one-piece template. The real
  rectangle is enlarged by one half beyond the last row and column, so it is
  nondegenerate and samples exactly the lattice rectangle. A rectangle that is
  safe with a clearance constant `D` is separated in the template sense when
  `4 D₀ s₀ ≤ D · size`. This is the rectangle of the exponent bootstrap.
* `Template.union`: the union of two templates with the same parameters is a
  template once the combined piece count and diameter satisfy the scale
  conditions. The pieces need not meet, so the union may be disconnected, as for
  the birth templates of Proposition 11.2.
* `Template.omitEmpty`: sampled pieces with no lattice point can be removed
  without changing the template, as stated after the source's union formula.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Definition 9.3 (`scanner:template`), `08-scanner.tex`,
  lines 546–569, and the proof of Proposition 9.5 (`prop:small-box`),
  lines 705–729. Source revision:
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-! ### Integer rectangles -/

private theorem int_le_add_half_iff (a b : ℤ) : (a : ℝ) ≤ b + 1 / 2 ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hab
    have : (b : ℝ) + 1 ≤ a := by exact_mod_cast (show b + 1 ≤ a by omega)
    linarith
  · intro h
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    linarith

/-- The axis-parallel real rectangle `[x₀, x₁ + 1/2] × [y₀, y₁ + 1/2]` sampling an
integer rectangle. The half-unit margin keeps it nondegenerate for thin rectangles.
Source: area-law Definition 9.3, applied in the proof of Proposition 9.5. -/
noncomputable def TemplatePolygon.ofIntRect (Q : IntRect) : TemplatePolygon :=
  .rectangle ((Q.x₀ : ℝ), (Q.y₀ : ℝ)) ((Q.x₁ : ℝ) - Q.x₀ + 1 / 2, 0)
    (0, (Q.y₁ : ℝ) - Q.y₀ + 1 / 2)
    (by
      have : (Q.x₀ : ℝ) ≤ Q.x₁ := by exact_mod_cast Q.hx
      intro h
      have h1 := congrArg Prod.fst h
      simp only [Prod.fst_zero] at h1
      linarith)
    (by
      have : (Q.y₀ : ℝ) ≤ Q.y₁ := by exact_mod_cast Q.hy
      intro h
      have h2 := congrArg Prod.snd h
      simp only [Prod.snd_zero] at h2
      linarith)
    (by ring) (Or.inr (Or.inl rfl)) (Or.inl rfl)

/-- The real rectangle of an integer rectangle is a product of closed intervals. -/
theorem TemplatePolygon.region_ofIntRect (Q : IntRect) :
    (TemplatePolygon.ofIntRect Q).region =
      Set.Icc (Q.x₀ : ℝ) (Q.x₁ + 1 / 2) ×ˢ Set.Icc (Q.y₀ : ℝ) (Q.y₁ + 1 / 2) := by
  have hx : (Q.x₀ : ℝ) ≤ Q.x₁ + 1 / 2 := by
    have : (Q.x₀ : ℝ) ≤ Q.x₁ := by exact_mod_cast Q.hx
    linarith
  have hy : (Q.y₀ : ℝ) ≤ Q.y₁ + 1 / 2 := by
    have : (Q.y₀ : ℝ) ≤ Q.y₁ := by exact_mod_cast Q.hy
    linarith
  have hv : ({((Q.x₀ : ℝ), (Q.y₀ : ℝ)), ((Q.x₀ : ℝ), (Q.y₀ : ℝ)) + ((Q.x₁ : ℝ) - Q.x₀ + 1 / 2, 0),
      ((Q.x₀ : ℝ), (Q.y₀ : ℝ)) + ((Q.x₁ : ℝ) - Q.x₀ + 1 / 2, 0) + (0, (Q.y₁ : ℝ) - Q.y₀ + 1 / 2),
      ((Q.x₀ : ℝ), (Q.y₀ : ℝ)) + (0, (Q.y₁ : ℝ) - Q.y₀ + 1 / 2)} : Set (ℝ × ℝ)) =
      ({(Q.x₀ : ℝ), (Q.x₁ : ℝ) + 1 / 2} : Set ℝ) ×ˢ
        ({(Q.y₀ : ℝ), (Q.y₁ : ℝ) + 1 / 2} : Set ℝ) := by
    ext ⟨p, q⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_prod, Prod.mk_add_mk,
      Prod.mk.injEq, add_zero]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        refine ⟨?_, ?_⟩ <;> first | (left; ring1) | (right; ring1)
    · rintro ⟨rfl | rfl, rfl | rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, by ring⟩))
      · exact Or.inr (Or.inl ⟨by ring, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨by ring, by ring⟩))
  change convexHull ℝ _ = _
  rw [hv, convexHull_prod, convexHull_pair, convexHull_pair, segment_eq_Icc hx,
    segment_eq_Icc hy]

/-- The real rectangle of an integer rectangle samples exactly its lattice points. -/
theorem TemplatePolygon.mem_toFinset_iff_integerPoint_mem_ofIntRect (Q : IntRect) (p : ℤ × ℤ) :
    p ∈ Q.toFinset ↔ integerPoint p ∈ (TemplatePolygon.ofIntRect Q).region := by
  rw [TemplatePolygon.region_ofIntRect, IntRect.mem_toFinset]
  simp only [integerPoint, Set.mem_prod, Set.mem_Icc, Int.cast_le, int_le_add_half_iff]
  tauto

private theorem abs_sub_le_of_mem_Icc {a b x y : ℝ} (hx : x ∈ Set.Icc a b)
    (hy : y ∈ Set.Icc a b) : |x - y| ≤ b - a := by
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- An integer rectangle of size at most `s₀`, in particular a thin rectangle of
one row or column, is a one-piece template with parameters `(n, s₀)` whenever
`Ctpl (s₀ + 1) ≤ n` and `1 ≤ Ctpl`. Source: area-law Definition 9.3, as applied
to a safe rectangle of maximal side `s₀` in the proof of Proposition 9.5,
`08-scanner.tex`, lines 705–729. -/
noncomputable def Template.ofIntRect {Ctpl : ℝ} {n s₀ : ℕ} (Q : IntRect)
    (hsize : Q.size ≤ s₀) (hC : 1 ≤ Ctpl) (hn : Ctpl * (s₀ + 1) ≤ n) :
    Template Ctpl n s₀ where
  n_pos := by
    have : (1 : ℝ) ≤ n := by nlinarith [show (0 : ℝ) ≤ s₀ from Nat.cast_nonneg _]
    exact_mod_cast this
  s₀_pos := Q.one_le_size.trans hsize
  pieceCount := 1
  pieceCount_pos := one_pos
  polygon _ := TemplatePolygon.ofIntRect Q
  sample _ := Q.toFinset
  mem_sample _ := TemplatePolygon.mem_toFinset_iff_integerPoint_mem_ofIntRect Q
  piece_diameter _ x hx y hy := by
    rw [TemplatePolygon.region_ofIntRect] at hx hy
    have hw : ((Q.x₁ + 1 - Q.x₀ : ℤ) : ℝ) ≤ (Q.size : ℤ) := by
      exact_mod_cast Q.width_le_size
    have hh : ((Q.y₁ + 1 - Q.y₀ : ℤ) : ℝ) ≤ (Q.size : ℤ) := by
      exact_mod_cast Q.height_le_size
    have hs : (Q.size : ℝ) ≤ s₀ := by exact_mod_cast hsize
    push_cast at hw hh
    have h1 := abs_sub_le_of_mem_Icc hx.1 hy.1
    have h2 := abs_sub_le_of_mem_Icc hx.2 hy.2
    rw [max_le_iff]
    constructor <;> linarith
  points := Q.toFinset
  nonempty := ⟨(Q.x₀, Q.y₀), IntRect.mem_toFinset.mpr ⟨le_rfl, Q.hx, le_rfl, Q.hy⟩⟩
  cover := by simp
  scale := by simpa using hn
  diameter x hx y hy := by
    rw [IntRect.mem_toFinset] at hx hy
    have hw : ((Q.x₁ + 1 - Q.x₀ : ℤ) : ℝ) ≤ (Q.size : ℤ) := by
      exact_mod_cast Q.width_le_size
    have hh : ((Q.y₁ + 1 - Q.y₀ : ℤ) : ℝ) ≤ (Q.size : ℤ) := by
      exact_mod_cast Q.height_le_size
    have hs : (Q.size : ℝ) ≤ s₀ := by exact_mod_cast hsize
    have hsn : (s₀ : ℝ) ≤ n := by nlinarith [show (0 : ℝ) ≤ s₀ from Nat.cast_nonneg _]
    push_cast at hw hh
    have h1 := abs_sub_le_of_mem_Icc (a := (Q.x₀ : ℝ)) (b := Q.x₁) (x := (x.1 : ℝ))
      (y := (y.1 : ℝ)) ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2.1⟩
      ⟨by exact_mod_cast hy.1, by exact_mod_cast hy.2.1⟩
    have h2 := abs_sub_le_of_mem_Icc (a := (Q.y₀ : ℝ)) (b := Q.y₁) (x := (x.2 : ℝ))
      (y := (y.2 : ℝ)) ⟨by exact_mod_cast hx.2.2.1, by exact_mod_cast hx.2.2.2⟩
      ⟨by exact_mod_cast hy.2.2.1, by exact_mod_cast hy.2.2.2⟩
    rw [max_le_iff]
    constructor <;> linarith

@[simp]
theorem Template.points_ofIntRect {Ctpl : ℝ} {n s₀ : ℕ} (Q : IntRect)
    (hsize : Q.size ≤ s₀) (hC : 1 ≤ Ctpl) (hn : Ctpl * (s₀ + 1) ≤ n) :
    (Template.ofIntRect Q hsize hC hn).points = Q.toFinset :=
  rfl

@[simp]
theorem Template.pieceCount_ofIntRect {Ctpl : ℝ} {n s₀ : ℕ} (Q : IntRect)
    (hsize : Q.size ≤ s₀) (hC : 1 ≤ Ctpl) (hn : Ctpl * (s₀ + 1) ≤ n) :
    (Template.ofIntRect Q hsize hC hn).pieceCount = 1 :=
  rfl

/-- A rectangle that is safe with clearance constant `D` is separated from the
cut in the sense of Definition 9.3 whenever `4 D₀ s₀ ≤ D · size Q`. In the
bootstrap, `D = 4 D₀` and `s₀ = size Q` give the template clearance. -/
theorem Template.isSeparated_ofIntRect_of_isSafe {Ctpl : ℝ} {n s₀ : ℕ} (Q : IntRect)
    (hsize : Q.size ≤ s₀) (hC : 1 ≤ Ctpl) (hn : Ctpl * (s₀ + 1) ≤ n)
    {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)} {D D₀ : ℕ} (hsafe : IsSafe Λ A D Q)
    (hD : 4 * D₀ * s₀ ≤ D * Q.size) :
    (Template.ofIntRect Q hsize hC hn).IsSeparated D₀ (boundaryEndpoints Λ A) := by
  classical
  intro x hx z hz
  simp only [boundaryEndpoints, Finset.mem_image, Finset.mem_biUnion,
    Sym2.mem_toFinset] at hz
  obtain ⟨w, ⟨e, he, hw⟩, rfl⟩ := hz
  have hfar := hsafe e he w hw x hx
  have hcast : (supDist x w.1 : ℝ) = max |(x.1 : ℝ) - (w.1).1| |(x.2 : ℝ) - (w.1).2| := by
    simp only [supDist, Nat.cast_max, Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
  rw [← hcast]
  have : 4 * D₀ * s₀ < supDist x w.1 := lt_of_le_of_lt hD hfar
  exact_mod_cast this

/-! ### Unions of templates -/

/-- The union of two templates with the same parameters, whose pieces are the
pieces of both. Only the combined scale and diameter conditions are required;
the two unions may be far apart, so the result may be disconnected.
Source: area-law Definition 9.3 and the remark after it, `08-scanner.tex`,
lines 566–569, which admits the disconnected fragments of the later tiling. -/
def Template.union {Ctpl : ℝ} {n s₀ : ℕ} (T₁ T₂ : Template Ctpl n s₀)
    (hscale : Ctpl * ((T₁.pieceCount + T₂.pieceCount : ℕ) : ℝ) * (s₀ + 1 : ℝ) ≤ n)
    (hdiam : ∀ x ∈ T₁.points ∪ T₂.points, ∀ y ∈ T₁.points ∪ T₂.points,
      max |(x.1 : ℝ) - y.1| |(x.2 : ℝ) - y.2| ≤ (n : ℝ)) :
    Template Ctpl n s₀ where
  n_pos := T₁.n_pos
  s₀_pos := T₁.s₀_pos
  pieceCount := T₁.pieceCount + T₂.pieceCount
  pieceCount_pos := Nat.add_pos_left T₁.pieceCount_pos _
  polygon := Fin.append T₁.polygon T₂.polygon
  sample := Fin.append T₁.sample T₂.sample
  mem_sample i x := by
    induction i using Fin.addCases with
    | left i => simpa only [Fin.append_left] using T₁.mem_sample i x
    | right i => simpa only [Fin.append_right] using T₂.mem_sample i x
  piece_diameter i := by
    induction i using Fin.addCases with
    | left i => simpa only [Fin.append_left] using T₁.piece_diameter i
    | right i => simpa only [Fin.append_right] using T₂.piece_diameter i
  points := T₁.points ∪ T₂.points
  nonempty := T₁.nonempty.mono Finset.subset_union_left
  cover := by
    rw [T₁.cover, T₂.cover]
    ext x
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
      · exact ⟨Fin.castAdd _ i, by simpa only [Fin.append_left] using hi⟩
      · exact ⟨Fin.natAdd _ i, by simpa only [Fin.append_right] using hi⟩
    · rintro ⟨i, hi⟩
      induction i using Fin.addCases with
      | left i => exact Or.inl ⟨i, by simpa only [Fin.append_left] using hi⟩
      | right i => exact Or.inr ⟨i, by simpa only [Fin.append_right] using hi⟩
  scale := hscale
  diameter := hdiam

@[simp]
theorem Template.points_union {Ctpl : ℝ} {n s₀ : ℕ} (T₁ T₂ : Template Ctpl n s₀)
    (hscale : Ctpl * ((T₁.pieceCount + T₂.pieceCount : ℕ) : ℝ) * (s₀ + 1 : ℝ) ≤ n)
    (hdiam : ∀ x ∈ T₁.points ∪ T₂.points, ∀ y ∈ T₁.points ∪ T₂.points,
      max |(x.1 : ℝ) - y.1| |(x.2 : ℝ) - y.2| ≤ (n : ℝ)) :
    (T₁.union T₂ hscale hdiam).points = T₁.points ∪ T₂.points :=
  rfl

@[simp]
theorem Template.pieceCount_union {Ctpl : ℝ} {n s₀ : ℕ} (T₁ T₂ : Template Ctpl n s₀)
    (hscale : Ctpl * ((T₁.pieceCount + T₂.pieceCount : ℕ) : ℝ) * (s₀ + 1 : ℝ) ≤ n)
    (hdiam : ∀ x ∈ T₁.points ∪ T₂.points, ∀ y ∈ T₁.points ∪ T₂.points,
      max |(x.1 : ℝ) - y.1| |(x.2 : ℝ) - y.2| ≤ (n : ℝ)) :
    (T₁.union T₂ hscale hdiam).pieceCount = T₁.pieceCount + T₂.pieceCount :=
  rfl

/-! ### Omitting empty pieces -/

/-- The pieces of a template whose samples contain a lattice point. -/
abbrev Template.NonemptyPiece {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀) : Type :=
  {i : Fin T.pieceCount // (T.sample i).Nonempty}

/-- The same template with its empty sampled pieces omitted. Omission keeps the
point set and can only lower the piece count. The scale condition then needs
only `0 ≤ Ctpl`. Source: area-law Definition 9.3, `08-scanner.tex`, line 557,
"Empty sampled pieces can be omitted." -/
noncomputable def Template.omitEmpty {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀)
    (hC : 0 ≤ Ctpl) : Template Ctpl n s₀ where
  n_pos := T.n_pos
  s₀_pos := T.s₀_pos
  pieceCount := Fintype.card T.NonemptyPiece
  pieceCount_pos := by
    obtain ⟨x, hx⟩ := T.nonempty
    rw [T.cover, Finset.mem_biUnion] at hx
    obtain ⟨i, -, hi⟩ := hx
    exact Fintype.card_pos_iff.mpr ⟨⟨i, x, hi⟩⟩
  polygon k := T.polygon ((Fintype.equivFin T.NonemptyPiece).symm k).1
  sample k := T.sample ((Fintype.equivFin T.NonemptyPiece).symm k).1
  mem_sample k := T.mem_sample _
  piece_diameter k := T.piece_diameter _
  points := T.points
  nonempty := T.nonempty
  cover := by
    rw [T.cover]
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨Fintype.equivFin T.NonemptyPiece ⟨i, x, hi⟩, by simpa using hi⟩
    · rintro ⟨k, hk⟩
      exact ⟨_, hk⟩
  scale := by
    have hcard : (Fintype.card T.NonemptyPiece : ℝ) ≤ T.pieceCount := by
      exact_mod_cast (Fintype.card_subtype_le _).trans (Fintype.card_fin _).le
    refine le_trans ?_ T.scale
    gcongr
  diameter := T.diameter

@[simp]
theorem Template.points_omitEmpty {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀)
    (hC : 0 ≤ Ctpl) : (T.omitEmpty hC).points = T.points :=
  rfl

/-- After omission, every sampled piece contains a lattice point. -/
theorem Template.sample_omitEmpty_nonempty {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀)
    (hC : 0 ≤ Ctpl) (k : Fin (T.omitEmpty hC).pieceCount) :
    ((T.omitEmpty hC).sample k).Nonempty :=
  ((Fintype.equivFin T.NonemptyPiece).symm k).2

/-- Omission never increases the number of pieces. -/
theorem Template.pieceCount_omitEmpty_le {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀)
    (hC : 0 ≤ Ctpl) : (T.omitEmpty hC).pieceCount ≤ T.pieceCount :=
  show Fintype.card T.NonemptyPiece ≤ T.pieceCount from
    (Fintype.card_subtype_le _).trans (Fintype.card_fin _).le

end TNLean.PEPS.AreaLaw.Geometry
