/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.DyadicScales
import TNLean.PEPS.AreaLaw.Geometry.PrimaryFragments
import TNLean.PEPS.AreaLaw.Geometry.Templates
import TNLean.PEPS.AreaLaw.Geometry.TwoFamilyExplicitThresholds
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Birth templates and scanner scales of primary tiles

A primary tile in layer `k` has layer-cell side `r = 2 ^ k`. Its birth template
is the lattice sample of its birth region, read as the union of the closed
rectangular fragments cut from the layer cells by its pitch interior. Each
fragment has sup diameter at most `r`, so `s₀ = r`. The scanner scale is
`n = ⌈C_P r ^ (1 + 2 δ₀)⌉`.

* `primaryBirthTemplate`: the template of Definition 9.3 whose pieces are the
  nonempty fragments and whose points are the lattice points of the birth region.
* `card_primaryBirthTemplate_pieces_le`: at most `9 r ^ (2 δ₀)` pieces.
* `exists_primaryScannerConstant`: one constant `C_P`, depending only on `C_tpl`,
  gives `n ≥ C_tpl N₀ (s₀ + 1)` and `diam_∞ T ≤ s_k ≤ n` for every primary.
* `primaryBirthTemplate_isSeparated`: endpoint distance at least `C₀ r` gives the
  cut clearance of Definition 9.3 once `4 D₀ < C₀`.
* `eventually_primaryScaleLimits`: `⌊n ^ (1 - ℓ)⌋ = o(r)`, `n ^ β = o(t_k)` and
  `n ^ β = o(r)`, as explicit thresholds in `k`, uniformly over primaries.
* `le_primaryScannerScale`: all primary scales exceed a fixed `n_*` for large `k`.
* `primaryScaleLimitThreshold` and `primaryScannerScaleThreshold`: the explicit
  layers beyond which the two previous statements hold
  (`primaryScaleLimits_of_primaryScaleLimitThreshold_le`,
  `le_primaryScannerScale_of_primaryScannerScaleThreshold_le`).

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11, `10-geometry.tex`, lines 200–249 (layers,
  pitches and `geometry:primary-pieces`), lines 709–729 (`geometry:primary-scale`
  and `geometry:primary-limits`) and lines 756–774 (the order of the constants),
  and Definition 9.3 (`scanner:template`).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

open Filter Topology

/-! ### The scanner scale -/

/-- The scanner scale `n = ⌈C_P r ^ (1 + 2 δ₀)⌉` of a primary in layer `k`, with
`r = 2 ^ k`. Source: area-law Section 11, `geometry:primary-scale`, lines 711–715. -/
def primaryScannerScale (CP : ℝ) (k : ℕ) : ℕ :=
  ⌈CP * ((2 : ℝ) ^ k) ^ (1 + 2 * (Exponents.geometryDelta : ℝ))⌉₊

private theorem rpow_two_pow (k : ℕ) (x : ℝ) :
    ((2 : ℝ) ^ k) ^ x = (2 : ℝ) ^ ((k : ℝ) * x) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

private theorem geometryDelta_nonneg : (0 : ℝ) ≤ Exponents.geometryDelta := by
  norm_num [Exponents.geometryDelta]

/-- The belt pitch is at most `r ^ (1 + 2 δ₀)`. -/
private theorem two_pow_pitchScaleIndex_le (k : ℕ) :
    (2 : ℝ) ^ pitchScaleIndex k ≤
      ((2 : ℝ) ^ k) ^ (1 + 2 * (Exponents.geometryDelta : ℝ)) := by
  have hp : (pitchScaleIndex k : ℝ) ≤ (1 + (Exponents.geometryDelta : ℝ)) * k :=
    Nat.floor_le (by positivity [geometryDelta_nonneg])
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [rpow_two_pow, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith [geometryDelta_nonneg]

/-- The number of nonempty fragments of a primary is at most `9 r ^ (2 δ₀)`.
Source: area-law Section 11, `geometry:primary-pieces`, lines 239–246, and
lines 716–717. -/
theorem card_primaryFragmentIndices_le_rpow (o : ℝ × ℝ) (k ℓ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (a b : ℤ) (j : ℤ × ℤ) :
    ((primaryFragmentIndices o k ℓ (pitchScaleIndex k) Z C a b j).card : ℝ) ≤
      9 * ((2 : ℝ) ^ k) ^ (2 * (Exponents.geometryDelta : ℝ)) := by
  have hkp := le_pitchScaleIndex k
  have hcard := card_primaryFragmentIndices_le o k ℓ (pitchScaleIndex k) Z C a b j hkp
  set m := pitchScaleIndex k - k with hm
  have hm1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hnat : (2 ^ m + 2) ^ 2 ≤ 9 * 2 ^ (2 * m) := by
    have h3 : 2 ^ m + 2 ≤ 3 * 2 ^ m := by omega
    calc (2 ^ m + 2) ^ 2 ≤ (3 * 2 ^ m) ^ 2 := Nat.pow_le_pow_left h3 2
      _ = 9 * 2 ^ (2 * m) := by ring
  have hreal : ((2 : ℝ) ^ (2 * m)) ≤ ((2 : ℝ) ^ k) ^ (2 * (Exponents.geometryDelta : ℝ)) := by
    have hp : (pitchScaleIndex k : ℝ) ≤ (1 + (Exponents.geometryDelta : ℝ)) * k :=
      Nat.floor_le (by positivity [geometryDelta_nonneg])
    rw [rpow_two_pow, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [hm]
    push_cast [Nat.cast_sub hkp]
    nlinarith
  calc ((primaryFragmentIndices o k ℓ (pitchScaleIndex k) Z C a b j).card : ℝ)
      ≤ ((9 * 2 ^ (2 * m) : ℕ) : ℝ) := by exact_mod_cast hcard.trans hnat
    _ = 9 * (2 : ℝ) ^ (2 * m) := by push_cast; ring
    _ ≤ 9 * ((2 : ℝ) ^ k) ^ (2 * (Exponents.geometryDelta : ℝ)) := by gcongr

/-! ### Fragments as template rectangles -/

/-- The lower integer offset of a clipped fragment in one coordinate. -/
private def fragmentLo (k ℓ p : ℕ) (a j z : ℤ) : ℤ :=
  max (2 ^ k * z) (2 ^ ℓ * a + 2 ^ p * j + 2 ^ ℓ)

/-- The upper integer offset of a clipped fragment in one coordinate. -/
private def fragmentHi (k ℓ p : ℕ) (a j z : ℤ) : ℤ :=
  min (2 ^ k * (z + 1)) (2 ^ ℓ * a + 2 ^ p * j + 2 ^ p)

private theorem primaryFragment_eq_Icc (o : ℝ × ℝ) (k ℓ p : ℕ) (a b : ℤ) (j z : ℤ × ℤ)
    (h : (dyadicCell o k z ∩ pitchInterior o ℓ p a b j).Nonempty) :
    primaryFragment o k ℓ p a b j z =
      Set.Icc (o.1 + fragmentLo k ℓ p a j.1 z.1) (o.1 + fragmentHi k ℓ p a j.1 z.1) ×ˢ
        Set.Icc (o.2 + fragmentLo k ℓ p b j.2 z.2) (o.2 + fragmentHi k ℓ p b j.2 z.2) := by
  rw [primaryFragment_eq_closedRectangle o k ℓ p a b j z h]
  simp only [fragmentLo, fragmentHi]
  push_cast
  rw [← max_add_add_left, ← min_add_add_left, ← max_add_add_left, ← min_add_add_left]
  ring_nf

private theorem fragmentLo_lt_fragmentHi (o : ℝ × ℝ) (k ℓ p : ℕ) (a b : ℤ) (j z : ℤ × ℤ)
    (h : (dyadicCell o k z ∩ pitchInterior o ℓ p a b j).Nonempty) :
    fragmentLo k ℓ p a j.1 z.1 < fragmentHi k ℓ p a j.1 z.1 ∧
      fragmentLo k ℓ p b j.2 z.2 < fragmentHi k ℓ p b j.2 z.2 := by
  obtain ⟨x, hx⟩ := h
  have hx' := subset_closure hx
  change x ∈ primaryFragment o k ℓ p a b j z at hx'
  rw [primaryFragment_eq_Icc o k ℓ p a b j z ⟨x, hx⟩] at hx'
  obtain ⟨hc, hp⟩ := hx
  change x ∈ Set.Ico _ _ ×ˢ Set.Ico _ _ at hc
  change x ∈ Set.Ioo _ _ ×ˢ Set.Ioo _ _ at hp
  have key (u : ℝ) (L H : ℤ) (c₀ c₁ d₀ d₁ : ℝ) (hL : (L : ℝ) = max c₀ d₀)
      (hH : (H : ℝ) = min c₁ d₁) (hu : u ∈ Set.Ico c₀ c₁) (hv : u ∈ Set.Ioo d₀ d₁) :
      L < H := by
    have : (L : ℝ) < H := by
      rw [hL, hH]
      exact (max_le hu.1 hv.1.le).trans_lt (lt_min hu.2 hv.2)
    exact_mod_cast this
  refine ⟨key (x.1 - o.1) _ _ ((2 : ℝ) ^ k * z.1) ((2 : ℝ) ^ k * (z.1 + 1))
    ((2 : ℝ) ^ ℓ * a + (2 : ℝ) ^ p * j.1 + (2 : ℝ) ^ ℓ)
    ((2 : ℝ) ^ ℓ * a + (2 : ℝ) ^ p * j.1 + (2 : ℝ) ^ p)
    (by simp [fragmentLo]) (by simp [fragmentHi])
    ⟨by linarith [hc.1.1], by linarith [hc.1.2]⟩ ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
    key (x.2 - o.2) _ _ ((2 : ℝ) ^ k * z.2) ((2 : ℝ) ^ k * (z.2 + 1))
    ((2 : ℝ) ^ ℓ * b + (2 : ℝ) ^ p * j.2 + (2 : ℝ) ^ ℓ)
    ((2 : ℝ) ^ ℓ * b + (2 : ℝ) ^ p * j.2 + (2 : ℝ) ^ p)
    (by simp [fragmentLo]) (by simp [fragmentHi])
    ⟨by linarith [hc.2.1], by linarith [hc.2.2]⟩ ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩

/-- The closed axis-parallel rectangle `[x₀, x₁] × [y₀, y₁]` with `x₀ < x₁` and
`y₀ < y₁`, as a template polygon. -/
private def boxPolygon (x₀ x₁ y₀ y₁ : ℝ) (hx : x₀ < x₁) (hy : y₀ < y₁) :
    TemplatePolygon :=
  .rectangle (x₀, y₀) (x₁ - x₀, 0) (0, y₁ - y₀)
    (by simp [Prod.ext_iff, (sub_pos.mpr hx).ne'])
    (by simp [Prod.ext_iff, (sub_pos.mpr hy).ne'])
    (by simp) (Or.inr (Or.inl rfl)) (Or.inl rfl)

private theorem boxPolygon_region (x₀ x₁ y₀ y₁ : ℝ) (hx : x₀ < x₁) (hy : y₀ < y₁) :
    (boxPolygon x₀ x₁ y₀ y₁ hx hy).region = Set.Icc x₀ x₁ ×ˢ Set.Icc y₀ y₁ := by
  have hset : ({(x₀, y₀), (x₀, y₀) + (x₁ - x₀, 0), (x₀, y₀) + (x₁ - x₀, 0) + (0, y₁ - y₀),
      (x₀, y₀) + (0, y₁ - y₀)} : Set (ℝ × ℝ)) = ({x₀, x₁} : Set ℝ) ×ˢ ({y₀, y₁} : Set ℝ) := by
    ext ⟨x, y⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_prod, Prod.ext_iff,
      Prod.fst_add, Prod.snd_add, add_zero, add_sub_cancel]
    tauto
  simp only [boxPolygon, TemplatePolygon.region]
  rw [hset, convexHull_prod, convexHull_pair, convexHull_pair, segment_eq_Icc hx.le,
    segment_eq_Icc hy.le]

/-- The lattice points of the closed rectangle of a fragment. -/
private def fragmentSample (o : ℝ × ℝ) (k ℓ p : ℕ) (a b : ℤ) (j z : ℤ × ℤ) :
    Finset (ℤ × ℤ) :=
  Finset.Icc ⌈o.1 + fragmentLo k ℓ p a j.1 z.1⌉ ⌊o.1 + fragmentHi k ℓ p a j.1 z.1⌋ ×ˢ
    Finset.Icc ⌈o.2 + fragmentLo k ℓ p b j.2 z.2⌉ ⌊o.2 + fragmentHi k ℓ p b j.2 z.2⌋

private theorem mem_fragmentSample_iff (o : ℝ × ℝ) (k ℓ p : ℕ) (a b : ℤ) (j z : ℤ × ℤ)
    (x : ℤ × ℤ) :
    x ∈ fragmentSample o k ℓ p a b j z ↔ integerPoint x ∈
      Set.Icc (o.1 + fragmentLo k ℓ p a j.1 z.1) (o.1 + fragmentHi k ℓ p a j.1 z.1) ×ˢ
        Set.Icc (o.2 + fragmentLo k ℓ p b j.2 z.2) (o.2 + fragmentHi k ℓ p b j.2 z.2) := by
  simp only [fragmentSample, Finset.mem_product, Finset.mem_Icc, Int.ceil_le, Int.le_floor,
    integerPoint, Set.mem_prod, Set.mem_Icc]

private theorem fragmentSample_nonempty (o : ℝ × ℝ) (k ℓ p : ℕ) (a b : ℤ) (j z : ℤ × ℤ)
    (h : (dyadicCell o k z ∩ pitchInterior o ℓ p a b j).Nonempty) :
    (fragmentSample o k ℓ p a b j z).Nonempty := by
  obtain ⟨h₁, h₂⟩ := fragmentLo_lt_fragmentHi o k ℓ p a b j z h
  have step (c : ℝ) (L H : ℤ) (hLH : L < H) : ⌈c + L⌉ ≤ ⌊c + H⌋ := by
    apply Int.le_floor.mpr
    have h1 : (L : ℝ) + 1 ≤ H := by exact_mod_cast hLH
    linarith [Int.ceil_lt_add_one (c + L)]
  exact ⟨(_, _), Finset.mem_product.mpr
    ⟨Finset.left_mem_Icc.mpr (step _ _ _ h₁), Finset.left_mem_Icc.mpr (step _ _ _ h₂)⟩⟩

/-- The rectangle of a nonempty fragment as a template polygon. -/
private def fragmentPolygon (o : ℝ × ℝ) (k ℓ p : ℕ) (a b : ℤ) (j z : ℤ × ℤ)
    (h : (dyadicCell o k z ∩ pitchInterior o ℓ p a b j).Nonempty) : TemplatePolygon :=
  boxPolygon (o.1 + fragmentLo k ℓ p a j.1 z.1) (o.1 + fragmentHi k ℓ p a j.1 z.1)
    (o.2 + fragmentLo k ℓ p b j.2 z.2) (o.2 + fragmentHi k ℓ p b j.2 z.2)
    (add_lt_add_right (Int.cast_lt.mpr (fragmentLo_lt_fragmentHi o k ℓ p a b j z h).1) _)
    (add_lt_add_right (Int.cast_lt.mpr (fragmentLo_lt_fragmentHi o k ℓ p a b j z h).2) _)

private theorem fragmentPolygon_region (o : ℝ × ℝ) (k ℓ p : ℕ) (a b : ℤ) (j z : ℤ × ℤ)
    (h : (dyadicCell o k z ∩ pitchInterior o ℓ p a b j).Nonempty) :
    (fragmentPolygon o k ℓ p a b j z h).region = primaryFragment o k ℓ p a b j z := by
  rw [fragmentPolygon, boxPolygon_region, primaryFragment_eq_Icc o k ℓ p a b j z h]

private theorem nonempty_of_mem_primaryFragmentIndices {o : ℝ × ℝ} {k ℓ p : ℕ}
    {Z : Finset (ℤ × ℤ)} {C : ℕ} {a b : ℤ} {j z : ℤ × ℤ}
    (hz : z ∈ primaryFragmentIndices o k ℓ p Z C a b j) :
    (dyadicCell o k z ∩ pitchInterior o ℓ p a b j).Nonempty := by
  classical
  simp only [primaryFragmentIndices, Finset.mem_filter] at hz
  exact hz.2

/-! ### The birth template -/

/-- The birth template of a primary: the lattice sample of its birth region, with one
closed rectangular piece for each nonempty fragment. It is a template of
Definition 9.3 with `s₀ = r = 2 ^ k` whenever the scanner scale `n` satisfies
`C_tpl N₀ (s₀ + 1) ≤ n` and bounds the belt pitch. The primary is required to
exist, that is, to have at least one fragment.
Source: area-law Section 11, lines 239–246 and 709–720, and Definition 9.3. -/
def primaryBirthTemplate (o : ℝ × ℝ) (k ℓ p : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : ℤ) (j : ℤ × ℤ) {Ctpl : ℝ} {n : ℕ}
    (hne : (primaryFragmentIndices o k ℓ p Z C a b j).Nonempty)
    (hscale : Ctpl * ((primaryFragmentIndices o k ℓ p Z C a b j).card : ℝ) *
      ((2 : ℝ) ^ k + 1) ≤ n)
    (hdiam : (2 : ℝ) ^ p ≤ n) : Template Ctpl n (2 ^ k) where
  n_pos := by
    have : (1 : ℝ) ≤ n := (one_le_pow₀ (by norm_num)).trans hdiam
    exact_mod_cast this
  s₀_pos := Nat.two_pow_pos k
  pieceCount := (primaryFragmentIndices o k ℓ p Z C a b j).card
  pieceCount_pos := Finset.card_pos.mpr hne
  polygon i :=
    let z := (primaryFragmentIndices o k ℓ p Z C a b j).equivFin.symm i
    fragmentPolygon o k ℓ p a b j z.1 (nonempty_of_mem_primaryFragmentIndices z.2)
  sample i := fragmentSample o k ℓ p a b j
    ((primaryFragmentIndices o k ℓ p Z C a b j).equivFin.symm i).1
  mem_sample i x := by
    rw [fragmentPolygon_region, primaryFragment_eq_Icc _ _ _ _ _ _ _ _
      (nonempty_of_mem_primaryFragmentIndices
        ((primaryFragmentIndices o k ℓ p Z C a b j).equivFin.symm i).2)]
    exact mem_fragmentSample_iff _ _ _ _ _ _ _ _ x
  piece_diameter i x hx y hy := by
    rw [fragmentPolygon_region] at hx hy
    have h := primaryFragment_dist_le o k ℓ p a b j _ x y hx hy
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at h
    simpa using h
  points := (primaryFragmentIndices o k ℓ p Z C a b j).biUnion
    (fragmentSample o k ℓ p a b j)
  nonempty := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨x, hx⟩ := fragmentSample_nonempty o k ℓ p a b j z
      (nonempty_of_mem_primaryFragmentIndices hz)
    exact ⟨x, Finset.mem_biUnion.mpr ⟨z, hz, hx⟩⟩
  cover := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨z, hz, hx⟩
      refine ⟨(primaryFragmentIndices o k ℓ p Z C a b j).equivFin ⟨z, hz⟩, ?_⟩
      simpa using hx
    · rintro ⟨i, hi⟩
      exact ⟨_, ((primaryFragmentIndices o k ℓ p Z C a b j).equivFin.symm i).2, hi⟩
  scale := by
    push_cast
    exact hscale
  diameter x hx y hy := by
    have hmem (w : ℤ × ℤ) (hw : w ∈ (primaryFragmentIndices o k ℓ p Z C a b j).biUnion
        (fragmentSample o k ℓ p a b j)) :
        integerPoint w ∈ primaryBirthRegion o k ℓ p Z C a b j := by
      obtain ⟨z, hz, hw⟩ := Finset.mem_biUnion.mp hw
      rw [primaryBirthRegion_eq_iUnion_primaryFragment]
      refine Set.mem_iUnion₂.mpr ⟨z, hz, ?_⟩
      rw [primaryFragment_eq_Icc o k ℓ p a b j z (nonempty_of_mem_primaryFragmentIndices hz)]
      exact (mem_fragmentSample_iff o k ℓ p a b j z w).mp hw
    have h := primaryBirthRegion_dist_le o k ℓ p Z C a b j _ _ (hmem x hx) (hmem y hy)
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at h
    exact h.trans hdiam

/-- The birth template has one piece for each nonempty fragment. -/
@[simp]
theorem primaryBirthTemplate_pieceCount (o : ℝ × ℝ) (k ℓ p : ℕ) (Z : Finset (ℤ × ℤ))
    (C : ℕ) (a b : ℤ) (j : ℤ × ℤ) {Ctpl : ℝ} {n : ℕ}
    (hne : (primaryFragmentIndices o k ℓ p Z C a b j).Nonempty)
    (hscale : Ctpl * ((primaryFragmentIndices o k ℓ p Z C a b j).card : ℝ) *
      ((2 : ℝ) ^ k + 1) ≤ n)
    (hdiam : (2 : ℝ) ^ p ≤ n) :
    (primaryBirthTemplate o k ℓ p Z C a b j hne hscale hdiam).pieceCount =
      (primaryFragmentIndices o k ℓ p Z C a b j).card :=
  rfl

/-- The points of the birth template are exactly the lattice points of the primary
birth region, `T = 𝓑 ∩ ℤ²`. Source: area-law Section 11, lines 709–710. -/
theorem primaryBirthTemplate_points (o : ℝ × ℝ) (k ℓ p : ℕ) (Z : Finset (ℤ × ℤ))
    (C : ℕ) (a b : ℤ) (j : ℤ × ℤ) {Ctpl : ℝ} {n : ℕ}
    (hne : (primaryFragmentIndices o k ℓ p Z C a b j).Nonempty)
    (hscale : Ctpl * ((primaryFragmentIndices o k ℓ p Z C a b j).card : ℝ) *
      ((2 : ℝ) ^ k + 1) ≤ n)
    (hdiam : (2 : ℝ) ^ p ≤ n) :
    ((primaryBirthTemplate o k ℓ p Z C a b j hne hscale hdiam).points : Set (ℤ × ℤ)) =
      integerPoint ⁻¹' primaryBirthRegion o k ℓ p Z C a b j := by
  ext x
  change x ∈ (primaryFragmentIndices o k ℓ p Z C a b j).biUnion _ ↔ _
  rw [Set.mem_preimage, primaryBirthRegion_eq_iUnion_primaryFragment, Finset.mem_biUnion,
    Set.mem_iUnion₂]
  simp only [exists_prop]
  refine exists_congr fun z ↦ and_congr_right fun hz ↦ ?_
  rw [primaryFragment_eq_Icc o k ℓ p a b j z (nonempty_of_mem_primaryFragmentIndices hz)]
  exact mem_fragmentSample_iff o k ℓ p a b j z x

/-- At the belt pitch `s_k`, the birth template has at most `9 r ^ (2 δ₀)` pieces.
Source: area-law Section 11, `geometry:primary-pieces` and lines 716–717. -/
theorem card_primaryBirthTemplate_pieces_le (o : ℝ × ℝ) (k ℓ : ℕ) (Z : Finset (ℤ × ℤ))
    (C : ℕ) (a b : ℤ) (j : ℤ × ℤ) {Ctpl : ℝ} {n : ℕ}
    (hne : (primaryFragmentIndices o k ℓ (pitchScaleIndex k) Z C a b j).Nonempty)
    (hscale : Ctpl * ((primaryFragmentIndices o k ℓ (pitchScaleIndex k) Z C a b j).card : ℝ) *
      ((2 : ℝ) ^ k + 1) ≤ n)
    (hdiam : (2 : ℝ) ^ pitchScaleIndex k ≤ n) :
    ((primaryBirthTemplate o k ℓ (pitchScaleIndex k) Z C a b j hne hscale hdiam).pieceCount :
      ℝ) ≤ 9 * ((2 : ℝ) ^ k) ^ (2 * (Exponents.geometryDelta : ℝ)) :=
  card_primaryFragmentIndices_le_rpow o k ℓ Z C a b j

/-! ### The choice of `C_P` -/

/-- If `C_P ≥ 18 C_tpl`, the scanner scale satisfies the template scale condition
`n ≥ C_tpl N₀ (s₀ + 1)` with `s₀ = r`. Source: area-law Section 11, lines 716–720. -/
theorem primaryBirthTemplate_scale {Ctpl CP : ℝ} (hCP : 18 * Ctpl ≤ CP) (o : ℝ × ℝ)
    (k ℓ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ) (a b : ℤ) (j : ℤ × ℤ) :
    Ctpl * ((primaryFragmentIndices o k ℓ (pitchScaleIndex k) Z C a b j).card : ℝ) *
      ((2 : ℝ) ^ k + 1) ≤ primaryScannerScale CP k := by
  set N := ((primaryFragmentIndices o k ℓ (pitchScaleIndex k) Z C a b j).card : ℝ)
  set R : ℝ := (2 : ℝ) ^ k with hR
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hR0 : 0 < R := by positivity
  rcases le_or_gt Ctpl 0 with hC | hC
  · have : Ctpl * N * (R + 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hC (Nat.cast_nonneg _))
        (by positivity)
    exact this.trans (Nat.cast_nonneg _)
  · have hN := card_primaryFragmentIndices_le_rpow o k ℓ Z C a b j
    have hsplit : R ^ (1 + 2 * (Exponents.geometryDelta : ℝ)) =
        R * R ^ (2 * (Exponents.geometryDelta : ℝ)) := by
      rw [Real.rpow_add hR0, Real.rpow_one]
    have hpow : 0 ≤ R ^ (2 * (Exponents.geometryDelta : ℝ)) := by positivity
    calc Ctpl * N * (R + 1)
        ≤ Ctpl * (9 * R ^ (2 * (Exponents.geometryDelta : ℝ))) * (2 * R) := by
          gcongr
          linarith
      _ = 18 * Ctpl * R ^ (1 + 2 * (Exponents.geometryDelta : ℝ)) := by
          rw [hsplit]
          ring
      _ ≤ CP * R ^ (1 + 2 * (Exponents.geometryDelta : ℝ)) := by gcongr
      _ ≤ primaryScannerScale CP k := Nat.le_ceil _

/-- If `C_P ≥ 1`, the scanner scale bounds the belt pitch, `s_k ≤ n`.
Source: area-law Section 11, lines 718–720. -/
theorem two_pow_pitchScaleIndex_le_primaryScannerScale {CP : ℝ} (hCP : 1 ≤ CP) (k : ℕ) :
    (2 : ℝ) ^ pitchScaleIndex k ≤ primaryScannerScale CP k := by
  have hpos : 0 ≤ ((2 : ℝ) ^ k) ^ (1 + 2 * (Exponents.geometryDelta : ℝ)) := by positivity
  calc (2 : ℝ) ^ pitchScaleIndex k
      ≤ ((2 : ℝ) ^ k) ^ (1 + 2 * (Exponents.geometryDelta : ℝ)) :=
        two_pow_pitchScaleIndex_le k
    _ ≤ CP * ((2 : ℝ) ^ k) ^ (1 + 2 * (Exponents.geometryDelta : ℝ)) :=
        le_mul_of_one_le_left hpos hCP
    _ ≤ primaryScannerScale CP k := Nat.le_ceil _

/-- The primary scanner coefficient `C_P = max (18 C_tpl) 1`. Auxiliary to the
explicit constant of Theorem 1.1 (`docs/notes/arealaw2d_explicit_constant.tex`).
Source: area-law Section 11, lines 716–720 and 756–757. -/
def primaryScannerConstant (Ctpl : ℝ) : ℝ :=
  max (18 * Ctpl) 1

/-- The primary scanner coefficient is at least one. -/
theorem one_le_primaryScannerConstant (Ctpl : ℝ) : 1 ≤ primaryScannerConstant Ctpl :=
  le_max_right _ _

/-- **Choice of `C_P`, explicitly.** With `C_P = primaryScannerConstant C_tpl`,
every primary of every layer, with the scanner scale `n = ⌈C_P r ^ (1 + 2 δ₀)⌉`,
satisfies `n ≥ C_tpl N₀ (s₀ + 1)` and `s_k ≤ n`.
Source: area-law Section 11, lines 716–720 and 756–757. -/
theorem primaryScannerConstant_spec (Ctpl : ℝ) (o : ℝ × ℝ) (k ℓ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (a b : ℤ) (j : ℤ × ℤ) :
    Ctpl * ((primaryFragmentIndices o k ℓ (pitchScaleIndex k) Z C a b j).card : ℝ) *
        ((2 : ℝ) ^ k + 1) ≤ primaryScannerScale (primaryScannerConstant Ctpl) k ∧
      (2 : ℝ) ^ pitchScaleIndex k ≤ primaryScannerScale (primaryScannerConstant Ctpl) k :=
  ⟨primaryBirthTemplate_scale (le_max_left _ _) o k ℓ Z C a b j,
    two_pow_pitchScaleIndex_le_primaryScannerScale (le_max_right _ _) k⟩

/-- **Choice of `C_P`.** For every template constant `C_tpl` there is `C_P ≥ 1` such
that every primary of every layer, with the scanner scale `n = ⌈C_P r ^ (1 + 2 δ₀)⌉`,
satisfies `n ≥ C_tpl N₀ (s₀ + 1)` and `s_k ≤ n`; its sup diameter is at most `s_k`.
Thus `primaryBirthTemplate` is a template of Definition 9.3 at this scale. The
constant is `primaryScannerConstant C_tpl = max (18 C_tpl) 1`.
Source: area-law Section 11, lines 716–720 and 756–757. -/
theorem exists_primaryScannerConstant (Ctpl : ℝ) :
    ∃ CP : ℝ, 1 ≤ CP ∧ ∀ (o : ℝ × ℝ) (k ℓ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ) (a b : ℤ)
      (j : ℤ × ℤ),
      Ctpl * ((primaryFragmentIndices o k ℓ (pitchScaleIndex k) Z C a b j).card : ℝ) *
          ((2 : ℝ) ^ k + 1) ≤ primaryScannerScale CP k ∧
        (2 : ℝ) ^ pitchScaleIndex k ≤ primaryScannerScale CP k :=
  ⟨_, one_le_primaryScannerConstant Ctpl, primaryScannerConstant_spec Ctpl⟩

/-! ### Cut clearance -/

/-- **Cut clearance of a primary birth template.** Its points have endpoint distance
at least `C₀ r`, so the clearance `dist_∞(T, Z) > 4 D₀ s₀` of Definition 9.3 holds
once `4 D₀ < C₀`; the source's choice `C₀ > 100 (D₀ + 1)` ensures this.
Source: area-law Section 11, `geometry:layer-distance`, lines 179–189, and
lines 720–722. -/
theorem primaryBirthTemplate_isSeparated {D₀ : ℝ} (o : ℝ × ℝ) (k ℓ p : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (hC : 4 * D₀ < C) (a b : ℤ) (j : ℤ × ℤ) {Ctpl : ℝ}
    {n : ℕ} (hne : (primaryFragmentIndices o k ℓ p Z C a b j).Nonempty)
    (hscale : Ctpl * ((primaryFragmentIndices o k ℓ p Z C a b j).card : ℝ) *
      ((2 : ℝ) ^ k + 1) ≤ n)
    (hdiam : (2 : ℝ) ^ p ≤ n) :
    (primaryBirthTemplate o k ℓ p Z C a b j hne hscale hdiam).IsSeparated D₀ Z := by
  intro x hx z hz
  have hx' : integerPoint x ∈ primaryBirthRegion o k ℓ p Z C a b j := by
    have := congrArg (x ∈ ·) (primaryBirthTemplate_points o k ℓ p Z C a b j hne hscale hdiam)
    simp only [Finset.mem_coe, Set.mem_preimage] at this
    exact this.mp hx
  have hd := dyadicLayer_dist_lower o k Z C (integerPoint x)
    (closure_mono Set.inter_subset_left hx') z hz
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hd
  have hR : (0 : ℝ) < 2 ^ k := by positivity
  push_cast
  calc 4 * D₀ * (2 : ℝ) ^ k < C * 2 ^ k := by gcongr
    _ ≤ _ := hd

/-! ### Scale limits -/

/-- The scanner scale is at most `(max C_P 0 + 1) r ^ (1 + 2 δ₀)`. -/
private theorem primaryScannerScale_le (CP : ℝ) (k : ℕ) :
    (primaryScannerScale CP k : ℝ) ≤
      (max CP 0 + 1) * ((2 : ℝ) ^ k) ^ (1 + 2 * (Exponents.geometryDelta : ℝ)) := by
  set E : ℝ := ((2 : ℝ) ^ k) ^ (1 + 2 * (Exponents.geometryDelta : ℝ))
  have hE : 1 ≤ E := Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by
    positivity [geometryDelta_nonneg])
  have h₁ : (primaryScannerScale CP k : ℝ) ≤ ⌈max CP 0 * E⌉₊ := by
    exact_mod_cast Nat.ceil_mono (by gcongr; exact le_max_left _ _)
  have h₂ := Nat.ceil_lt_add_one (show 0 ≤ max CP 0 * E by positivity)
  nlinarith [le_max_right CP 0]

/-- The layer threshold for the primary scale limits with parameter `ε`. With
`C_n = max C_P 0 + 1` and `e = 1 + 2 δ₀`, it is the dyadic index of the larger
of the power-ratio thresholds for `C_n ^ (1 - ℓ) r ^ (e (1 - ℓ)) ≤ ε r` and
`C_n ^ β r ^ (e β) ≤ (ε / 2) r ^ ζ`. -/
def primaryScaleLimitThreshold (CP ε : ℝ) : ℕ :=
  dyadicIndexThreshold (max
    (Real.powerRatioThreshold ((max CP 0 + 1) ^ (1 - (Exponents.geometryEll : ℝ))) ε
      (1 - (1 + 2 * (Exponents.geometryDelta : ℝ)) * (1 - (Exponents.geometryEll : ℝ))))
    (Real.powerRatioThreshold ((max CP 0 + 1) ^ (Exponents.beta : ℝ)) (ε / 2)
      ((Exponents.zeta : ℝ) -
        (1 + 2 * (Exponents.geometryDelta : ℝ)) * (Exponents.beta : ℝ))))

/-- **Explicit primary scale limits** (`geometry:primary-limits`). For `ε > 0`,
every layer `k ≥ primaryScaleLimitThreshold C_P ε` has, with
`n = ⌈C_P r ^ (1 + 2 δ₀)⌉`, `r = 2 ^ k` and `t_k = 2 ^ ⌊ζ k⌋`, the bounds
`⌊n ^ (1 - ℓ)⌋ ≤ ε r`, `n ^ β ≤ ε t_k` and `n ^ β ≤ ε r`. Source: area-law
Section 11, `10-geometry.tex`, lines 722–729 and 768–772. -/
theorem primaryScaleLimits_of_primaryScaleLimitThreshold_le (CP : ℝ) {ε : ℝ}
    (hε : 0 < ε) {k : ℕ} (hk : primaryScaleLimitThreshold CP ε ≤ k) :
    (⌊(primaryScannerScale CP k : ℝ) ^ (1 - (Exponents.geometryEll : ℝ))⌋₊ : ℝ) ≤
        ε * 2 ^ k ∧
      (primaryScannerScale CP k : ℝ) ^ (Exponents.beta : ℝ) ≤ ε * 2 ^ fineScaleIndex k ∧
      (primaryScannerScale CP k : ℝ) ^ (Exponents.beta : ℝ) ≤ ε * 2 ^ k := by
  obtain ⟨hβζ, -, hℓ, -, -, -⟩ := Exponents.geometry_gaps
  have hβζ' : (1 + 2 * (Exponents.geometryDelta : ℝ)) * Exponents.beta <
      Exponents.zeta := by exact_mod_cast hβζ
  have hℓ' : (1 + 2 * (Exponents.geometryDelta : ℝ)) * (1 - Exponents.geometryEll) < 1 := by
    exact_mod_cast hℓ
  have hβ0 : (0 : ℝ) ≤ Exponents.beta := by norm_num [Exponents.beta, Exponents.boxError]
  have hℓ0 : (0 : ℝ) ≤ 1 - Exponents.geometryEll := by norm_num [Exponents.geometryEll]
  set e : ℝ := 1 + 2 * (Exponents.geometryDelta : ℝ)
  set Cn : ℝ := max CP 0 + 1
  have hCn : 0 ≤ Cn := by positivity
  set R : ℝ := (2 : ℝ) ^ k
  have hR0 : 0 < R := by positivity
  have hRT := le_two_pow_of_dyadicIndexThreshold_le hk
  have h₁ : Cn ^ (1 - (Exponents.geometryEll : ℝ)) *
      R ^ (e * (1 - (Exponents.geometryEll : ℝ))) ≤ ε * R ^ (1 : ℝ) :=
    Real.mul_rpow_le_mul_rpow_of_powerRatioThreshold_le (by positivity) hε hℓ'
      ((le_max_left _ _).trans hRT)
  have h₂ : Cn ^ (Exponents.beta : ℝ) * R ^ (e * Exponents.beta) ≤
      ε / 2 * R ^ (Exponents.zeta : ℝ) :=
    Real.mul_rpow_le_mul_rpow_of_powerRatioThreshold_le (by positivity) (half_pos hε) hβζ'
      ((le_max_right _ _).trans hRT)
  have hn := primaryScannerScale_le CP k
  have hn0 : (0 : ℝ) ≤ primaryScannerScale CP k := Nat.cast_nonneg _
  have hpow (x : ℝ) (hx : 0 ≤ x) :
      (primaryScannerScale CP k : ℝ) ^ x ≤ Cn ^ x * R ^ (e * x) := by
    calc (primaryScannerScale CP k : ℝ) ^ x ≤ (Cn * R ^ e) ^ x :=
          Real.rpow_le_rpow hn0 hn hx
      _ = Cn ^ x * R ^ (e * x) := by
          rw [Real.mul_rpow hCn (by positivity), ← Real.rpow_mul hR0.le]
  -- `t_k ≥ r ^ ζ / 2`
  have ht : R ^ (Exponents.zeta : ℝ) ≤ 2 * 2 ^ fineScaleIndex k := by
    have hf := Nat.lt_floor_add_one ((Exponents.zeta : ℝ) * (k : ℝ))
    change (Exponents.zeta : ℝ) * k < (fineScaleIndex k : ℝ) + 1 at hf
    rw [show R ^ (Exponents.zeta : ℝ) = (2 : ℝ) ^ ((k : ℝ) * Exponents.zeta) by
      simp only [R]; rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)], ← pow_succ',
      ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hβt : (primaryScannerScale CP k : ℝ) ^ (Exponents.beta : ℝ) ≤
      ε * 2 ^ fineScaleIndex k :=
    calc (primaryScannerScale CP k : ℝ) ^ (Exponents.beta : ℝ)
        ≤ Cn ^ (Exponents.beta : ℝ) * R ^ (e * Exponents.beta) := hpow _ hβ0
      _ ≤ ε / 2 * R ^ (Exponents.zeta : ℝ) := h₂
      _ ≤ ε / 2 * (2 * 2 ^ fineScaleIndex k) := by gcongr
      _ = ε * 2 ^ fineScaleIndex k := by ring
  refine ⟨?_, hβt, hβt.trans ?_⟩
  · calc (⌊(primaryScannerScale CP k : ℝ) ^ (1 - (Exponents.geometryEll : ℝ))⌋₊ : ℝ)
        ≤ (primaryScannerScale CP k : ℝ) ^ (1 - (Exponents.geometryEll : ℝ)) :=
          Nat.floor_le (by positivity)
      _ ≤ Cn ^ (1 - (Exponents.geometryEll : ℝ)) *
            R ^ (e * (1 - (Exponents.geometryEll : ℝ))) := hpow _ hℓ0
      _ ≤ ε * R ^ (1 : ℝ) := h₁
      _ = ε * 2 ^ k := by rw [Real.rpow_one]
  · exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num) (fineScaleIndex_le k)) hε.le

/-- The layer threshold `dyadicIndexThreshold (n_* / C_P)` from which every
primary scanner scale is at least `n_*`. -/
def primaryScannerScaleThreshold (CP : ℝ) (nstar : ℕ) : ℕ :=
  dyadicIndexThreshold ((nstar : ℝ) / CP)

/-- **Explicit lower scale threshold.** For `C_P > 0`, every layer
`k ≥ primaryScannerScaleThreshold C_P n_*` has primary scanner scale at least
`n_*`. Source: area-law Section 11,
`10-geometry.tex`, lines 768–770. -/
theorem le_primaryScannerScale_of_primaryScannerScaleThreshold_le {CP : ℝ} (hCP : 0 < CP)
    {nstar k : ℕ} (hk : primaryScannerScaleThreshold CP nstar ≤ k) :
    nstar ≤ primaryScannerScale CP k := by
  have hdiv := le_two_pow_of_dyadicIndexThreshold_le hk
  rw [div_le_iff₀ hCP] at hdiv
  have hR : (2 : ℝ) ^ k ≤ ((2 : ℝ) ^ k) ^ (1 + 2 * (Exponents.geometryDelta : ℝ)) := by
    conv_lhs => rw [← Real.rpow_one ((2 : ℝ) ^ k)]
    exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
      (by linarith [geometryDelta_nonneg])
  have : (nstar : ℝ) ≤ primaryScannerScale CP k := by
    refine hdiv.trans ?_
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_left hR hCP.le).trans (Nat.le_ceil _)
  exact_mod_cast this

/-- **Primary scale limits** (`geometry:primary-limits`). For every `ε > 0`, every
sufficiently large layer index `k` has, with `n = ⌈C_P r ^ (1 + 2 δ₀)⌉`, `r = 2 ^ k`
and `t_k = 2 ^ ⌊ζ k⌋`, the bounds `⌊n ^ (1 - ℓ)⌋ ≤ ε r`, `n ^ β ≤ ε t_k` and
`n ^ β ≤ ε r`. The scale depends only on the layer, so the threshold is uniform
over primaries; it is `primaryScaleLimitThreshold C_P ε`.
Source: area-law Section 11, lines 722–729 and 768–772. -/
theorem eventually_primaryScaleLimits (CP : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      (⌊(primaryScannerScale CP k : ℝ) ^ (1 - (Exponents.geometryEll : ℝ))⌋₊ : ℝ) ≤
          ε * 2 ^ k ∧
        (primaryScannerScale CP k : ℝ) ^ (Exponents.beta : ℝ) ≤ ε * 2 ^ fineScaleIndex k ∧
        (primaryScannerScale CP k : ℝ) ^ (Exponents.beta : ℝ) ≤ ε * 2 ^ k :=
  eventually_atTop.2 ⟨primaryScaleLimitThreshold CP ε,
    fun _ hk ↦ primaryScaleLimits_of_primaryScaleLimitThreshold_le CP hε hk⟩

/-- **Lower scale threshold.** For `C_P > 0` and every `n_*`, all primary scanner
scales are at least `n_*` in all sufficiently large layers; the threshold is
`primaryScannerScaleThreshold C_P n_*`.
Source: area-law Section 11, lines 768–770. -/
theorem le_primaryScannerScale {CP : ℝ} (hCP : 0 < CP) (nstar : ℕ) :
    ∀ᶠ k : ℕ in atTop, nstar ≤ primaryScannerScale CP k :=
  eventually_atTop.2 ⟨primaryScannerScaleThreshold CP nstar,
    fun _ hk ↦ le_primaryScannerScale_of_primaryScannerScaleThreshold_le hCP hk⟩

end TNLean.PEPS.AreaLaw.Geometry
