/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CellChambers

/-!
# One active square of the recursive coloured partition

This module treats one active square of the recursion in the proof of the
conditional information bound for one cell. Ambient points carry one of three
labels: allowed (`none`) or forbidden colour `0` or `1` (`some i`).

An active square of side `u` comes with finitely many vertical and horizontal
lines, including its four sides, distinct parallel lines at least `u / 8` apart,
such that the labels are constant on their chambers in the radius-`u` padding of
the square (`IsChamberSquare`). At a nonterminal square put `t = t₀ = u ^ γ`; the
estimates here assume only `0 < t` and `1000 t ≤ u`.

* Around each line intersection within `10 t` of the square a hole of radius
  `4 t` is reserved (`holes`, `InHole`).
* An allowed point of the square outside the holes sees at most one forbidden
  colour within `t` (`IsChamberSquare.colour_eq_of_ne`).
* The remaining allowed points within `t` of forbidden colour `0` form the
  family-`1` tile, the others the family-`0` tile (`tile`); each tile is at
  distance greater than `t` from the forbidden set of its own family
  (`IsChamberSquare.lt_dist_of_mem_tile`).
* The lattice sample of each tile is a union of at most `66 ^ 2` closed lattice
  rectangles (`IsChamberSquare.isRectUnion_tileSample`).
* Each hole, with lines at offsets `0, ± t, ± 4 t` from its centre, is an active
  square of side `8 t` satisfying the chamber invariant again for the colouring
  after this square's tiles are assigned (`IsChamberSquare.child`).

Boundaries follow the half-open convention of `CellChambers`, which is the
source's common infinitesimal displacement. The source reserves closed holes;
under that convention they are the half-open boxes used here.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, proof of Lemma 3.2 (`lem:cell-cmi`), `02-information.tex`,
  lines 224–300.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.Approximation.CellPartition

open TNLean.PEPS.AreaLaw.Geometry

/-- The labels of ambient points: `none` is allowed and `some i` is forbidden
colour `i`. Source: Lemma 3.2, `02-information.tex`, lines 181–188 and 228–233. -/
abbrev Colouring := ℝ × ℝ → Option (Fin 2)

/-- An active square, given by its lower-left corner, with its vertical and
horizontal chamber lines; the common side is a parameter of the generation.
Source: Lemma 3.2, `02-information.tex`, lines 228–233. -/
structure ActiveSquare where
  /-- The lower-left corner. -/
  corner : ℝ × ℝ
  /-- The vertical chamber lines. -/
  vlines : Finset ℝ
  /-- The horizontal chamber lines. -/
  hlines : Finset ℝ

/-- The radius-`u` padding of the square of side `u` at `c`.
Source: Lemma 3.2, `02-information.tex`, lines 230–231. -/
def window (c : ℝ × ℝ) (u : ℝ) : Set (ℝ × ℝ) := box (c.1 - u, c.2 - u) (3 * u)

theorem mem_window_of_dist_le {c a q : ℝ × ℝ} {u r : ℝ} (ha : a ∈ box c u)
    (hq : dist q a ≤ r) (hr : r < u) : q ∈ window c u := by
  obtain ⟨h1, h2, h3, h4⟩ := ha
  have hx := abs_le.mp ((abs_fst_sub_le_dist q a).trans hq)
  have hy := abs_le.mp ((abs_snd_sub_le_dist q a).trans hq)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- A point of a half-open box lies within `r` of a reference point `z` once the
box lies in the closed square of radius `r` about `z`. -/
theorem dist_le_of_mem_box_of_le {c z p : ℝ × ℝ} {s r : ℝ} (hp : p ∈ box c s)
    (h1 : z.1 - r ≤ c.1) (h2 : c.1 + s ≤ z.1 + r) (h3 : z.2 - r ≤ c.2)
    (h4 : c.2 + s ≤ z.2 + r) : dist p z ≤ r := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
  exact dist_le_of_abs_le (abs_le.mpr ⟨by linarith, by linarith⟩)
    (abs_le.mpr ⟨by linarith, by linarith⟩)

/-- **The chamber invariant** of an active square of side `u`: its sides are among
its lines, distinct parallel lines are at least `u / 8` apart, there are at most
five lines in each direction, and the labels are constant on chambers in the
radius-`u` padding. Source: Lemma 3.2, `02-information.tex`, lines 228–233. -/
structure IsChamberSquare (col : Colouring) (u : ℝ) (Q : ActiveSquare) : Prop where
  sides_v : Q.corner.1 ∈ Q.vlines ∧ Q.corner.1 + u ∈ Q.vlines
  sides_h : Q.corner.2 ∈ Q.hlines ∧ Q.corner.2 + u ∈ Q.hlines
  spacing_v : ∀ x ∈ Q.vlines, ∀ x' ∈ Q.vlines, x ≠ x' → u / 8 ≤ |x - x'|
  spacing_h : ∀ y ∈ Q.hlines, ∀ y' ∈ Q.hlines, y ≠ y' → u / 8 ≤ |y - y'|
  card_v : Q.vlines.card ≤ 5
  card_h : Q.hlines.card ≤ 5
  const : ∀ p ∈ window Q.corner u, ∀ q ∈ window Q.corner u,
    SameChamber Q.vlines Q.hlines p q → col p = col q

open Classical in
/-- The line intersections within distance `10 t` of the square, at which holes
are reserved. Source: Lemma 3.2, `02-information.tex`, lines 240–243. -/
def holes (Q : ActiveSquare) (u t : ℝ) : Finset (ℝ × ℝ) :=
  (Q.vlines ×ˢ Q.hlines).filter fun z ↦ ∃ a ∈ box Q.corner u, dist z a ≤ 10 * t

/-- The lower-left corner of the hole of radius `4 t` about `z`. -/
def holeCorner (t : ℝ) (z : ℝ × ℝ) : ℝ × ℝ := (z.1 - 4 * t, z.2 - 4 * t)

/-- The point lies in a reserved hole. Source: Lemma 3.2, `02-information.tex`,
lines 240–245. -/
def InHole (Q : ActiveSquare) (u t : ℝ) (p : ℝ × ℝ) : Prop :=
  ∃ z ∈ holes Q u t, p ∈ box (holeCorner t z) (8 * t)

/-- The point is within sup distance `t` of forbidden colour `0`.
Source: Lemma 3.2, `02-information.tex`, lines 254–256. -/
def NearZero (col : Colouring) (t : ℝ) (p : ℝ × ℝ) : Prop :=
  ∃ q, col q = some 0 ∧ dist p q ≤ t

/-- The family-`f` tile of an active square: allowed points of the square outside
the holes, within `t` of forbidden colour `0` for `f = 1` and not for `f = 0`.
Source: Lemma 3.2, `02-information.tex`, lines 254–257. -/
def tile (col : Colouring) (Q : ActiveSquare) (u t : ℝ) (f : Fin 2) : Set (ℝ × ℝ) :=
  {p | p ∈ box Q.corner u ∧ col p = none ∧ ¬InHole Q u t p ∧ (NearZero col t p ↔ f = 1)}

theorem mem_holes {Q : ActiveSquare} {u t : ℝ} {z : ℝ × ℝ} :
    z ∈ holes Q u t ↔ (z.1 ∈ Q.vlines ∧ z.2 ∈ Q.hlines) ∧
      ∃ a ∈ box Q.corner u, dist z a ≤ 10 * t := by
  simp [holes, Finset.mem_product]

theorem card_holes_le {col : Colouring} {Q : ActiveSquare} {u : ℝ}
    (hQ : IsChamberSquare col u Q) (t : ℝ) : (holes Q u t).card ≤ 25 := by
  refine (Finset.card_le_card (s := holes Q u t) (t := Q.vlines ×ˢ Q.hlines)
    fun z hz ↦ Finset.mem_product.mpr (mem_holes.mp hz).1).trans ?_
  rw [Finset.card_product]
  exact Nat.mul_le_mul hQ.card_v hQ.card_h

/-- Distinct holes are centred at intersections at least `u / 8` apart in one
coordinate. Source: Lemma 3.2, `02-information.tex`, lines 244 and 276–277. -/
theorem IsChamberSquare.hole_sep {col : Colouring} {Q : ActiveSquare} {u t : ℝ}
    (hQ : IsChamberSquare col u Q) {z z' : ℝ × ℝ} (hz : z ∈ holes Q u t)
    (hz' : z' ∈ holes Q u t) (hne : z ≠ z') :
    u / 8 ≤ |z.1 - z'.1| ∨ u / 8 ≤ |z.2 - z'.2| := by
  obtain ⟨⟨hz1, hz2⟩, -⟩ := mem_holes.mp hz
  obtain ⟨⟨hz1', hz2'⟩, -⟩ := mem_holes.mp hz'
  by_cases h1 : z.1 = z'.1
  · exact Or.inr (hQ.spacing_h _ hz2 _ hz2' fun h2 ↦ hne (Prod.ext h1 h2))
  · exact Or.inl (hQ.spacing_v _ hz1 _ hz1' h1)

theorem dist_le_of_mem_holeBox {t : ℝ} {z p : ℝ × ℝ} (hp : p ∈ box (holeCorner t z) (8 * t)) :
    dist p z ≤ 4 * t :=
  dist_le_of_mem_box_of_le hp (by simp [holeCorner]) (by simp [holeCorner]; linarith)
    (by simp [holeCorner]) (by simp [holeCorner]; linarith)

/-- **One forbidden colour near an allowed point.** A point of the square outside
the holes sees, within distance `t`, at most one label different from its own:
it sees no two parallel lines, and not lines of both orientations, since their
intersection would be reserved. Source: Lemma 3.2, `02-information.tex`,
lines 245–252. -/
theorem IsChamberSquare.colour_eq_of_ne {col : Colouring} {Q : ActiveSquare} {u t : ℝ}
    (hQ : IsChamberSquare col u Q) (ht : 0 < t) (htu : 1000 * t ≤ u) {p q₀ q₁ : ℝ × ℝ}
    (hp : p ∈ box Q.corner u) (hhole : ¬InHole Q u t p) (h₀ : dist q₀ p ≤ t)
    (h₁ : dist q₁ p ≤ t) (hc₀ : col q₀ ≠ col p) (hc₁ : col q₁ ≠ col p) :
    col q₀ = col q₁ := by
  have hw : ∀ q, dist q p ≤ t → q ∈ window Q.corner u := fun q hq ↦
    mem_window_of_dist_le hp hq (by linarith)
  -- a label change within distance `t` of `p` is caused by a line within `t` of `p`
  have sep : ∀ a b, dist a p ≤ t → dist b p ≤ t → col a ≠ col b →
      (∃ x ∈ Q.vlines, |x - p.1| ≤ t ∧ ¬(x ≤ a.1 ↔ x ≤ b.1)) ∨
        (∃ y ∈ Q.hlines, |y - p.2| ≤ t ∧ ¬(y ≤ a.2 ↔ y ≤ b.2)) := by
    intro a b ha hb hab
    by_contra hcon
    apply hab
    refine hQ.const a (hw a ha) b (hw b hb) ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩
    · by_contra hne
      exact hcon (Or.inl ⟨x, hx, (abs_sub_le_max_of_not_iff hne).trans
        (max_le ((abs_fst_sub_le_dist a p).trans ha) ((abs_fst_sub_le_dist b p).trans hb)),
        hne⟩)
    · by_contra hne
      exact hcon (Or.inr ⟨y, hy, (abs_sub_le_max_of_not_iff hne).trans
        (max_le ((abs_snd_sub_le_dist a p).trans ha) ((abs_snd_sub_le_dist b p).trans hb)),
        hne⟩)
  have noBoth : ∀ x ∈ Q.vlines, |x - p.1| ≤ t → ∀ y ∈ Q.hlines, |y - p.2| ≤ t → False := by
    intro x hx hxp y hy hyp
    apply hhole
    refine ⟨(x, y), mem_holes.mpr ⟨⟨hx, hy⟩, p, hp,
      (dist_le_of_abs_le hxp hyp).trans (by linarith)⟩, ?_⟩
    rw [abs_le] at hxp hyp
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [holeCorner] <;> linarith [hxp.1, hxp.2, hyp.1, hyp.2]
  have uniq : ∀ {L : Finset ℝ} {r : ℝ}, (∀ x ∈ L, ∀ x' ∈ L, x ≠ x' → u / 8 ≤ |x - x'|) →
      ∀ x ∈ L, ∀ x' ∈ L, |x - r| ≤ t → |x' - r| ≤ t → x = x' := by
    intro L r hL x hx x' hx' h h'
    by_contra hne
    have := hL x hx x' hx' hne
    have := abs_sub_le x r x'
    rw [abs_sub_comm r x'] at this
    linarith
  have hpp : dist p p ≤ t := by rw [dist_self]; exact ht.le
  by_contra h01
  rcases sep q₀ p h₀ hpp hc₀ with ⟨x1, hx1, hd1, hn1⟩ | ⟨y1, hy1, hd1, hn1⟩
  · rcases sep q₁ p h₁ hpp hc₁ with ⟨x2, hx2, hd2, hn2⟩ | ⟨y2, hy2, hd2, -⟩
    · rcases sep q₀ q₁ h₀ h₁ h01 with ⟨x3, hx3, hd3, hn3⟩ | ⟨y3, hy3, hd3, -⟩
      · obtain rfl := uniq hQ.spacing_v x1 hx1 x2 hx2 hd1 hd2
        obtain rfl := uniq hQ.spacing_v x1 hx1 x3 hx3 hd1 hd3
        tauto
      · exact noBoth x1 hx1 hd1 y3 hy3 hd3
    · exact noBoth x1 hx1 hd1 y2 hy2 hd2
  · rcases sep q₁ p h₁ hpp hc₁ with ⟨x2, hx2, hd2, -⟩ | ⟨y2, hy2, hd2, hn2⟩
    · exact noBoth x2 hx2 hd2 y1 hy1 hd1
    · rcases sep q₀ q₁ h₀ h₁ h01 with ⟨x3, hx3, hd3, -⟩ | ⟨y3, hy3, hd3, hn3⟩
      · exact noBoth x3 hx3 hd3 y1 hy1 hd1
      · obtain rfl := uniq hQ.spacing_h y1 hy1 y2 hy2 hd1 hd2
        obtain rfl := uniq hQ.spacing_h y1 hy1 y3 hy3 hd1 hd3
        tauto

/-- **Clearance of a new tile.** Every point of the family-`f` tile is at distance
greater than `t` from the forbidden set of colour `f`, as it was at the start of
the generation. Source: Lemma 3.2, `02-information.tex`, lines 257–259. -/
theorem IsChamberSquare.lt_dist_of_mem_tile {col : Colouring} {Q : ActiveSquare} {u t : ℝ}
    (hQ : IsChamberSquare col u Q) (ht : 0 < t) (htu : 1000 * t ≤ u) {f : Fin 2}
    {p q : ℝ × ℝ} (hp : p ∈ tile col Q u t f) (hq : col q = some f) : t < dist p q := by
  obtain ⟨hpQ, hpc, hph, hpn⟩ := hp
  by_contra hle
  push Not at hle
  have hf : f = 0 ∨ f = 1 := by fin_cases f <;> simp
  rcases hf with rfl | rfl
  · exact absurd (hpn.mp ⟨q, hq, hle⟩) (by decide)
  · obtain ⟨q₀, hq₀, hd₀⟩ := hpn.mpr rfl
    have h := hQ.colour_eq_of_ne (q₀ := q₀) (q₁ := q) ht htu hpQ hph (by rwa [dist_comm])
      (by rwa [dist_comm])
      (by rw [hq₀, hpc]; simp) (by rw [hq, hpc]; simp)
    rw [hq₀, hq] at h
    exact absurd h (by decide)

/-- The vertical lines on whose chambers the tiles of a square are constant: the
old lines, their translates by `± t` from the distance test, and the hole sides.
Source: Lemma 3.2, `02-information.tex`, lines 260–265. -/
def tileLinesV (Q : ActiveSquare) (u t : ℝ) : Finset ℝ :=
  Q.vlines ∪ shifted Q.vlines t ∪ (holes Q u t).image (fun z ↦ (holeCorner t z).1) ∪
    (holes Q u t).image (fun z ↦ (holeCorner t z).1 + 8 * t)

/-- The horizontal lines on whose chambers the tiles of a square are constant. -/
def tileLinesH (Q : ActiveSquare) (u t : ℝ) : Finset ℝ :=
  Q.hlines ∪ shifted Q.hlines t ∪ (holes Q u t).image (fun z ↦ (holeCorner t z).2) ∪
    (holes Q u t).image (fun z ↦ (holeCorner t z).2 + 8 * t)

private theorem card_shifted_le (X : Finset ℝ) (t : ℝ) : (shifted X t).card ≤ 2 * X.card :=
  (Finset.card_union_le _ _).trans (by
    have := Finset.card_image_le (s := X) (f := (· + t))
    have := Finset.card_image_le (s := X) (f := (· - t))
    omega)

private theorem card_tileLines_le {L : Finset ℝ} {H : Finset (ℝ × ℝ)} {t : ℝ}
    {g₁ g₂ : ℝ × ℝ → ℝ} (hL : L.card ≤ 5) (hH : H.card ≤ 25) :
    (L ∪ shifted L t ∪ H.image g₁ ∪ H.image g₂).card ≤ 65 := by
  have h1 := Finset.card_union_le (L ∪ shifted L t ∪ H.image g₁) (H.image g₂)
  have h2 := Finset.card_union_le (L ∪ shifted L t) (H.image g₁)
  have h3 := Finset.card_union_le L (shifted L t)
  have h4 := card_shifted_le L t
  have h5 := Finset.card_image_le (s := H) (f := g₁)
  have h6 := Finset.card_image_le (s := H) (f := g₂)
  omega

open Classical in
/-- The lattice sample of a tile. -/
def tileSample (col : Colouring) (Q : ActiveSquare) (u t : ℝ) (f : Fin 2) :
    Finset (ℤ × ℤ) :=
  (latticeBox Q.corner u).filter fun p ↦ integerPoint p ∈ tile col Q u t f

/-- Every tile is a union of chambers of `tileLinesV` and `tileLinesH` inside its
square. Source: Lemma 3.2, `02-information.tex`, lines 260–265. -/
theorem IsChamberSquare.mem_tile_iff_of_sameChamber {col : Colouring} {Q : ActiveSquare}
    {u t : ℝ} (hQ : IsChamberSquare col u Q) (ht : 0 < t) (htu : 1000 * t ≤ u) (f : Fin 2)
    {p q : ℝ × ℝ} (hp : p ∈ box Q.corner u) (hq : q ∈ box Q.corner u)
    (hpq : SameChamber (tileLinesV Q u t) (tileLinesH Q u t) p q) :
    p ∈ tile col Q u t f ↔ q ∈ tile col Q u t f := by
  have hV : Q.vlines ⊆ tileLinesV Q u t := fun x hx ↦ by simp [tileLinesV, hx]
  have hH : Q.hlines ⊆ tileLinesH Q u t := fun x hx ↦ by simp [tileLinesH, hx]
  have hVs : shifted Q.vlines t ⊆ tileLinesV Q u t := fun x hx ↦ by simp [tileLinesV, hx]
  have hHs : shifted Q.hlines t ⊆ tileLinesH Q u t := fun x hx ↦ by simp [tileLinesH, hx]
  have hw : ∀ {a w}, a ∈ box Q.corner u → dist w a ≤ t → w ∈ window Q.corner u :=
    fun ha hw ↦ mem_window_of_dist_le ha hw (by linarith)
  have hwbox : ∀ {a}, a ∈ box Q.corner u → a ∈ window Q.corner u := fun ha ↦
    hw ha (by rw [dist_self]; exact ht.le)
  have hold := hpq.mono hV hH
  have hcol : col p = col q := hQ.const p (hwbox hp) q (hwbox hq) hold
  have hhole : InHole Q u t p ↔ InHole Q u t q := by
    refine exists_congr fun z ↦ and_congr_right fun hz ↦ mem_box_iff_of_sameChamber
      ⟨?_, ?_⟩ ⟨?_, ?_⟩ hpq
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hz))
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem
        (fun z ↦ (holeCorner t z).1 + 8 * t) hz)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hz))
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem
        (fun z ↦ (holeCorner t z).2 + 8 * t) hz)
  have one : ∀ {a b}, a ∈ box Q.corner u → b ∈ box Q.corner u →
      SameChamber (tileLinesV Q u t) (tileLinesH Q u t) a b → NearZero col t a →
        NearZero col t b := by
    rintro a b ha hb hab ⟨q₀, hq₀, hd⟩
    obtain ⟨q₁, hd₁, hc⟩ := exists_sameChamber_clamp (by rwa [dist_comm]) (hab.mono hVs hHs)
    refine ⟨q₁, ?_, by rwa [dist_comm]⟩
    rw [← hQ.const q₀ (hw ha (by rwa [dist_comm])) q₁ (hw hb hd₁) hc, hq₀]
  have hnear : NearZero col t p ↔ NearZero col t q := ⟨one hp hq hpq, one hq hp hpq.symm⟩
  simp only [tile, Set.mem_ofPred_eq, hcol, hhole, hnear, hp, hq]

/-- **Tiles are rectangular unions.** The lattice sample of each tile is a union of
at most `66 ^ 2` closed lattice rectangles. Source: Lemma 3.2, `02-information.tex`,
lines 260–265. -/
theorem IsChamberSquare.isRectUnion_tileSample {col : Colouring} {Q : ActiveSquare}
    {u t : ℝ} (hQ : IsChamberSquare col u Q) (ht : 0 < t) (htu : 1000 * t ≤ u) (f : Fin 2) :
    IsRectUnion (66 * 66) (tileSample col Q u t f) := by
  refine (isRectUnion_filter_of_sameChamber Q.corner u (tileLinesV Q u t) (tileLinesH Q u t)
    (tile col Q u t f) fun p hp q hq hpq ↦ ?_).mono ?_
  · rw [mem_latticeBox] at hp hq
    exact (hQ.mem_tile_iff_of_sameChamber ht htu f hp hq hpq).mp
  · have hv : (tileLinesV Q u t).card ≤ 65 := card_tileLines_le hQ.card_v (card_holes_le hQ t)
    have hh : (tileLinesH Q u t).card ≤ 65 := card_tileLines_le hQ.card_h (card_holes_le hQ t)
    exact Nat.mul_le_mul (by omega) (by omega)

/-- The lines of a child square: offsets `0, ± t, ± 4 t` from the parent line.
Source: Lemma 3.2, `02-information.tex`, lines 284–290. -/
def childLines (a t : ℝ) : Finset ℝ := {a - 4 * t, a - t, a, a + t, a + 4 * t}

/-- The child square reserved about the intersection `z`, of side `8 t`.
Source: Lemma 3.2, `02-information.tex`, lines 274–280. -/
def child (t : ℝ) (z : ℝ × ℝ) : ActiveSquare :=
  ⟨holeCorner t z, childLines z.1 t, childLines z.2 t⟩

open Classical in
/-- The colouring after the tiles of one square are assigned their forbidden colours.
Source: Lemma 3.2, `02-information.tex`, lines 184–186 and 254–257. -/
def localNext (col : Colouring) (Q : ActiveSquare) (u t : ℝ) : Colouring := fun p ↦
  if p ∈ tile col Q u t 1 then some 1 else if p ∈ tile col Q u t 0 then some 0 else col p

theorem mem_childLines_self (a t : ℝ) : a ∈ childLines a t := by simp [childLines]

theorem sub_mem_childLines (a t : ℝ) : a - 4 * t ∈ childLines a t := by simp [childLines]

theorem add_mem_childLines (a t : ℝ) : a - 4 * t + 8 * t ∈ childLines a t := by
  rw [show a - 4 * t + 8 * t = a + 4 * t by ring]; simp [childLines]

theorem shifted_singleton_subset_childLines (a t : ℝ) : shifted {a} t ⊆ childLines a t := by
  intro x hx
  simp only [shifted, Finset.image_singleton, Finset.mem_union, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> simp [childLines]

theorem spacing_childLines {a t : ℝ} (ht : 0 < t) :
    ∀ x ∈ childLines a t, ∀ x' ∈ childLines a t, x ≠ x' → 8 * t / 8 ≤ |x - x'| := by
  intro x hx x' hx' hne
  rw [show 8 * t / 8 = t by ring]
  simp only [childLines, Finset.mem_insert, Finset.mem_singleton] at hx hx'
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> rcases hx' with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hne
    | exact le_abs.mpr (Or.inl (by linarith))
    | exact le_abs.mpr (Or.inr (by linarith))

/-- **Children satisfy the chamber invariant.** Each reserved hole, with the lines
at offsets `0, ± t, ± 4 t` from its centre, is an active square of side `8 t`
satisfying the chamber invariant for any colouring that agrees near the parent
with the colouring after this square's tiles are assigned. In the child's padded
window the only old lines are the two through its centre, other holes are absent,
and the distance test changes the label only at offsets `± t`.
Source: Lemma 3.2, `02-information.tex`, lines 274–300. -/
theorem IsChamberSquare.isChamberSquare_child {col : Colouring} {Q : ActiveSquare} {u t : ℝ}
    (hQ : IsChamberSquare col u Q) (ht : 0 < t) (htu : 1000 * t ≤ u) {z : ℝ × ℝ}
    (hz : z ∈ holes Q u t) {col' : Colouring}
    (hcol' : ∀ p a, a ∈ box Q.corner u → dist p a ≤ 22 * t → col' p = localNext col Q u t p) :
    IsChamberSquare col' (8 * t) (child t z) where
  sides_v := ⟨sub_mem_childLines _ _, add_mem_childLines _ _⟩
  sides_h := ⟨sub_mem_childLines _ _, add_mem_childLines _ _⟩
  spacing_v := spacing_childLines ht
  spacing_h := spacing_childLines ht
  card_v := Finset.card_le_five
  card_h := Finset.card_le_five
  const := by
    intro p hp q hq hpq
    obtain ⟨⟨hzv, hzh⟩, a, ha, hza⟩ := mem_holes.mp hz
    have hwz : ∀ {w}, w ∈ window (child t z).corner (8 * t) → dist w z ≤ 12 * t := fun {w} hw ↦
      dist_le_of_mem_box_of_le hw (by simp [child, holeCorner]; linarith)
        (by simp [child, holeCorner]; linarith) (by simp [child, holeCorner]; linarith)
        (by simp [child, holeCorner]; linarith)
    have hpz := hwz hp
    have hqz := hwz hq
    have hnear_a : ∀ {w}, dist w z ≤ 13 * t → dist w a ≤ 23 * t := fun {w} hw ↦
      (dist_triangle w z a).trans (by linarith)
    have hwin : ∀ {w}, dist w z ≤ 13 * t → w ∈ window Q.corner u := fun {w} hw ↦
      mem_window_of_dist_le ha (hnear_a hw) (by linarith)
    have hlt : 13 * t < u / 8 := by linarith
    -- near the centre, the old chambers are decided by the two lines through it
    have hiso : ∀ {w w' : ℝ × ℝ}, dist w z ≤ 13 * t → dist w' z ≤ 13 * t →
        (z.1 ≤ w.1 ↔ z.1 ≤ w'.1) → (z.2 ≤ w.2 ↔ z.2 ≤ w'.2) →
          SameChamber Q.vlines Q.hlines w w' := by
      intro w w' hw hw' h1 h2
      exact ⟨sameSide_of_isolated (fun x hx hne ↦ hQ.spacing_v x hx z.1 hzv hne)
          (((abs_fst_sub_le_dist w z).trans hw).trans_lt hlt)
          (((abs_fst_sub_le_dist w' z).trans hw').trans_lt hlt) h1,
        sameSide_of_isolated (fun y hy hne ↦ hQ.spacing_h y hy z.2 hzh hne)
          (((abs_snd_sub_le_dist w z).trans hw).trans_lt hlt)
          (((abs_snd_sub_le_dist w' z).trans hw').trans_lt hlt) h2⟩
    have h12 : 12 * t ≤ 13 * t := by linarith
    have hold : SameChamber Q.vlines Q.hlines p q :=
      hiso (hpz.trans h12) (hqz.trans h12) (hpq.1 z.1 (mem_childLines_self _ _))
        (hpq.2 z.2 (mem_childLines_self _ _))
    have hcol : col p = col q :=
      hQ.const p (hwin (hpz.trans h12)) q (hwin (hqz.trans h12)) hold
    have hbox : p ∈ box Q.corner u ↔ q ∈ box Q.corner u :=
      mem_box_iff_of_sameChamber hQ.sides_v hQ.sides_h hold
    have hkey : ∀ {w}, dist w z ≤ 12 * t →
        (InHole Q u t w ↔ w ∈ box (holeCorner t z) (8 * t)) := by
      intro w hw
      refine ⟨fun ⟨z', hz', hwz'⟩ ↦ ?_, fun h ↦ ⟨z, hz, h⟩⟩
      by_cases hzz : z' = z
      · exact hzz ▸ hwz'
      · exfalso
        have h4 := dist_le_of_mem_holeBox hwz'
        have hd : dist z' z ≤ 16 * t := (dist_triangle z' w z).trans (by
          rw [dist_comm] at h4; linarith)
        rcases hQ.hole_sep hz' hz hzz with h | h
        · linarith [abs_fst_sub_le_dist z' z]
        · linarith [abs_snd_sub_le_dist z' z]
    have hhole : InHole Q u t p ↔ InHole Q u t q := by
      rw [hkey hpz, hkey hqz]
      exact mem_box_iff_of_sameChamber ⟨sub_mem_childLines _ _, add_mem_childLines _ _⟩
        ⟨sub_mem_childLines _ _, add_mem_childLines _ _⟩ hpq
    have one : ∀ {w w'}, dist w z ≤ 12 * t → dist w' z ≤ 12 * t →
        SameChamber (child t z).vlines (child t z).hlines w w' → NearZero col t w →
          NearZero col t w' := by
      rintro w w' hw hw' hww' ⟨q₀, hq₀, hd⟩
      obtain ⟨q₁, hd₁, hc⟩ := exists_sameChamber_clamp (by rwa [dist_comm])
        (hww'.mono (shifted_singleton_subset_childLines z.1 t)
          (shifted_singleton_subset_childLines z.2 t))
      have hq₀z : dist q₀ z ≤ 13 * t :=
        (dist_triangle q₀ w z).trans (by rw [dist_comm] at hd; linarith)
      have hq₁z : dist q₁ z ≤ 13 * t := (dist_triangle q₁ w' z).trans (by linarith)
      have hc' := hiso hq₀z hq₁z (hc.1 z.1 (Finset.mem_singleton_self _))
        (hc.2 z.2 (Finset.mem_singleton_self _))
      refine ⟨q₁, ?_, by rwa [dist_comm]⟩
      rw [← hQ.const q₀ (hwin hq₀z) q₁ (hwin hq₁z) hc', hq₀]
    have hnear : NearZero col t p ↔ NearZero col t q := ⟨one hpz hqz hpq, one hqz hpz hpq.symm⟩
    have htile : ∀ f, p ∈ tile col Q u t f ↔ q ∈ tile col Q u t f := fun f ↦ by
      simp only [tile, Set.mem_ofPred_eq, hcol, hhole, hnear, hbox]
    rw [hcol' p a ha ((dist_triangle p z a).trans (by linarith)),
      hcol' q a ha ((dist_triangle q z a).trans (by linarith))]
    unfold localNext
    by_cases h1 : p ∈ tile col Q u t 1
    · rw [ite_eq_left h1, ite_eq_left ((htile 1).mp h1)]
    · rw [ite_eq_right h1, ite_eq_right (mt (htile 1).mpr h1)]
      by_cases h0 : p ∈ tile col Q u t 0
      · rw [ite_eq_left h0, ite_eq_left ((htile 0).mp h0)]
      · rw [ite_eq_right h0, ite_eq_right (mt (htile 0).mpr h0), hcol]

end TNLean.PEPS.Approximation.CellPartition
