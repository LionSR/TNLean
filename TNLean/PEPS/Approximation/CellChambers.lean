/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.TemplateRows
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Data.Int.Interval

/-!
# Chambers of finitely many axis-parallel lines

The recursive coloured partition in the proof of the conditional information
bound for one cell keeps its colours constant on the chambers of finitely many
horizontal and vertical lines. This module records the elementary chamber
calculus used there.

The source fixes boundaries by one consistent infinitesimal generic displacement
(`02-information.tex`, lines 152–158). Here that convention is the half-open
one: a vertical line at `x` puts a point `p` on its right side exactly when
`x ≤ p.1`, and boxes are half-open. Under this convention

* two points lie in the same chamber when no line separates them (`SameChamber`);
* a line separating two points lies between them, so near a single isolated line
  the chamber of a point is decided by that line alone;
* if `p` and `p'` lie in the same chamber of the lines shifted by `± t`, every
  point within sup distance `t` of `p` has a partner in its own chamber within
  sup distance `t` of `p'`. This is why the distance test of the construction
  creates new boundaries only at offsets `± t₀` (lines 287–290);
* the lattice sample of a set that is a union of chambers inside a half-open box
  is a union of at most `(|X| + 1) (|Y| + 1)` closed lattice rectangles.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, proof of Lemma 3.2 (`lem:cell-cmi`), `02-information.tex`,
  lines 152–158 (boundary convention) and 263–290 (chambers, distance tests and
  rectangular chambers).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.Approximation.CellPartition

open TNLean.PEPS.AreaLaw.Geometry

/-! ### Lines in one coordinate -/

/-- No line of `X` separates the coordinates `a` and `b`, with the half-open
convention that `a` lies on the right of the line `x` exactly when `x ≤ a`.
Source: Lemma 3.2, `02-information.tex`, lines 152–158 and 228–233. -/
def SameSide (X : Finset ℝ) (a b : ℝ) : Prop := ∀ x ∈ X, (x ≤ a ↔ x ≤ b)

variable {X Y : Finset ℝ} {a b c : ℝ}

theorem SameSide.refl (X : Finset ℝ) (a : ℝ) : SameSide X a a := fun _ _ ↦ Iff.rfl

theorem SameSide.symm (h : SameSide X a b) : SameSide X b a := fun x hx ↦ (h x hx).symm

theorem SameSide.trans (h : SameSide X a b) (h' : SameSide X b c) : SameSide X a c :=
  fun x hx ↦ (h x hx).trans (h' x hx)

theorem SameSide.mono (hXY : X ⊆ Y) (h : SameSide Y a b) : SameSide X a b :=
  fun x hx ↦ h x (hXY hx)

/-- A line separating two coordinates lies between them, hence no farther from
any reference coordinate than the farther of the two. -/
theorem abs_sub_le_max_of_not_iff {x z : ℝ} (h : ¬(x ≤ a ↔ x ≤ b)) :
    |x - z| ≤ max |a - z| |b - z| := by
  by_cases hxa : x ≤ a <;> by_cases hxb : x ≤ b
  · exact absurd (iff_of_true hxa hxb) h
  · exact max_comm |a - z| |b - z| ▸
      abs_le_max_abs_abs (sub_le_sub_right (not_le.mp hxb).le z) (sub_le_sub_right hxa z)
  · exact abs_le_max_abs_abs (sub_le_sub_right (not_le.mp hxa).le z) (sub_le_sub_right hxb z)
  · exact absurd (iff_of_false hxa hxb) h

/-- Near an isolated line `z` of `X`, the chamber of a coordinate is decided by
`z` alone: if all other lines are at least `δ` from `z` and `a`, `b` are closer
than `δ` to `z`, then `z` not separating them means no line of `X` does.
Source: Lemma 3.2, `02-information.tex`, lines 280–283. -/
theorem sameSide_of_isolated {z δ : ℝ}
    (hsep : ∀ x ∈ X, x ≠ z → δ ≤ |x - z|) (ha : |a - z| < δ) (hb : |b - z| < δ)
    (h : z ≤ a ↔ z ≤ b) : SameSide X a b := by
  intro x hx
  by_contra hne
  by_cases hxz : x = z
  · exact hne (hxz ▸ h)
  · have h1 := hsep x hx hxz
    have h2 := abs_sub_le_max_of_not_iff (z := z) hne
    have h3 : max |a - z| |b - z| < δ := max_lt ha hb
    linarith

/-- The lines of `X` translated by `+ t` and by `- t`.
Source: Lemma 3.2, `02-information.tex`, lines 263–265 and 284–287. -/
def shifted (X : Finset ℝ) (t : ℝ) : Finset ℝ := X.image (· + t) ∪ X.image (· - t)

theorem subset_shifted_of_mem {t x : ℝ} (hx : x ∈ X) :
    ({x + t, x - t} : Finset ℝ) ⊆ shifted X t := by
  intro y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)

/-- **Distance tests in one coordinate.** If `a` and `b` are not separated by the
lines of `X` shifted by `± t`, then every `q` within `t` of `a` has a partner
within `t` of `b` that no line of `X` separates from `q`; the partner is `q`
clamped to `[b - t, b + t]`. -/
theorem exists_sameSide_clamp {t q : ℝ} (hq : |q - a| ≤ t) (h : SameSide (shifted X t) a b) :
    ∃ q', |q' - b| ≤ t ∧ SameSide X q q' := by
  have ht : 0 ≤ t := (abs_nonneg _).trans hq
  rw [abs_le] at hq
  refine ⟨max (b - t) (min q (b + t)), ?_, ?_⟩
  · rw [abs_le]
    constructor
    · linarith [le_max_left (b - t) (min q (b + t))]
    · have : max (b - t) (min q (b + t)) ≤ b + t :=
        max_le (by linarith) (min_le_right _ _)
      linarith
  · intro x hx
    have h1 := h (x + t) (subset_shifted_of_mem hx (by simp))
    have h2 := h (x - t) (subset_shifted_of_mem hx (by simp))
    constructor
    · intro hxq
      by_cases hc : x ≤ b + t
      · exact le_max_of_le_right (le_min hxq hc)
      · exfalso
        have hb : ¬(x - t ≤ b) := by intro h'; exact hc (by linarith)
        have ha : ¬(x - t ≤ a) := fun h' ↦ hb (h2.mp h')
        linarith
    · intro hxq'
      rcases le_max_iff.mp hxq' with h' | h'
      · have : x + t ≤ a := h1.mpr (by linarith)
        linarith
      · exact h'.trans (min_le_left _ _)

/-! ### Chambers in the plane -/

/-- Two points lie in one chamber of the vertical lines `X` and horizontal lines `Y`.
Source: Lemma 3.2, `02-information.tex`, lines 228–233. -/
def SameChamber (X Y : Finset ℝ) (p q : ℝ × ℝ) : Prop :=
  SameSide X p.1 q.1 ∧ SameSide Y p.2 q.2

theorem SameChamber.refl (X Y : Finset ℝ) (p : ℝ × ℝ) : SameChamber X Y p p :=
  ⟨SameSide.refl _ _, SameSide.refl _ _⟩

theorem SameChamber.symm {p q : ℝ × ℝ} (h : SameChamber X Y p q) : SameChamber X Y q p :=
  ⟨h.1.symm, h.2.symm⟩

theorem SameChamber.trans {p q r : ℝ × ℝ} (h : SameChamber X Y p q)
    (h' : SameChamber X Y q r) : SameChamber X Y p r :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

theorem SameChamber.mono {X' Y' : Finset ℝ} {p q : ℝ × ℝ} (hX : X' ⊆ X) (hY : Y' ⊆ Y)
    (h : SameChamber X Y p q) : SameChamber X' Y' p q :=
  ⟨h.1.mono hX, h.2.mono hY⟩

/-- The sup distance on the plane in coordinates. -/
theorem dist_eq_max (p q : ℝ × ℝ) : dist p q = max |p.1 - q.1| |p.2 - q.2| := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]

theorem abs_fst_sub_le_dist (p q : ℝ × ℝ) : |p.1 - q.1| ≤ dist p q :=
  (dist_eq_max p q).symm ▸ le_max_left _ _

theorem abs_snd_sub_le_dist (p q : ℝ × ℝ) : |p.2 - q.2| ≤ dist p q :=
  (dist_eq_max p q).symm ▸ le_max_right _ _

theorem dist_le_of_abs_le {p q : ℝ × ℝ} {r : ℝ} (h1 : |p.1 - q.1| ≤ r)
    (h2 : |p.2 - q.2| ≤ r) : dist p q ≤ r := by
  rw [dist_eq_max]; exact max_le h1 h2

/-- **Distance tests in the plane.** If `p` and `p'` lie in one chamber of the
lines shifted by `± t`, every point within sup distance `t` of `p` has a partner
in its own chamber within sup distance `t` of `p'`.
Source: Lemma 3.2, `02-information.tex`, lines 284–290. -/
theorem exists_sameChamber_clamp {t : ℝ} {p p' q : ℝ × ℝ} (hq : dist q p ≤ t)
    (h : SameChamber (shifted X t) (shifted Y t) p p') :
    ∃ q', dist q' p' ≤ t ∧ SameChamber X Y q q' := by
  obtain ⟨x, hx, hxX⟩ := exists_sameSide_clamp ((abs_fst_sub_le_dist q p).trans hq) h.1
  obtain ⟨y, hy, hyY⟩ := exists_sameSide_clamp ((abs_snd_sub_le_dist q p).trans hq) h.2
  exact ⟨(x, y), dist_le_of_abs_le hx hy, hxX, hyY⟩

/-- A half-open axis-parallel square with lower-left corner `c` and side `a`.
Source: Lemma 3.2, `02-information.tex`, lines 152–158 and 228–229. -/
def box (c : ℝ × ℝ) (a : ℝ) : Set (ℝ × ℝ) :=
  {p | c.1 ≤ p.1 ∧ p.1 < c.1 + a ∧ c.2 ≤ p.2 ∧ p.2 < c.2 + a}

/-- Membership in a box is constant on chambers containing its sides. -/
theorem mem_box_iff_of_sameChamber {c' : ℝ × ℝ} {a' : ℝ} {p q : ℝ × ℝ}
    (hX : c'.1 ∈ X ∧ c'.1 + a' ∈ X) (hY : c'.2 ∈ Y ∧ c'.2 + a' ∈ Y)
    (h : SameChamber X Y p q) : p ∈ box c' a' ↔ q ∈ box c' a' := by
  change (c'.1 ≤ p.1 ∧ p.1 < c'.1 + a' ∧ c'.2 ≤ p.2 ∧ p.2 < c'.2 + a') ↔
    (c'.1 ≤ q.1 ∧ q.1 < c'.1 + a' ∧ c'.2 ≤ q.2 ∧ q.2 < c'.2 + a')
  simp only [← not_le, h.1 _ hX.1, h.1 _ hX.2, h.2 _ hY.1, h.2 _ hY.2]

theorem abs_sub_lt_of_mem_box {c' : ℝ × ℝ} {a' : ℝ} {p q : ℝ × ℝ} (hp : p ∈ box c' a')
    (hq : q ∈ box c' a') : |p.1 - q.1| < a' ∧ |p.2 - q.2| < a' := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  obtain ⟨h5, h6, h7, h8⟩ := hq
  exact ⟨abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩,
    abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩⟩

theorem dist_le_of_mem_box {c' : ℝ × ℝ} {a' : ℝ} {p q : ℝ × ℝ} (hp : p ∈ box c' a')
    (hq : q ∈ box c' a') : dist p q ≤ a' :=
  dist_le_of_abs_le (abs_sub_lt_of_mem_box hp hq).1.le (abs_sub_lt_of_mem_box hp hq).2.le

/-! ### Lattice samples -/

/-- The lattice sample of `box c a`. -/
def latticeBox (c : ℝ × ℝ) (a : ℝ) : Finset (ℤ × ℤ) :=
  Finset.Icc ⌈c.1⌉ (⌈c.1 + a⌉ - 1) ×ˢ Finset.Icc ⌈c.2⌉ (⌈c.2 + a⌉ - 1)

private theorem mem_Icc_ceil_iff {n : ℤ} {r a' : ℝ} :
    n ∈ Finset.Icc ⌈r⌉ (⌈r + a'⌉ - 1) ↔ r ≤ n ∧ (n : ℝ) < r + a' := by
  rw [Finset.mem_Icc, Int.ceil_le, Int.le_sub_one_iff, Int.lt_ceil]

theorem mem_latticeBox {c : ℝ × ℝ} {a : ℝ} {p : ℤ × ℤ} :
    p ∈ latticeBox c a ↔ integerPoint p ∈ box c a := by
  simp only [latticeBox, Finset.mem_product, mem_Icc_ceil_iff, box, integerPoint,
    Set.mem_ofPred_eq, and_assoc]

private theorem card_Icc_ceil_le (r a' : ℝ) (ha : 0 ≤ a') :
    ((Finset.Icc ⌈r⌉ (⌈r + a'⌉ - 1)).card : ℝ) ≤ a' + 1 := by
  rw [Int.card_Icc]
  have h1 : ⌈r + a'⌉ - 1 + 1 - ⌈r⌉ ≤ ⌈a'⌉ := by
    have := Int.ceil_add_le r a'
    omega
  have h2 : (0 : ℤ) ≤ ⌈a'⌉ := Int.ceil_nonneg ha
  have h3 : ((⌈r + a'⌉ - 1 + 1 - ⌈r⌉).toNat : ℤ) ≤ ⌈a'⌉ := by omega
  have h4 : (((⌈r + a'⌉ - 1 + 1 - ⌈r⌉).toNat : ℤ) : ℝ) ≤ (⌈a'⌉ : ℝ) := by exact_mod_cast h3
  have h5 := Int.ceil_lt_add_one a'
  push_cast at h4
  linarith

/-- A half-open square of side `a ≥ 0` has at most `(a + 1) ^ 2` lattice points.
Source: Lemma 3.2, `02-information.tex`, lines 302–303 (boundedly many sites in a
terminal square). -/
theorem card_latticeBox_le (c : ℝ × ℝ) {a : ℝ} (ha : 0 ≤ a) :
    ((latticeBox c a).card : ℝ) ≤ (a + 1) ^ 2 := by
  rw [latticeBox, Finset.card_product, Nat.cast_mul, sq]
  exact mul_le_mul (card_Icc_ceil_le _ _ ha) (card_Icc_ceil_le _ _ ha) (by positivity)
    (by linarith)

/-- A closed lattice rectangle: the full lattice sample of a closed axis-parallel
rectangle with integer corners; empty products are allowed. -/
def IsLatticeRect (R : Finset (ℤ × ℤ)) : Prop :=
  ∃ a₁ b₁ a₂ b₂ : ℤ, R = Finset.Icc a₁ b₁ ×ˢ Finset.Icc a₂ b₂

theorem isLatticeRect_empty : IsLatticeRect ∅ := ⟨1, 0, 1, 0, by simp⟩

/-- A lattice set that is the union of at most `N` closed lattice rectangles.
Source: Lemma 3.2, `02-information.tex`, lines 263–265 (each tile is a union of
boundedly many rectangular chambers). -/
def IsRectUnion (N : ℕ) (T : Finset (ℤ × ℤ)) : Prop :=
  ∃ n ≤ N, ∃ R : Fin n → Finset (ℤ × ℤ), (∀ i, IsLatticeRect (R i)) ∧
    T = Finset.univ.biUnion R

theorem IsRectUnion.mono {N M : ℕ} {T : Finset (ℤ × ℤ)} (hNM : N ≤ M)
    (h : IsRectUnion N T) : IsRectUnion M T := by
  obtain ⟨n, hn, R, hR, hT⟩ := h
  exact ⟨n, hn.trans hNM, R, hR, hT⟩

/-- A finite order-connected set of integers is a closed interval, possibly empty. -/
theorem exists_eq_Icc_of_ordConnected (s : Finset ℤ)
    (h : ∀ a ∈ s, ∀ b ∈ s, ∀ c, a ≤ c → c ≤ b → c ∈ s) : ∃ lo hi, s = Finset.Icc lo hi := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨1, 0, by simp⟩
  · exact ⟨_, _, finset_eq_Icc_min'_max'_of_between hs fun ha hb hac hcb ↦ h _ ha _ hb _ hac hcb⟩

/-- The number of lines of `X` weakly left of `a`; it indexes the chamber of `a`. -/
def rank (X : Finset ℝ) (a : ℝ) : ℕ := (X.filter (· ≤ a)).card

theorem rank_mono (X : Finset ℝ) {a b : ℝ} (hab : a ≤ b) : rank X a ≤ rank X b :=
  Finset.card_le_card fun x hx ↦ by
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans hab⟩

theorem rank_le_card (X : Finset ℝ) (a : ℝ) : rank X a ≤ X.card := Finset.card_filter_le _ _

private theorem sameSide_of_rank_eq_of_le (hab : a ≤ b) (h : rank X a = rank X b) :
    SameSide X a b := by
  have hsub : X.filter (· ≤ a) ⊆ X.filter (· ≤ b) := fun x hx ↦ by
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans hab⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq h.symm)
  intro x hx
  constructor
  · exact fun h' ↦ h'.trans hab
  · intro h'
    have : x ∈ X.filter (· ≤ b) := Finset.mem_filter.mpr ⟨hx, h'⟩
    rw [← heq] at this
    exact (Finset.mem_filter.mp this).2

/-- Coordinates with equal rank lie on the same side of every line. -/
theorem sameSide_of_rank_eq (h : rank X a = rank X b) : SameSide X a b := by
  rcases le_total a b with hab | hab
  · exact sameSide_of_rank_eq_of_le hab h
  · exact (sameSide_of_rank_eq_of_le hab h.symm).symm

open Classical in
/-- **Rectangular chambers.** If a plane set is a union of chambers of `X` and `Y`
on the lattice points of a half-open box, its lattice sample in the box is a union
of at most `(|X| + 1) (|Y| + 1)` closed lattice rectangles.
Source: Lemma 3.2, `02-information.tex`, lines 263–265. -/
theorem isRectUnion_filter_of_sameChamber (c : ℝ × ℝ) (a : ℝ) (X Y : Finset ℝ)
    (S : Set (ℝ × ℝ))
    (hS : ∀ p ∈ latticeBox c a, ∀ q ∈ latticeBox c a,
      SameChamber X Y (integerPoint p) (integerPoint q) → integerPoint p ∈ S →
        integerPoint q ∈ S) :
    IsRectUnion ((X.card + 1) * (Y.card + 1))
      ((latticeBox c a).filter fun p ↦ integerPoint p ∈ S) := by
  classical
  set Ix := Finset.Icc ⌈c.1⌉ (⌈c.1 + a⌉ - 1)
  set Iy := Finset.Icc ⌈c.2⌉ (⌈c.2 + a⌉ - 1)
  have hbox : latticeBox c a = Ix ×ˢ Iy := rfl
  let base : ℕ → ℕ → Finset (ℤ × ℤ) := fun k l ↦
    (latticeBox c a).filter fun p ↦ rank X (p.1 : ℝ) = k ∧ rank Y (p.2 : ℝ) = l
  let cls : ℕ → ℕ → Finset (ℤ × ℤ) := fun k l ↦
    (base k l).filter fun p ↦ integerPoint p ∈ S
  have hconv (I : Finset ℤ) (hI : ∀ a ∈ I, ∀ b ∈ I, ∀ c, a ≤ c → c ≤ b → c ∈ I)
      (Z : Finset ℝ) (k : ℕ) :
      ∃ lo hi, I.filter (fun n : ℤ ↦ rank Z (n : ℝ) = k) = Finset.Icc lo hi := by
    apply exists_eq_Icc_of_ordConnected
    intro x hx y hy z hxz hzy
    rw [Finset.mem_filter] at hx hy ⊢
    refine ⟨hI x hx.1 y hy.1 z hxz hzy, le_antisymm ?_ ?_⟩
    · exact hy.2 ▸ rank_mono Z (by exact_mod_cast hzy)
    · exact hx.2 ▸ rank_mono Z (by exact_mod_cast hxz)
  have hIcc (lo hi : ℤ) : ∀ a ∈ Finset.Icc lo hi, ∀ b ∈ Finset.Icc lo hi, ∀ c,
      a ≤ c → c ≤ b → c ∈ Finset.Icc lo hi := by
    intro a ha b hb c hac hcb
    rw [Finset.mem_Icc] at ha hb ⊢
    exact ⟨ha.1.trans hac, hcb.trans hb.2⟩
  have hrect (k l : ℕ) : IsLatticeRect (cls k l) := by
    by_cases hne : ∃ p ∈ base k l, integerPoint p ∈ S
    · obtain ⟨p, hp, hpS⟩ := hne
      have hall : cls k l = base k l := by
        apply Finset.filter_true_of_mem
        intro q hq
        rw [Finset.mem_filter] at hp hq
        refine hS p hp.1 q hq.1 ⟨?_, ?_⟩ hpS
        · exact sameSide_of_rank_eq (hp.2.1.trans hq.2.1.symm)
        · exact sameSide_of_rank_eq (hp.2.2.trans hq.2.2.symm)
      have hprod : base k l = Ix.filter (fun n : ℤ ↦ rank X (n : ℝ) = k) ×ˢ
          Iy.filter (fun n : ℤ ↦ rank Y (n : ℝ) = l) := by
        ext p
        simp only [base, hbox, Finset.mem_filter, Finset.mem_product]
        tauto
      obtain ⟨a₁, b₁, h₁⟩ := hconv Ix (hIcc _ _) X k
      obtain ⟨a₂, b₂, h₂⟩ := hconv Iy (hIcc _ _) Y l
      exact ⟨a₁, b₁, a₂, b₂, by rw [hall, hprod, h₁, h₂]⟩
    · push Not at hne
      have : cls k l = ∅ := Finset.filter_false_of_mem hne
      rw [this]
      exact isLatticeRect_empty
  refine ⟨_, le_rfl, fun i ↦ cls (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2,
    fun i ↦ hrect _ _, ?_⟩
  ext p
  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, cls, base]
  constructor
  · rintro ⟨hp, hpS⟩
    refine ⟨finProdFinEquiv (⟨rank X (p.1 : ℝ), Nat.lt_succ_of_le (rank_le_card _ _)⟩,
      ⟨rank Y (p.2 : ℝ), Nat.lt_succ_of_le (rank_le_card _ _)⟩), ?_⟩
    simp [hp, hpS]
  · rintro ⟨i, ⟨hp, -⟩, hpS⟩
    exact ⟨hp, hpS⟩

end TNLean.PEPS.Approximation.CellPartition
