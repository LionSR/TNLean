/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.BirthSeparationReplacement
import TNLean.PEPS.AreaLaw.Geometry.FanRegularity

/-!
# Elementary triangles of the normalized belt arrangement

Normalize a belt cell of side `u` to `[0, 4]²`, so that lengths are measured in
units of `u / 4`. The cells of the same and adjacent layers then have sides
`2`, `4` or `8` and corners in `(2ℤ)²`, and every edge of a cell, of a fan
triangle or of a closed square lies on one of the lines

`x₁ = m`, `x₂ = m`, `x₁ + x₂ = 2m`, `x₁ - x₂ = 2m`, `m ∈ ℤ`.

Any two of these lines that are not parallel meet in an integer point. The
faces of this arrangement are the *atoms*: the eight elementary triangles of
each square of side two centred at a point with odd coordinates. This file
collects the finitely many local facts about atoms used in the compactness step
of the birth-separation lemma:

* atoms are compact, convex, and quarter-sectorial at integer points;
* the interior of an atom meets none of the lines above, so a closed convex
  set whose frontier lies on these lines contains every atom whose interior
  it meets, and contains with each point an atom through that point;
* two atoms with a common point that is not an integer point share a
  nondegenerate segment;
* an atom through an integer point with coordinates of opposite parity
  contains a horizontal and a vertical unit segment from that point;
* there is one `η > 0` such that two points of atoms meeting only in integer
  points are at distance at least `η`, or both lie within `1/4` of a common
  point `q` of the two atoms and satisfy the angular estimate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:birth-separation`, lines 573–659,
especially the belt case of the finite local patterns, lines 597–604, and
the compactness and contact estimates, lines 606–645; the quarter mesh and
the four slopes are from `geometry:initial-stars`, lines 352–359.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

open Filter Topology

namespace TNLean.PEPS.AreaLaw.Geometry

/-! ### Lines of the normalized belt arrangement -/

/-- A point on a line of the normalized belt arrangement: a vertical or
horizontal line at an integer level, or a diagonal line at an even level.
Source: area-law Section 11, `geometry:initial-stars`, lines 352–359. -/
def IsBeltArrangementPoint (p : ℝ × ℝ) : Prop :=
  (∃ m : ℤ, p.1 = m) ∨ (∃ m : ℤ, p.2 = m) ∨ (∃ m : ℤ, p.1 + p.2 = 2 * m) ∨
    ∃ m : ℤ, p.1 - p.2 = 2 * m

/-- A facet `a x₁ + b x₂ ≤ n` of the normalized belt arrangement: an axis
normal at any integer level, or a diagonal normal at an even level.
Source: area-law Section 11, `geometry:initial-stars`, lines 352–359. -/
def IsBeltFacet (f : ℤ × ℤ × ℤ) : Prop :=
  ((f.1 = 1 ∨ f.1 = -1) ∧ f.2.1 = 0) ∨ (f.1 = 0 ∧ (f.2.1 = 1 ∨ f.2.1 = -1)) ∨
    ((f.1 = 1 ∨ f.1 = -1) ∧ (f.2.1 = 1 ∨ f.2.1 = -1) ∧ Even f.2.2)

private theorem isBeltFacet_det_dvd {f g : ℤ × ℤ × ℤ} (hf : IsBeltFacet f)
    (hg : IsBeltFacet g) (hdet : f.1 * g.2.1 - g.1 * f.2.1 ≠ 0) :
    (f.1 * g.2.1 - g.1 * f.2.1) ∣ (f.2.2 * g.2.1 - g.2.2 * f.2.1) ∧
      (f.1 * g.2.1 - g.1 * f.2.1) ∣ (f.1 * g.2.2 - g.1 * f.2.2) := by
  obtain ⟨a, b, n⟩ := f
  obtain ⟨a', b', n'⟩ := g
  simp only [IsBeltFacet] at hf hg hdet ⊢
  rcases hf with ⟨ha | ha, hb⟩ | ⟨ha, hb | hb⟩ | ⟨ha | ha, hb | hb, r, hr⟩ <;>
    rcases hg with ⟨ha' | ha', hb'⟩ | ⟨ha', hb' | hb'⟩ | ⟨ha' | ha', hb' | hb', r', hr'⟩ <;>
    subst_vars <;> (try norm_num at hdet ⊢) <;> omega

/-- Two lines of the normalized belt arrangement that are not parallel meet in
an integer point.
Source: area-law Section 11, `geometry:initial-stars`, lines 352–359. -/
theorem exists_int_eq_of_isBeltFacet {f g : ℤ × ℤ × ℤ} (hf : IsBeltFacet f)
    (hg : IsBeltFacet g) (hdet : f.1 * g.2.1 - g.1 * f.2.1 ≠ 0) {z : ℝ × ℝ}
    (hzf : (f.1 : ℝ) * z.1 + f.2.1 * z.2 = f.2.2)
    (hzg : (g.1 : ℝ) * z.1 + g.2.1 * z.2 = g.2.2) :
    ∃ i j : ℤ, z = ((i : ℝ), (j : ℝ)) := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := isBeltFacet_det_dvd hf hg hdet
  obtain ⟨a, b, n⟩ := f
  obtain ⟨a', b', n'⟩ := g
  simp only at hdet hzf hzg hp hq
  have hD : ((a * b' - a' * b : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hdet
  have e₁ : ((a * b' - a' * b : ℤ) : ℝ) * z.1 = ((n * b' - n' * b : ℤ) : ℝ) := by
    push_cast; linear_combination (b' : ℝ) * hzf - (b : ℝ) * hzg
  have e₂ : ((a * b' - a' * b : ℤ) : ℝ) * z.2 = ((a * n' - a' * n : ℤ) : ℝ) := by
    push_cast; linear_combination (a : ℝ) * hzg - (a' : ℝ) * hzf
  refine ⟨p, q, Prod.ext (mul_left_cancel₀ hD ?_) (mul_left_cancel₀ hD ?_)⟩
  · rw [e₁, hp]; push_cast; ring
  · rw [e₂, hq]; push_cast; ring

private theorem isBeltFacet_abs {f : ℤ × ℤ × ℤ} (hf : IsBeltFacet f) :
    |f.1| + |f.2.1| ≤ 2 := by
  rcases hf with ⟨ha | ha, hb⟩ | ⟨ha, hb | hb⟩ | ⟨ha | ha, hb | hb, -⟩ <;>
    simp [ha, hb]

private theorem isBeltFacet_ne_zero {f : ℤ × ℤ × ℤ} (hf : IsBeltFacet f) :
    ((f.1 : ℝ), (f.2.1 : ℝ)) ≠ 0 := by
  intro h
  have h₁ : (f.1 : ℝ) = 0 := congrArg Prod.fst h
  have h₂ : (f.2.1 : ℝ) = 0 := congrArg Prod.snd h
  norm_cast at h₁ h₂
  rcases hf with ⟨ha | ha, hb⟩ | ⟨ha, hb | hb⟩ | ⟨ha | ha, hb | hb, -⟩ <;> omega

/-- A point in the interior of a closed half-plane with nonzero normal
satisfies its strict inequality. -/
theorem lt_of_mem_interior_intHalfPlane {a b n : ℤ} (hab : ((a : ℝ), (b : ℝ)) ≠ 0)
    {x : ℝ × ℝ} (hx : x ∈ interior (intHalfPlane a b n)) :
    (a : ℝ) * x.1 + b * x.2 < n := by
  have hpath : Tendsto (fun t : ℝ ↦ x + t • ((a : ℝ), (b : ℝ))) (𝓝[>] 0) (𝓝 x) := by
    have : Continuous (fun t : ℝ ↦ x + t • ((a : ℝ), (b : ℝ))) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨t, ht, htpos⟩ := ((hpath.eventually (mem_interior_iff_mem_nhds.mp hx)).and
    self_mem_nhdsWithin).exists
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at ht
  have hpos : 0 < (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
    rcases eq_or_ne (a : ℝ) 0 with ha | ha
    · have hb : (b : ℝ) ≠ 0 := fun hb ↦ hab (by simp [ha, hb])
      positivity
    · positivity
  have htp : (0 : ℝ) < t := htpos
  nlinarith [mul_pos htp hpos]

/-! ### Atoms -/

/-- The center of the square of side two indexed by `c`, a point with odd
integer coordinates.
Source: area-law Section 11, `geometry:birth-separation`, lines 597–604. -/
def beltAtomCenter (c : ℤ × ℤ) : ℝ × ℝ :=
  (((2 * c.1 + 1 : ℤ) : ℝ), ((2 * c.2 + 1 : ℤ) : ℝ))

/-- The atom of slot `s` in the square of side two indexed by `c`: the translate
of the normalized elementary triangle of `[-1, 1]²` to the center of that square.
Source: area-law Section 11, `geometry:birth-separation`, lines 597–604. -/
def beltAtom (c : ℤ × ℤ) (s : RepairFanSlot) : Set (ℝ × ℝ) :=
  {p | p - beltAtomCenter c ∈ repairNormTriangle 1 s}

/-- The three facets of an atom, with levels shifted to its center. -/
def beltAtomFacet (c : ℤ × ℤ) (s : RepairFanSlot) : Fin 3 → ℤ × ℤ × ℤ
  | 0 => ((repairSlotFacets s).1.1, (repairSlotFacets s).1.2,
      1 + (repairSlotFacets s).1.1 * (2 * c.1 + 1) + (repairSlotFacets s).1.2 * (2 * c.2 + 1))
  | 1 => ((repairSlotFacets s).2.1.1, (repairSlotFacets s).2.1.2,
      (repairSlotFacets s).2.1.1 * (2 * c.1 + 1) + (repairSlotFacets s).2.1.2 * (2 * c.2 + 1))
  | 2 => ((repairSlotFacets s).2.2.1, (repairSlotFacets s).2.2.2,
      (repairSlotFacets s).2.2.1 * (2 * c.1 + 1) + (repairSlotFacets s).2.2.2 * (2 * c.2 + 1))

private theorem sub_center_mem_intHalfPlane_iff (c : ℤ × ℤ) (a b n : ℤ) (p : ℝ × ℝ) :
    p - beltAtomCenter c ∈ intHalfPlane a b n ↔
      p ∈ intHalfPlane a b (n + a * (2 * c.1 + 1) + b * (2 * c.2 + 1)) := by
  simp only [intHalfPlane, Set.mem_ofPred_eq, beltAtomCenter, Prod.fst_sub, Prod.snd_sub]
  push_cast
  constructor <;> intro h <;> linarith

/-- An atom is the intersection of its three shifted facets. -/
theorem beltAtom_eq_iInter (c : ℤ × ℤ) (s : RepairFanSlot) :
    beltAtom c s = ⋂ i, intHalfPlane (beltAtomFacet c s i).1 (beltAtomFacet c s i).2.1
      (beltAtomFacet c s i).2.2 := by
  ext p
  simp only [beltAtom, repairNormTriangle, Set.mem_ofPred_eq, Set.mem_inter_iff,
    Set.mem_iInter, sub_center_mem_intHalfPlane_iff]
  constructor
  · rintro ⟨⟨h₀, h₁⟩, h₂⟩ i
    fin_cases i
    · simpa [beltAtomFacet] using h₀
    · simpa [beltAtomFacet] using h₁
    · simpa [beltAtomFacet] using h₂
  · intro h
    exact ⟨⟨by simpa [beltAtomFacet] using h 0, by simpa [beltAtomFacet] using h 1⟩,
      by simpa [beltAtomFacet] using h 2⟩

/-- The facets of an atom are facets of the normalized belt arrangement. -/
theorem isBeltFacet_beltAtomFacet (c : ℤ × ℤ) (s : RepairFanSlot) (i : Fin 3) :
    IsBeltFacet (beltAtomFacet c s i) := by
  rcases s with ⟨k, j⟩
  fin_cases k <;> fin_cases j <;> fin_cases i <;>
    simp [beltAtomFacet, repairSlotFacets, IsBeltFacet] <;>
    first
    | (refine ⟨-(c.1 + c.2 + 1), ?_⟩; omega)
    | (refine ⟨c.1 + c.2 + 1, ?_⟩; omega)
    | (refine ⟨c.1 - c.2, ?_⟩; omega)
    | (refine ⟨c.2 - c.1, ?_⟩; omega)

theorem isClosed_beltAtom (c : ℤ × ℤ) (s : RepairFanSlot) : IsClosed (beltAtom c s) := by
  rw [beltAtom_eq_iInter]; exact isClosed_iInter fun _ ↦ isClosed_intHalfPlane _ _ _

theorem convex_beltAtom (c : ℤ × ℤ) (s : RepairFanSlot) : Convex ℝ (beltAtom c s) := by
  rw [beltAtom_eq_iInter]; exact convex_iInter fun _ ↦ convex_intHalfPlane _ _ _

theorem norm_sub_beltAtomCenter_le {c : ℤ × ℤ} {s : RepairFanSlot} {p : ℝ × ℝ}
    (hp : p ∈ beltAtom c s) : ‖p - beltAtomCenter c‖ ≤ 1 := by
  simpa using norm_le_of_mem_repairNormTriangle hp

theorem isCompact_beltAtom (c : ℤ × ℤ) (s : RepairFanSlot) : IsCompact (beltAtom c s) :=
  (isCompact_closedBall (beltAtomCenter c) 1).of_isClosed_subset (isClosed_beltAtom c s)
    fun _ hp ↦ by
      rw [Metric.mem_closedBall, dist_eq_norm]; exact norm_sub_beltAtomCenter_le hp

/-- Atoms are quarter-sectorial at every integer point.
Source: area-law Section 11, `geometry:angular-gap`, lines 627–645. -/
theorem isQuarterSectorial_beltAtom (c : ℤ × ℤ) (s : RepairFanSlot) (i j : ℤ) :
    IsQuarterSectorial ((i : ℝ), (j : ℝ)) (beltAtom c s) := by
  rw [beltAtom_eq_iInter]
  exact .iInter fun k ↦ isQuarterSectorial_intHalfPlane
    (isBeltFacet_abs (isBeltFacet_beltAtomFacet c s k)) i j

private theorem beltAtom_eq_preimage (c : ℤ × ℤ) (s : RepairFanSlot) :
    beltAtom c s = (Homeomorph.subRight (beltAtomCenter c)) ⁻¹' repairNormTriangle 1 s :=
  rfl

/-- Atoms have nonempty interior. -/
theorem interior_beltAtom_nonempty (c : ℤ × ℤ) (s : RepairFanSlot) :
    (interior (beltAtom c s)).Nonempty := by
  obtain ⟨x, hx⟩ := (cellFanPolygon_interior_nonempty_and_closure_eq (-1, -1) 1 (0, 0)
    repairFanSplit s).1
  have hx' := interior_mono (cellFanPolygon_region_subset_repairNormTriangle s) hx
  refine ⟨x + beltAtomCenter c, ?_⟩
  rw [beltAtom_eq_preimage, ← Homeomorph.preimage_interior]
  simpa using hx'

theorem closure_interior_beltAtom (c : ℤ × ℤ) (s : RepairFanSlot) :
    closure (interior (beltAtom c s)) = beltAtom c s := by
  rw [Convex.closure_interior_eq_closure_of_nonempty_interior (convex_beltAtom c s)
    (interior_beltAtom_nonempty c s), (isClosed_beltAtom c s).closure_eq]

private theorem no_int_between_zero_one (m : ℤ) (h₁ : (0 : ℝ) < m) (h₂ : (m : ℝ) < 1) :
    False := by
  have a₁ : 0 < m := by exact_mod_cast h₁
  have a₂ : m < 1 := by exact_mod_cast h₂
  omega

private theorem no_int_between_neg_one_zero (m : ℤ) (h₁ : (-1 : ℝ) < m) (h₂ : (m : ℝ) < 0) :
    False := by
  have a₁ : -1 < m := by exact_mod_cast h₁
  have a₂ : m < 0 := by exact_mod_cast h₂
  omega

private theorem interior_repairNormTriangle_avoid {s : RepairFanSlot} {x : ℝ × ℝ}
    (hx : x ∈ interior (repairNormTriangle 1 s)) :
    (∀ m : ℤ, x.1 ≠ m) ∧ (∀ m : ℤ, x.2 ≠ m) ∧ (∀ m : ℤ, x.1 + x.2 ≠ 2 * m) ∧
      ∀ m : ℤ, x.1 - x.2 ≠ 2 * m := by
  rw [repairNormTriangle, interior_inter, interior_inter] at hx
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hx
  have hne (s : RepairFanSlot) (k : Fin 3) :
      (((beltAtomFacet 0 s k).1 : ℝ), ((beltAtomFacet 0 s k).2.1 : ℝ)) ≠ 0 :=
    isBeltFacet_ne_zero (isBeltFacet_beltAtomFacet 0 s k)
  have g₁ := lt_of_mem_interior_intHalfPlane (hne s 0) h₁
  have g₂ := lt_of_mem_interior_intHalfPlane (hne s 1) h₂
  have g₃ := lt_of_mem_interior_intHalfPlane (hne s 2) h₃
  obtain ⟨x₁, x₂⟩ := x
  rcases s with ⟨k, j⟩
  fin_cases k <;> fin_cases j <;> simp [beltAtomFacet, repairSlotFacets] at g₁ g₂ g₃ <;>
    refine ⟨fun m hm ↦ ?_, fun m hm ↦ ?_, fun m hm ↦ ?_, fun m hm ↦ ?_⟩ <;>
    simp only at hm <;>
    first
    | exact no_int_between_zero_one m (by linarith) (by linarith)
    | exact no_int_between_neg_one_zero m (by linarith) (by linarith)

/-- The interior of an atom meets no line of the normalized belt arrangement. -/
theorem not_isBeltArrangementPoint_of_mem_interior {c : ℤ × ℤ} {s : RepairFanSlot}
    {p : ℝ × ℝ} (hp : p ∈ interior (beltAtom c s)) : ¬ IsBeltArrangementPoint p := by
  rw [beltAtom_eq_preimage, ← Homeomorph.preimage_interior] at hp
  obtain ⟨a₁, a₂, a₃, a₄⟩ := interior_repairNormTriangle_avoid hp
  simp only [Homeomorph.subRight_apply, beltAtomCenter, Prod.fst_sub, Prod.snd_sub] at a₁ a₂ a₃ a₄
  rintro (⟨m, hm⟩ | ⟨m, hm⟩ | ⟨m, hm⟩ | ⟨m, hm⟩)
  · exact a₁ (m - (2 * c.1 + 1)) (by push_cast at hm ⊢; linarith)
  · exact a₂ (m - (2 * c.2 + 1)) (by push_cast at hm ⊢; linarith)
  · exact a₃ (m - (c.1 + c.2 + 1)) (by push_cast at hm ⊢; linarith)
  · exact a₄ (m - (c.1 - c.2)) (by push_cast at hm ⊢; linarith)

/-- The atoms of one square cover its closed square.
Source: area-law Section 11, lines 404–417. -/
theorem exists_mem_beltAtom_of_norm_le {c : ℤ × ℤ} {p : ℝ × ℝ}
    (hp : ‖p - beltAtomCenter c‖ ≤ 1) : ∃ s, p ∈ beltAtom c s := by
  have hcover := cellFanPolygons_cover (-1, -1) 1 (0, 0) repairFanSplit
  rw [closure_dyadicCell] at hcover
  have hmem : p - beltAtomCenter c ∈ Set.Icc ((-1, -1).1 + (2 : ℝ) ^ 1 * ((0, 0) : ℤ × ℤ).1)
      ((-1, -1).1 + (2 : ℝ) ^ 1 * (((0, 0) : ℤ × ℤ).1 + 1)) ×ˢ
      Set.Icc ((-1, -1).2 + (2 : ℝ) ^ 1 * ((0, 0) : ℤ × ℤ).2)
        ((-1, -1).2 + (2 : ℝ) ^ 1 * (((0, 0) : ℤ × ℤ).2 + 1)) := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff, abs_le, abs_le] at hp
    simp only [Prod.fst_sub, Prod.snd_sub] at hp
    simp only [Set.mem_prod, Set.mem_Icc, Prod.fst_sub, Prod.snd_sub]
    norm_num
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  rw [← hcover] at hmem
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hmem
  exact ⟨s, cellFanPolygon_region_subset_repairNormTriangle s hs⟩

/-- Membership in a translated square: translating by an even vector moves an
atom to the atom of the translated square. -/
theorem mem_beltAtom_add_iff (c e : ℤ × ℤ) (s : RepairFanSlot) (p : ℝ × ℝ) :
    p ∈ beltAtom (c + e) s ↔
      p - (((2 * e.1 : ℤ) : ℝ), ((2 * e.2 : ℤ) : ℝ)) ∈ beltAtom c s := by
  simp only [beltAtom, Set.mem_ofPred_eq]
  have : p - beltAtomCenter (c + e) =
      p - (((2 * e.1 : ℤ) : ℝ), ((2 * e.2 : ℤ) : ℝ)) - beltAtomCenter c := by
    ext <;> simp [beltAtomCenter] <;> ring
  rw [this]

/-! ### Atoms along a ray -/

/-- A ray issuing from a point of a finite union of closed convex sets that
covers an initial piece of the ray stays, for a short time, in one of them. -/
theorem exists_mem_of_finite_cover_ray {ι : Type*} [Finite ι] (S : ι → Set (ℝ × ℝ))
    (hS : ∀ i, IsClosed (S i)) (hconv : ∀ i, Convex ℝ (S i)) (q d : ℝ × ℝ) {τ₀ : ℝ}
    (hτ₀ : 0 < τ₀) (hcov : ∀ t ∈ Set.Icc 0 τ₀, q + t • d ∈ ⋃ i, S i) :
    ∃ i, ∃ τ : ℝ, 0 < τ ∧ ∀ t ∈ Set.Icc 0 τ, q + t • d ∈ S i := by
  have hcont : Continuous (fun t : ℝ ↦ q + t • d) := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, q ∉ S i → q + t • d ∉ S i := by
    rw [eventually_all]
    intro i
    by_cases hq : q ∈ S i
    · exact Eventually.of_forall fun _ h ↦ (h hq).elim
    · have hopen : IsOpen ((fun t : ℝ ↦ q + t • d) ⁻¹' (S i)ᶜ) :=
        (hS i).isOpen_compl.preimage hcont
      filter_upwards [hopen.mem_nhds (by simpa using hq)] with t ht _
      exact ht
  obtain ⟨t, ht, htpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (Ioo_mem_nhdsGT hτ₀ : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo 0 τ₀)).exists
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov t ⟨htpos.1.le, htpos.2.le⟩)
  have hq : q ∈ S i := by
    by_contra hq
    exact ht i hq hi
  refine ⟨i, t, htpos.1, fun t' ht' ↦ ?_⟩
  have hseg := (hconv i).segment_subset hq hi
  apply hseg
  refine ⟨1 - t' / t, t' / t, ?_, div_nonneg ht'.1 htpos.1.le, by ring, ?_⟩
  · rw [sub_nonneg, div_le_one htpos.1]; exact ht'.2
  · rw [smul_add, smul_smul, ← add_assoc, ← add_smul, div_mul_cancel₀ _ htpos.1.ne']
    simp

private theorem exists_odd_center_ray (a e : ℝ) :
    ∃ m : ℤ, ∃ τ : ℝ, 0 < τ ∧ ∀ t ∈ Set.Icc (0 : ℝ) τ, |a + t * e - ((2 * m + 1 : ℤ) : ℝ)| ≤ 1 := by
  rcases le_or_gt 0 e with he | he
  · refine ⟨⌊a / 2⌋, (2 * ⌊a / 2⌋ + 2 - a) / (e + 1), ?_, fun t ht ↦ ?_⟩
    · have h := Int.lt_floor_add_one (a / 2)
      apply div_pos <;> linarith
    · have h₁ := Int.floor_le (a / 2)
      have h₂ := Int.lt_floor_add_one (a / 2)
      have hτ : (2 * ⌊a / 2⌋ + 2 - a) / (e + 1) * (e + 1) = 2 * ⌊a / 2⌋ + 2 - a :=
        div_mul_cancel₀ _ (by linarith)
      have hte : t * e ≤ (2 * ⌊a / 2⌋ + 2 - a) / (e + 1) * (e + 1) := by
        have := mul_le_mul ht.2 (le_add_of_nonneg_right zero_le_one : e ≤ e + 1) he
          (ht.1.trans ht.2)
        linarith
      rw [abs_le]; push_cast
      constructor <;> nlinarith [mul_nonneg ht.1 he]
  · refine ⟨⌈a / 2⌉ - 1, (a - 2 * (⌈a / 2⌉ - 1)) / (-e + 1), ?_, fun t ht ↦ ?_⟩
    · have h := Int.ceil_lt_add_one (a / 2)
      apply div_pos <;> linarith
    · have h₁ := Int.le_ceil (a / 2)
      have h₂ := Int.ceil_lt_add_one (a / 2)
      have hτ : (a - 2 * (⌈a / 2⌉ - 1)) / (-e + 1) * (-e + 1) = a - 2 * (⌈a / 2⌉ - 1) :=
        div_mul_cancel₀ _ (by linarith)
      have hte : t * (-e) ≤ (a - 2 * (⌈a / 2⌉ - 1)) / (-e + 1) * (-e + 1) := by
        have := mul_le_mul ht.2 (by linarith : -e ≤ -e + 1) (by linarith) (ht.1.trans ht.2)
        linarith
      rw [abs_le]; push_cast
      constructor <;> nlinarith [mul_nonneg ht.1 (by linarith : (0 : ℝ) ≤ -e)]

/-- A ray issuing from any point stays, for a short time, in one atom.
Source: area-law Section 11, `geometry:birth-separation`, lines 597–604. -/
theorem exists_beltAtom_ray (q d : ℝ × ℝ) :
    ∃ c s, ∃ τ : ℝ, 0 < τ ∧ ∀ t ∈ Set.Icc 0 τ, q + t • d ∈ beltAtom c s := by
  obtain ⟨m₁, τ₁, hτ₁, h₁⟩ := exists_odd_center_ray q.1 d.1
  obtain ⟨m₂, τ₂, hτ₂, h₂⟩ := exists_odd_center_ray q.2 d.2
  have hcov : ∀ t ∈ Set.Icc 0 (min τ₁ τ₂), q + t • d ∈ ⋃ s, beltAtom (m₁, m₂) s := by
    intro t ht
    obtain ⟨s, hs⟩ := exists_mem_beltAtom_of_norm_le (c := (m₁, m₂)) (p := q + t • d) (by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff]
      exact ⟨by simpa [beltAtomCenter] using h₁ t ⟨ht.1, ht.2.trans (min_le_left _ _)⟩,
        by simpa [beltAtomCenter] using h₂ t ⟨ht.1, ht.2.trans (min_le_right _ _)⟩⟩)
    exact Set.mem_iUnion.mpr ⟨s, hs⟩
  obtain ⟨s, τ, hτ, h⟩ := exists_mem_of_finite_cover_ray (beltAtom (m₁, m₂))
    (isClosed_beltAtom _) (convex_beltAtom _) q d (lt_min hτ₁ hτ₂) hcov
  exact ⟨(m₁, m₂), s, τ, hτ, h⟩

/-! ### Atoms in sets bounded by the arrangement -/

/-- **Atoms in a set bounded by the arrangement.** Let `P` be closed and convex
with nonempty interior, and let every frontier point of `P` lie on a line of
the normalized belt arrangement. Then every point of `P` lies in an atom
contained in `P`.
Source: area-law Section 11, `geometry:birth-separation`, lines 597–604. -/
theorem exists_beltAtom_subset {P : Set (ℝ × ℝ)} (hP : IsClosed P) (hconv : Convex ℝ P)
    (hint : (interior P).Nonempty) (hfr : ∀ p ∈ frontier P, IsBeltArrangementPoint p)
    {q : ℝ × ℝ} (hq : q ∈ P) : ∃ c s, q ∈ beltAtom c s ∧ beltAtom c s ⊆ P := by
  obtain ⟨c₀, hc₀⟩ := hint
  obtain ⟨c, s, τ, hτ, hray⟩ := exists_beltAtom_ray q (c₀ - q)
  refine ⟨c, s, by simpa using hray 0 ⟨le_rfl, hτ.le⟩, ?_⟩
  set t := min τ (1 / 2)
  have ht : 0 < t := lt_min hτ (by norm_num)
  have ht1 : t < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hmem : q + t • (c₀ - q) ∈ interior P := by
    have h := hconv.openSegment_closure_interior_subset_interior
      (subset_closure hq : q ∈ closure P) hc₀
    apply h
    refine ⟨1 - t, t, by linarith, ht, by ring, ?_⟩
    rw [smul_sub, sub_smul, one_smul]; abel
  have hA : q + t • (c₀ - q) ∈ beltAtom c s := hray t ⟨ht.le, min_le_left _ _⟩
  have hnon : (interior (beltAtom c s) ∩ interior P).Nonempty := by
    rw [← closure_inter_open_nonempty_iff isOpen_interior, closure_interior_beltAtom]
    exact ⟨_, hA, hmem⟩
  have hsub : interior (beltAtom c s) ⊆ interior P := by
    refine (convex_beltAtom c s).interior.isPreconnected.subset_left_of_subset_union
      isOpen_interior hP.isOpen_compl ?_ ?_ hnon
    · exact Set.disjoint_left.mpr fun x hx hx' ↦ hx' (interior_subset hx)
    · intro x hx
      by_cases hxi : x ∈ interior P
      · exact Or.inl hxi
      by_cases hxP : x ∈ P
      · exact (not_isBeltArrangementPoint_of_mem_interior hx
          (hfr x ⟨subset_closure hxP, hxi⟩)).elim
      · exact Or.inr hxP
  calc beltAtom c s = closure (interior (beltAtom c s)) := (closure_interior_beltAtom c s).symm
    _ ⊆ closure (interior P) := closure_mono hsub
    _ ⊆ P := closure_minimal interior_subset hP

end TNLean.PEPS.AreaLaw.Geometry
