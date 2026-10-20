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

Any two of these lines that are not parallel meet in an integer point
(`exists_int_eq_of_isBeltFacet`). The
faces of this arrangement are the *atoms*: the eight elementary triangles of
each square of side two centred at a point with odd coordinates. This file
collects the finitely many local facts about atoms used in the separation step
of the birth-separation lemma:

* atoms are compact, convex, and quarter-sectorial at integer points;
* the interior of an atom meets none of the lines above, so a closed convex
  set whose frontier lies on these lines contains every atom whose interior
  it meets, and contains with each point an atom through that point;
* two atoms with a common point that is not an integer point share a
  nondegenerate segment;
* an atom through an integer point with coordinates of opposite parity
  contains a horizontal and a vertical unit segment from that point;
* two points of atoms meeting only in integer points are at distance at least
  `birthSeparationConstant = 1/28`, or both lie within `1/4` of a common point
  `q` of the two atoms and satisfy the angular estimate. The atoms are cut out
  by belt facets, so this explicit constant can be used instead of the
  compactness minimum.

The manuscript's contact dichotomy for two compact sets that are
quarter-sectorial at integer points and meet only there
(`exists_pos_common_contact_dichotomy`) is proved by compactness and gives a
positive `η` without a value. The explicit separation constant
`birthSeparationConstant = 1/28` gives a quantitative version for atoms; the
birth-separation estimate and the explicit area-law constant use that version.

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

/-- The three facets of an atom, with levels shifted to its center.
Source: area-law Section 11, `geometry:birth-separation`, lines 597–604. -/
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
    simp [beltAtomFacet, repairSlotFacets, IsBeltFacet, parity_simps, Int.odd_mul]

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

/-! ### Common points of atoms -/

/-- At a point of a finite intersection of arrangement half-planes that is not
an integer point, the intersection contains a nondegenerate segment through
that point: all facets tight at the point lie on one line.
Source: area-law Section 11, `geometry:birth-separation`, lines 597–625. -/
theorem exists_segment_subset_iInter_intHalfPlane {ι : Type*} [Finite ι]
    (F : ι → ℤ × ℤ × ℤ) (hF : ∀ i, IsBeltFacet (F i)) {z : ℝ × ℝ}
    (hz : ∀ i, z ∈ intHalfPlane (F i).1 (F i).2.1 (F i).2.2)
    (hzZ : ∀ i j : ℤ, z ≠ ((i : ℝ), (j : ℝ))) :
    ∃ a b : ℝ × ℝ, a ≠ b ∧
      segment ℝ a b ⊆ ⋂ i, intHalfPlane (F i).1 (F i).2.1 (F i).2.2 := by
  obtain ⟨d, hd0, hd⟩ : ∃ d : ℝ × ℝ, d ≠ 0 ∧ ∀ i,
      ((F i).1 : ℝ) * z.1 + (F i).2.1 * z.2 = (F i).2.2 →
        ((F i).1 : ℝ) * d.1 + (F i).2.1 * d.2 = 0 := by
    by_cases hT : ∃ i₀, ((F i₀).1 : ℝ) * z.1 + (F i₀).2.1 * z.2 = (F i₀).2.2
    · obtain ⟨i₀, hi₀⟩ := hT
      refine ⟨(-((F i₀).2.1 : ℝ), ((F i₀).1 : ℝ)), ?_, fun i hi ↦ ?_⟩
      · intro h
        apply isBeltFacet_ne_zero (hF i₀)
        have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        simp only [Prod.fst_zero, Prod.snd_zero, neg_eq_zero] at h₁ h₂
        simp [h₁, h₂]
      · by_contra hne
        have hdet : (F i).1 * (F i₀).2.1 - (F i₀).1 * (F i).2.1 ≠ 0 := by
          intro h0
          apply hne
          have h0' : (((F i).1 * (F i₀).2.1 - (F i₀).1 * (F i).2.1 : ℤ) : ℝ) = 0 := by
            exact_mod_cast h0
          push_cast at h0'
          linarith
        obtain ⟨p, q, hpq⟩ := exists_int_eq_of_isBeltFacet (hF i) (hF i₀) hdet hi hi₀
        exact hzZ p q hpq
    · push Not at hT
      exact ⟨(1, 0), by simp, fun i hi ↦ (hT i hi).elim⟩
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, z + t • d ∈ intHalfPlane (F i).1 (F i).2.1 (F i).2.2 := by
    rw [eventually_all]
    intro i
    by_cases hti : ((F i).1 : ℝ) * z.1 + (F i).2.1 * z.2 = (F i).2.2
    · refine Eventually.of_forall fun t ↦ ?_
      simp only [intHalfPlane, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]
      have h := hd i hti
      have : ((F i).1 : ℝ) * (z.1 + t * d.1) + (F i).2.1 * (z.2 + t * d.2) =
          (((F i).1 : ℝ) * z.1 + (F i).2.1 * z.2) +
            t * (((F i).1 : ℝ) * d.1 + (F i).2.1 * d.2) := by
        ring
      rw [this, hti, h, mul_zero, add_zero]
    · have hlt : ((F i).1 : ℝ) * z.1 + (F i).2.1 * z.2 < (F i).2.2 := lt_of_le_of_ne (hz i) hti
      have hcont : Continuous (fun t : ℝ ↦
          ((F i).1 : ℝ) * (z + t • d).1 + (F i).2.1 * (z + t • d).2) := by fun_prop
      have hlim := (hcont.tendsto 0).eventually (gt_mem_nhds (by simpa using hlt))
      filter_upwards [hlim] with t ht
      exact ht.le
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hmem (t : ℝ) (ht : |t| < ε) :
      z + t • d ∈ ⋂ i, intHalfPlane (F i).1 (F i).2.1 (F i).2.2 :=
    Set.mem_iInter.mpr (hball (by simpa [Real.dist_eq] using ht))
  refine ⟨z + (-(ε / 2)) • d, z + (ε / 2) • d, ?_, ?_⟩
  · intro h
    have h' : ε • d = (z + (ε / 2) • d) - (z + (-(ε / 2)) • d) := by module
    rw [← h, sub_self, smul_eq_zero] at h'
    rcases h' with h' | h'
    · exact hε.ne' h'
    · exact hd0 h'
  · apply (convex_iInter fun i ↦ convex_intHalfPlane _ _ _).segment_subset
    · exact hmem _ (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
    · exact hmem _ (by rw [abs_of_pos (by linarith)]; linarith)

/-- **Common points of two atoms.** Two atoms sharing a point that is not an
integer point share a nondegenerate segment.
Source: area-law Section 11, `geometry:birth-separation`, lines 597–625. -/
theorem exists_segment_subset_beltAtom_inter {c c' : ℤ × ℤ} {s s' : RepairFanSlot}
    {z : ℝ × ℝ} (hz : z ∈ beltAtom c s) (hz' : z ∈ beltAtom c' s')
    (hzZ : ∀ i j : ℤ, z ≠ ((i : ℝ), (j : ℝ))) :
    ∃ a b : ℝ × ℝ, a ≠ b ∧ segment ℝ a b ⊆ beltAtom c s ∩ beltAtom c' s' := by
  rw [beltAtom_eq_iInter] at hz hz'
  obtain ⟨a, b, hab, hseg⟩ := exists_segment_subset_iInter_intHalfPlane
    (Sum.elim (beltAtomFacet c s) (beltAtomFacet c' s'))
    (by rintro (i | i) <;> exact isBeltFacet_beltAtomFacet _ _ i)
    (by rintro (i | i)
        · exact Set.mem_iInter.mp hz i
        · exact Set.mem_iInter.mp hz' i) hzZ
  refine ⟨a, b, hab, fun x hx ↦ ?_⟩
  have h := Set.mem_iInter.mp (hseg hx)
  rw [beltAtom_eq_iInter, beltAtom_eq_iInter]
  exact ⟨Set.mem_iInter.mpr fun i ↦ h (Sum.inl i), Set.mem_iInter.mpr fun i ↦ h (Sum.inr i)⟩

private theorem repairNormTriangle_axis {s : RepairFanSlot} {α β : ℤ} (hodd : Odd (α + β))
    (h : ((α : ℝ), (β : ℝ)) ∈ repairNormTriangle 1 s) :
    (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ((α : ℝ) + σ, (β : ℝ)) ∈ repairNormTriangle 1 s) ∧
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ((α : ℝ), (β : ℝ) + σ) ∈ repairNormTriangle 1 s := by
  have hn := norm_le_of_mem_repairNormTriangle h
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff, abs_le, abs_le] at hn
  obtain ⟨⟨a₁, a₂⟩, b₁, b₂⟩ := hn
  simp only [Int.cast_one] at a₁ a₂ b₁ b₂
  have ha₁ : -1 ≤ α := by exact_mod_cast a₁
  have ha₂ : α ≤ 1 := by exact_mod_cast a₂
  have hb₁ : -1 ≤ β := by exact_mod_cast b₁
  have hb₂ : β ≤ 1 := by exact_mod_cast b₂
  obtain ⟨r, hr⟩ := hodd
  have hα : α = -1 ∨ α = 0 ∨ α = 1 := by omega
  have hβ : β = -1 ∨ β = 0 ∨ β = 1 := by omega
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
  rcases s with ⟨k, l⟩
  have hh := And.intro h₁ (And.intro h₂ h₃)
  clear h₁ h₂ h₃
  simp only [intHalfPlane, Set.mem_ofPred_eq] at hh
  rcases hα with rfl | rfl | rfl <;> rcases hβ with rfl | rfl | rfl <;>
    (try (exfalso; omega)) <;>
    fin_cases k <;> fin_cases l
  all_goals norm_num [repairSlotFacets] at hh
  all_goals simp [repairNormTriangle, intHalfPlane, repairSlotFacets, or_and_right, exists_or]

/-- **Axis segments at a contact of opposite parity.** An atom through an
integer point whose coordinates have odd sum contains a horizontal and a
vertical unit segment issuing from that point.
Source: area-law Section 11, `geometry:birth-separation`, lines 597–625. -/
theorem beltAtom_axis_segments {c : ℤ × ℤ} {s : RepairFanSlot} {i j : ℤ}
    (hodd : Odd (i + j)) (hq : ((i : ℝ), (j : ℝ)) ∈ beltAtom c s) :
    (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      segment ℝ ((i : ℝ), (j : ℝ)) ((i : ℝ) + σ, (j : ℝ)) ⊆ beltAtom c s) ∧
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      segment ℝ ((i : ℝ), (j : ℝ)) ((i : ℝ), (j : ℝ) + σ) ⊆ beltAtom c s := by
  have key (p : ℝ × ℝ) : p ∈ beltAtom c s ↔
      (p.1 - ((2 * c.1 + 1 : ℤ) : ℝ), p.2 - ((2 * c.2 + 1 : ℤ) : ℝ)) ∈ repairNormTriangle 1 s :=
    Iff.rfl
  have hodd' : Odd ((i - (2 * c.1 + 1)) + (j - (2 * c.2 + 1))) := by
    obtain ⟨r, hr⟩ := hodd
    exact ⟨r - c.1 - c.2 - 1, by omega⟩
  have hmem : (((i - (2 * c.1 + 1) : ℤ) : ℝ), ((j - (2 * c.2 + 1) : ℤ) : ℝ)) ∈
      repairNormTriangle 1 s := by
    have h := (key _).mp hq
    push_cast at h ⊢
    exact h
  obtain ⟨⟨σ, hσ, h₁⟩, ⟨τ, hτ, h₂⟩⟩ := repairNormTriangle_axis hodd' hmem
  refine ⟨⟨σ, hσ, (convex_beltAtom c s).segment_subset hq ?_⟩,
    ⟨τ, hτ, (convex_beltAtom c s).segment_subset hq ?_⟩⟩
  · rw [key]
    push_cast at h₁ ⊢
    convert h₁ using 2
    ring
  · rw [key]
    push_cast at h₂ ⊢
    convert h₂ using 2
    ring

/-! ### The uniform dichotomy for atoms -/

/-- **Contact dichotomy at common points.** Two compact sets, quarter-sectorial at
every integer point and meeting only in integer points, have a constant `η > 0`
such that each pair of their points is at distance at least `η`, or lies in the
open quarter-square about a common point `q` of the two sets, where the angular
estimate `‖x - y‖ ≥ ‖y - q‖ / 2` holds.
Source: area-law Section 11, `geometry:birth-separation`, lines 616–645. -/
theorem exists_pos_common_contact_dichotomy {X Y : Set (ℝ × ℝ)}
    (hX : IsCompact X) (hY : IsCompact Y)
    (hXs : ∀ i j : ℤ, IsQuarterSectorial ((i : ℝ), (j : ℝ)) X)
    (hYs : ∀ i j : ℤ, IsQuarterSectorial ((i : ℝ), (j : ℝ)) Y)
    (hXY : ∀ z ∈ X, z ∈ Y → ∃ i j : ℤ, z = ((i : ℝ), (j : ℝ))) :
    ∃ η > 0, ∀ x ∈ X, ∀ y ∈ Y, η ≤ ‖x - y‖ ∨ ∃ q ∈ X ∩ Y,
      ‖x - q‖ < 1 / 4 ∧ ‖y - q‖ < 1 / 4 ∧ ‖y - q‖ / 2 ≤ ‖x - y‖ := by
  set K : Set ((ℝ × ℝ) × (ℝ × ℝ)) := (X ×ˢ Y) ∩ ⋂ q ∈ X ∩ Y,
    {p | ¬ (‖p.1 - q‖ < 1 / 4 ∧ ‖p.2 - q‖ < 1 / 4)}
  have hKc : IsCompact K := by
    refine (hX.prod hY).inter_right (isClosed_biInter fun q _ ↦ ?_)
    refine IsOpen.isClosed_compl ?_
    exact (isOpen_lt (continuous_norm.comp (continuous_fst.sub continuous_const))
      continuous_const).inter
      (isOpen_lt (continuous_norm.comp (continuous_snd.sub continuous_const)) continuous_const)
  have hnear : ∀ x ∈ X, ∀ y ∈ Y, (x, y) ∉ K → ∃ q ∈ X ∩ Y,
      ‖x - q‖ < 1 / 4 ∧ ‖y - q‖ < 1 / 4 ∧ ‖y - q‖ / 2 ≤ ‖x - y‖ := by
    intro x hx y hy hK
    have : ∃ q ∈ X ∩ Y, ‖x - q‖ < 1 / 4 ∧ ‖y - q‖ < 1 / 4 := by
      by_contra hne
      push Not at hne
      exact hK ⟨⟨hx, hy⟩, Set.mem_iInter₂.mpr fun q hq h ↦
        absurd (hne q hq h.1) (not_le.mpr h.2)⟩
    obtain ⟨q, hq, hxq, hyq⟩ := this
    refine ⟨q, hq, hxq, hyq, ?_⟩
    obtain ⟨i, j, rfl⟩ := hXY q hq.1 hq.2
    have hcontact : ∀ z ∈ X, z ∈ Y → ‖z - ((i : ℝ), (j : ℝ))‖ ≤ 1 / 4 →
        z = ((i : ℝ), (j : ℝ)) := by
      intro z hzX hzY hz
      obtain ⟨i', j', rfl⟩ := hXY z hzX hzY
      obtain ⟨rfl, rfl⟩ := eq_of_norm_sub_intPoint_le_quarter hz
      rfl
    have := half_max_le_norm_sub_of_isQuarterSectorial (hXs i j) (hYs i j) hcontact hx hy
      hxq.le hyq.le
    linarith [le_max_right ‖x - ((i : ℝ), (j : ℝ))‖ ‖y - ((i : ℝ), (j : ℝ))‖]
  rcases K.eq_empty_or_nonempty with hK | hK
  · refine ⟨1, one_pos, fun x hx y hy ↦ Or.inr (hnear x hx y hy (by rw [hK]; exact id))⟩
  obtain ⟨p, hp, hmin⟩ := hKc.exists_isMinOn hK
    (continuous_norm.comp (continuous_fst.sub continuous_snd)).continuousOn
  refine ⟨‖p.1 - p.2‖, ?_, fun x hx y hy ↦ ?_⟩
  · refine norm_pos_iff.mpr fun h0 ↦ ?_
    have he : p.1 = p.2 := sub_eq_zero.mp h0
    have := Set.mem_iInter₂.mp hp.2 p.1 ⟨hp.1.1, he ▸ hp.1.2⟩
    apply this
    rw [← he]; simp
  · by_cases hxy : (x, y) ∈ K
    · exact Or.inl (hmin hxy)
    · exact Or.inr (hnear x hx y hy hxy)

theorem beltAtom_eq_facetPolygon (c : ℤ × ℤ) (s : RepairFanSlot) :
    beltAtom c s = facetPolygon (Set.range (beltAtomFacet c s)) := by
  rw [facetPolygon_range, beltAtom_eq_iInter]

/-- **The explicit uniform dichotomy for atoms.** For any two atoms meeting only
in integer points, each pair of their points is at distance at least
`birthSeparationConstant = 1/28`, or lies in the open quarter-square about a
common point `q` of the two atoms, where `‖x - y‖ ≥ ‖y - q‖ / 2`.
Source: area-law Section 11, `geometry:birth-separation`, lines 597–645. -/
theorem beltAtom_dichotomy (c c' : ℤ × ℤ) (s s' : RepairFanSlot)
    (hV : ∀ z ∈ beltAtom c s, z ∈ beltAtom c' s' → ∃ i j : ℤ, z = ((i : ℝ), (j : ℝ))) :
    ∀ x ∈ beltAtom c s, ∀ y ∈ beltAtom c' s', birthSeparationConstant ≤ ‖x - y‖ ∨
      ∃ q ∈ beltAtom c s ∩ beltAtom c' s',
        ‖x - q‖ < 1 / 4 ∧ ‖y - q‖ < 1 / 4 ∧ ‖y - q‖ / 2 ≤ ‖x - y‖ := by
  simp only [beltAtom_eq_facetPolygon] at hV ⊢
  intro x hx y hy
  refine facetPolygon_contact_dichotomy ?_ ?_ hV hx hy <;>
    exact fun _ ⟨i, hi⟩ ↦ hi ▸ isBeltFacet_beltAtomFacet _ _ i

/-- **The uniform dichotomy for atoms.** There is one `η ∈ (0, 1]` such that,
for any two atoms meeting only in integer points, each pair of their points is
at distance at least `η`, or lies in the open quarter-square about a common
point `q` of the two atoms, where `‖x - y‖ ≥ ‖y - q‖ / 2`. One may take
`η = 1/28` (`beltAtom_dichotomy`).
Source: area-law Section 11, `geometry:birth-separation`, lines 597–645. -/
theorem exists_beltAtom_dichotomy :
    ∃ η > 0, η ≤ 1 ∧ ∀ (c c' : ℤ × ℤ) (s s' : RepairFanSlot),
      (∀ z ∈ beltAtom c s, z ∈ beltAtom c' s' → ∃ i j : ℤ, z = ((i : ℝ), (j : ℝ))) →
      ∀ x ∈ beltAtom c s, ∀ y ∈ beltAtom c' s', η ≤ ‖x - y‖ ∨
        ∃ q ∈ beltAtom c s ∩ beltAtom c' s',
          ‖x - q‖ < 1 / 4 ∧ ‖y - q‖ < 1 / 4 ∧ ‖y - q‖ / 2 ≤ ‖x - y‖ :=
  ⟨birthSeparationConstant, birthSeparationConstant_pos, birthSeparationConstant_le_one,
    beltAtom_dichotomy⟩

end TNLean.PEPS.AreaLaw.Geometry
