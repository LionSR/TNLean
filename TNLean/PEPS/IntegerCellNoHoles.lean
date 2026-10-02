/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusRegionLiftRealization
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Combinatorics.SimpleGraph.Cayley


/-!
# No finite holes in simply connected integer cell domains

A finite four-neighbor component of missing cells has an exposed oriented
square-boundary chain. Summing square curls cancels all internal edges. A
continuous angular lift on a simply connected occupied cell union makes the
boundary increments an exact potential, whereas the branch cut through a
missing cell gives total curl one. These two evaluations are incompatible.
Consequently every missing-cell component is infinite.

The final theorem applies this argument to the genuine planar image of a
simply connected torus closed-cell realization. Its local path connectedness
and its angular lift are derived from the finite cells and covering theory.

**Scope restriction (no-hole obstruction):** This is an auxiliary geometric
step in SCP10, Theorem 6.9, local source lines 1935–1990. It does not define a
disk or assert path connectedness of the exterior collar. Routing the exposed
boundary contours within that collar remains a separate theorem; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators
open Set
namespace TNLean.PEPS

private theorem sum_internal_shift (K : Finset (ℤ × ℤ)) (d : ℤ × ℤ)
    (f : ℤ × ℤ → ℝ) :
    (∑ a ∈ K, if a + d ∈ K then f (a + d) else 0) =
      ∑ a ∈ K, if a - d ∈ K then f a else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun a _ => a + d)
  · intro a ha
    obtain ⟨ha, had⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨had, by simpa using ha⟩
  · intro a ha b hb hab
    exact add_right_cancel hab
  · intro b hb
    obtain ⟨hb, hbd⟩ := Finset.mem_filter.mp hb
    exact ⟨b - d, Finset.mem_filter.mpr ⟨hbd, by simpa using hb⟩, sub_add_cancel b d⟩
  · intro a ha
    rfl

private theorem sum_difference_eq_boundary (K : Finset (ℤ × ℤ)) (d : ℤ × ℤ)
    (f : ℤ × ℤ → ℝ) :
    (∑ a ∈ K, (f a - f (a + d))) =
      (∑ a ∈ K, if a - d ∉ K then f a else 0) -
      ∑ a ∈ K, if a + d ∉ K then f (a + d) else 0 := by
  have hp (a : ℤ × ℤ) : f a =
      (if a - d ∉ K then f a else 0) + (if a - d ∈ K then f a else 0) := by
    by_cases h : a - d ∈ K <;> simp only [h, not_true_eq_false, not_false_eq_true,
      ite_true, ite_false, zero_add, add_zero]
  have hn (a : ℤ × ℤ) : f (a + d) =
      (if a + d ∉ K then f (a + d) else 0) +
        (if a + d ∈ K then f (a + d) else 0) := by
    by_cases h : a + d ∈ K <;> simp only [h, not_true_eq_false, not_false_eq_true,
      ite_true, ite_false, zero_add, add_zero]
  rw [Finset.sum_sub_distrib]
  conv_lhs => lhs; arg 2; ext a; rw [hp a]
  conv_lhs => rhs; arg 2; ext a; rw [hn a]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_internal_shift]
  ring

private abbrev east : ℤ × ℤ := (1, 0)
private abbrev north : ℤ × ℤ := (0, 1)

/-- Finite square curls sum to their exposed oriented boundary. This is the
finite cancellation used in the auxiliary block geometry for SCP10,
Theorem 6.9, lines 1935–1990. -/
theorem sum_integerGrid_curl_eq_boundary (K : Finset (ℤ × ℤ))
    (H V : ℤ × ℤ → ℝ) :
    (∑ a ∈ K, (H a + V (a + (1, 0)) - H (a + (0, 1)) - V a)) =
      (∑ a ∈ K, if a - (0, 1) ∉ K then H a else 0) +
      (∑ a ∈ K, if a + (1, 0) ∉ K then V (a + (1, 0)) else 0) -
      (∑ a ∈ K, if a + (0, 1) ∉ K then H (a + (0, 1)) else 0) -
      (∑ a ∈ K, if a - (1, 0) ∉ K then V a else 0) := by
  have hH := sum_difference_eq_boundary K north H
  have hV := sum_difference_eq_boundary K east V
  simp only [Finset.sum_sub_distrib] at hH hV
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linarith

private def vortexVertical (a : ℤ × ℤ) : ℝ :=
  if a.2 = 0 ∧ a.1 ≤ 0 then 1 else 0

private theorem vortex_curl (a : ℤ × ℤ) :
    vortexVertical (a + east) - vortexVertical a = if a = 0 then -1 else 0 := by
  obtain ⟨x, y⟩ := a
  simp only [vortexVertical, Prod.fst_add, Prod.snd_add, east]
  by_cases hy : y = 0
  · subst y
    by_cases hx : x = 0
    · subst x
      norm_num
    · have hiff : x + 1 ≤ 0 ↔ x ≤ 0 := by omega
      simp only [zero_add, true_and, hiff, sub_self]
      rw [ite_eq_right]
      intro h
      exact hx (congrArg Prod.fst h)
  · simp only [add_zero, hy, false_and, ite_false, sub_self]
    rw [ite_eq_right]
    intro h
    exact hy (congrArg Prod.snd h)

private theorem integerGridBoundary_vortex_obstruction (K : Finset (ℤ × ℤ)) (hzero : 0 ∈ K)
    (p : ℤ × ℤ → ℝ)
    (hbottom : ∀ a ∈ K, a - north ∉ K → p (a + east) - p a = 0)
    (htop : ∀ a ∈ K, a + north ∉ K →
      p (a + north + east) - p (a + north) = 0)
    (hleft : ∀ a ∈ K, a - east ∉ K → p (a + north) - p a = vortexVertical a)
    (hright : ∀ a ∈ K, a + east ∉ K →
      p (a + east + north) - p (a + east) = vortexVertical (a + east)) : False := by
  let H := fun a => p (a + east) - p a
  let V := fun a => p (a + north) - p a
  have hcurl (a : ℤ × ℤ) : H a + V (a + east) - H (a + north) - V a = 0 := by
    simp only [H, V]
    rw [show a + north + east = a + east + north by abel]
    ring
  have hp := sum_integerGrid_curl_eq_boundary K H V
  simp_rw [hcurl, Finset.sum_const_zero] at hp
  have hb := sum_integerGrid_curl_eq_boundary K (fun _ => 0) vortexVertical
  simp only [zero_add, sub_zero, ite_self, Finset.sum_const_zero] at hb
  have hsum : (∑ a ∈ K, (vortexVertical (a + east) - vortexVertical a)) = -1 := by
    simp_rw [vortex_curl]
    simp [hzero]
  rw [hsum] at hb
  have H0 (a : ℤ × ℤ) (ha : a ∈ K) :
      (if a - north ∉ K then H a else 0) = 0 := by
    by_cases hn : a - north ∉ K <;> simp only [hn, ite_false]
    exact hbottom a ha hn
  have H1 (a : ℤ × ℤ) (ha : a ∈ K) :
      (if a + north ∉ K then H (a + north) else 0) = 0 := by
    by_cases hn : a + north ∉ K <;> simp only [hn, ite_false]
    exact htop a ha hn
  have V0 (a : ℤ × ℤ) (ha : a ∈ K) :
      (if a - east ∉ K then V a else 0) =
        if a - east ∉ K then vortexVertical a else 0 := by
    by_cases he : a - east ∉ K <;> simp only [he, ite_false]
    exact hleft a ha he
  have V1 (a : ℤ × ℤ) (ha : a ∈ K) :
      (if a + east ∉ K then V (a + east) else 0) =
        if a + east ∉ K then vortexVertical (a + east) else 0 := by
    by_cases he : a + east ∉ K <;> simp only [he, ite_false]
    exact hright a ha he
  rw [Finset.sum_congr rfl H0, Finset.sum_congr rfl H1,
    Finset.sum_congr rfl V0, Finset.sum_congr rfl V1] at hp
  simp only [Finset.sum_const_zero, zero_add, sub_zero] at hp
  linarith

private theorem angleLift_difference {f g : unitInterval → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (heq : ∀ t, (f t : Real.Angle) = (g t : Real.Angle)) :
    f 1 - f 0 = g 1 - g 0 := by
  have h := (AddCircle.isCoveringMap_coe (2 * Real.pi)).eq_of_comp_eq hf
    (hg.add continuous_const) (show
      (fun t => (f t : Real.Angle)) =
        (fun t => ((g t + (f 0 - g 0) : ℝ) : Real.Angle)) by
      funext t
      simp only [Real.Angle.coe_add, Real.Angle.coe_sub, heq, sub_self, add_zero])
    (0 : unitInterval) (by simp)
  have h1 := congrFun h 1
  dsimp at h1
  linarith

private def corner (a : ℤ × ℤ) : ℝ × ℝ :=
  ((a.1 : ℝ) - 1 / 2, (a.2 : ℝ) - 1 / 2)

private def asComplex (p : ℝ × ℝ) : ℂ := p.1 + p.2 * Complex.I

open Classical in
private def angularPotential (P : Set (ℝ × ℝ)) (F : C(P, ℝ)) (a : ℤ × ℤ) : ℝ :=
  if h : corner a ∈ P then (Complex.arg (asComplex (corner a)) - F ⟨corner a, h⟩) /
    (2 * Real.pi) else 0

private theorem angularPotential_difference (P : Set (ℝ × ℝ)) (F : C(P, ℝ))
    (hF : ∀ p : P, (F p : Real.Angle) = Complex.arg (asComplex p.1))
    (a b : ℤ × ℤ) (γ : unitInterval → ℝ × ℝ) (hγ : Continuous γ)
    (ha : γ 0 = corner a) (hb : γ 1 = corner b) (hp : ∀ t, γ t ∈ P)
    (g : unitInterval → ℝ) (hg : Continuous g)
    (harg : ∀ t, (g t : Real.Angle) = Complex.arg (asComplex (γ t))) :
    angularPotential P F b - angularPotential P F a =
      (Complex.arg (asComplex (corner b)) - Complex.arg (asComplex (corner a)) -
        (g 1 - g 0)) / (2 * Real.pi) := by
  classical
  let f : unitInterval → ℝ := fun t => F ⟨γ t, hp t⟩
  have hf : Continuous f := F.continuous.comp (hγ.subtype_mk hp)
  have he := angleLift_difference hf hg (fun t => (hF ⟨γ t, hp t⟩).trans (harg t).symm)
  have hpa : corner a ∈ P := ha ▸ hp 0
  have hpb : corner b ∈ P := hb ▸ hp 1
  have hfa : f 0 = F ⟨corner a, hpa⟩ := by
    apply congrArg F
    exact Subtype.ext ha
  have hfb : f 1 = F ⟨corner b, hpb⟩ := by
    apply congrArg F
    exact Subtype.ext hb
  simp only [angularPotential, dite_eq_left hpa, dite_eq_left hpb]
  rw [hfa, hfb] at he
  rw [← he]
  ring

private def cellEdge (a d : ℤ × ℤ) (t : unitInterval) : ℝ × ℝ :=
  corner a + (t : ℝ) • ((d.1 : ℝ), (d.2 : ℝ))

private theorem continuous_cellEdge (a d : ℤ × ℤ) : Continuous (cellEdge a d) := by
  unfold cellEdge
  fun_prop

private theorem cellEdge_zero (a d : ℤ × ℤ) : cellEdge a d 0 = corner a := by
  simp [cellEdge]

private theorem cellEdge_one (a d : ℤ × ℤ) : cellEdge a d 1 = corner (a + d) := by
  apply Prod.ext <;> simp [cellEdge, corner] <;> ring

private theorem corner_im_ne_zero (a : ℤ × ℤ) : (asComplex (corner a)).im ≠ 0 := by
  simp only [asComplex, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, zero_mul, mul_one, add_zero, zero_add]
  change (a.2 : ℝ) - 1 / 2 ≠ 0
  intro h
  have : (2 : ℝ) * (a.2 : ℝ) = 1 := by linarith
  have : (2 : ℤ) * a.2 = 1 := by exact_mod_cast this
  omega

private theorem angularPotential_horizontal (P : Set (ℝ × ℝ)) (F : C(P, ℝ))
    (hF : ∀ p : P, (F p : Real.Angle) = Complex.arg (asComplex p.1))
    (a : ℤ × ℤ) (hp : ∀ t, cellEdge a east t ∈ P) :
    angularPotential P F (a + east) - angularPotential P F a = 0 := by
  let γ := cellEdge a east
  have hs t : asComplex (γ t) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simpa [γ, cellEdge, asComplex, corner, east] using corner_im_ne_zero a
  have hc : Continuous (fun t => asComplex (γ t)) := by
    unfold asComplex γ
    fun_prop
  have hg : Continuous (fun t => Complex.arg (asComplex (γ t))) :=
    Complex.continuousOn_arg.comp_continuous hc hs
  have he := angularPotential_difference P F hF a (a + east) γ
    (continuous_cellEdge a east) (cellEdge_zero a east) (cellEdge_one a east) hp
    (fun t => Complex.arg (asComplex (γ t))) hg (fun _ => rfl)
  simpa only [γ, cellEdge_one, cellEdge_zero, sub_self, zero_div] using he

private theorem angularPotential_vertical (P : Set (ℝ × ℝ)) (F : C(P, ℝ))
    (hF : ∀ p : P, (F p : Real.Angle) = Complex.arg (asComplex p.1))
    (a : ℤ × ℤ) (hp : ∀ t, cellEdge a north t ∈ P) :
    angularPotential P F (a + north) - angularPotential P F a = vortexVertical a := by
  let γ := cellEdge a north
  have hc : Continuous (fun t => asComplex (γ t)) := by
    unfold asComplex γ
    fun_prop
  by_cases hx : 0 < a.1
  · have hs t : asComplex (γ t) ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      have hr : (1 : ℝ) ≤ (a.1 : ℝ) := by exact_mod_cast (show 1 ≤ a.1 by omega)
      simp [γ, cellEdge, asComplex, corner, north]
      linarith
    have hg : Continuous (fun t => Complex.arg (asComplex (γ t))) :=
      Complex.continuousOn_arg.comp_continuous hc hs
    have he := angularPotential_difference P F hF a (a + north) γ
      (continuous_cellEdge a north) (cellEdge_zero a north) (cellEdge_one a north) hp
      (fun t => Complex.arg (asComplex (γ t))) hg (fun _ => rfl)
    simpa only [γ, cellEdge_one, cellEdge_zero, sub_self, zero_div, vortexVertical,
      show ¬a.1 ≤ 0 by omega, and_false, ite_false] using he
  · have hr : (a.1 : ℝ) ≤ 0 := by exact_mod_cast (show a.1 ≤ 0 by omega)
    have hs t : -(asComplex (γ t)) ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      simp [γ, cellEdge, asComplex, corner, north]
      linarith
    have hz t : asComplex (γ t) ≠ 0 := by
      intro he
      simpa [he] using hs t
    have hg0 : Continuous (fun t => Complex.arg (-asComplex (γ t))) :=
      Complex.continuousOn_arg.comp_continuous hc.neg hs
    have he := angularPotential_difference P F hF a (a + north) γ
      (continuous_cellEdge a north) (cellEdge_zero a north) (cellEdge_one a north) hp
      (fun t => Complex.arg (-asComplex (γ t)) - Real.pi) (hg0.sub continuous_const) (by
        intro t
        rw [Real.Angle.coe_sub, Complex.arg_neg_coe_angle (hz t), add_sub_cancel_right])
    simp only [γ, cellEdge_one, cellEdge_zero] at he
    rw [he]
    have hy0 : (asComplex (corner a)).im = (a.2 : ℝ) - 1 / 2 := by
      simp [asComplex, corner]
    have hy1 : (asComplex (corner (a + north))).im = (a.2 : ℝ) + 1 / 2 := by
      simp [asComplex, corner, north]
      ring
    rcases lt_trichotomy a.2 0 with hy | hy | hy
    · have h0 : (asComplex (corner a)).im < 0 := by rw [hy0]; exact sub_neg.mpr (by
        have : (a.2 : ℝ) < 0 := by exact_mod_cast hy
        linarith)
      have h1 : (asComplex (corner (a + north))).im < 0 := by
        rw [hy1]
        have : (a.2 : ℝ) ≤ -1 := by exact_mod_cast (show a.2 ≤ -1 by omega)
        linarith
      rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg h0,
        Complex.arg_neg_eq_arg_add_pi_of_im_neg h1]
      simp only [vortexVertical, hy.ne, false_and, ite_false]
      ring
    · have h0 : (asComplex (corner a)).im < 0 := by rw [hy0, hy]; norm_num
      have h1 : 0 < (asComplex (corner (a + north))).im := by rw [hy1, hy]; norm_num
      rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg h0,
        Complex.arg_neg_eq_arg_sub_pi_of_im_pos h1]
      simp only [vortexVertical, hy, show a.1 ≤ 0 by omega, and_self, ite_true]
      field_simp
      ring
    · have h0 : 0 < (asComplex (corner a)).im := by
        rw [hy0]
        have : (1 : ℝ) ≤ (a.2 : ℝ) := by exact_mod_cast (show 1 ≤ a.2 by omega)
        linarith
      have h1 : 0 < (asComplex (corner (a + north))).im := by
        rw [hy1]
        have : (0 : ℝ) < (a.2 : ℝ) := by exact_mod_cast hy
        linarith
      rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos h0,
        Complex.arg_neg_eq_arg_sub_pi_of_im_pos h1]
      simp only [vortexVertical, hy.ne', false_and, ite_false]
      ring

/-- The finite union of closed unit squares with the specified integer centers.
This is the planar cell domain underlying the block diagrams in SCP10,
§6.3, lines 1935–1957. -/
def integerClosedCellUnion (A : Finset (ℤ × ℤ)) : Set (ℝ × ℝ) :=
  ⋃ a ∈ A, (fun d : ℝ × ℝ => ((a.1 : ℝ), (a.2 : ℝ)) + d) ''
    (Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Icc (-1 / 2 : ℝ) (1 / 2))

/-- Local path connectedness follows from the finite compact-cell quotient.
Source: SCP10, §6.3, lines 1935–1957; auxiliary geometric statement. -/
instance integerClosedCellUnion_locallyPathConnectedSpace (A : Finset (ℤ × ℤ)) :
    LocallyPathConnectedSpace (integerClosedCellUnion A) := by
  let S := Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)
  let : CompactSpace S := isCompact_iff_compactSpace.mp
    (isCompact_Icc.prod isCompact_Icc)
  let : LocallyPathConnectedSpace S :=
    ((convex_Icc (-1 / 2 : ℝ) (1 / 2)).prod
      (convex_Icc (-1 / 2 : ℝ) (1 / 2))).locallyPathConnectedSpace
  let f (a : {a // a ∈ A}) : C(S, ℝ × ℝ) :=
    ⟨fun d => ((a.1.1 : ℝ), (a.1.2 : ℝ)) + d.1, continuous_const.add continuous_subtype_val⟩
  have hset : (⋃ a, Set.range (f a)) = integerClosedCellUnion A := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, d, rfl⟩ := Set.mem_iUnion.mp hx
      exact mem_iUnion_of_mem a.1 (mem_iUnion_of_mem a.2 ⟨d.1, d.2, rfl⟩)
    · intro hx
      obtain ⟨a, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨ha, d, hd, rfl⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, ⟨d, hd⟩, rfl⟩
  rw [← hset]
  exact locallyPathConnectedSpace_iUnion_range f

private theorem zero_not_mem_integerClosedCellUnion (A : Finset (ℤ × ℤ))
    (hA : (0 : ℤ × ℤ) ∉ A) : (0 : ℝ × ℝ) ∉ integerClosedCellUnion A := by
  intro h
  obtain ⟨a, h⟩ := Set.mem_iUnion.mp h
  obtain ⟨ha, d, hd, he⟩ := Set.mem_iUnion.mp h
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change (a.1 : ℝ) + d.1 = 0 at hx
  change (a.2 : ℝ) + d.2 = 0 at hy
  have hxi : (-1 : ℤ) < a.1 ∧ a.1 < 1 := by
    exact_mod_cast (show (-1 : ℝ) < (a.1 : ℝ) ∧ (a.1 : ℝ) < 1 by
      constructor <;> linarith [hd.1.1, hd.1.2])
  have hyi : (-1 : ℤ) < a.2 ∧ a.2 < 1 := by
    exact_mod_cast (show (-1 : ℝ) < (a.2 : ℝ) ∧ (a.2 : ℝ) < 1 by
      constructor <;> linarith [hd.2.1, hd.2.2])
  have ha0 : a = 0 := Prod.ext (by change a.1 = 0; omega) (by change a.2 = 0; omega)
  exact hA (ha0 ▸ ha)

private theorem horizontal_cellEdge_mem (A : Finset (ℤ × ℤ)) (a : ℤ × ℤ)
    (ha : a ∈ A ∨ a - north ∈ A) (t : unitInterval) :
    cellEdge a east t ∈ integerClosedCellUnion A := by
  rcases ha with ha | ha
  · apply mem_iUnion_of_mem a
    apply mem_iUnion_of_mem ha
    refine ⟨cellEdge a east t - ((a.1 : ℝ), (a.2 : ℝ)), ?_, add_sub_cancel _ _⟩
    constructor <;> constructor <;> simp [cellEdge, corner] <;>
      linarith [t.2.1, t.2.2]
  · apply mem_iUnion_of_mem (a - north)
    apply mem_iUnion_of_mem ha
    refine ⟨cellEdge a east t -
      (((a - north).1 : ℝ), ((a - north).2 : ℝ)), ?_, add_sub_cancel _ _⟩
    constructor <;> constructor <;> simp [cellEdge, corner, north] <;>
      linarith [t.2.1, t.2.2]

private theorem vertical_cellEdge_mem (A : Finset (ℤ × ℤ)) (a : ℤ × ℤ)
    (ha : a ∈ A ∨ a - east ∈ A) (t : unitInterval) :
    cellEdge a north t ∈ integerClosedCellUnion A := by
  rcases ha with ha | ha
  · apply mem_iUnion_of_mem a
    apply mem_iUnion_of_mem ha
    refine ⟨cellEdge a north t - ((a.1 : ℝ), (a.2 : ℝ)), ?_, add_sub_cancel _ _⟩
    constructor <;> constructor <;> simp [cellEdge, corner] <;>
      linarith [t.2.1, t.2.2]
  · apply mem_iUnion_of_mem (a - east)
    apply mem_iUnion_of_mem ha
    refine ⟨cellEdge a north t -
      (((a - east).1 : ℝ), ((a - east).2 : ℝ)), ?_, add_sub_cancel _ _⟩
    constructor <;> constructor <;> simp [cellEdge, corner, east] <;>
      linarith [t.2.1, t.2.2]

private theorem exists_angularLift_integerClosedCellUnion (A : Finset (ℤ × ℤ))
    (hSC : IsSimplyConnected (integerClosedCellUnion A)) (hzero : (0 : ℤ × ℤ) ∉ A) :
    ∃ F : C(integerClosedCellUnion A, ℝ),
      ∀ p, (F p : Real.Angle) = Complex.arg (asComplex p.1) := by
  let : SimplyConnectedSpace (integerClosedCellUnion A) := hSC.simplyConnectedSpace
  have hnonzero (p : integerClosedCellUnion A) : asComplex p.1 ≠ 0 := by
    intro h
    have hp : p.1 = 0 := by
      apply Prod.ext
      · simpa [asComplex] using congrArg Complex.re h
      · simpa [asComplex] using congrArg Complex.im h
    exact zero_not_mem_integerClosedCellUnion A hzero (hp ▸ p.2)
  let f : C(integerClosedCellUnion A, Real.Angle) :=
    ⟨fun p => Complex.arg (asComplex p.1), by
      apply continuous_iff_continuousAt.mpr
      intro p
      exact (Complex.continuousAt_arg_coe_angle (hnonzero p)).comp
        (f := fun p : integerClosedCellUnion A => asComplex p.1) (by
          unfold asComplex
          fun_prop)⟩
  obtain ⟨p₀, hp₀⟩ := hSC.nonempty
  let o : integerClosedCellUnion A := ⟨p₀, hp₀⟩
  obtain ⟨F, hF, _⟩ := (AddCircle.isCoveringMap_coe (2 * Real.pi)).existsUnique_continuousMap_lifts
    f o (Complex.arg (asComplex p₀)) rfl
  exact ⟨F, fun p => congrFun hF.2 p⟩

/-- A simply connected finite union of closed lattice cells has no finite
missing-cell component containing the origin. The neighbor conditions express
closure of that component in the ordinary four-neighbor lattice. -/
private theorem not_finite_integerCellHole_zero_of_isSimplyConnected
    (A : Finset (ℤ × ℤ)) (hSC : IsSimplyConnected (integerClosedCellUnion A))
    (hzero : (0 : ℤ × ℤ) ∉ A) (K : Finset (ℤ × ℤ)) (hK : 0 ∈ K)
    (hright : ∀ a ∈ K, a + (1, 0) ∈ K ∨ a + (1, 0) ∈ A)
    (hleft : ∀ a ∈ K, a - (1, 0) ∈ K ∨ a - (1, 0) ∈ A)
    (htop : ∀ a ∈ K, a + (0, 1) ∈ K ∨ a + (0, 1) ∈ A)
    (hbottom : ∀ a ∈ K, a - (0, 1) ∈ K ∨ a - (0, 1) ∈ A) : False := by
  obtain ⟨F, hF⟩ := exists_angularLift_integerClosedCellUnion A hSC hzero
  apply integerGridBoundary_vortex_obstruction K hK (angularPotential _ F)
  · intro a ha hn
    apply angularPotential_horizontal _ F hF
    exact horizontal_cellEdge_mem A a (Or.inr ((hbottom a ha).resolve_left hn))
  · intro a ha hn
    apply angularPotential_horizontal _ F hF
    exact horizontal_cellEdge_mem A (a + north) (Or.inl ((htop a ha).resolve_left hn))
  · intro a ha he
    apply angularPotential_vertical _ F hF
    exact vertical_cellEdge_mem A a (Or.inr ((hleft a ha).resolve_left he))
  · intro a ha he
    apply angularPotential_vertical _ F hF
    exact vertical_cellEdge_mem A (a + east) (Or.inl ((hright a ha).resolve_left he))

/-- Simple connectedness excludes every finite four-neighbor component of
missing cells. The finite candidate is specified by closure under all lattice
neighbors outside the occupied cells; this is a conclusion, not a definition
of a disk. Source: SCP10, Theorem 6.9, lines 1935–1990;
auxiliary no-hole statement. -/
theorem not_finite_integerCellHole_of_isSimplyConnected
    (A : Finset (ℤ × ℤ)) (hSC : IsSimplyConnected (integerClosedCellUnion A))
    (K : Finset (ℤ × ℤ)) (o : ℤ × ℤ) (ho : o ∈ K) (hmissing : o ∉ A)
    (hright : ∀ a ∈ K, a + (1, 0) ∈ K ∨ a + (1, 0) ∈ A)
    (hleft : ∀ a ∈ K, a - (1, 0) ∈ K ∨ a - (1, 0) ∈ A)
    (htop : ∀ a ∈ K, a + (0, 1) ∈ K ∨ a + (0, 1) ∈ A)
    (hbottom : ∀ a ∈ K, a - (0, 1) ∈ K ∨ a - (0, 1) ∈ A) : False := by
  let e := Equiv.addRight (-o)
  let A' := A.map e.toEmbedding
  let K' := K.map e.toEmbedding
  let h := Homeomorph.addRight (-((o.1 : ℝ), (o.2 : ℝ)))
  have hset : h '' integerClosedCellUnion A = integerClosedCellUnion A' := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨a, hp⟩ := Set.mem_iUnion.mp hp
      obtain ⟨ha, d, hd, rfl⟩ := Set.mem_iUnion.mp hp
      apply mem_iUnion_of_mem (e a)
      apply mem_iUnion_of_mem (Finset.mem_map.mpr ⟨a, ha, rfl⟩)
      refine ⟨d, hd, ?_⟩
      apply Prod.ext <;> simp [h, e] <;> ring
    · intro hx
      obtain ⟨a, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨ha, d, hd, rfl⟩ := Set.mem_iUnion.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
      refine ⟨((b.1 : ℝ), (b.2 : ℝ)) + d,
        mem_iUnion_of_mem b (mem_iUnion_of_mem hb ⟨d, hd, rfl⟩), ?_⟩
      apply Prod.ext <;> simp [h, e] <;> ring
  have hA (a : ℤ × ℤ) : a ∈ A' ↔ a + o ∈ A := by
    simp [A', e, Finset.mem_map_equiv, Equiv.addRight]
  have hK (a : ℤ × ℤ) : a ∈ K' ↔ a + o ∈ K := by
    simp [K', e, Finset.mem_map_equiv, Equiv.addRight]
  apply not_finite_integerCellHole_zero_of_isSimplyConnected A'
    (hset ▸ h.isSimplyConnected_image.mpr hSC) (by simpa only [hA, zero_add] using hmissing)
    K' (by simpa only [hK, zero_add] using ho)
  · intro a ha
    simpa only [hK, hA, add_right_comm _ (1, 0) o] using hright (a + o) ((hK a).mp ha)
  · intro a ha
    simpa only [hK, hA, sub_add_eq_add_sub] using hleft (a + o) ((hK a).mp ha)
  · intro a ha
    simpa only [hK, hA, add_right_comm _ (0, 1) o] using htop (a + o) ((hK a).mp ha)
  · intro a ha
    simpa only [hK, hA, sub_add_eq_add_sub] using hbottom (a + o) ((hK a).mp ha)

/-- Every four-neighbor component of the missing integer cells is infinite
when the occupied closed-cell union is simply connected. Thus no bounded
lattice hole can occur. Source: SCP10, Theorem 6.9,
lines 1935–1990; auxiliary geometric statement. -/
theorem infinite_integerCellComplement_component_of_isSimplyConnected
    (A : Finset (ℤ × ℤ)) (hSC : IsSimplyConnected (integerClosedCellUnion A))
    (v : {a : ℤ × ℤ // a ∉ A}) :
    let Γ := (SimpleGraph.addCayley {(1, 0), (0, 1)}).induce {a : ℤ × ℤ | a ∉ A}
    (Γ.connectedComponentMk v).supp.Infinite := by
  dsimp only
  classical
  let Γ := (SimpleGraph.addCayley {(1, 0), (0, 1)}).induce {a : ℤ × ℤ | a ∉ A}
  let C := Γ.connectedComponentMk v
  intro hfinite
  let K := (hfinite.image (fun w : {a : ℤ × ℤ // a ∉ A} => w.1)).toFinset
  have hK (a : ℤ × ℤ) : a ∈ K ↔ ∃ w : {a : ℤ × ℤ // a ∉ A}, w ∈ C.supp ∧ w.1 = a := by
    exact Set.Finite.mem_toFinset _
  have hv : v.1 ∈ K := (hK v.1).mpr ⟨v, rfl, rfl⟩
  have hclosure (a : ℤ × ℤ) (ha : a ∈ K) (b : ℤ × ℤ)
      (hne : a ≠ b)
      (hstep : ∃ d ∈ ({(1, 0), (0, 1)} : Set (ℤ × ℤ)), a + d = b ∨ a = b + d) :
      b ∈ K ∨ b ∈ A := by
    by_cases hb : b ∈ A
    · exact Or.inr hb
    · apply Or.inl
      obtain ⟨w, hw, hwa⟩ := (hK a).mp ha
      let w' : {a : ℤ × ℤ // a ∉ A} := ⟨b, hb⟩
      have hadj : Γ.Adj w w' := by
        change (SimpleGraph.addCayley {(1, 0), (0, 1)}).Adj w.1 b
        rw [hwa]
        exact (SimpleGraph.addCayley_adj' _ _ _).mpr ⟨hne, hstep⟩
      exact (hK b).mpr ⟨w', (C.mem_supp_congr_adj hadj).mp hw, rfl⟩
  apply not_finite_integerCellHole_of_isSimplyConnected A hSC K v.1 hv v.2
  · intro a ha
    refine hclosure a ha (a + (1, 0)) ?_ ?_
    · intro h
      have hx := congrArg Prod.fst h
      simp at hx
    · exact ⟨(1, 0), by simp, Or.inl rfl⟩
  · intro a ha
    refine hclosure a ha (a - (1, 0)) ?_ ?_
    · intro h
      have hx := congrArg Prod.fst h
      simp at hx
      omega
    · exact ⟨(1, 0), by simp, Or.inr (sub_add_cancel _ _).symm⟩
  · intro a ha
    refine hclosure a ha (a + (0, 1)) ?_ ?_
    · intro h
      have hy := congrArg Prod.snd h
      simp at hy
    · exact ⟨(0, 1), by simp, Or.inl rfl⟩
  · intro a ha
    refine hclosure a ha (a - (0, 1)) ?_ ?_
    · intro h
      have hy := congrArg Prod.snd h
      simp at hy
      omega
    · exact ⟨(0, 1), by simp, Or.inr (sub_add_cancel _ _).symm⟩

/-- The native planar realization is the ordinary closed-cell union of its
finite set of integer centers. Source: SCP10, §6.3, lines 1935–1957;
auxiliary realization identity. -/
theorem integerClosedCellUnion_image_eq_torusRegionPlanarRealization
    {width height : ℕ} (R : Finset (TorusVertex width height))
    (L : {v // v ∈ R} → ℤ × ℤ) :
    integerClosedCellUnion (Finset.univ.image L) = torusRegionPlanarRealization R L := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨a, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨ha, d, hd, he⟩ := Set.mem_iUnion.mp hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp ha
    exact Set.mem_iUnion.mpr ⟨v, d, hd, he⟩
  · intro hx
    obtain ⟨v, d, hd, he⟩ := Set.mem_iUnion.mp hx
    exact mem_iUnion_of_mem (L v)
      (mem_iUnion_of_mem (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩) ⟨d, hd, he⟩)

/-- A simply connected genuine torus cell region admits planar integer
coordinates for which every component of the missing cells is infinite.
This excludes finite holes; it does not yet assert collar connectivity.
Source: SCP10, Theorem 6.9, lines 1935–1990; auxiliary geometric theorem. -/
theorem exists_integerLift_no_finite_cellHole_of_isSimplyConnected
    {width height : ℕ} [NeZero width] [NeZero height]
    (R : Finset (TorusVertex width height))
    (hSC : IsSimplyConnected (torusRegionRealization R)) (o : {v // v ∈ R}) :
    ∃ L : {v // v ∈ R} → ℤ × ℤ, IsTorusRegionIntegerLift R L ∧
      let A := Finset.univ.image L
      ∀ v : {a : ℤ × ℤ // a ∉ A},
        let Γ := (SimpleGraph.addCayley {(1, 0), (0, 1)}).induce {a : ℤ × ℤ | a ∉ A}
        (Γ.connectedComponentMk v).supp.Infinite := by
  classical
  obtain ⟨F, hF⟩ := exists_continuousLift_torusRegionRealization R hSC o
  obtain ⟨L, hL, hreal, _⟩ := exists_integerLift_torusRegionPlanarRealization R F hF
  let : SimplyConnectedSpace (torusRegionRealization R) := hSC.simplyConnectedSpace
  have hp : IsSimplyConnected (torusRegionPlanarRealization R L) :=
    (torusRegionLiftHomeomorph R F hF L hreal).symm.toHomotopyEquiv.simplyConnectedSpace
  have hA : IsSimplyConnected (integerClosedCellUnion (Finset.univ.image L)) := by
    rwa [integerClosedCellUnion_image_eq_torusRegionPlanarRealization]
  exact ⟨L, hL, fun v => infinite_integerCellComplement_component_of_isSimplyConnected _ hA v⟩

end TNLean.PEPS
