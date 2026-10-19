/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Topology.LocallyConstant.Basic
import TNLean.PEPS.Approximation.DyadicChamberSampling

/-!
# Wall directions and wall slopes

The walls of the guides of the dyadic protocol lie on lines whose normals belong to the finite
set `wallNormals`. This file records the facts about these lines used for an explicit footprint
ratio near a mark:

* affine reparametrizations keep walls on lines, and there are finitely many wall normals;
* the wall directions `IsWallDirection`, the vectors on lines through the origin with these
  normals, are invariant under nonzero scalings;
* the wall slopes `wallSlopes`, the slopes `m`, `|m| < 3`, with `(1, m)` a wall direction, are
  multiples `k / 1000` with `|k| ≤ 8`, so distinct wall slopes differ by at least `1/1000`;
* a function of the slope that is locally constant off the wall slopes takes at most two values
  on three slopes within `1/1000` of each other, and changes value only across a wall slope.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: the walls of the guides
  (lines 69–80, 142–221), the straight-ray charts (lines 301–302), the point treatment (lines
  330–338), the compactness observation (lines 447–479) and the point covers (lines 481–505).
-/

open Set Metric Filter Topology

namespace TNLean.PEPS.Approximation

/-! ### Walls on lines through a point -/

/-- Rescaling the argument about a point keeps a set lying locally in lines so, with the same
normals. -/
theorem IsLocallyInLines.preimage_affine {𝒩 Z : Set (ℝ × ℝ)} (h : IsLocallyInLines 𝒩 Z)
    (c : ℝ × ℝ) {a : ℝ} (ha : a ≠ 0) : IsLocallyInLines 𝒩 ((fun u => c + a • u) ⁻¹' Z) :=
  fun p => by
  obtain ⟨U, hU, F, hF, h𝒩, hs⟩ := h (c + a • p)
  refine ⟨(fun u => c + a • u) ⁻¹' U,
    (by fun_prop : Continuous fun u : ℝ × ℝ => c + a • u).continuousAt.preimage_mem_nhds hU,
    (fun L => (L.1, (L.2 - (L.1.1 * c.1 + L.1.2 * c.2)) / a)) '' F, hF.image _, ?_, ?_⟩
  · rintro _ ⟨L, hL, rfl⟩
    exact h𝒩 L hL
  · rintro q ⟨hqZ, hqU⟩
    obtain ⟨L, hL, hm⟩ := mem_iUnion₂.1 (hs ⟨hqZ, hqU⟩)
    refine mem_iUnion₂.2 ⟨_, mem_image_of_mem _ hL, ?_⟩
    simp only [normalLine, mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] at hm ⊢
    rw [eq_div_iff ha]
    linear_combination hm

/-- Composing with an affine map of nonzero ratio keeps the walls on lines with the same
normals. -/
theorem HasLineWalls.comp_affine {𝒩 : Set (ℝ × ℝ)} {ι : Sort*} {f : ℝ × ℝ → ι}
    (h : HasLineWalls 𝒩 f) (c : ℝ × ℝ) {a : ℝ} (ha : a ≠ 0) :
    HasLineWalls 𝒩 fun u => f (c + a • u) := by
  obtain ⟨Z, hZ, hl⟩ := h
  exact ⟨_, hZ.preimage_affine c ha, fun q hq =>
    ((by fun_prop : Continuous fun u : ℝ × ℝ => c + a • u).tendsto q).eventually (hl _ hq)⟩

/-- There are finitely many wall normals. -/
theorem finite_wallNormals : wallNormals.Finite := by
  have hT : wallThresholds.Finite := by simp [wallThresholds]
  refine (hT.biUnion fun t _ =>
    Set.toFinite ({(t, 1000), (-t, 1000), (1000, t), (1000, -t)} : Set (ℝ × ℝ))).subset ?_
  rintro N ⟨t, ht, h⟩
  exact mem_biUnion ht (by rcases h with rfl | rfl | rfl | rfl <;> simp)

/-! ### Wall directions -/

/-- The vector `w` lies on a line through the origin with normal in `wallNormals`: a direction
of the walls of the guides near a mark.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:142–221, 301–302`. -/
def IsWallDirection (w : ℝ × ℝ) : Prop := ∃ N ∈ wallNormals, N.1 * w.1 + N.2 * w.2 = 0

/-- The wall directions, by threshold. -/
theorem isWallDirection_iff {w : ℝ × ℝ} : IsWallDirection w ↔ ∃ t ∈ wallThresholds,
    t * w.1 + 1000 * w.2 = 0 ∨ -t * w.1 + 1000 * w.2 = 0 ∨ 1000 * w.1 + t * w.2 = 0 ∨
      1000 * w.1 + -t * w.2 = 0 := by
  constructor
  · rintro ⟨N, ⟨t, ht, rfl | rfl | rfl | rfl⟩, h⟩
    exacts [⟨t, ht, Or.inl h⟩, ⟨t, ht, Or.inr (Or.inl h)⟩, ⟨t, ht, Or.inr (Or.inr (Or.inl h))⟩,
      ⟨t, ht, Or.inr (Or.inr (Or.inr h))⟩]
  · rintro ⟨t, ht, h | h | h | h⟩
    exacts [⟨_, ⟨t, ht, Or.inl rfl⟩, h⟩, ⟨_, ⟨t, ht, Or.inr (Or.inl rfl)⟩, h⟩,
      ⟨_, ⟨t, ht, Or.inr (Or.inr (Or.inl rfl))⟩, h⟩,
      ⟨_, ⟨t, ht, Or.inr (Or.inr (Or.inr rfl))⟩, h⟩]

/-- Wall directions are invariant under nonzero scalings. -/
theorem isWallDirection_smul_iff {a : ℝ} (ha : a ≠ 0) {w : ℝ × ℝ} :
    IsWallDirection (a • w) ↔ IsWallDirection w := by
  simp only [IsWallDirection, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine exists_congr fun N => and_congr_right fun _ => ?_
  rw [show N.1 * (a * w.1) + N.2 * (a * w.2) = a * (N.1 * w.1 + N.2 * w.2) by ring,
    mul_eq_zero, or_iff_right ha]

/-- The wall thresholds are integers of absolute value at most `8`. -/
theorem wallThresholds_bound {t : ℝ} (ht : t ∈ wallThresholds) :
    ∃ k : ℤ, t = k ∧ |t| ≤ 8 := by
  simp only [wallThresholds, mem_insert_iff, mem_singleton_iff] at ht
  have h8 : |t| ≤ 8 := by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [abs_le]
  refine ⟨⌊t⌋, ?_, h8⟩
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- The slopes `m`, `|m| < 3`, of the wall directions `(1, m)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:142–221`. -/
def wallSlopes : Set ℝ := {m | |m| < 3 ∧ IsWallDirection (1, m)}

/-- The wall slopes are multiples `k / 1000` with `|k| ≤ 8`. -/
theorem exists_int_of_mem_wallSlopes {m : ℝ} (hm : m ∈ wallSlopes) :
    ∃ k : ℤ, 1000 * m = k ∧ |(k : ℝ)| ≤ 8 := by
  obtain ⟨hm3, hw⟩ := hm
  obtain ⟨t, ht, h⟩ := isWallDirection_iff.1 hw
  obtain ⟨k, rfl, hk⟩ := wallThresholds_bound ht
  simp only [mul_one] at h
  have hb : |(k : ℝ) * m| < 1000 := by
    rw [abs_mul]; nlinarith [abs_nonneg (k : ℝ), abs_nonneg m]
  rw [abs_lt] at hb
  rcases h with h | h | h | h
  · exact ⟨-k, by push_cast; linarith, by rwa [Int.cast_neg, abs_neg]⟩
  · exact ⟨k, by linarith, hk⟩
  · exact absurd h (by nlinarith)
  · exact absurd h (by nlinarith)

/-- The wall slopes are at most `1/100` in absolute value. -/
theorem abs_le_of_mem_wallSlopes {m : ℝ} (hm : m ∈ wallSlopes) : |m| ≤ 1 / 100 := by
  obtain ⟨k, hk, hk8⟩ := exists_int_of_mem_wallSlopes hm
  have : |1000 * m| ≤ 8 := by rw [hk]; exact hk8
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1000)] at this
  linarith

/-- **Distinct wall slopes differ by at least `1/1000`.**

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:142–221`. -/
theorem le_abs_sub_of_mem_wallSlopes {m m' : ℝ} (hm : m ∈ wallSlopes) (hm' : m' ∈ wallSlopes)
    (hne : m ≠ m') : 1 / 1000 ≤ |m - m'| := by
  obtain ⟨k, hk, -⟩ := exists_int_of_mem_wallSlopes hm
  obtain ⟨k', hk', -⟩ := exists_int_of_mem_wallSlopes hm'
  have hkk : k ≠ k' := fun h => hne (by
    have : (1000 : ℝ) * m = 1000 * m' := by rw [hk, hk', h]
    linarith)
  have h1 : (1 : ℝ) ≤ |(k : ℝ) - k'| := by
    rw [← Int.cast_sub, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.2 hkk)
  have : |(k : ℝ) - k'| = 1000 * |m - m'| := by
    rw [← hk, ← hk', ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1000)]
  linarith

/-! ### Slopes off the walls -/

section Slopes

variable {κ : Type*} {φ : ℝ → κ}

/-- A function on the slopes locally constant off the wall slopes is constant on every interval
in `(-3, 3)` without wall slopes. -/
theorem eq_of_forall_notMem_wallSlopes
    (hloc : ∀ m, |m| < 3 → m ∉ wallSlopes → ∀ᶠ m' in 𝓝 m, φ m' = φ m) {a b : ℝ} (hab : a ≤ b)
    (ha : -3 < a) (hb : b < 3) (hno : ∀ m ∈ Icc a b, m ∉ wallSlopes) : φ a = φ b := by
  have : PreconnectedSpace (Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  have hlc : IsLocallyConstant fun m : Icc a b => φ m := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro m
    have hm3 : |(m : ℝ)| < 3 := abs_lt.2 ⟨by linarith [m.2.1], by linarith [m.2.2]⟩
    exact continuous_subtype_val.continuousAt.eventually (hloc m hm3 (hno m m.2))
  exact hlc.apply_eq_of_preconnectedSpace ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩

/-- Two slopes within `1/1000`, off the wall slopes and with different values, have a wall slope
strictly between them; the value is constant from each of them up to that slope.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:447–479`. -/
theorem exists_wallSlope_between
    (hloc : ∀ m, |m| < 3 → m ∉ wallSlopes → ∀ᶠ m' in 𝓝 m, φ m' = φ m) {m₁ m₂ : ℝ}
    (h₁ : |m₁| ≤ 2) (h₂ : |m₂| ≤ 2) (h₁' : m₁ ∉ wallSlopes) (h₂' : m₂ ∉ wallSlopes)
    (h₁₂ : |m₁ - m₂| < 1 / 1000) (hne : φ m₁ ≠ φ m₂) :
    ∃ β ∈ wallSlopes, (m₁ < β ∧ β < m₂ ∨ m₂ < β ∧ β < m₁) ∧
      (∀ m, (m₁ ≤ m ∧ m < β ∨ β < m ∧ m ≤ m₁) → φ m = φ m₁ ∧ m ∉ wallSlopes) ∧
      ∀ m, (m₂ ≤ m ∧ m < β ∨ β < m ∧ m ≤ m₂) → φ m = φ m₂ ∧ m ∉ wallSlopes := by
  rw [abs_le] at h₁ h₂
  rw [abs_lt] at h₁₂
  -- a wall slope in the closed interval between the two slopes
  have hex : ∃ β ∈ wallSlopes, min m₁ m₂ ≤ β ∧ β ≤ max m₁ m₂ := by
    by_contra hc
    push Not at hc
    have h := eq_of_forall_notMem_wallSlopes hloc (min_le_max (a := m₁) (b := m₂))
      (lt_min (by linarith) (by linarith)) (max_lt (by linarith) (by linarith))
      fun m hm hmB => absurd hm.2 (not_le.2 (hc m hmB hm.1))
    rcases le_total m₁ m₂ with h' | h'
    · rw [min_eq_left h', max_eq_right h'] at h; exact hne h
    · rw [min_eq_right h', max_eq_left h'] at h; exact hne h.symm
  obtain ⟨β, hβ, hβ₁, hβ₂⟩ := hex
  -- it is the only wall slope within `1/1000` of both
  have huniq : ∀ b ∈ wallSlopes, min m₁ m₂ ≤ b → b ≤ max m₁ m₂ → b = β := by
    intro b hb hb₁ hb₂
    by_contra hbβ
    have := le_abs_sub_of_mem_wallSlopes hb hβ hbβ
    rw [le_abs] at this
    rcases le_total m₁ m₂ with h' | h' <;>
      simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h'] at hβ₁ hβ₂ hb₁ hb₂ <;>
      rcases this with h | h <;> linarith
  have hne₁ : β ≠ m₁ := fun h => h₁' (h ▸ hβ)
  have hne₂ : β ≠ m₂ := fun h => h₂' (h ▸ hβ)
  have side (m₀ : ℝ) (hm₀ : m₀ = m₁ ∨ m₀ = m₂) (m : ℝ)
      (hm : m₀ ≤ m ∧ m < β ∨ β < m ∧ m ≤ m₀) : φ m = φ m₀ ∧ m ∉ wallSlopes := by
    have h0lo : min m₁ m₂ ≤ m₀ := by
      rcases hm₀ with rfl | rfl
      exacts [min_le_left _ _, min_le_right _ _]
    have h0hi : m₀ ≤ max m₁ m₂ := by
      rcases hm₀ with rfl | rfl
      exacts [le_max_left _ _, le_max_right _ _]
    have hlo : min m₁ m₂ ≤ min m₀ m := le_min h0lo (by rcases hm with hm | hm <;> linarith)
    have hhi : max m₀ m ≤ max m₁ m₂ := max_le h0hi (by rcases hm with hm | hm <;> linarith)
    have hno : ∀ b ∈ Icc (min m₀ m) (max m₀ m), b ∉ wallSlopes := by
      intro b hb hbB
      have := huniq b hbB (hlo.trans hb.1) (hb.2.trans hhi)
      subst this
      rcases hm with hm | hm
      · rw [min_eq_left hm.1, max_eq_right hm.1] at hb; linarith [hb.2]
      · rw [min_eq_right hm.2, max_eq_left hm.2] at hb; linarith [hb.1]
    have hrange : -3 < min m₁ m₂ ∧ max m₁ m₂ < 3 :=
      ⟨lt_min (by linarith) (by linarith), max_lt (by linarith) (by linarith)⟩
    have h := eq_of_forall_notMem_wallSlopes hloc min_le_max (by linarith [hlo, hrange.1])
      (by linarith [hhi, hrange.2]) hno
    have hmm : m ∈ Icc (min m₀ m) (max m₀ m) := ⟨min_le_right _ _, le_max_right _ _⟩
    refine ⟨?_, hno m hmm⟩
    rcases hm with hm | hm
    · rw [min_eq_left hm.1, max_eq_right hm.1] at h; exact h.symm
    · rw [min_eq_right hm.2, max_eq_left hm.2] at h; exact h
  refine ⟨β, hβ, ?_, side m₁ (Or.inl rfl), side m₂ (Or.inr rfl)⟩
  rcases le_total m₁ m₂ with h' | h'
  · rw [min_eq_left h'] at hβ₁; rw [max_eq_right h'] at hβ₂
    exact Or.inl ⟨lt_of_le_of_ne hβ₁ (Ne.symm hne₁), lt_of_le_of_ne hβ₂ hne₂⟩
  · rw [min_eq_right h'] at hβ₁; rw [max_eq_left h'] at hβ₂
    exact Or.inr ⟨lt_of_le_of_ne hβ₁ (Ne.symm hne₂), lt_of_le_of_ne hβ₂ hne₁⟩

/-- Three slopes within `1/1000` of each other, off the wall slopes, carry at most two values.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:447–479`. -/
theorem eq_or_eq_or_eq_of_slopes
    (hloc : ∀ m, |m| < 3 → m ∉ wallSlopes → ∀ᶠ m' in 𝓝 m, φ m' = φ m) {m₁ m₂ m₃ : ℝ}
    (h₁ : |m₁| ≤ 2) (h₂ : |m₂| ≤ 2) (h₃ : |m₃| ≤ 2) (h₁' : m₁ ∉ wallSlopes)
    (h₂' : m₂ ∉ wallSlopes) (h₃' : m₃ ∉ wallSlopes) (h₁₂ : |m₁ - m₂| < 1 / 1000)
    (h₁₃ : |m₁ - m₃| < 1 / 1000) (h₂₃ : |m₂ - m₃| < 1 / 1000) :
    φ m₁ = φ m₂ ∨ φ m₁ = φ m₃ ∨ φ m₂ = φ m₃ := by
  by_contra hc
  push Not at hc
  obtain ⟨n12, n13, n23⟩ := hc
  obtain ⟨β, hβ, hb, -, -⟩ := exists_wallSlope_between hloc h₁ h₂ h₁' h₂' h₁₂ n12
  obtain ⟨β', hβ', hb', -, -⟩ := exists_wallSlope_between hloc h₁ h₃ h₁' h₃' h₁₃ n13
  obtain ⟨β'', hβ'', hb'', -, -⟩ := exists_wallSlope_between hloc h₂ h₃ h₂' h₃' h₂₃ n23
  rw [abs_lt] at h₁₂ h₁₃ h₂₃
  have e1 : β' = β := by
    by_contra h
    have := le_abs_sub_of_mem_wallSlopes hβ' hβ h
    rw [le_abs] at this
    rcases hb with hb | hb <;> rcases hb' with hb' | hb' <;> rcases this with h | h <;> linarith
  have e2 : β'' = β := by
    by_contra h
    have := le_abs_sub_of_mem_wallSlopes hβ'' hβ h
    rw [le_abs] at this
    rcases hb with hb | hb <;> rcases hb'' with hb'' | hb'' <;> rcases this with h | h <;>
      linarith
  subst e1 e2
  rcases hb with hb | hb <;> rcases hb' with hb' | hb' <;> rcases hb'' with hb'' | hb'' <;>
    linarith

end Slopes

end TNLean.PEPS.Approximation
