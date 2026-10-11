/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.DesignatedDilution
import TNLean.PEPS.AreaLaw.Scan.BandMargins

/-!
# Uniqueness of an actual splitting band and side

The two front intervals of one band and those of different bands are disjoint
throughout the prescribed `nm` fills. Therefore a labelled designated support
incident with a middle and a receiving side has a unique such band and side.
No goodness or independence of the split event is assumed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Lemma 9.1(1), at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan
namespace CollarScan

variable {V I : Type*} (S : CollarScan V I)

/-- Oppositely oriented front intervals cannot contain the same physical depth
in any two bands, throughout the source horizon. -/
theorem front_intervals_opposite_disjoint {g g' r r' k : ℕ} {z : ℤ}
    (hn : 0 < S.n) (hk : k ≤ S.n * S.m) (hr : S.r₀ ≤ S.D)
    (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m) (hoff : r < S.m) (hoff' : r' < S.m)
    (hsame : g = g' → r = r')
    (hne : S.front g r k false - S.r₀ ≤ z ∧
      z ≤ S.front g r k false + S.D + 2 * S.r₀)
    (hfar : S.front g' r' k true - S.r₀ ≤ -z ∧
      -z ≤ S.front g' r' k true + S.D + 2 * S.r₀) : False := by
  have hnearShift := fillCount_div_le_window hn hk false
  have hfarShift := fillCount_div_le_window hn hk true
  have hn0 : (0 : ℤ) ≤ (fillCount k false / S.n : ℕ) := by positivity
  have hf0 : (0 : ℤ) ≤ (fillCount k true / S.n : ℕ) := by positivity
  have hn1 : ((fillCount k false / S.n : ℕ) : ℤ) ≤ S.m := by exact_mod_cast hnearShift
  have hf1 : ((fillCount k true / S.n : ℕ) : ℤ) ≤ S.m := by exact_mod_cast hfarShift
  have hm : (4 : ℤ) * S.D ≤ S.m := by exact_mod_cast hD
  have hdp : (1 : ℤ) ≤ S.D := by exact_mod_cast hDpos
  have hrad : (S.r₀ : ℤ) ≤ S.D := by exact_mod_cast hr
  have ho : (r : ℤ) < S.m := by exact_mod_cast hoff
  have ho' : (r' : ℤ) < S.m := by exact_mod_cast hoff'
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hr0' : (0 : ℤ) ≤ r' := by positivity
  simp only [front, nominalFront, initialFront, lower, upper, Bool.false_eq_true,
    ↓reduceIte, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hne hfar
  rcases lt_trichotomy g g' with hgg | hgg | hgg
  · have hgg' : (g : ℤ) + 1 ≤ g' := by exact_mod_cast hgg
    nlinarith
  · have hrr := hsame hgg
    subst g'; subst r'; omega
  · have hgg' : (g' : ℤ) + 1 ≤ g := by exact_mod_cast hgg
    nlinarith

/-- At one actual history's offsets, a physical depth belongs to at most one
band-side split interval during the prescribed horizon. -/
theorem front_intervals_unique {k : ℕ} (offset : Fin S.K → Fin S.m)
    (hn : 0 < S.n) (hk : k ≤ S.n * S.m) (hr : S.r₀ ≤ S.D)
    (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (g g' : Fin S.K) (side side' : Bool) (z : ℤ)
    (h : S.front g (offset g) k side - S.r₀ ≤ (if side then -z else z) ∧
      (if side then -z else z) ≤ S.front g (offset g) k side + S.D + 2 * S.r₀)
    (h' : S.front g' (offset g') k side' - S.r₀ ≤ (if side' then -z else z) ∧
      (if side' then -z else z) ≤ S.front g' (offset g') k side' + S.D + 2 * S.r₀) :
    g = g' ∧ side = side' := by
  have hs (he : g.val = g'.val) : (offset g).val = (offset g').val := by
    have : g = g' := Fin.ext he
    simp [this]
  have hm : 0 < S.m := by omega
  cases side <;> cases side'
  · exact ⟨Fin.ext (S.split_interval_band_unique (k := k) (z := z) (a := S.r₀) (b := S.D + 2 * S.r₀)
      hm (by omega)
      (offset g).isLt (offset g').isLt false
      (by simpa [Nat.cast_add, Nat.cast_mul, add_assoc] using h)
      (by simpa [Nat.cast_add, Nat.cast_mul, add_assoc] using h')), rfl⟩
  · exact (S.front_intervals_opposite_disjoint hn hk hr hDpos hD
      (offset g).isLt (offset g').isLt hs h h').elim
  · have hs' (he : g'.val = g.val) : (offset g').val = (offset g).val :=
      (hs he.symm).symm
    exact (S.front_intervals_opposite_disjoint hn hk hr hDpos hD
      (offset g').isLt (offset g).isLt hs' h' h).elim
  · exact ⟨Fin.ext (S.split_interval_band_unique (k := k) (z := -z)
      (a := S.r₀) (b := S.D + 2 * S.r₀)
      hm (by omega)
      (offset g).isLt (offset g').isLt true
      (by simpa [Nat.cast_add, Nat.cast_mul, add_assoc] using h)
      (by simpa [Nat.cast_add, Nat.cast_mul, add_assoc] using h')), rfl⟩

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
