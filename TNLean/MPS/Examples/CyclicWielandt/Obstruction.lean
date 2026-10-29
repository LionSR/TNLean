/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.CyclicWielandt.WordNormalForm
import Mathlib.Tactic.Ring

/-!
# The two-entry obstruction before the cyclic Wielandt length

At length `D(D-1)-1`, every word has equal entries at `(D-1,0)` and `(0,1)`.
Pure shifts have equal entries there, while every shifted-jump word vanishes
at both positions. Their difference is a nonzero linear functional on the
full matrix algebra, so the exact word span is proper.

This is the lower obstruction in arXiv:0909.5347, source lines 691–700,
proved without a separate dimension count or a primitivity hypothesis.
-/

noncomputable section

open scoped Matrix Fin.NatCast

namespace MPSTensor.CyclicWielandt

variable {D : ℕ} [NeZero D]

omit [NeZero D] in
private theorem no_pred_length_padding (hD : 2 ≤ D) {k l n m : ℕ}
    (hs : k + l = 2 * D - 3) :
    D * (D - 1) - 1 ≠ 1 + k + l + n * (D - 1) + m * D := by
  intro hlen
  have hd : D - 1 + 1 = D := by omega
  have hs' : k + l + 3 = 2 * D := by omega
  have hpos : 0 < D * (D - 1) := Nat.mul_pos (by omega) (by omega)
  have hpred : D * (D - 1) - 1 + 1 = D * (D - 1) := by omega
  have heq : D * (D - 1) = (n + m + 2) * (D - 1) + m + 1 := by
    nlinarith
  have hsmall : m + 1 < D - 1 := by
    by_contra h
    have hm : D ≤ m + 2 := by omega
    have hprod := Nat.mul_le_mul_right (D - 1) hm
    nlinarith [Nat.zero_le (n * (D - 1))]
  have hcoef : n + m + 2 < D := by
    by_contra h
    have hprod := Nat.mul_le_mul_right (D - 1) (show D ≤ n + m + 2 by omega)
    nlinarith
  have hprod := Nat.mul_le_mul_right (D - 1) (show n + m + 3 ≤ D by omega)
  nlinarith

private theorem cast_eq_last (hD : 2 ≤ D) {k : ℕ} (hk : k < D)
    (h : (k : Fin D) = ((D - 1 : ℕ) : Fin D)) : k = D - 1 := by
  have hv := congrArg Fin.val h
  simpa only [Fin.val_natCast, Nat.mod_eq_of_lt hk,
    Nat.mod_eq_of_lt (show D - 1 < D by omega)] using hv

private theorem sandwich_pred_entries_zero (hD : 2 ≤ D) {k l n m : ℕ}
    (hk : k < D) (hl : l < D)
    (hlen : D * (D - 1) - 1 = 1 + k + l + n * (D - 1) + m * D) :
    (shift D ^ k * jump D * shift D ^ l) ((D - 1 : ℕ) : Fin D) 0 = 0 ∧
      (shift D ^ k * jump D * shift D ^ l) 0 1 = 0 := by
  rw [sandwich_eq_single]
  constructor
  · rw [Matrix.single_apply]
    apply ite_eq_right
    rintro ⟨hrow, hcol⟩
    have hk' := (return_coordinate_iff hD k hk).1 hrow
    have hl' : l = D - 1 := cast_eq_last hD hl (sub_eq_zero.mp hcol).symm
    exact no_pred_length_padding hD (k := k) (l := l) (n := n) (m := m) (by omega) hlen
  · rw [Matrix.single_apply]
    apply ite_eq_right
    rintro ⟨hrow, hcol⟩
    have hk' : k = D - 1 := cast_eq_last hD hk
      (add_left_cancel (hrow.trans (one_add_last hD).symm))
    have hl' := (return_coordinate_iff hD l hl).1 ((sub_eq_iff_eq_add.mp hcol).symm)
    exact no_pred_length_padding hD (k := k) (l := l) (n := n) (m := m) (by omega) hlen

/-- Every word at the predecessor length has equal entries at the two
inaccessible matrix-unit positions. Source: arXiv:0909.5347, lines 697–700. -/
theorem evalWord_pred_entries_eq (hD : 2 ≤ D) (w : List (Fin 2))
    (hw : w.length = D * (D - 1) - 1) :
    Kraus.evalWord (tensor D) w ((D - 1 : ℕ) : Fin D) 0 =
      Kraus.evalWord (tensor D) w 0 1 := by
  rcases evalWord_normalForm hD w with hz | hp | ⟨k, l, n, m, hk, hl, hlen, hmat⟩
  · simp [hz]
  · rw [hp, shift_pow_apply, shift_pow_apply]
    simp only [zero_add]
    have hcond : ((D - 1 : ℕ) : Fin D) = (w.length : Fin D) ↔
        (0 : Fin D) = 1 + (w.length : Fin D) := by
      constructor
      · intro h
        rw [← h]
        exact (one_add_last hD).symm
      · intro h
        exact add_left_cancel ((one_add_last hD).trans h)
    simp only [hcond]
  · rw [hmat]
    have hzero := sandwich_pred_entries_zero hD hk hl (hw ▸ hlen)
    rw [hzero.1, hzero.2]

/-- The predecessor word span is contained in the equality hyperplane of
the two inaccessible entries. Source: arXiv:0909.5347, lines 697–700. -/
theorem wordSpan_pred_entries_eq (hD : 2 ≤ D)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hX : X ∈ Kraus.wordSpan (tensor D) (D * (D - 1) - 1)) :
    X ((D - 1 : ℕ) : Fin D) 0 = X 0 1 := by
  let f : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun X ↦ X ((D - 1 : ℕ) : Fin D) 0 - X 0 1
      map_add' := by intros; simp; ring
      map_smul' := by intros; simp; ring }
  have hle : Kraus.wordSpan (tensor D) (D * (D - 1) - 1) ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, rfl⟩
    apply LinearMap.mem_ker.mpr
    change _ - _ = 0
    exact sub_eq_zero.mpr (evalWord_pred_entries_eq hD (List.ofFn σ) (by simp))
  have hz : f X = 0 := LinearMap.mem_ker.mp (hle hX)
  exact sub_eq_zero.mp hz

/-- The exact word span is proper at length `D(D-1)-1`.
Source: arXiv:0909.5347, source lines 691–700. -/
theorem wordSpan_pred_ne_top (hD : 2 ≤ D) :
    Kraus.wordSpan (tensor D) (D * (D - 1) - 1) ≠ ⊤ := by
  intro htop
  have hX := wordSpan_pred_entries_eq hD
    (Matrix.single ((D - 1 : ℕ) : Fin D) 0 (1 : ℂ)) (by rw [htop]; trivial)
  have hlast : ((D - 1 : ℕ) : Fin D) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natCast, Fin.val_zero,
      Nat.mod_eq_of_lt (show D - 1 < D by omega)] at hv
    omega
  simp [Matrix.single_apply, hlast] at hX

end MPSTensor.CyclicWielandt
