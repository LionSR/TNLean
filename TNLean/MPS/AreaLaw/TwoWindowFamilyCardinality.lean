/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fintype.Prod

/-!
# Cardinality of a common two-window polynomial family

The low-frequency crossing choices and interpolation samples contribute finite
factors to the number of middle operators. The numerical estimate below absorbs
these factors into the square of an explicit power of the local dimension and
the polynomial degree. It is supporting arithmetic for ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333. No operator representation,
bond bound or running-time estimate is part of this implication.
-/

namespace TNLean.MPS.AreaLaw

/-- The selected crossing positions and low frequencies have at most
`(q * k) ^ (4 * ell)` choices. This coarse estimate uses only existing power
bounds. Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1324–1333; it concerns the size of the index set alone. -/
private theorem card_crossing_frequency_choices_le {q k ell : ℕ}
    (hq : 2 ≤ q) (hk : 1 ≤ k) (hell : 1 ≤ ell) :
    Fintype.card (Fin (2 * ell) × Fin (2 * ell) ×
      Fin (k / (2 * ell) + 1) × Fin (k / (2 * ell) + 1)) ≤ (q * k) ^ (4 * ell) := by
  have htwo : 2 ≤ q * k := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul hq hk
  have hbase : k + 1 ≤ q * k :=
    (show k + 1 ≤ 2 * k by omega).trans (Nat.mul_le_mul_right k hq)
  have hposition : 2 * ell ≤ (q * k) ^ ell :=
    (Nat.mul_le_pow (by decide : (2 : ℕ) ≠ 1) ell).trans
      (Nat.pow_le_pow_left htwo ell)
  have hfrequency : k / (2 * ell) + 1 ≤ (q * k) ^ ell :=
    ((Nat.add_le_add_right (Nat.div_le_self k (2 * ell)) 1).trans hbase).trans
      (Nat.le_self_pow (by omega : ell ≠ 0) (q * k))
  calc
    Fintype.card (Fin (2 * ell) × Fin (2 * ell) ×
      Fin (k / (2 * ell) + 1) × Fin (k / (2 * ell) + 1)) =
        (2 * ell) ^ 2 * (k / (2 * ell) + 1) ^ 2 := by
      simp only [Fintype.card_prod, Fintype.card_fin, pow_two, Nat.mul_assoc]
    _ ≤ ((q * k) ^ ell) ^ 2 * ((q * k) ^ ell) ^ 2 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hposition 2) (Nat.pow_le_pow_left hfrequency 2)
    _ = (q * k) ^ (4 * ell) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega

/-- Absorb the crossing choices and a supplied sampling-grid bound into one
coarse polynomial-base estimate for the complete family. The parameter `Z`
is the number of sampling nodes. Supporting ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1311–1333; no operator bond or running-time conclusion
is part of this numerical implication. -/
private theorem crossing_grid_cardinality_absorption {q k ell Z N : ℕ}
    (hq : 2 ≤ q) (hk : 1 ≤ k) (hell : 1 ≤ ell)
    (hZ : Z ≤ (k + 1) ^ (4 * ell + 3))
    (hN : N ≤ Fintype.card (Fin (2 * ell) × Fin (2 * ell) ×
      Fin (k / (2 * ell) + 1) × Fin (k / (2 * ell) + 1)) * Z *
      (q * k) ^ (24 * ell + 4 * (k / ell))) :
    N ≤ (q * k) ^ (35 * ell + 4 * (k / ell)) := by
  have hpos : 0 < q * k := Nat.mul_pos (by omega) (by omega)
  have hbase : k + 1 ≤ q * k :=
    (show k + 1 ≤ 2 * k by omega).trans (Nat.mul_le_mul_right k hq)
  have hgrid : Z ≤ (q * k) ^ (7 * ell) :=
    (hZ.trans (Nat.pow_le_pow_left hbase _)).trans
      (Nat.pow_le_pow_right hpos (by omega : 4 * ell + 3 ≤ 7 * ell))
  calc
    N ≤ Fintype.card (Fin (2 * ell) × Fin (2 * ell) ×
      Fin (k / (2 * ell) + 1) × Fin (k / (2 * ell) + 1)) * Z *
        (q * k) ^ (24 * ell + 4 * (k / ell)) := hN
    _ ≤ (q * k) ^ (4 * ell) * (q * k) ^ (7 * ell) *
        (q * k) ^ (24 * ell + 4 * (k / ell)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul
        (card_crossing_frequency_choices_le hq hk hell) hgrid)
    _ = (q * k) ^ (35 * ell + 4 * (k / ell)) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega

/-- An explicit square cardinal bound for the complete crossing/grid family.
Its exponent has a margin of `ell` relative to the preceding estimate.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333;
this is a count parameter, not a sharp virtual dimension or complexity bound. -/
theorem crossing_grid_cardinality_le_square {q k ell Z N : ℕ}
    (hq : 2 ≤ q) (hk : 1 ≤ k) (hell : 1 ≤ ell)
    (hZ : Z ≤ (k + 1) ^ (4 * ell + 3))
    (hN : N ≤ Fintype.card (Fin (2 * ell) × Fin (2 * ell) ×
      Fin (k / (2 * ell) + 1) × Fin (k / (2 * ell) + 1)) * Z *
      (q * k) ^ (24 * ell + 4 * (k / ell))) :
    let D := (q * k) ^ (18 * ell + 2 * (k / ell))
    N ≤ D ^ 2 := by
  have hpos : 0 < q * k := Nat.mul_pos (by omega) (by omega)
  change N ≤ ((q * k) ^ (18 * ell + 2 * (k / ell))) ^ 2
  rw [← pow_mul]
  exact (crossing_grid_cardinality_absorption hq hk hell hZ hN).trans
    (Nat.pow_le_pow_right hpos (by omega))

end TNLean.MPS.AreaLaw
