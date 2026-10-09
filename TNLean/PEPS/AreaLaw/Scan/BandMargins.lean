/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PhysicalPartition
import TNLean.PEPS.AreaLaw.Scan.ChargeSlots

/-!
# Positive-depth margins of the actual charge intervals

The deterministic fill count advances either front by at most `m` rows during
`nm` fills. The bands start at `8gm`, with near and far cutoffs `8gm+m+r` and
`8gm+5m+r`. Under `4D ≤ m`, their actual charge intervals therefore remain
inside the positive-depth rows from `1` to `L`. A row bound on that physical
interval consequently bounds the labelled charge candidates without an extra
assumption about which rows the candidate list visits.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 83–137, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- Either deterministic side consumes at most `m` complete rows during `nm` fills
(`08-scanner.tex`, lines 106–124). -/
theorem fillCount_div_le_window {n m k : ℕ} (hn : 0 < n) (hk : k ≤ n * m)
    (side : Bool) : fillCount k side / n ≤ m := by
  have hcount : fillCount k side ≤ k := by
    cases side <;> simp only [fillCount, Bool.false_eq_true, ↓reduceIte] <;> omega
  calc
    fillCount k side / n ≤ (n * m) / n := Nat.div_le_div_right (hcount.trans hk)
    _ = m := Nat.mul_div_cancel_left m hn

/-- Every oriented charge depth in an actual band has unsigned depth in `[1,L]`
(`08-scanner.tex`, lines 126–137). -/
theorem bandChargeInterval_bounds {n m K L g offset k r₀ D : ℕ}
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hg : g < K) (hoffset : offset < m)
    (hk : k ≤ n * m) (hr : r₀ ≤ D) (hD : 4 * D ≤ m) (hL : 8 * K * m ≤ L)
    (side : Bool) {d : ℤ}
    (hd : d ∈ Finset.Icc
      (nominalFront n (8 * g * m + m + offset) (8 * g * m + 5 * m + offset) k side - r₀)
      (nominalFront n (8 * g * m + m + offset) (8 * g * m + 5 * m + offset) k side + D)) :
    (if side then -d else d) ∈ Finset.Icc (1 : ℤ) L := by
  have hshift := fillCount_div_le_window (show 0 < n by omega) hk side
  have hband : 8 * g * m + 8 * m ≤ L := by
    calc
      8 * g * m + 8 * m = 8 * (g + 1) * m := by ring
      _ ≤ 8 * K * m := Nat.mul_le_mul_right m (Nat.mul_le_mul_left 8 hg)
      _ ≤ L := hL
  have hband' : (8 : ℤ) * g * m + 8 * m ≤ L := by exact_mod_cast hband
  have hshift0 : (0 : ℤ) ≤ (fillCount k side / n : ℕ) := by positivity
  have hoffset' : (offset : ℤ) < m := by exact_mod_cast hoffset
  have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
  have hr' : (r₀ : ℤ) ≤ D := by exact_mod_cast hr
  have hD' : (4 : ℤ) * D ≤ m := by exact_mod_cast hD
  have hg' : 0 ≤ (8 : ℤ) * g * m := by positivity
  cases side <;>
    simp only [nominalFront, initialFront, Bool.false_eq_true, ↓reduceIte,
      Finset.mem_Icc] at hd ⊢ <;> omega

/-- Positive physical row bounds apply to every row of the actual band charge interval
(`08-scanner.tex`, lines 83–84 and 127–137). -/
theorem bandChargeInterval_row_bound {V : Type*} [Fintype V] (depth : V → ℤ)
    {n m K L g offset k r₀ D : ℕ}
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hg : g < K) (hoffset : offset < m)
    (hk : k ≤ n * m) (hr : r₀ ≤ D) (hD : 4 * D ≤ m) (hL : 8 * K * m ≤ L)
    (hrow : ∀ t ∈ Finset.Icc (1 : ℤ) L,
      (Finset.univ.filter fun v ↦ depth v = t).card ≤ n)
    (side : Bool) {d : ℤ}
    (hd : d ∈ Finset.Icc
      (nominalFront n (8 * g * m + m + offset) (8 * g * m + 5 * m + offset) k side - r₀)
      (nominalFront n (8 * g * m + m + offset) (8 * g * m + 5 * m + offset) k side + D)) :
    (Finset.univ.filter fun v ↦ orientedDepth depth side v = d).card ≤ n := by
  have h := hrow _ (bandChargeInterval_bounds hn hm hg hoffset hk hr hD hL side hd)
  cases side <;> simpa [orientedDepth, neg_eq_iff_eq_neg] using h

/-- The actual band schedule supplies the row hypotheses of the labelled padding bound
(`08-scanner.tex`, lines 127–137). -/
theorem card_bandChargeCandidates_le_chargeSlotCount {V I : Type*}
    [Fintype V] [Fintype I] [DecidableEq V] (depth : V → ℤ) (anchor : I → V)
    {n m K L g offset k r₀ D μ : ℕ} {C₁ : ℝ}
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hg : g < K) (hoffset : offset < m)
    (hk : k ≤ n * m) (hr : r₀ ≤ D) (hD : 4 * D ≤ m) (hDpos : 1 ≤ D)
    (hL : 8 * K * m ≤ L) (hC : 3 * (μ : ℝ) ≤ C₁)
    (hrow : ∀ t ∈ Finset.Icc (1 : ℤ) L,
      (Finset.univ.filter fun v ↦ depth v = t).card ≤ n)
    (hmult : ∀ v, (Finset.univ.filter fun i ↦ anchor i = v).card ≤ μ) (side : Bool) :
    (chargeCandidates (orientedDepth depth side) anchor
      (nominalFront n (8 * g * m + m + offset) (8 * g * m + 5 * m + offset) k side - r₀)
      (nominalFront n (8 * g * m + m + offset) (8 * g * m + 5 * m + offset) k side + D)).card ≤
        chargeSlotCount C₁ n D := by
  apply card_chargeCandidates_le_chargeSlotCount _ _ _ r₀ n D μ C₁ hr hDpos hC _ hmult
  intro d hd
  exact bandChargeInterval_row_bound depth hn hm hg hoffset hk hr hD hL hrow side hd

end TNLean.PEPS.AreaLaw.Scan
