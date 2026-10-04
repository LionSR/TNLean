/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Dimensions of encoded bond registers

A bond of positive dimension `r` fits in `Nat.clog d r` qudits, and
its padded dimension is at most `d * r`. Two such flags together with
one physical site therefore have dimension polynomial in their bond
dimensions. A second site may be included when needed for pair-gate
synthesis without changing this estimate.

Source: the register encoding in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

namespace MPUCircuit

/-- Ceiling-logarithmic encoding has at most a factor of the local dimension
in padding. Source: the register encoding in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem bond_register_dimension_bounds {d r : ℕ} (hd : 2 ≤ d) (hr : 0 < r) :
    r ≤ d ^ Nat.clog d r ∧ d ^ Nat.clog d r ≤ d * r := by
  refine ⟨Nat.le_pow_clog (by omega) r, ?_⟩
  by_cases hr1 : 1 < r
  · have hq := Nat.clog_pos (by omega : 1 < d) hr1
    calc
      d ^ Nat.clog d r = d ^ ((Nat.clog d r - 1) + 1) := by congr 1; omega
      _ = d ^ (Nat.clog d r - 1) * d := pow_succ _ _
      _ ≤ r * d := Nat.mul_le_mul_right d
        (Nat.le_of_lt (Nat.pow_pred_clog_lt_self (by omega) hr1))
      _ = d * r := Nat.mul_comm _ _
  · have : r = 1 := by omega
    simpa only [this, Nat.clog_one_right, pow_zero, mul_one] using (by omega : 1 ≤ d)

/-- Every finite bond basis embeds in a ceiling-logarithmic qudit register.
Source: the register encoding in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem nonempty_bond_register_embedding {ι : Type*} [Fintype ι]
    {d : ℕ} (hd : 2 ≤ d) :
    Nonempty (ι ↪ (Fin (Nat.clog d (Fintype.card ι)) → Fin d)) := by
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_fun, Fintype.card_fin] using
    Nat.le_pow_clog (by omega : 1 < d) (Fintype.card ι)

/-- A bond basis can be encoded with its zero label represented by the
all-zero qudit configuration. Source: initialized and reset bond flags
in Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_bond_register_embedding_zero {d r : ℕ} (hd : 2 ≤ d) (hr : 0 < r) :
    ∃ e : Fin r ↪ (Fin (Nat.clog d r) → Fin d),
      e ⟨0, hr⟩ = fun _ ↦ ⟨0, by omega⟩ := by
  classical
  obtain ⟨e⟩ : Nonempty (Fin r ↪ (Fin (Nat.clog d r) → Fin d)) := by
    simpa only [Fintype.card_fin] using
      (nonempty_bond_register_embedding (ι := Fin r) hd)
  let z : Fin (Nat.clog d r) → Fin d := fun _ ↦ ⟨0, by omega⟩
  refine ⟨e.trans (Equiv.swap (e ⟨0, hr⟩) z).toEmbedding, ?_⟩
  exact Equiv.swap_apply_left _ _

/-- Two encoded bonds and one physical site have dimension at most
`d^3 * r * s`. Source: the leaf synthesis estimate in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem two_bond_register_dimension_le {d r s : ℕ}
    (hd : 2 ≤ d) (hr : 0 < r) (hs : 0 < s) :
    d ^ (Nat.clog d r + Nat.clog d s + 1) ≤ d ^ 3 * r * s := by
  rw [pow_succ, pow_add]
  calc
    _ ≤ ((d * r) * (d * s)) * d := Nat.mul_le_mul_right d
      (Nat.mul_le_mul (bond_register_dimension_bounds hd hr).2
        (bond_register_dimension_bounds hd hs).2)
    _ = _ := by ring

/-- Padding a leaf packet to at least two sites still fits the same bound.
Source: the pair-gate synthesis step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem leaf_packet_dimension_le {d r s : ℕ}
    (hd : 2 ≤ d) (hr : 0 < r) (hs : 0 < s) :
    d ^ max 2 (Nat.clog d r + Nat.clog d s + 1) ≤ d ^ 3 * r * s := by
  by_cases hn : 2 ≤ Nat.clog d r + Nat.clog d s + 1
  · rw [Nat.max_eq_right hn]
    exact two_bond_register_dimension_le hd hr hs
  · rw [Nat.max_eq_left (by omega)]
    calc
      d ^ 2 ≤ d ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
      _ ≤ d ^ 3 * (r * s) := le_mul_of_one_le_right (Nat.zero_le _)
        (by have := Nat.mul_pos hr hs; omega)
      _ = _ := by ring

end MPUCircuit
