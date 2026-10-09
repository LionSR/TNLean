/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PhysicalPartition

/-!
# Completed padded rows have no unassigned sites

Every physical site of a completed row occurs in a consumed slot. This remains
true when intervening charges assigned that site first: the scheduled fill is
still consumed. The resulting lower bound on the oriented depth of the middle
uses the actual row enumeration, not a geometric sampling certificate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 106–125 and 331–337, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every nonblank site in a padded row occurs at its prescribed row and slot. -/
theorem exists_fillSlot (A : Finset V) (depth : V → ℤ) {n : ℕ} (hn : 0 < n)
    (lo hi : ℤ) (side : Bool) (q : ℕ) (x : V) (hx : x ∈ A)
    (hd : orientedDepth depth side x = initialFront lo hi side + (q : ℤ))
    (hrow : (orientedRow depth side (orientedDepth depth side x)).length ≤ n) :
    ∃ t, t / n = q ∧ t < (q + 1) * n ∧ fillSlot A depth n lo hi side t = some x := by
  have hm : x ∈ orientedRow depth side (initialFront lo hi side + (q : ℤ)) := by
    simpa only [mem_orientedRow] using hd
  obtain ⟨i, hi', hix⟩ := List.mem_iff_getElem.mp hm
  have hin : i < n := hi'.trans_le (by simpa only [hd] using hrow)
  have hdiv : (q * n + i) / n = q := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hin, Nat.zero_add]
  have hmod : (q * n + i) % n = i := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hin]
  refine ⟨q * n + i, hdiv, by simpa [Nat.add_mul] using Nat.add_lt_add_left hin (q * n), ?_⟩
  simp only [fillSlot, hdiv, hmod, List.getElem?_eq_getElem hi', hix]
  simp [hx]

/-- The `t`-th fill on a fixed side occurs at the corresponding alternating index. -/
theorem fill_at_side_index (side : Bool) (t : ℕ) :
    fillSide (2 * t + if side then 1 else 0) = side ∧
      fillCount (2 * t + if side then 1 else 0) side = t := by
  cases side <;> simp [fillSide, fillCount, Nat.add_div]

/-- Every slot counted before fill `k` was consumed at a strictly earlier fill index. -/
theorem side_index_lt {k t : ℕ} (side : Bool) (ht : t < fillCount k side) :
    2 * t + (if side then 1 else 0) < k := by
  cases side <;> simp only [fillCount, Bool.false_eq_true, ↓reduceIte] at * <;> omega

omit [Fintype V] in
/-- An initially unassigned site is on or beyond both initial nominal fronts. -/
theorem initial_middle_depth (A : Finset V) (depth : V → ℤ) (lo hi : ℤ)
    {x : V} (hx : initialPartition A depth lo hi x = none) (side : Bool) :
    x ∈ A ∧ initialFront lo hi side ≤ orientedDepth depth side x := by
  simp only [initialPartition] at hx
  split_ifs at hx with hA hlo hhi
  cases side <;> simp only [initialFront, orientedDepth, Bool.false_eq_true, ↓reduceIte]
  all_goals exact ⟨by simpa using hA, by omega⟩

/-- If a site survives every consumed fill, its row is not behind the nominal front.
The hypotheses describe precisely the initial membership and consumed slots; they
are proved for the finite history evaluator, rather than assumed as scan geometry. -/
theorem nominalFront_le_of_unconsumed (A : Finset V) (depth : V → ℤ)
    {n : ℕ} (hn : 0 < n) (lo hi : ℤ) (k : ℕ) (side : Bool) (x : V)
    (hx : initialPartition A depth lo hi x = none)
    (hrow : (orientedRow depth side (orientedDepth depth side x)).length ≤ n)
    (hconsumed : ∀ f < k,
      fillSlot A depth n lo hi (fillSide f) (fillCount f (fillSide f)) ≠ some x) :
    nominalFront n lo hi k side ≤ orientedDepth depth side x := by
  obtain ⟨hA, hbase⟩ := initial_middle_depth A depth lo hi hx side
  by_contra hfront
  let q := (orientedDepth depth side x - initialFront lo hi side).toNat
  have hq : orientedDepth depth side x = initialFront lo hi side + (q : ℤ) := by
    dsimp [q]
    omega
  obtain ⟨t, ht, htn, hslot⟩ := exists_fillSlot A depth hn lo hi side q x hA hq hrow
  have hqt : q < fillCount k side / n := by
    simp only [nominalFront] at hfront
    omega
  have htt : t < fillCount k side :=
    htn.trans_le ((Nat.mul_le_mul_right n (Nat.succ_le_of_lt hqt)).trans
      (Nat.div_mul_le_self (fillCount k side) n))
  let f := 2 * t + if side then 1 else 0
  have hf : f < k := side_index_lt side htt
  have hs := fill_at_side_index side t
  apply hconsumed f hf
  simpa only [f, hs.1, hs.2] using hslot

end TNLean.PEPS.AreaLaw.Scan
