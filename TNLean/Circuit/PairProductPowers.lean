/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.PairProduct

/-!
# Gate counts for repeated circuits

Concatenating a circuit with itself multiplies its gate count by the number
of repetitions. This is the counting step for exact amplification in
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open QuantumCircuit

open Matrix

namespace QuantumCircuit.IsPairProduct

variable {d n K : ℕ}

/-- Repeating a circuit multiplies its gate count by the number of repetitions.
Source: the amplification count in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem pow {X : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ}
    (hX : IsPairProduct d n K X) (k : ℕ) :
    IsPairProduct d n (k * K) (X ^ k) := by
  induction k with
  | zero => simpa using one 0
  | succ k ih => simpa only [pow_succ, Nat.succ_mul] using ih.mul hX

end QuantumCircuit.IsPairProduct
