/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.PairProduct
open QuantumCircuit

/-!
# Placing a circuit at arbitrary sites

An injective placement of a smaller register preserves the unitary of a
circuit. Its neighboring two-site gates become gates on arbitrary pairs
of the larger chain. Routing each pair by swaps gives at most `2 * n`
neighboring gates per original gate on an `n`-site chain.

This is the placement and routing step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`; the underlying swap
construction is already proved in `PairProduct`.
-/

open Matrix

namespace QuantumCircuit

variable {d m n K : ℕ}

/-- Placing a neighboring-pair circuit at arbitrary distinct sites increases
its gate count by at most the swap-routing factor `2 * n`.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem IsPairProduct.embedOp_injective (hd : 0 < d) {e : Fin m → Fin n}
    (he : Function.Injective e) {X : Matrix ((Fin m → Fin d)) ((Fin m → Fin d)) ℂ}
    (hX : IsPairProduct d m K X) :
    IsPairProduct d n (K * (2 * n)) (QuantumCircuit.embedOp e X) := by
  obtain ⟨l, hl, hg, rfl⟩ := hX
  rw [embedOp_list_prod he]
  apply IsPairProduct.mono (Nat.mul_le_mul_right (2 * n) (by simpa using hl))
  suffices IsPairProduct d n ((l.map (QuantumCircuit.embedOp e)).length * (2 * n))
      (l.map (QuantumCircuit.embedOp e)).prod by
    simpa only [List.length_map] using this
  apply IsPairProduct.list_prod
  intro Z hZ
  obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hZ
  obtain ⟨hu, p, q, hpq, hS⟩ := hg Y hY
  have hne : p ≠ q := by
    intro h
    rw [h] at hpq
    omega
  apply isPairProduct_of_mem_supportedOperators_pair hd (fun h ↦ hne (he h))
    (embedOp_mem_unitary he hu)
  simpa only [Set.image_pair] using embedOp_mem_supportedOperators_image he hS

end QuantumCircuit
