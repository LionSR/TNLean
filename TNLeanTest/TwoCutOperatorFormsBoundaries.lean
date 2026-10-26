/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.TwoCutOperatorForms
import TNLean.Circuit.PairProduct

/-!
# Applications of the two-cut operator forms

The applications use a zero-dimensional chain and actual adjacent SWAP operators.
The six-site example has ordinary bond terms in each of the three regions.
-/

open Matrix QuantumCircuit
open TNLean.MPS.AreaLaw

/-- The left endpoint of an actual bond. -/
private def edgeFirst {L : ℕ} (r : Fin (L - 1)) : Fin L :=
  ⟨r.val, by omega⟩

/-- The right endpoint of an actual bond. -/
private def edgeSecond {L : ℕ} (r : Fin (L - 1)) : Fin L :=
  ⟨r.val + 1, by omega⟩

/-- The two actual endpoints are exactly the existing interval support. -/
private theorem edgePair_range {L : ℕ} (r : Fin (L - 1)) :
    Set.range (pairSites (edgeFirst r) (edgeSecond r)) =
      (interval L r.val (r.val + 2) : Set (Fin L)) := by
  rw [range_pairSites]
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
    mem_interval, Fin.ext_iff]
  change (x.val = r.val ∨ x.val = r.val + 1) ↔
    r.val ≤ x.val ∧ x.val < r.val + 2
  omega

/-- The actual adjacent SWAP at every bond of a chain. -/
private noncomputable abbrev adjacentSwapFamily (L q : ℕ) :
    Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  fun r ↦ embedOp (pairSites (edgeFirst r) (edgeSecond r)) (swapTwo (d := q))

/-- Each embedded SWAP has its actual two-site interval support. -/
private theorem adjacentSwapFamily_supported (L q : ℕ) (r : Fin (L - 1)) :
    adjacentSwapFamily L q r ∈ supportedOperators q
      (interval L r.val (r.val + 2) : Set (Fin L)) := by
  have hne : edgeFirst r ≠ edgeSecond r := by
    intro h
    have hval := congrArg Fin.val h
    change r.val = r.val + 1 at hval
    omega
  rw [← edgePair_range r]
  exact embedOp_mem_supportedOperators (pairSites_injective hne) (swapTwo (d := q))

-- Both bond operators are explicitly zero. There are no global configurations,
-- but the two valid selected bonds are still 0 and 1.
private noncomputable abbrev zeroDimensionThreeSites :=
  exists_threeSplit_edge_factors (L := 3) (q := 0)
    (fun _ : Fin 2 ↦ (0 : Matrix (Fin 3 → Fin 0) (Fin 3 → Fin 0) ℂ))
    (fun _ ↦ Submodule.zero_mem _) (0 : Fin 2) 1 (by decide)

-- These are the two actual adjacent SWAPs on three qubits. The crossing supports
-- share site 1; no commutation premise is supplied.
private noncomputable abbrev adjacentCrossingsThreeSites :=
  exists_threeSplit_edge_factors (L := 3) (q := 2)
    (adjacentSwapFamily 3 2) (adjacentSwapFamily_supported 3 2)
    (0 : Fin 2) 1 (by decide)

-- T={0,1}, E={2,3}, U={4,5}. Selected bonds 1 and 3 cross the two boundaries;
-- ordinary bonds 0, 2 and 4 lie wholly in T, E and U respectively.
private noncomputable abbrev separatedCrossingsSixSites :=
  exists_threeSplit_edge_factors (L := 6) (q := 2)
    (adjacentSwapFamily 6 2) (adjacentSwapFamily_supported 6 2)
    (1 : Fin 5) 3 (by decide)
