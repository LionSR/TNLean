/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.LeftSupportedSchmidtRank
import TNLean.Circuit.PairProduct

/-! Applications of the supported left-factor rank bound, including zero local dimension
and a two-site SWAP with a nonempty spectator. -/

open Matrix QuantumCircuit
open TNLean.Lattice.Sheet

-- With no sites and q=0 there is one empty configuration. The identity is a
-- nonzero scalar matrix, and the bound is 0^0=1.
private noncomputable abbrev emptySitesScalarIdentity :=
  exists_threeSplit_eq_kronecker_one_rank_le
    (q := 0) (T := (∅ : Finset (Fin 0))) (E := ∅) (D := ∅)
    (A := (1 : Matrix (Fin 0 → Fin 0) (Fin 0 → Fin 0) ℂ))
    (by simp) (by simp)
    (by simpa only [Finset.coe_empty] using
      one_mem_supportedOperators (d := 0) (∅ : Set (Fin 0)))

-- The global configuration space and the first factor are empty. The designated
-- support meets T in one site, so the theorem gives the rank bound 0^2=0.
private noncomputable abbrev emptyConfigurationNonemptyLeft :=
  exists_threeSplit_eq_kronecker_one_rank_le
    (q := 0) (T := (Finset.univ : Finset (Fin 1))) (E := ∅) (D := Finset.univ)
    (A := (0 : Matrix (Fin 1 → Fin 0) (Fin 1 → Fin 0) ℂ))
    (by simp) (by simp) (Submodule.zero_mem _)

-- T and E have one empty configuration each, whereas U contains one site of
-- dimension zero and therefore has no configurations. This checks the case in
-- which cancelling the spectator identity would be invalid. The global matrix
-- is explicitly zero and the theorem chooses a factor with rank at most 0^0=1.
private noncomputable abbrev emptySpectatorConfiguration :=
  exists_threeSplit_eq_kronecker_one_rank_le
    (q := 0) (T := (∅ : Finset (Fin 1))) (E := ∅) (D := ∅)
    (A := (0 : Matrix (Fin 1 → Fin 0) (Fin 1 → Fin 0) ℂ))
    (by simp) (by simp) (Submodule.zero_mem _)

-- An explicit nonzero diagonal operator on one qubit.
private noncomputable abbrev onsiteZ :
    Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ := by
  classical
  exact Matrix.diagonal fun σ ↦ if σ 0 = 0 then 1 else -1

-- T is empty and E is the whole one-site chain. The actual onsite operator is
-- nonzero, but the empty T factor gives the rank bound 2^0=1.
private noncomputable abbrev emptyLeftOnsite :=
  exists_threeSplit_eq_kronecker_one_rank_le
    (q := 2) (T := (∅ : Finset (Fin 1))) (E := Finset.univ) (D := Finset.univ)
    (A := onsiteZ)
    (by simp) (by simp)
    (by
      simpa only [Finset.coe_univ] using mem_supportedOperators_univ onsiteZ)

-- SWAP on sites 0 and 1 of a three-qubit chain, with site 2 as a genuine
-- spectator. It crosses T={0} and E={1}.
private noncomputable abbrev threeSiteSwap :
    Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ :=
  embedOp (pairSites (0 : Fin 3) 1) (swapTwo (d := 2))

private noncomputable abbrev threeSiteCrossingSwap :=
  exists_threeSplit_eq_kronecker_one_rank_le
    (q := 2) (T := ({0} : Finset (Fin 3))) (E := {1}) (D := {0, 1})
    (A := threeSiteSwap)
    (by decide) (by decide)
    (by
      simpa only [threeSiteSwap, range_pairSites,
        Finset.coe_insert, Finset.coe_singleton] using
        embedOp_mem_supportedOperators
          (pairSites_injective (by decide : (0 : Fin 3) ≠ 1))
          (swapTwo (d := 2)))

-- Numerical values of the actual theorem's right-hand sides; these do not
-- restate or simplify its configuration equivalences or chosen factors.
example : (0 : ℕ) ^ (2 * ((∅ : Finset (Fin 0)) ∩ ∅).card) = 1 := by
  decide

example : (0 : ℕ) ^
    (2 * ((Finset.univ : Finset (Fin 1)) ∩ Finset.univ).card) = 0 := by
  decide

example : (0 : ℕ) ^ (2 * ((∅ : Finset (Fin 1)) ∩ ∅).card) = 1 := by
  decide

example : (2 : ℕ) ^
    (2 * ((Finset.univ : Finset (Fin 1)) ∩ ∅).card) = 1 := by
  decide

example : (2 : ℕ) ^ (2 * (({0, 1} : Finset (Fin 3)) ∩ {0}).card) = 4 := by
  decide

-- The onsite data are nonzero; this is independent of any chosen factor B.
example : onsiteZ (fun _ ↦ 0) (fun _ ↦ 0) = 1 := by
  classical
  simp [onsiteZ]
