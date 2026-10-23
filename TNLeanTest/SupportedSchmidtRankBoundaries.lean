/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.SupportedSchmidtRank
import TNLean.Circuit.PairProduct

/-!
# Boundary applications for the supported right-factor rank bound
-/

open Matrix QuantumCircuit
open TNLean.Lattice.Sheet

-- No sites and q=0 still give one configuration, so this is the scalar identity.
-- The rank bound is 0^0=1, not zero.
private noncomputable abbrev emptySitesScalarIdentity :=
  exists_threeSplit_eq_reindex_one_kronecker_rank_le
    (q := 0) (T := (∅ : Finset (Fin 0))) (E := ∅) (D := ∅) (A := 1)
    (by simp) (by simp)
    (by simpa only [Finset.coe_empty] using
      one_mem_supportedOperators (d := 0) (∅ : Set (Fin 0)))

-- One site and q=0 have no configurations. The middle support has cardinality one,
-- so the bound is 0^2=0. The actual global operator and chosen right factor are zero.
private noncomputable abbrev emptyConfiguration :=
  exists_threeSplit_eq_reindex_one_kronecker_rank_le
    (q := 0) (T := (∅ : Finset (Fin 1))) (E := Finset.univ) (D := Finset.univ)
    (by simp) (by simp) (Submodule.zero_mem _)

-- A nonzero identity on two qubits, with an empty middle region and nonempty outer regions.
-- The intersection D∩E is empty, giving the rank bound 2^0=1.
private noncomputable abbrev emptyMiddleIdentity :=
  exists_threeSplit_eq_reindex_one_kronecker_rank_le
    (q := 2) (T := ({0} : Finset (Fin 2))) (E := ∅) (D := {1}) (A := 1)
    (by simp) (by decide)
    (by simpa only [Finset.coe_singleton] using
      one_mem_supportedOperators (d := 2) ({1} : Set (Fin 2)))

-- The genuine two-qubit SWAP crosses E={0} and U={1}; there is no left region.
-- Its support is the entire two-site set, hence D∩E={0} and the bound is four.
private noncomputable abbrev twoSiteSwap :=
  exists_threeSplit_eq_reindex_one_kronecker_rank_le
    (q := 2) (T := (∅ : Finset (Fin 2))) (E := {0}) (D := Finset.univ)
    (by simp) (by simp)
    (by
      simpa only [Finset.coe_univ] using
        mem_supportedOperators_univ (swapTwo (d := 2)))

-- This is exactly the numerical bound in the preceding theorem application.
example : (2 : ℕ) ^ (2 * ((Finset.univ : Finset (Fin 2)) ∩ {0}).card) = 4 := by
  decide
