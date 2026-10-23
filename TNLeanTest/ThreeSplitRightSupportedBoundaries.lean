/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.Splitting

/-! Concrete applications of the three-region supported-operator factorization. -/

open Matrix QuantumCircuit
open TNLean.Lattice.Sheet

-- There is one global configuration when both the site set and local dimension are zero.
private noncomputable abbrev emptySitesZeroDimension :=
  exists_threeSplit_eq_reindex_one_kronecker
    (q := 0) (T := (∅ : Finset (Fin 0))) (E := ∅) (D := ∅)
    (by simp) (by simp) (one_mem_supportedOperators (d := 0) (∅ : Set (Fin 0)))

-- A nonempty zero-dimensional factor has no configurations.
private noncomputable abbrev emptyLeftConfiguration :=
  exists_threeSplit_eq_reindex_one_kronecker
    (q := 0) (T := (Finset.univ : Finset (Fin 1))) (E := ∅) (D := ∅)
    (by simp) (by simp) (Submodule.zero_mem _)

private noncomputable def rightSiteFactors (i : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  if i = 0 then 1 else Matrix.diagonal (fun j ↦ if j = 0 then 1 else -1)

-- The actual product acts on the middle and right sites and is the identity on the left site.
private noncomputable abbrev middleAndRightSites :=
  exists_threeSplit_eq_reindex_one_kronecker
    (q := 2) (T := ({0} : Finset (Fin 3))) (E := {1}) (D := {i | i ≠ 0})
    (by decide) (by simp [Set.disjoint_left])
    (rectKronecker_mem_supportedOperators (m := rightSiteFactors)
      (by intro i hi; simp_all [rightSiteFactors]))
