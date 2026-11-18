/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.Layer

/-!
# Arbitrary bond labels and site sets

Regression checks for the single Set-valued geometry and its finite operator boundary.
Infinite labels do not require an infinite product: a layer selects finitely many bonds.
The geometry itself also permits infinite sites and infinite one-step neighbourhoods.

Discovered by `scripts/ci_lean_checks.py` through the `_regression.lean` suffix; the
Channel.Layer import transitively covers LocalCircuit and Geometry changes.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix

namespace BondGeometryRegression

private def repeatedBond (_ : ℕ) : Finset (Fin 2) := {0, 1}

private noncomputable def selectedLayer (d : ℕ) : BondLayer d repeatedBond where
  bonds := {37}
  gate := fun _ ↦ 1
  gate_mem_unitary := fun _ _ ↦ one_mem _
  gate_mem_supportedOperators := fun _ _ ↦ one_mem _
  pairwiseDisjoint := by simp

open Classical in
example (d : ℕ) (L : BondLayer d repeatedBond)
    (X : Finset (Fin 2)) (A : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
    (hA : A ∈ ManyBody.supportedOperators (fun _ : Fin 2 ↦ Fin d) X) :
    star L.op * A * L.op ∈ ManyBody.supportedOperators (fun _ : Fin 2 ↦ Fin d)
      (bondNeighbourhood (fun b ↦ (repeatedBond b : Set (Fin 2))) X).toFinset :=
  L.conj_op_mem_supportedOperators hA

open Classical in
example (d : ℕ) (L : BondChannelLayer d repeatedBond)
    (X : Finset (Fin 2)) (A : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
    (hA : A ∈ ManyBody.supportedOperators (fun _ : Fin 2 ↦ Fin d) X) :
    L.dual A ∈ ManyBody.supportedOperators (fun _ : Fin 2 ↦ Fin d)
      (bondNeighbourhood (fun b ↦ (repeatedBond b : Set (Fin 2))) X).toFinset :=
  L.dual_mem_supportedOperators hA

private noncomputable def selectedChannel (d : ℕ) : BondChannelLayer d repeatedBond :=
  (selectedLayer d).toChannelLayer

open Classical in
example (L : BondChannelLayer 0 repeatedBond) (X : Finset (Fin 2))
    (A : Matrix (Fin 2 → Fin 0) (Fin 2 → Fin 0) ℂ)
    (hA : A ∈ ManyBody.supportedOperators (fun _ : Fin 2 ↦ Fin 0) X) :
    L.dual A ∈ ManyBody.supportedOperators (fun _ : Fin 2 ↦ Fin 0)
      (bondNeighbourhood (fun b ↦ (repeatedBond b : Set (Fin 2))) X).toFinset :=
  L.dual_mem_supportedOperators hA

open Classical in
example (d : ℕ) (Ls : List (BondChannelLayer d repeatedBond)) (X : Finset (Fin 2))
    (A : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
    (hA : A ∈ ManyBody.supportedOperators (fun _ : Fin 2 ↦ Fin d) X) :
    channelCircuitDual Ls A ∈ ManyBody.supportedOperators (fun _ : Fin 2 ↦ Fin d)
      (lightCone (fun b ↦ (repeatedBond b : Set (Fin 2))) X Ls.length).toFinset :=
  channelCircuitDual_mem_supportedOperators_lightCone Ls hA

example :
    lightCone (fun n : ℕ ↦ ({0, n} : Set ℕ)) {0} 1 = Set.univ := by
  ext x
  simp only [lightCone_succ, lightCone_zero, Set.mem_univ, iff_true]
  exact mem_bondNeighbourhood.mpr (Or.inr ⟨x, by simp, 0, by simp, by simp⟩)

example (X : Set ℕ) (r : ℕ) :
    lightCone (fun e ↦ (edgeBond (⊤ : SimpleGraph ℕ) e : Set ℕ)) X r ⊆
      {v | ∃ x ∈ X, (⊤ : SimpleGraph ℕ).edist x v ≤ r} :=
  lightCone_edgeBond_subset X r

example (e : (⊤ : SimpleGraph ℕ).edgeSet) (n : ℕ) :
    n ∈ edgeBond (⊤ : SimpleGraph ℕ) e ↔ n ∈ (e : Sym2 ℕ) := mem_edgeBond

example (X : Set ℕ) : bondNeighbourhood (fun e : Empty ↦ nomatch e) X = X := by
  ext x
  simp [mem_bondNeighbourhood]

example (r : ℕ) : lightCone (fun _ : ℕ ↦ (Set.univ : Set Empty)) Set.univ r = Set.univ := by
  ext x
  exact x.elim

example (X : Finset (Fin 1)) (r : ℕ) :
    lightCone (fun b : Fin 1 ↦ (ringBond b : Set (Fin 1))) X r =
      (neighbourhood X r : Set (Fin 1)) := lightCone_ringBond X r

example (X : Finset (Fin 2)) (r : ℕ) :
    lightCone (fun b : Fin 2 ↦ (ringBond b : Set (Fin 2))) X r =
      (neighbourhood X r : Set (Fin 2)) := lightCone_ringBond X r

end BondGeometryRegression
