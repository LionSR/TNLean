/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentBondCut

/-! # Regressions for unequal-dimensional labelled bonds and joint boundaries -/

noncomputable section
open scoped BigOperators
open TNLean.PEPS.DependentBondNetwork
set_option linter.hashCommand false

namespace DependentBondCutTest

-- Two separately labelled self edges at one vertex, of dimensions two and three.
private def bothEnds : Bool → Unit := fun _ ↦ ()
private abbrev dimension (e : Bool) := Fin (if e then 3 else 2)

example : Fintype.card (IncidentEndpoint bothEnds bothEnds ()) = 4 := by decide

example : Fintype.card (EndpointConfig dimension) = 36 := by decide

example : Fintype.card (CutConfig ({false} : Finset Bool) dimension) = 4 := by decide

example : Fintype.card (CutConfig Finset.univ dimension) = 36 := by decide

-- Distinct parallel edges between different vertices remain separate incidences.
example : Fintype.card (IncidentEndpoint (fun _ : Bool ↦ false)
    (fun _ ↦ true) false) = 2 := by decide

example : Fintype.card (LocalConfig (fun _ : Bool ↦ false)
    (fun _ ↦ true) dimension false) = 6 := by decide

-- The regrouping neither merges parallel self edges nor identifies their endpoints.
example (β : EndpointConfig dimension) :
    (endpointSiteEquiv bothEnds bothEnds dimension).symm
      (endpointSiteEquiv bothEnds bothEnds dimension β) = β :=
  (endpointSiteEquiv bothEnds bothEnds dimension).symm_apply_apply β

-- Identity insertions contribute a dimension factor for each independent bond.
example : network bothEnds bothEnds dimension
    (Phys := fun _ ↦ Unit) (fun _ _ _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ ()) = 6 := by
  simp only [network, bondWeight, Finset.prod_const_one, mul_one]
  rw [sum_endpoint_prod_eq_prod_sum dimension
    (fun e h t ↦ (1 : Matrix (dimension e) (dimension e) ℂ) h t)]
  norm_num [dimension, Matrix.one_apply]

-- Physical dimensions can vary independently of the virtual dimensions.
example (tail head : Bool → Bool)
    (A : (v : Bool) → LocalConfig tail head dimension v →
      Fin (if v then 5 else 7) → ℂ)
    (C : Finset Bool) (η : CutConfig C dimension)
    (σ : (v : Bool) → Fin (if v then 5 else 7)) :
    cutMap tail head dimension A C (Pi.single η 1) σ =
      network tail head dimension A (cutBondUnits dimension C η) σ :=
  cutMap_single_eq_network tail head dimension A C η σ

-- The cut range uses arbitrary joint endpoint tensors, without a rank-one condition.
example (A : (v : Unit) → LocalConfig bothEnds bothEnds dimension v → Bool → ℂ)
    (M : CutConfig Finset.univ dimension → ℂ) :
    cutMap bothEnds bothEnds dimension A Finset.univ M ∈
      cutSpace bothEnds bothEnds dimension A Finset.univ :=
  ⟨M, rfl⟩

private def correlatedBoundary (η : CutConfig (Finset.univ : Finset Bool) dimension) : ℂ :=
  if (η (⟨false, Finset.mem_univ _⟩, true)).val =
    (η (⟨true, Finset.mem_univ _⟩, true)).val then 1 else 0

private def constantBoundaryConfig (i : Fin 2) (j : Fin 3) :
    CutConfig (Finset.univ : Finset Bool) dimension
  | (⟨false, _⟩, _) => i
  | (⟨true, _⟩, _) => j

-- A concrete correlated boundary is not a product of independent bond matrices.
example : ¬ ∃ B : (e : Bool) → Matrix (dimension e) (dimension e) ℂ,
    cutBondBoundary dimension Finset.univ B = correlatedBoundary := by
  rintro ⟨B, h⟩
  have h00 := congr_fun h (constantBoundaryConfig 0 0)
  have h01 := congr_fun h (constantBoundaryConfig 0 1)
  have h11 := congr_fun h (constantBoundaryConfig 1 1)
  norm_num [cutBondBoundary, correlatedBoundary, constantBoundaryConfig] at h00 h01 h11
  rcases h01 with ht | hf
  · simp [ht] at h11
  · simp [hf] at h00

-- Empty bond alphabets are allowed and force an actual network to vanish.
example (A : (v : Unit) → LocalConfig bothEnds bothEnds (fun _ ↦ Fin 0) v → Unit → ℂ) :
    network bothEnds bothEnds (fun _ ↦ Fin 0) A (fun _ ↦ 1) (fun _ ↦ ()) = 0 := by
  simp [network]

-- Empty edge sets also remain admissible.
example (A : (v : Unit) → LocalConfig (fun e : Empty ↦ e.elim)
    (fun e : Empty ↦ e.elim) (fun _ ↦ Empty) v → Unit → ℂ)
    (ψ : (Unit → Unit) → ℂ) :
    ψ ∈ cutSpace (fun e : Empty ↦ e.elim) (fun e : Empty ↦ e.elim)
      (fun _ ↦ Empty) A ∅ ↔
      ∃ M, ∀ σ, cutCoeff (fun e : Empty ↦ e.elim) (fun e : Empty ↦ e.elim)
        (fun _ ↦ Empty) A ∅ M σ = ψ σ :=
  mem_cutSpace_iff _ _ _ _ _ _

/--
info: 'TNLean.PEPS.DependentBondNetwork.cutMap_single_eq_network' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentBondNetwork.cutMap_single_eq_network

/--
info: 'TNLean.PEPS.DependentBondNetwork.cutSpace_eq_span_single' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentBondNetwork.cutSpace_eq_span_single

end DependentBondCutTest
