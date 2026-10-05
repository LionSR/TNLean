/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.GInjectiveParentTransport

/-! # Regression checks for rectangular parent-space transport -/

open scoped Matrix
open TNLean.PEPS

-- The ambient physical dimension may grow; only the genuine parent range is transported.
example {V : Type*} [Fintype V] [LinearOrder V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] (A : Tensor Γ 1)
    {ι : Type*} (R : ι → Finset V) (hcover : ∀ v, ∃ i, v ∈ R i) :
    Module.finrank ℂ (regionParentGroundSpace
      (physicalDeform A (fun _ (i : Fin 2) (_ : Fin 1) => if i = 0 then 1 else 0)) R) =
      Module.finrank ℂ (regionParentGroundSpace A R) := by
  apply finrank_regionParentGroundSpace_physicalDeform_of_injOn A _ _ R hcover
  intro v x _ y _ hxy
  funext i
  fin_cases i
  have h := congrFun hxy 0
  change (∑ j : Fin 1, (if (0 : Fin 2) = 0 then (1 : ℂ) else 0) * x j) =
    ∑ j : Fin 1, (if (0 : Fin 2) = 0 then (1 : ℂ) else 0) * y j at h
  simpa using h

-- Vertex coverage cannot be omitted: no regions impose no physical support constraints.
example (A : Tensor (⊥ : SimpleGraph (Fin 1)) 1)
    (B : Tensor (⊥ : SimpleGraph (Fin 1)) 2) :
    Module.finrank ℂ (regionParentGroundSpace A (fun i : Empty => nomatch i)) ≠
      Module.finrank ℂ (regionParentGroundSpace B (fun i : Empty => nomatch i)) := by
  have empty_parent {d : ℕ} (T : Tensor (⊥ : SimpleGraph (Fin 1)) d) :
      regionParentGroundSpace T (fun i : Empty => nomatch i) = ⊤ := by
    apply top_unique
    intro ψ _
    simp only [regionParentGroundSpace, Submodule.mem_iInf]
    intro i
    exact nomatch i
  rw [empty_parent A, empty_parent B]
  simp [Module.finrank_fintype_fun_eq_card]
