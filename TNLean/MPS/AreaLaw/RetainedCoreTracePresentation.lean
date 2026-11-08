/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.RetainedCoreFamilies
import TNLean.MPS.MPDO.TraceChainOperator

/-!
# Trace presentations of actual retained cores

The supplied stacked site tensors represent each actual retained core with
one closing matrix at the same virtual dimension. This closing matrix is
chosen for the whole operator before the physical configurations.
-/

namespace MPOTensor

/-- Each actual retained core has a trace presentation using the supplied
stacked site tensors and the same virtual dimension. The closing matrix is
chosen for the whole operator, before its two physical configurations.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem exists_retainedStackCore_traceChainOperator
    {m : Type*} [Fintype m] [DecidableEq m] {L q B : ℕ}
    (R : Fin B × Fin B → Matrix m m ℂ)
    (steps : List (Matrix m m ℂ × ℂ)) (A : Fin L → MPOTensor q B)
    (t : ℕ) (i j : m) :
    ∃ C : Matrix (Fin (B ^ t)) (Fin (B ^ t)) ℂ,
      retainedStackCore R steps A t i j =
        traceChainOperator (fun v : Fin L ↦ stackedTensor (A v) t) C := by
  unfold retainedStackCore traceChainOperator
  exact ⟨_, rfl⟩

end MPOTensor
