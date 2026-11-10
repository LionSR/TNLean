/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SiteEmbeddingOrder
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Operator norm under placement on additional sites

Placing a matrix on an injectively selected family of sites is a complex
star-algebra homomorphism. Mathlib's contractivity theorem therefore bounds
its Hilbert-space operator norm independently of the additional sites.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit

/-- Placing an operator on an injectively selected set of sites does not
increase its Hilbert-space operator norm, including zero-dimensional
configuration spaces. Auxiliary to the tensor placement in ALVV,
arXiv:1602.08828v2, `prop:Cheby-AGSP-eff`, lines 1324–1333. -/
theorem norm_embedOp_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {q : ℕ} (e : κ → ι) (he : Function.Injective e)
    (X : Matrix (κ → Fin q) (κ → Fin q) ℂ) : ‖QuantumCircuit.embedOp e X‖ ≤ ‖X‖ := by
  let phi : Matrix (κ → Fin q) (κ → Fin q) ℂ →⋆ₙₐ[ℂ]
      Matrix (ι → Fin q) (ι → Fin q) ℂ :=
    { toFun := QuantumCircuit.embedOp e
      map_zero' := by ext σ τ; simp [QuantumCircuit.embedOp_apply]
      map_add' := QuantumCircuit.embedOp_add e
      map_mul' := fun X Y ↦ (QuantumCircuit.embedOp_mul he X Y).symm
      map_smul' := QuantumCircuit.embedOp_smul e
      map_star' := fun X ↦ (QuantumCircuit.embedOp_star e X).symm }
  exact NonUnitalStarAlgHom.norm_apply_le phi X

end QuantumCircuit
