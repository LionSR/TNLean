/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SiteEmbedding

/-!
# Regional operators as circuit embeddings

For a constant physical dimension, agreement of two configurations outside the inclusion of a
region is agreement at every vertex outside the region. With it, the placement of a regional
matrix is its circuit embedding along the inclusion of the region
(`QuantumCircuit.place_eq_embedOp`). The identity holds for arbitrary complex matrices,
including zero physical dimension and empty regions or ambient vertex sets.

This is an original identification of the existing operator conventions for
the polynomial-PEPS approximation manuscript cited below. The definitions
come from the regional parent construction in arXiv:2011.12127, Section IV.C.1,
lines 2003–2011, and the local gates of arXiv:2307.01696, before Theorem 1;
the comparison itself is proved here by its matrix coefficients.
-/

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V] {d : ℕ}

omit [Fintype V] [LinearOrder V] in
/-- Agreement outside the inclusion of a region is agreement at every vertex
outside that region. -/
theorem agreeOff_region_iff (R : Finset V) (σ τ : V → Fin d) :
    QuantumCircuit.AgreeOff (Subtype.val : R → V) σ τ ↔
      ∀ v, v ∉ R → σ v = τ v := by
  constructor
  · intro h v hv
    exact h v fun w hw => hv (hw ▸ w.2)
  · intro h v hv
    exact h v fun hvR => hv ⟨v, hvR⟩ rfl

end TNLean.PEPS
