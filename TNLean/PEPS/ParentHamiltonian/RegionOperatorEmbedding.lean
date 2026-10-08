/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SiteEmbedding
import TNLean.PEPS.ParentHamiltonian.DependentRegionOperatorLift

/-!
# Regional operators as circuit embeddings

For a constant physical dimension, extending a regional matrix by the identity
is the circuit embedding along the inclusion of the region. The same embedding,
reindexed by the existing equivalence for full-region configurations, is the
dependent regional lift. These identities hold for arbitrary complex matrices,
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

/-- Extending a regional matrix by the identity is its circuit embedding along
the inclusion of the region. No positivity or nonzero-dimension hypothesis is needed. -/
theorem regionLocalTerm_eq_embedOp (R : Finset V)
    (H : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ) :
    regionLocalTerm R H = QuantumCircuit.embedOp (Subtype.val : R → V) H := by
  classical
  ext σ τ
  simp [regionLocalTerm, regionConfigEquiv, Matrix.one_apply,
    QuantumCircuit.embedOp_apply, agreeOff_region_iff, funext_iff, mul_ite,
    Function.comp_def]

/-- In constant physical dimension, the dependent regional lift is the circuit
embedding reindexed by full-region configurations. -/
theorem dependentRegionOperatorLift_eq_reindex_embedOp (R : Finset V)
    (H : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ) :
    dependentRegionOperatorLift (Out := fun _ => Fin d) R H =
      Matrix.reindex (fullRegionConfigEquiv d) (fullRegionConfigEquiv d)
        (QuantumCircuit.embedOp (Subtype.val : R → V) H) := by
  classical
  ext σ τ
  rw [dependentRegionOperatorLift_apply]
  simp [Matrix.reindex_apply, QuantumCircuit.embedOp_apply, agreeOff_region_iff,
    fullRegionConfigEquiv, Function.comp_def]

end TNLean.PEPS
