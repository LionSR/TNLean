/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularRegionEntropy

/-!
# Regular isometry of an actual connected block

Contracting a connected region of regular isometric sites gives an isometric map
on the invariant boundary subspace, up to the positive scalar contributed by the
site factors and the internal cycles. The statement uses the genuine open-region
map: no Gram identity for the block is supplied as a hypothesis.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Lemma 6.2 and the
blocking discussion, `Papers/1001.3807/paper_v3.tex`, lines 1709–1716 and 1825–1880.
The positive-factor convention is that of `IsGIsometric`, documented in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`. This also applies to
regions with internal cycles or no crossing bonds.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
attribute [local instance] Representation.invertibleFintypeCardComplex

omit [DecidableEq G] in
/-- The actual blocked physical map is invariant under the regular boundary action.
Source: SCP10, virtual symmetry of a block in the blocking discussion, lines 1825–1840. -/
theorem regularOpenRegionMatrix_invariant
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ g v η s, a v (fun f => g * η f) s = a v η s)
    (R : Finset V) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) (g : G) :
    Matrix.mulVecLin (regularOpenRegionMatrix a R e) ∘ₗ
      regularBoundaryRepresentation b g = Matrix.mulVecLin (regularOpenRegionMatrix a R e) := by
  classical
  ext x σ
  simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    regularBoundaryRepresentation_apply]
  simp only [LinearMap.single_apply, Pi.single_apply, inv_smul_eq_iff]
  simpa using regularOpenRegionMatrix_translation a ha R e g σ x

omit [DecidableEq G] in
/-- Contracting an actual connected region of regular isometric sites preserves
isometry on the invariant boundary space, with its derived positive factor.
Source: SCP10, Lemma 6.2 and blocking, lines 1709–1716 and 1825–1880. -/
theorem isGIsometric_regularOpenRegionMatrix_of_connected
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    IsGIsometric (regularBoundaryRepresentation b)
      (Matrix.mulVecLin (regularOpenRegionMatrix a R e)) := by
  classical
  obtain ⟨c, hc, h⟩ := exists_positive_gram_regularOpenRegionMatrix_of_connected a ha R hR e
  apply isGIsometric_of_coordinateAdjoint_comp
    (fun g => regularOpenRegionMatrix_invariant a
      (fun g v η s => (ha v).toIsGInjective.regularSiteMap_translation g η s) R e g) hc
  apply LinearMap.toMatrix'.injective
  simp only [LinearMap.toMatrix'_comp, coordinateAdjoint, map_smul]
  simp only [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  exact h

end TNLean.PEPS
