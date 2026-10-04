/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularRegionProjectorCoordinates
import TNLean.PEPS.RegularRegionIsometry

/-!
# G-injectivity of an actual connected regular block

Local inverses expose the canonical projector contraction. In spanning-tree
coordinates, a row with identity reference, vertex, and cycle labels is a
nonzero multiple of the boundary projector. Hence the actual block is injective
on the invariant boundary space whenever its local tensors are G-injective.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Lemma 5.2 and the
blocking discussion, `Papers/1001.3807/paper_v3.tex`, lines 1300–1350 and
1825–1840. This is the regular-representation connected-region consequence;
no local isometry or block Gram identity is assumed.

**Scope restriction (regular bonds):** The source allows semi-regular virtual
representations; this connected-region result uses regular group coordinates.
The scope is documented in `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

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

private theorem regularLegProjector_numbering {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : ℕ} (e : ι ≃ Fin b) (y x : Fin b → G) :
    regularLegProjector ι (fun f => y (e f)) (fun f => x (e f)) =
      regularBoundaryProjector b y x := by
  classical
  rw [← regularLegProjector_fin b, regularLegProjector_apply, regularLegProjector_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  have h : (fun f => y (e f)) = g • (fun f => x (e f)) ↔ y = g • x := by
    change y ∘ e = (g • x) ∘ e ↔ y = g • x
    exact e.surjective.right_cancellable
  simp only [h]

private theorem canonical_boundary_row (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})
    {b : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b)
    (y x : Fin b → G) :
    regularProjectorOpenRegionMatrix R
        ((regularRegionCoordinatesEquiv R T hT htree o).symm
          (fun f => y (e f), 1, ⟨1, rfl⟩, 1)) (fun f => x (e f)) =
      (Fintype.card G : ℂ) * (Fintype.card G : ℂ)⁻¹ ^ R.card *
        regularBoundaryProjector b y x := by
  rw [regularProjectorOpenRegionMatrix_coordinates]
  simp only [ite_true, mul_one]
  rw [regularLegProjector_numbering]

omit [DecidableEq G] in
/-- An actual connected block of regular G-injective sites is G-injective
on its invariant boundary space. Internal cycles and empty boundaries are allowed.
Source: SCP10, Lemma 5.2 and its following observation, lines 1318–1358;
the regular blocking discussion, lines 1825–1840. -/
theorem isGInjective_regularOpenRegionMatrix_of_connected
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    IsGInjective (regularBoundaryRepresentation b)
      (Matrix.mulVecLin (regularOpenRegionMatrix a R e)) := by
  classical
  refine ⟨fun g => regularOpenRegionMatrix_invariant a
    (fun g v η s => (ha v).regularSiteMap_translation g η s) R e g, ?_⟩
  intro x hInv hx
  choose F hF using fun v => (ha v).exists_regularProjectorCoefficients
  have hcan := congrArg (fun M => M *ᵥ x)
    (regionPhysicalProductMatrix_mul_regularOpenRegionMatrix a F hF R e)
  rw [← Matrix.mulVec_mulVec, show regularOpenRegionMatrix a R e *ᵥ x = 0 from hx,
    Matrix.mulVec_zero] at hcan
  obtain ⟨T, hT, htree⟩ := hR.exists_isTree_le
  let o : {v : V // v ∈ R} := Classical.choice hR.nonempty
  ext y
  have hrow := congrFun hcan ((regularRegionCoordinatesEquiv R T hT htree o).symm
    (fun f => y (e f), 1, ⟨1, rfl⟩, 1))
  simp only [Pi.zero_apply, Matrix.mulVec, dotProduct,
    canonical_boundary_row R T hT htree o e y, mul_assoc, ← Finset.mul_sum] at hrow
  change 0 = (Fintype.card G : ℂ) * ((Fintype.card G : ℂ)⁻¹ ^ R.card *
    (regularBoundaryProjector b *ᵥ x) y) at hrow
  rw [regularBoundaryProjector_mulVec_of_mem_invariants b x hInv] at hrow
  have hκ : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simpa [hκ] using hrow.symm

end TNLean.PEPS
