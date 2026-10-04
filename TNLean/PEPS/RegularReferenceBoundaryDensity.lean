/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.FixedBoundaryFactorDensity
import TNLean.Algebra.FlatDensityRenyiEntropy
import TNLean.PEPS.RegularControlledBoundaryFactor

/-!
# The fixed density in regular region coordinates

Boundary reference coordinates separate the relative boundary label from the
fixed region ancillary vector. This produces a density on the actual physical
half-edge labels, before any closure sector or coherent coefficient is chosen.
Source: SCP10, arXiv:1001.3807, lines 1840–1920 and 2043–2072.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace TNLean.PEPS

variable {V G : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable [Group G] [Fintype G] [DecidableEq G]

/-- The reference label and the internal ancillary coordinates of a region. -/
abbrev RegularReferenceRegionLabels
    (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) (o : {v : V // v ∈ R}) :=
  G × ({f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R} → G) ×
    RootedGroupLabels (G := G) o ×
    ({f : {f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R} //
      ¬ T.Adj ⟨f.1.1.1, f.2.1⟩ ⟨f.1.1.2, f.2.2⟩} → G)

noncomputable instance regularReferenceRegionLabelsFintype
    (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (o : {v : V // v ∈ R}) :
    Fintype (RegularReferenceRegionLabels (Γ := Γ) (G := G) R T o) := by
  classical
  letI : Fintype (RootedGroupLabels (G := G) o ×
      ({f : {f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R} //
        ¬ T.Adj ⟨f.1.1.1, f.2.1⟩ ⟨f.1.1.2, f.2.2⟩} → G)) := inferInstance
  exact inferInstanceAs (Fintype (G ×
    (({f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R} → G) × _)))

/-- Reorder the actual spanning-tree coordinates into a relative boundary label
and a reference-region ancillary label. -/
noncomputable def regularRegionReferenceCoordinatesEquiv
    (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    {n : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    RegionHalfEdgeConfig (Γ := Γ) G R ≃
      (Fin n → G) × G ×
        ({f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R} → G) ×
        RootedGroupLabels (G := G) o ×
        ({f : {f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R} //
          ¬ T.Adj ⟨f.1.1.1, f.2.1⟩ ⟨f.1.1.2, f.2.2⟩} → G) :=
  (regularRegionCoordinatesEquiv R T hT htree o).trans
    ((Equiv.prodCongr
      ((e.arrowCongr (Equiv.refl G)).trans (regularBoundaryRelativeEquiv n))
      (Equiv.refl _)).trans
      ((Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.refl _)).trans
        (Equiv.prodAssoc _ _ _)))

/-- The fixed normalized ancillary vector has squared norm one in the product
index type used by the physical density. -/
theorem star_dotProduct_regularReferenceRegionAncilla
    (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (o : {v : V // v ∈ R}) :
    star (regularReferenceRegionAncilla (Γ := Γ) (G := G) R T o) ⬝ᵥ
      regularReferenceRegionAncilla (Γ := Γ) R T o = 1 := by
  simpa only [dotProduct, Pi.star_apply, Fintype.sum_prod_type] using
    regularReferenceRegionAncilla_dotProduct (Γ := Γ) (G := G) R T o

/-- The common normalized physical density of a regular region boundary factor. -/
noncomputable def regularReferenceBoundaryDensity
    (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    {n : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G R) (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ :=
  (fixedBoundaryFactorDensity (D := Fin n → G)
    (regularReferenceRegionAncilla (Γ := Γ) (G := G) R T o)).submatrix
      (regularRegionReferenceCoordinatesEquiv R T hT htree o e)
      (regularRegionReferenceCoordinatesEquiv R T hT htree o e)

/-- The common density has trace one, rank equal to the relative boundary
cardinality, and a flat nonzero spectrum. -/
theorem regularReferenceBoundaryDensity_properties
    (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    {n : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    (regularReferenceBoundaryDensity (G := G) R T hT htree o e).PosSemidef ∧
      (regularReferenceBoundaryDensity (G := G) R T hT htree o e).trace = 1 ∧
      (regularReferenceBoundaryDensity (G := G) R T hT htree o e).rank = Fintype.card G ^ n ∧
      regularReferenceBoundaryDensity (G := G) R T hT htree o e *
          regularReferenceBoundaryDensity (G := G) R T hT htree o e =
        ((Fintype.card G : ℂ) ^ n)⁻¹ • regularReferenceBoundaryDensity R T hT htree o e := by
  classical
  simpa only [regularReferenceBoundaryDensity, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow] using fixedBoundaryFactorDensity_submatrix_properties
      (regularRegionReferenceCoordinatesEquiv R T hT htree o e)
      (regularReferenceRegionAncilla (Γ := Γ) (G := G) R T o)
      (star_dotProduct_regularReferenceRegionAncilla R T o)

/-- The von Neumann entropy of the fixed physical density is the boundary area
term minus one group logarithm. -/
theorem vonNeumannEntropy_regularReferenceBoundaryDensity
    (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    {n : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    vonNeumannEntropy (regularReferenceBoundaryDensity (G := G) R T hT htree o e)
        (regularReferenceBoundaryDensity_properties R T hT htree o e).1.isHermitian =
      n * Real.log (Fintype.card G : ℝ) := by
  have hp := regularReferenceBoundaryDensity_properties (G := G) R T hT htree o e
  have he := vonNeumannEntropy_of_mul_self_eq_inv_smul hp.1 hp.2.1
    (r := (Fintype.card G : ℝ) ^ n)
    (by simpa only [Complex.ofReal_pow, Complex.ofReal_natCast] using hp.2.2.2)
  simpa only [Real.log_pow] using he

/-- Every nonnegative finite Rényi order of the fixed density equals the same
boundary entropy. Source: SCP10, lines 2027–2037. -/
theorem renyiEntropy_regularReferenceBoundaryDensity
    (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    {n : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1))
    (α : ℝ) (hα : 0 ≤ α) :
    renyiEntropy (regularReferenceBoundaryDensity (G := G) R T hT htree o e)
        (regularReferenceBoundaryDensity_properties R T hT htree o e).1.isHermitian α =
      n * Real.log (Fintype.card G : ℝ) := by
  have hp := regularReferenceBoundaryDensity_properties (G := G) R T hT htree o e
  have hr : 0 < (Fintype.card G : ℝ) ^ n := pow_pos (Nat.cast_pos.mpr Fintype.card_pos) n
  have he := renyiEntropy_of_mul_self_eq_inv_smul_of_rank hp.1 hp.2.1 hr hα
    (by simpa only [Complex.ofReal_pow, Complex.ofReal_natCast] using hp.2.2.2)
    (by exact_mod_cast hp.2.2.1)
  simpa only [Real.log_pow] using he

end TNLean.PEPS
