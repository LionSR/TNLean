/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Symmetry.LiteralSymmetry
import TNLean.MPS.Symmetry.Defs

/-!
# Pointwise symmetry gauges for a periodic block tensor

The single-unitary corollary of arXiv:1708.00029, Section 4.2, lines 834--845,
can be applied to each element of an on-site symmetry group. This produces
unitary gauges pointwise; it does not assert a coherent group law for them.
-/

open scoped Matrix BigOperators Matrix.Norms.Operator

namespace MPSTensor

/-- Each on-site symmetry of a literal irreducible form II has the diagonal
unitary and unitary bond conjugation of the source symmetry corollary.
No equal-case fundamental theorem is assumed as an extra hypothesis.
Source: arXiv:1708.00029, Section 4.2, lines 834--845, equation `eq:symm`,
applied separately to each group element. -/
theorem exists_diagonal_unitary_of_irreducibleForm_onSiteSymmetry
    {d r : ℕ} {dim : Fin r → ℕ} {G : Type*} [Group G]
    (A : (j : Fin r) → MPSTensor d (dim j))
    (μ : Fin r → ℂ) (hμ : ∀ j, μ j ≠ 0)
    (hIrr : ∀ j, Kraus.IsIrreducibleFamily (A j))
    (hRad : ∀ j, spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin (dim j)) (Fin (dim j)) ℂ))
        (Kraus.transferMap (A j))) = 1)
    (hTP : ∀ j, IsLeftCanonical (A j))
    (u : G →* Matrix (Fin d) (Fin d) ℂ) (hu : ∀ g, (u g)ᴴ * u g = 1)
    (hSym : IsOnSiteSymmetric (toTensorFromBlocks μ A) u) :
    ∀ g, ∃ Z U : Matrix (Fin (∑ j, dim j)) (Fin (∑ j, dim j)) ℂ,
      (∃ z, Z = Matrix.diagonal z) ∧ Matrix.IsUnitaryBetween Z ∧
      Matrix.IsUnitaryBetween U ∧
      (∀ i, Z * toTensorFromBlocks μ A i = toTensorFromBlocks μ A i * Z) ∧
      SameMPV₂ (toTensorFromBlocks μ A) (fun i => Z * toTensorFromBlocks μ A i) ∧
      ∀ i, twistedTensor (toTensorFromBlocks μ A) u g i =
        Z * U * toTensorFromBlocks μ A i * Uᴴ := by
  intro g
  exact exists_diagonal_unitary_of_irreducibleForm_physical_symmetry
    A μ hμ hIrr hRad hTP (u g) (hu g) (fun N _ σ => hSym g N σ)

end MPSTensor
