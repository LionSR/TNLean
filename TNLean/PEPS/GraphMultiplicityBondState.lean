/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphAveragingBondState
import TNLean.PEPS.TorusBlockMultiplicityState
import TNLean.PEPS.PhysicalCoherentTransport
import TNLean.PEPS.CoherentMultiplicityTransport

/-!
# Actual graph bond states and multiplicity restoration

The explicit fourth-root weights give square-root dimension weights on each
physical bond. Expanding the actual graph contraction derives its
matching-sector support. Applying the existing multiplicity-restoring map
separately on all physical bonds then gives the actual averaging-site state
of the repeated block representation. Neither support nor a global state
identity is supplied as a hypothesis.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2977–3019.
The finite-simple-graph statement requires only positive block dimensions;
irreducible representations and the group-derived Fourier data can be inserted
subsequently. No torus, connectedness, or parent-Hamiltonian hypothesis is used.

**Local fix (group-average normalization):** The site averages are normalized
by |G|, and both actual states carry the same factor |G|⁻ᴺ. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G I : Type*} [Group G] [Fintype G] [Fintype I] [DecidableEq I]

/-- The concrete fourth-root-weighted graph state has matching-sector support,
and actual multiplicity restoration gives the repeated-block averaging state. Source: SCP10,
Section 7, lines 2977–3019. -/
theorem graphBondRegrouping_blockFourthRootWeight
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) :
    let Ψ := graphBondRegrouping (Γ := Γ) (graphBondNetwork
      (graphDressedAveragingSite (blockMatrixRepresentation d D) (blockFourthRootWeight d)))
    (∃ χ, physicalProductMap (Edge Γ) (blockBondInclusion (fun i => Fin (d i))) χ = Ψ) ∧
    physicalProductMap (Edge Γ)
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i))) Ψ =
      graphBondRegrouping (graphBondNetwork (graphAveragingSite
        (multiplicityRestoredRepresentation d D))) := by
  classical
  dsimp only
  rw [graphBondRegrouping_dressedAveragingSite_coherent
    (blockMatrixRepresentation d D) (blockFourthRootWeight d)
    (blockFourthRootWeight_commute d D), graphBondRegrouping_averagingSite_coherent]
  exact coherentWeightedBlocks_support_restore (E := Edge Γ) (Q := V → G) (A := G)
    d (fun i g => D i g)
    (fun g => blockFourthRootWeight d ^ 2 * blockMatrixRepresentation d D g)
    (fun g => blockFourthRootWeight_sq_mul d D g) hd
    (fun _ : V → G => (Fintype.card G : ℂ)⁻¹ ^ Fintype.card V)
    (fun (q : V → G) (e : Edge Γ) => q e.1.2 * (q e.1.1)⁻¹)

end TNLean.PEPS
