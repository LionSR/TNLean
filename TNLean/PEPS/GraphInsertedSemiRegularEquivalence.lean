/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphInsertedBondState
import TNLean.PEPS.CoherentMultiplicityTransport
import TNLean.PEPS.GraphSemiRegularEquivalence

/-!
# A fixed physical isometry for closed graph states with group insertions

The same bond isometry carries every group-inserted fourth-root-weighted
closed graph state to the corresponding regular inserted state. The actual
contraction formula supplies the weighted blocks and their support.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2977–3019.
**Scope restriction (chosen Fourier coordinates):** The theorem takes positive
block dimensions and an isometric coordinate change identifying their repeated
representation with the regular representation. It does not assert an
all-boundary open-state equivalence. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped Matrix BigOperators Kronecker
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G I : Type*} [Group G] [Fintype G] [DecidableEq G]
variable [Fintype I] [DecidableEq I]

/-- One full-domain physical isometry, independent of all edge insertions, carries
actual closed weighted graph states to actual regular inserted states.
Source: SCP10, Section 7, lines 2977–3019; this is an auxiliary inserted-state extension. -/
theorem exists_isometric_graphInsertedSemiRegularBondMap
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (B : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ)
    (hB : B.IsIsometry)
    (hreg : ∀ g, leftRegularMatrix G g =
      B * multiplicityRestoredRepresentation d D g * B.conjTranspose) :
    let U := blockMatrixRepresentation d D
    let W := blockFourthRootWeight d
    ∃ T : Matrix
        ((Σ i, Fin (d i) × Fin (d i)) × (Σ i, Fin (d i) × Fin (d i)))
        ((Σ i, Fin (d i)) × (Σ i, Fin (d i))) ℂ,
      T.IsIsometry ∧
      let 𝒯 := physicalProductMap (Edge Γ) (bondCoordinateMatrix B) ∘ₗ
        physicalProductMap (Edge Γ) T
      (∀ u : Edge Γ → G,
        𝒯 (graphBondRegrouping (graphInsertedBondNetwork (fun e => U (u e))
          (graphDressedAveragingSite U W))) =
        graphBondRegrouping (graphInsertedBondNetwork
          (fun e => leftRegularMatrix G (u e))
          (graphAveragingSite (leftRegularMatrix G)))) ∧
      ∀ ψ φ, star (𝒯 ψ) ⬝ᵥ 𝒯 φ = star ψ ⬝ᵥ φ := by
  classical
  let U := blockMatrixRepresentation d D
  let W := blockFourthRootWeight d
  obtain ⟨T, hT, hcoherent, hoverlap⟩ :=
    exists_isometric_coherentWeightedBlocks (E := Edge Γ) (Q := V → G)
      d (fun i g => D i g) (fun g => W ^ 2 * U g)
      (fun g => blockFourthRootWeight_sq_mul d D g) hd B hB (leftRegularMatrix G) hreg
  refine ⟨T, hT, ?_, hoverlap⟩
  intro u
  have hin : graphBondRegrouping (graphInsertedBondNetwork (fun e => U (u e))
      (graphDressedAveragingSite U W)) =
      fun β => ∑ q : V → G, (Fintype.card G : ℂ)⁻¹ ^ Fintype.card V *
        ∏ e : Edge Γ, (W ^ 2 * U (q e.1.2 * u e * (q e.1.1)⁻¹))
          (β e).1 (β e).2 := by
    funext β
    exact graphInsertedBondNetwork_dressedAveragingSite_group U W
      (blockFourthRootWeight_commute d D) u β
  have hout : graphBondRegrouping (graphInsertedBondNetwork
      (fun e => leftRegularMatrix G (u e))
      (graphAveragingSite (leftRegularMatrix G))) =
      fun β => ∑ q : V → G, (Fintype.card G : ℂ)⁻¹ ^ Fintype.card V *
        ∏ e : Edge Γ, leftRegularMatrix G (q e.1.2 * u e * (q e.1.1)⁻¹)
          (β e).1 (β e).2 := by
    funext β
    exact graphInsertedBondNetwork_averagingSite_group (leftRegularMatrix G) u β
  rw [hin, hout]
  exact hcoherent (fun _ => (Fintype.card G : ℂ)⁻¹ ^ Fintype.card V)
    (fun q e => q e.1.2 * u e * (q e.1.1)⁻¹)

end TNLean.PEPS
