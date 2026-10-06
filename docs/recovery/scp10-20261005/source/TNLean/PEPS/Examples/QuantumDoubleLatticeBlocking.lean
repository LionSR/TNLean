/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.QuantumDoubleLatticeSourceParent
import TNLean.PEPS.QuantumDoubleBlockingTransport

/-!
# The full explicit K Hamiltonian transported to the actual elementary T network

The previously derived full-space physical blocking unitary pulls the three
explicit K term families back to commuting orthogonal projectors on all original
fine physical spins. Every transported term annihilates the actual elementary T
contraction. The entire transported kernel, not merely the selected state,
corresponds exactly to the actual commuting K closure span.

Source: SCP10, arXiv:1001.3807v3, equation (7.10) and Section 7.2. The statements
are about this derived physical pullback. They do not substitute the definition
of a pullback for a coefficient comparison with separately defined original
unblocked A/B Hamiltonian terms. Coarse periods are at least three.

**Scope restriction (native simple torus):** Both periods are at least three.
See `docs/paper-gaps/rmp_peps_examples_small_torus.tex`.
-/

open scoped BigOperators Matrix

noncomputable section
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "E" => Edge (torusGraph width height)
local notation "F" => TorusVertex (width * 2) (height * 2)
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Each explicit blocked term pulled back by the actual physical blocking unitary. -/
def quantumDoubleKLatticeUnblockedTerm (j : (X ⊕ X) ⊕ E) : Matrix (F → G) (F → G) ℂ :=
  quantumDoubleUnblockOperator (quantumDoubleKLatticeTerm j)

/-- The complete explicit Hamiltonian pulled back to the original fine spins. -/
def quantumDoubleKLatticeUnblockedHamiltonian : Matrix (F → G) (F → G) ℂ :=
  quantumDoubleUnblockOperator (quantumDoubleKLatticeHamiltonian (G := G))

/-- The full pullback is exactly the sum of the individually transported terms. -/
theorem quantumDoubleKLatticeUnblockedHamiltonian_eq_sum :
    quantumDoubleKLatticeUnblockedHamiltonian (width := width) (height := height) (G := G) =
      ∑ j : (X ⊕ X) ⊕ E, quantumDoubleKLatticeUnblockedTerm j := by
  simp only [quantumDoubleKLatticeUnblockedHamiltonian, quantumDoubleKLatticeHamiltonian,
    quantumDoubleUnblockOperator, Matrix.mul_sum, Matrix.sum_mul,
    quantumDoubleKLatticeUnblockedTerm]

/-- Every transported term is an orthogonal projector on the entire fine spin space. -/
theorem quantumDoubleKLatticeUnblockedTerm_isStarProjection (j : (X ⊕ X) ⊕ E) :
    IsStarProjection (quantumDoubleKLatticeUnblockedTerm (G := G) j) :=
  quantumDoubleUnblockOperator_isStarProjection _ (quantumDoubleKLatticeTerm_isStarProjection j)

/-- Every pair of transported terms commutes on the full original physical space. -/
theorem quantumDoubleKLatticeUnblockedTerm_commute (j k : (X ⊕ X) ⊕ E) :
    Commute (quantumDoubleKLatticeUnblockedTerm (G := G) j)
      (quantumDoubleKLatticeUnblockedTerm k) :=
  quantumDoubleUnblockOperator_commute _ _ (quantumDoubleKLatticeTerm_commute j k)

/-- Every transported physical term annihilates the actual source elementary T
network, by the proved scalar-one T-to-K contraction identity. -/
theorem quantumDoubleKLatticeUnblockedTerm_checkerboard (j : (X ⊕ X) ⊕ E) :
    quantumDoubleKLatticeUnblockedTerm (G := G) j *ᵥ
      (fun σ => torusBondNetwork (quantumDoublePeriodicElementarySite σ) 1 1) = 0 := by
  apply (quantumDoubleUnblockOperator_annihilates_checkerboard_iff _).mpr
  have hstate : (fun τ : QuantumDoubleKLatticeConfig width height G =>
      torusBondNetwork (fun v c =>
        quantumDoubleKTensor G c.1 c.2.1 c.2.2.1 c.2.2.2 (τ v)) 1 1) =
        quantumDoubleKLatticeContraction :=
    funext fun τ => (quantumDoubleKLatticeContraction_eq_torusBondNetwork τ).symm
  rw [hstate]
  exact quantumDoubleKLatticeTerm_contraction (G := G) j

/-- The entire transported Hamiltonian annihilates the actual elementary T state. -/
theorem quantumDoubleKLatticeUnblockedHamiltonian_checkerboard :
    quantumDoubleKLatticeUnblockedHamiltonian (width := width) (height := height) (G := G) *ᵥ
      (fun σ => torusBondNetwork (quantumDoublePeriodicElementarySite σ) 1 1) = 0 := by
  rw [quantumDoubleKLatticeUnblockedHamiltonian_eq_sum, Matrix.sum_mulVec]
  simp only [quantumDoubleKLatticeUnblockedTerm_checkerboard, Finset.sum_const_zero]

/-- The full fine-spin kernel corresponds to the actual commuting closure
span under the proved physical blocking unitary, for every input vector. -/
theorem quantumDoubleKLatticeUnblockedHamiltonian_mulVec_eq_zero_iff
    (ψ : (F → G) → ℂ) :
    quantumDoubleKLatticeUnblockedHamiltonian *ᵥ ψ = 0 ↔
      quantumDoublePhysicalBlockingMatrix *ᵥ ψ ∈
        quantumDoubleKCommutingClosureSpan (width := width) (height := height) := by
  rw [quantumDoubleKLatticeUnblockedHamiltonian, quantumDoubleUnblockOperator_mulVec_eq_zero_iff]
  change _ ∈ LinearMap.ker (Matrix.mulVecLin quantumDoubleKLatticeHamiltonian) ↔ _
  rw [ker_quantumDoubleKLatticeHamiltonian_eq_commutingClosureSpan]

end TNLean.PEPS
