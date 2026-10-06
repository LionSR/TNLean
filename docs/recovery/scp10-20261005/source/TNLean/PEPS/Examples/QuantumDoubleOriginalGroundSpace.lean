/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.QuantumDoubleOriginalHamiltonian

/-!
# All sectors of the original-spin quantum-double Hamiltonian

SCP10, arXiv:1001.3807v3, Section 7.2 and Theorem 5.9: the literal
original-spin Hamiltonian has the full commuting-pair sector count. Its
kernel is the span of actual source K seam closures pulled back to the
original spins. The untwisted elementary T state is explicitly nonzero.

**Scope restriction (native even torus):** fine periods are 2w,2h with w,h≥3.
See `docs/paper-gaps/rmp_peps_examples_small_torus.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
local notation "V" => TorusVertex width height
local notation "F" => TorusVertex (width * 2) (height * 2)
local notation "C" => (F → G)
local notation "K" => QuantumDoubleKLatticeConfig width height G
local notation "block" => quantumDoublePhysicalBlockingEquiv
  (G := G) (width := width) (height := height)

/-- The linear physical regrouping of the full spin Hilbert space. -/
def quantumDoubleOriginalBlockingLinearEquiv : (C → ℂ) ≃ₗ[ℂ] (K → ℂ) :=
  LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) block

omit [Group G] in
/-- This coordinate equivalence is the previously derived physical blocking matrix. -/
theorem quantumDoubleOriginalBlockingLinearEquiv_apply (ψ : C → ℂ) :
    quantumDoubleOriginalBlockingLinearEquiv ψ = quantumDoublePhysicalBlockingMatrix *ᵥ ψ := by
  funext τ
  obtain ⟨σ, rfl⟩ := (block).surjective τ
  simpa [quantumDoubleOriginalBlockingLinearEquiv, LinearEquiv.piCongrLeft'_apply,
    quantumDoublePhysicalBlockingMatrix] using
      (endpointEmbeddingMatrix_mulVec_image (block).toEmbedding ψ σ).symm

variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "E" => Edge (torusGraph width height)

/-- The literal source T state has coefficient |G| on the all-identity
configuration. Its unnormalized contraction is therefore nonzero. -/
theorem quantumDoubleOriginalCheckerboard_one_coefficient :
    torusBondNetwork (quantumDoublePeriodicElementarySite
      (width := width) (height := height) (fun _ => (1 : G))) 1 1 = (Fintype.card G : ℂ) := by
  rw [torusBondNetwork_quantumDoublePeriodicElementarySite_eq_KNetwork]
  change torusBondNetwork (fun _ c => quantumDoubleKTensor G
    c.1 c.2.1 c.2.2.1 c.2.2.2 (1, 1, 1, 1)) 1 1 = (Fintype.card G : ℂ)
  rw [← quantumDoubleKLatticeContraction_eq_torusBondNetwork]
  rw [quantumDoubleKLatticeContraction_eq_card]
  simp only [quantumDoubleDualToK, Equiv.coe_fn_symm_mk]
  apply ite_eq_left
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro v
    simp
  · intro v
    simp
  · simp [IsQuantumDoubleTrivialHolonomy, quantumDoubleDualRowTransport,
      quantumDoubleDualColumnTransport, zmodTransport]

/-- The source elementary T contraction is genuinely a nonzero physical state. -/
theorem quantumDoubleOriginalCheckerboard_ne_zero :
    (fun σ : C => torusBondNetwork (quantumDoublePeriodicElementarySite σ) 1 1) ≠ 0 := by
  intro h
  have he := congrFun h (fun _ => 1)
  rw [quantumDoubleOriginalCheckerboard_one_coefficient] at he
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) he

/-- Exact transport of the entire original quantum-double kernel, not just one PEPS vector. -/
theorem map_ker_quantumDoubleOriginalHamiltonian :
    (Matrix.mulVecLin
      (quantumDoubleOriginalHamiltonian (width := width) (height := height) (G := G))).ker.map
        quantumDoubleOriginalBlockingLinearEquiv.toLinearMap =
      (Matrix.mulVecLin (quantumDoubleKLatticeHamiltonian (G := G))).ker := by
  ext χ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    change quantumDoubleKLatticeHamiltonian *ᵥ quantumDoubleOriginalBlockingLinearEquiv ψ = 0
    rw [quantumDoubleOriginalBlockingLinearEquiv_apply]
    apply (quantumDoubleUnblockOperator_mulVec_eq_zero_iff _ ψ).mp
    change quantumDoubleOriginalHamiltonian *ᵥ ψ = 0 at hψ
    simpa only [quantumDoubleOriginalHamiltonian_eq_unblocked,
      quantumDoubleKLatticeUnblockedHamiltonian] using hψ
  · intro hχ
    refine ⟨quantumDoubleOriginalBlockingLinearEquiv.symm χ, ?_,
      quantumDoubleOriginalBlockingLinearEquiv.apply_symm_apply χ⟩
    change quantumDoubleOriginalHamiltonian *ᵥ _ = 0
    rw [quantumDoubleOriginalHamiltonian_eq_unblocked, quantumDoubleKLatticeUnblockedHamiltonian,
      quantumDoubleUnblockOperator_mulVec_eq_zero_iff,
      ← quantumDoubleOriginalBlockingLinearEquiv_apply, LinearEquiv.apply_symm_apply]
    exact hχ

/-- The dimension of the full original-spin ground space is exactly the
number of simultaneous conjugacy classes of commuting pairs in G. -/
theorem finrank_ker_quantumDoubleOriginalHamiltonian :
    Module.finrank ℂ (Matrix.mulVecLin
      (quantumDoubleOriginalHamiltonian (width := width) (height := height) (G := G))).ker =
        Nat.card (CommutingPairConjugacyClass G) := by
  have h := (quantumDoubleOriginalBlockingLinearEquiv.submoduleMap
    (Matrix.mulVecLin
      (quantumDoubleOriginalHamiltonian
        (width := width) (height := height) (G := G))).ker).finrank_eq
  rw [map_ker_quantumDoubleOriginalHamiltonian, finrank_ker_quantumDoubleKLatticeHamiltonian] at h
  exact h

/-- One actual commuting K closure in the original physical coordinates. -/
def quantumDoubleOriginalClosure (g h : G) : C → ℂ :=
  quantumDoubleOriginalBlockingLinearEquiv.symm (quantumDoubleKClosure g h)

/-- The complete original physical kernel is spanned by actual commuting
closure states; neither noncontractible holonomy is set to the identity. -/
theorem ker_quantumDoubleOriginalHamiltonian_eq_span_closures :
    (Matrix.mulVecLin
      (quantumDoubleOriginalHamiltonian (width := width) (height := height) (G := G))).ker =
      Submodule.span ℂ (Set.range (fun p : {p : G × G // Commute p.1 p.2} =>
        quantumDoubleOriginalClosure (width := width) (height := height) p.1.1 p.1.2)) := by
  apply Submodule.map_injective_of_injective quantumDoubleOriginalBlockingLinearEquiv.injective
  rw [map_ker_quantumDoubleOriginalHamiltonian,
    ker_quantumDoubleKLatticeHamiltonian_eq_commutingClosureSpan,
    quantumDoubleKCommutingClosureSpan, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext p
  exact (quantumDoubleOriginalBlockingLinearEquiv.apply_symm_apply
    (quantumDoubleKClosure p.1.1 p.1.2)).symm

end TNLean.PEPS
