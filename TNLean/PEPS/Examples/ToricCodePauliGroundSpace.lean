/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.ToricCodePauliHamiltonian

/-!
# Four physical toric-code ground-state sectors

Physical regrouping identifies the complete original Pauli kernel with
the K kernel. Pulling the four actual binary commuting closures back to
the original spins gives a spanning family, and the kernel has dimension
four. The source elementary T contraction also agrees exactly with the
previous binary checkerboard network, with no normalization scalar.

Source: SCP10, arXiv:1001.3807v3, Section 7.1, lines 2636–2748,
and Theorem 5.9. The native comparison uses fine periods 2w,2h with w,h≥3.

**Scope restriction (native even torus):** the full comparison uses fine
periods 2w,2h with w,h≥3. Small periodic lattices are not classified here.
See `docs/paper-gaps/scp10_toric_code_projector_normalization.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

/-- For Z₂, inverse equals itself, so the arrow-sensitive group elementary
tensor is exactly the source binary tensor T in additive bit coordinates. -/
theorem quantumDoubleElementaryTensor_toricCode (turned reversed : Bool)
    (η : Fin 4 → KitaevBit) (s : KitaevBit) :
    quantumDoubleElementaryTensor turned reversed (fun i => Multiplicative.ofAdd (η i))
        (Multiplicative.ofAdd s) = kitaevElementaryTensor turned η s := by
  cases reversed <;>
    simp [quantumDoubleElementaryTensor, kitaevElementaryTensor, toricCodeGroup_inv,
      ← ofAdd_add, add_comm]

variable {width height : ℕ} [NeZero width] [NeZero height]
local notation "V" => TorusVertex width height
local notation "F" => TorusVertex (width * 2) (height * 2)
local notation "C" => (F → ToricCodeGroup)
local notation "K" => QuantumDoubleKLatticeConfig width height ToricCodeGroup
local notation "block" => quantumDoublePhysicalBlockingEquiv
  (G := ToricCodeGroup) (width := width) (height := height)

/-- The complete group-basis elementary T contraction is the same binary
source PEPS, after merely writing each group element as its bit. -/
theorem torusBondNetwork_quantumDoubleElementary_toricCode (σ : C) :
    torusBondNetwork (quantumDoublePeriodicElementarySite σ) 1 1 =
      torusBondNetwork (kitaevPeriodicElementarySite
        (width := width) (height := height) (fun p => Multiplicative.toAdd (σ p))) 1 1 := by
  rw [torusBondNetwork_one, torusBondNetwork_one]
  apply Finset.sum_congr₂
  intro hb _ vb _
  apply Finset.prod_congr rfl
  intro p _
  exact quantumDoubleElementaryTensor_toricCode _ _
    ![Multiplicative.toAdd (vb p), Multiplicative.toAdd (hb p),
      Multiplicative.toAdd (vb (p.1, p.2 - 1)),
      Multiplicative.toAdd (hb (p.1 - 1, p.2))] _

/-- The linear physical regrouping of the full qubit Hilbert space. -/
def toricCodeBlockingLinearEquiv : (C → ℂ) ≃ₗ[ℂ] (K → ℂ) :=
  LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) block

/-- This coordinate equivalence is the previously derived physical blocking matrix. -/
theorem toricCodeBlockingLinearEquiv_apply (ψ : C → ℂ) :
    toricCodeBlockingLinearEquiv ψ = quantumDoublePhysicalBlockingMatrix *ᵥ ψ := by
  funext τ
  obtain ⟨σ, rfl⟩ := (block).surjective τ
  simpa [toricCodeBlockingLinearEquiv, LinearEquiv.piCongrLeft'_apply,
    quantumDoublePhysicalBlockingMatrix] using
      (endpointEmbeddingMatrix_mulVec_image (block).toEmbedding ψ σ).symm

variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "E" => Edge (torusGraph width height)

/-- The literal source T state has coefficient two on the all-zero bit
configuration. Its unnormalized contraction is therefore nonzero. -/
theorem toricCodeCheckerboard_zero_coefficient :
    torusBondNetwork (quantumDoublePeriodicElementarySite
      (width := width) (height := height) (fun _ => (1 : ToricCodeGroup))) 1 1 = 2 := by
  rw [torusBondNetwork_quantumDoublePeriodicElementarySite_eq_KNetwork]
  change torusBondNetwork (fun _ c => quantumDoubleKTensor ToricCodeGroup
    c.1 c.2.1 c.2.2.1 c.2.2.2 (1, 1, 1, 1)) 1 1 = 2
  rw [← quantumDoubleKLatticeContraction_eq_torusBondNetwork]
  rw [quantumDoubleKLatticeContraction_eq_card]
  simp only [quantumDoubleDualToK, Equiv.coe_fn_symm_mk]
  have hc : (Fintype.card ToricCodeGroup : ℂ) = 2 := by norm_num [ToricCodeGroup]
  rw [hc]
  apply ite_eq_left
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro v
    simp
  · intro v
    simp
  · simp [IsQuantumDoubleTrivialHolonomy, quantumDoubleDualRowTransport,
      quantumDoubleDualColumnTransport, zmodTransport]

/-- The source elementary T contraction is genuinely a nonzero physical state. -/
theorem toricCodeCheckerboard_ne_zero :
    (fun σ : C => torusBondNetwork (quantumDoublePeriodicElementarySite σ) 1 1) ≠ 0 := by
  intro h
  have he := congrFun h (fun _ => 1)
  rw [toricCodeCheckerboard_zero_coefficient] at he
  norm_num at he

/-- Exact transport of the entire original Pauli kernel, not just one PEPS vector. -/
theorem map_ker_toricCodePauliHamiltonian :
    (Matrix.mulVecLin (toricCodePauliHamiltonian (width := width) (height := height))).ker.map
        toricCodeBlockingLinearEquiv.toLinearMap =
      (Matrix.mulVecLin (quantumDoubleKLatticeHamiltonian (G := ToricCodeGroup))).ker := by
  ext χ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    change quantumDoubleKLatticeHamiltonian *ᵥ toricCodeBlockingLinearEquiv ψ = 0
    rw [toricCodeBlockingLinearEquiv_apply]
    apply (quantumDoubleUnblockOperator_mulVec_eq_zero_iff _ ψ).mp
    change toricCodePauliHamiltonian *ᵥ ψ = 0 at hψ
    simpa only [toricCodePauliHamiltonian_eq_unblocked,
      quantumDoubleKLatticeUnblockedHamiltonian] using hψ
  · intro hχ
    refine ⟨toricCodeBlockingLinearEquiv.symm χ, ?_,
      toricCodeBlockingLinearEquiv.apply_symm_apply χ⟩
    change toricCodePauliHamiltonian *ᵥ _ = 0
    rw [toricCodePauliHamiltonian_eq_unblocked, quantumDoubleKLatticeUnblockedHamiltonian,
      quantumDoubleUnblockOperator_mulVec_eq_zero_iff,
      ← toricCodeBlockingLinearEquiv_apply, LinearEquiv.apply_symm_apply]
    exact hχ

/-- The literal original toric-code Hamiltonian has exactly four ground-state
sectors, as an equality of complex dimensions of its full kernel. -/
theorem finrank_ker_toricCodePauliHamiltonian :
    Module.finrank ℂ (Matrix.mulVecLin
      (toricCodePauliHamiltonian (width := width) (height := height))).ker = 4 := by
  have h := (toricCodeBlockingLinearEquiv.submoduleMap
    (Matrix.mulVecLin
      (toricCodePauliHamiltonian (width := width) (height := height))).ker).finrank_eq
  rw [map_ker_toricCodePauliHamiltonian, finrank_ker_quantumDoubleKLatticeHamiltonian,
    card_commutingPairConjugacyClass_of_commGroup] at h
  simpa [ToricCodeGroup, Nat.card_eq_fintype_card] using h

/-- One actual binary commuting K closure, placed back on the original
physical qubits through the fixed bijective regrouping. -/
def toricCodePauliClosure (g h : ToricCodeGroup) : C → ℂ :=
  toricCodeBlockingLinearEquiv.symm (quantumDoubleKClosure g h)

omit [Fact (2 < width)] [Fact (2 < height)] in
private theorem binary_closureSpan :
    quantumDoubleKCommutingClosureSpan (width := width) (height := height)
      (G := ToricCodeGroup) =
      Submodule.span ℂ (Set.range (fun p : ToricCodeGroup × ToricCodeGroup =>
        quantumDoubleKClosure (width := width) (height := height) p.1 p.2)) := by
  unfold quantumDoubleKCommutingClosureSpan
  congr 1
  ext ψ
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨⟨p, Commute.all _ _⟩, rfl⟩

/-- The complete original physical ground space is the span of the four
actual closure states. The closures are not an assumed kernel basis. -/
theorem ker_toricCodePauliHamiltonian_eq_span_closures :
    (Matrix.mulVecLin (toricCodePauliHamiltonian (width := width) (height := height))).ker =
      Submodule.span ℂ (Set.range (fun p : ToricCodeGroup × ToricCodeGroup =>
        toricCodePauliClosure (width := width) (height := height) p.1 p.2)) := by
  apply Submodule.map_injective_of_injective toricCodeBlockingLinearEquiv.injective
  rw [map_ker_toricCodePauliHamiltonian,
    ker_quantumDoubleKLatticeHamiltonian_eq_commutingClosureSpan, binary_closureSpan,
    Submodule.map_span, ← Set.range_comp]
  congr 2
  funext p
  exact (toricCodeBlockingLinearEquiv.apply_symm_apply (quantumDoubleKClosure p.1 p.2)).symm

/-- Every literal Pauli term annihilates the previously formalized binary T
network, with its original physical-site orientation and exact coefficients. -/
theorem toricCodePauliTerm_binary_checkerboard (j : (V ⊕ V) ⊕ E) :
    toricCodePauliTerm j *ᵥ
      (fun σ => torusBondNetwork (kitaevPeriodicElementarySite
        (width := width) (height := height) (fun p => Multiplicative.toAdd (σ p))) 1 1) = 0 := by
  simp_rw [← torusBondNetwork_quantumDoubleElementary_toricCode]
  exact toricCodePauliTerm_checkerboard j

end TNLean.PEPS
