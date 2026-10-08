/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors

Adapted predicates from openai/math (Apache-2.0), revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a, PEPSFilters/Basic.lean and
TensorNetwork/VectorColumn.lean. The phase and normalization helper definitions
are unfolded; both original error conventions are retained. The native target
is the independently written predicate in Approximation/Basic.lean. Transfer proofs are original.
-/
import TNLean.PEPS.Approximation.RegionalStates

/-!
# Transferring the source approximation constraints

These theorems convert an already supplied approximation witness. They do not
construct approximations to ground states or prove the polynomial-PEPS theorem.
-/

noncomputable section

namespace TNLean.PEPS.Approximation

namespace Pinned

/-- Adapted from `OAI.PolynomialPEPS.PinnedEntropy.HasPEPSApproximation`,
Basic.lean lines 88–95, with `phase` unfolded. -/
def HasPEPSApproximation {L q : ℕ} (Ω : State L q) (C c : ℝ) : Prop :=
  ∃ (D : ForwardEdge L → ℕ) (A : (v : Vertex L) → LocalTensor q D v),
    (∀ e, 0 < D e) ∧
    (∀ e, (D e : ℝ) ≤ C * Real.rpow (L : ℝ) c) ∧
    contractPEPS D A ≠ 0 ∧
    ∃ θ : ℝ,
      ‖((‖contractPEPS D A‖⁻¹ : ℝ) : ℂ) • contractPEPS D A -
        Complex.exp ((θ : ℂ) * Complex.I) • Ω‖ ≤ (L : ℝ)⁻¹

end Pinned

namespace Vector

/-- Adapted from `OAI.PolynomialPEPS.PhaseErrorAtMost`, VectorColumn.lean,
with `phase` and `normalized` unfolded. The minimizing-phase condition is retained. -/
def PhaseErrorAtMost {q L : ℕ} (x Ω : State q L) (ε : ℝ) : Prop :=
  ∃ θ : ℝ,
    (∀ φ : ℝ,
      ‖(‖x‖ : ℂ)⁻¹ • x - Complex.exp ((θ : ℂ) * Complex.I) • Ω‖ ≤
        ‖(‖x‖ : ℂ)⁻¹ • x - Complex.exp ((φ : ℂ) * Complex.I) • Ω‖) ∧
    ‖(‖x‖ : ℂ)⁻¹ • x - Complex.exp ((θ : ℂ) * Complex.I) • Ω‖ ≤ ε

end Vector

variable {L q : ℕ}

/-- The full minimizing-phase predicate, not only its error bound, is preserved. -/
theorem phaseErrorAtMost_vectorTensorToGraphTensor (P : Vector.Tensor q L)
    (Ω : Vector.State q L) (ε : ℝ) :
    Vector.PhaseErrorAtMost (pepsVector (vectorTensorToGraphTensor P)) Ω ε ↔
      Vector.PhaseErrorAtMost P.contract Ω ε := by
  rw [vector_vectorTensorToGraphTensor]

/-- Every physical-first source witness supplies a native approximation with identical bounds. -/
theorem hasPEPSApproximation_of_pinned {Ω : Pinned.State L q} {C c : ℝ}
    (h : Pinned.HasPEPSApproximation Ω C c) : HasPEPSApproximation C c L q Ω := by
  rcases h with ⟨D, A, hpos, hbound, hn, θ, herr⟩
  refine ⟨pinnedTensorToGraphTensor D A, ?_, ?_, ?_, θ, ?_⟩
  · intro e
    exact hpos ((forwardSquareEdgeEquiv L).symm e)
  · intro e
    exact hbound ((forwardSquareEdgeEquiv L).symm e)
  · rwa [vector_pinnedTensorToGraphTensor]
  · rwa [vector_pinnedTensorToGraphTensor]

/-- Every positive virtual-first witness transfers to the native predicate without dimension
or error loss. Its minimizing phase in particular witnesses the native existential phase. -/
theorem hasPEPSApproximation_of_vector (P : Vector.Tensor q L) {Ω : Vector.State q L}
    {C c : ℝ} (hbound : ∀ e, (P.bondDim e : ℝ) ≤ C * (L : ℝ) ^ c)
    (hn : P.contract ≠ 0) (herr : Vector.PhaseErrorAtMost P.contract Ω (L : ℝ)⁻¹) :
    HasPEPSApproximation C c L q Ω := by
  rcases herr with ⟨θ, _, herr⟩
  refine ⟨vectorTensorToGraphTensor P, vectorTensorToGraphTensor_bondDim_pos P, ?_, ?_, θ, ?_⟩
  · intro e
    exact hbound ((forwardSquareEdgeEquiv L).symm e)
  · rwa [vector_vectorTensorToGraphTensor]
  · rw [vector_vectorTensorToGraphTensor]
    simpa only [Complex.ofReal_inv] using herr

/-- A source bound on the real-valued maximum bond dimension suffices directly;
there is no rounding or replacement of the transported edge dimensions. -/
theorem hasPEPSApproximation_of_vector_max (P : Vector.Tensor q L) {Ω : Vector.State q L}
    {C c : ℝ} (hbound : (P.maxBondDim : ℝ) ≤ C * (L : ℝ) ^ c)
    (hn : P.contract ≠ 0) (herr : Vector.PhaseErrorAtMost P.contract Ω (L : ℝ)⁻¹) :
    HasPEPSApproximation C c L q Ω := by
  classical
  apply hasPEPSApproximation_of_vector P (fun e => ?_) hn herr
  have he : P.bondDim e ≤ P.maxBondDim := Finset.le_sup (Finset.mem_univ e)
  exact (Nat.cast_le.mpr he).trans hbound

end TNLean.PEPS.Approximation
