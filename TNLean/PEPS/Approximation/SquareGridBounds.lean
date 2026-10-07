/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
/-
Provenance ledger: docs/provenance/openai-math.d/8740-squaregridbounds.json.
Adapted from OpenAI's openai/math repository (Apache-2.0).
September 24, 2026 manuscript; PEPS definition preceding thm:main.
Changes: rename the predicates; expand phase and normalization; use exact vector equality.
Provenance-ID: 8740-state-vector-phaseerroratmost
Downstream: TNLean.PEPS.Approximation.Vector.PhaseErrorAtMost
Upstream: OAI.PolynomialPEPS.PhaseErrorAtMost
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/TensorNetwork/VectorColumn.lean#L91-L94
Provenance-ID: 8740-state-vector-tensor-maxbonddim-le-iff
Downstream: TNLean.PEPS.Approximation.Vector.Tensor.maxBondDim_le_iff
Upstream: OAI.PolynomialPEPS.maxBondDim_le_iff
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/TensorNetwork/VectorColumn.lean#L252-L255
Provenance-ID: 8740-state-pinnedtensortographtensor-normalized
Downstream: TNLean.PEPS.Approximation.pinnedTensorToGraphTensor_normalized
Upstream: OAI.PolynomialPEPS.norm_normalized
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/TensorNetwork/VectorColumn.lean#L137-L140
-/
/-
Provenance ledger: docs/provenance/openai-math.d/8740-squaregridbounds.json.
Original proofs; no upstream Lean proof text reused.
September 24, 2026 manuscript; PEPS definition preceding thm:main.
Original exact comparison for native square-grid PEPS.
Provenance-ID: 8740-state-statevector-pinnedtensortographtensor
Downstream: TNLean.PEPS.Approximation.stateVector_pinnedTensorToGraphTensor
Provenance-ID: 8740-state-statevector-vectortensortographtensor
Downstream: TNLean.PEPS.Approximation.stateVector_vectorTensorToGraphTensor
Provenance-ID: 8740-state-isometry-squaregridstate
Downstream: TNLean.PEPS.Approximation.isometry_squareGridState
Provenance-ID: 8740-state-phaseerroratmost-vectortensortographtensor
Downstream: TNLean.PEPS.Approximation.phaseErrorAtMost_vectorTensorToGraphTensor
Provenance-ID: 8740-state-vectortensortographtensor-bonddim
Downstream: TNLean.PEPS.Approximation.vectorTensorToGraphTensor_bondDim
Provenance-ID: 8740-state-maxbonddim-vectortensortographtensor
Downstream: TNLean.PEPS.Approximation.maxBondDim_vectorTensorToGraphTensor
Provenance-ID: 8740-state-pinnedtensortographtensor-bond-bounds
Downstream: TNLean.PEPS.Approximation.pinnedTensorToGraphTensor_bond_bounds
Provenance-ID: 8740-state-norm-statevector-pinnedtensortographtensor
Downstream: TNLean.PEPS.Approximation.norm_stateVector_pinnedTensorToGraphTensor
Provenance-ID: 8740-state-pinnedtensortographtensor-approximation
Downstream: TNLean.PEPS.Approximation.pinnedTensorToGraphTensor_approximation
Provenance-ID: 8740-state-vectortensortographtensor-approximation
Downstream: TNLean.PEPS.Approximation.vectorTensorToGraphTensor_approximation
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import TNLean.PEPS.Approximation.SquareGridContraction

/-!
# Preservation of PEPS bond bounds and normalized error

Conversion to a graph tensor changes neither the physical vector nor any edge
dimension. In particular, a nonzero approximation keeps its normalization and
the same phase-adjusted error. The maximum of an empty family of natural bond
dimensions is zero.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Theorem 1.1 and its preceding PEPS definition.
-/

namespace TNLean.PEPS.Approximation

noncomputable section

variable {L q : ℕ}

/-- Exact physical-first equality in the common Euclidean configuration space. -/
theorem stateVector_pinnedTensorToGraphTensor (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v) :
    WithLp.toLp 2 (stateCoeff (pinnedTensorToGraphTensor D A)) = Pinned.contractPEPS D A := by
  ext σ
  exact stateCoeff_pinnedTensorToGraphTensor D A σ

/-- Exact virtual-first equality, with physical dimension before grid size in the source. -/
theorem stateVector_vectorTensorToGraphTensor (P : Vector.Tensor q L) :
    WithLp.toLp 2 (stateCoeff (vectorTensorToGraphTensor P)) = P.contract := by
  ext σ
  exact stateCoeff_vectorTensorToGraphTensor P σ

/-- The two physical configuration spaces coincide, so their coordinate map is an isometry. -/
theorem isometry_squareGridState :
    Isometry (fun ψ : Pinned.State L q =>
      (ψ : EuclideanSpace ℂ (SquareLatticeVertex L L → Fin q))) := isometry_id

/-- The source phase-error predicate includes an actual minimizing phase. -/
def Vector.PhaseErrorAtMost (x Ω : Pinned.State L q) (ε : ℝ) : Prop :=
  ∃ θ : ℝ,
    (∀ φ : ℝ, ‖(‖x‖ : ℂ)⁻¹ • x - Complex.exp ((θ : ℂ) * Complex.I) • Ω‖ ≤
      ‖(‖x‖ : ℂ)⁻¹ • x - Complex.exp ((φ : ℂ) * Complex.I) • Ω‖) ∧
    ‖(‖x‖ : ℂ)⁻¹ • x - Complex.exp ((θ : ℂ) * Complex.I) • Ω‖ ≤ ε

/-- The complete minimizing-phase predicate is preserved, including its minimizer. -/
theorem phaseErrorAtMost_vectorTensorToGraphTensor (P : Vector.Tensor q L)
    (Ω : Pinned.State L q) (ε : ℝ) :
    Vector.PhaseErrorAtMost (WithLp.toLp 2 (stateCoeff (vectorTensorToGraphTensor P))) Ω ε ↔
      Vector.PhaseErrorAtMost P.contract Ω ε := by
  rw [stateVector_vectorTensorToGraphTensor]

/-- A bound for the maximum is exactly a bound for each source edge, even on an empty grid. -/
theorem Vector.Tensor.maxBondDim_le_iff (P : Vector.Tensor q L) (N : ℕ) :
    P.maxBondDim ≤ N ↔ ∀ e, P.bondDim e ≤ N := by
  simp [maxBondDim, Finset.sup_le_iff]

/-- Every bond of the virtual-first presentation retains its original dimension. -/
@[simp] theorem vectorTensorToGraphTensor_bondDim (P : Vector.Tensor q L)
    (e : ForwardEdge L) :
    (vectorTensorToGraphTensor P).bondDim (forwardSquareEdgeEquiv L e) = P.bondDim e := rfl

/-- Conversion preserves a maximum over edge dimensions exactly, not merely as an upper bound. -/
theorem maxBondDim_vectorTensorToGraphTensor (P : Vector.Tensor q L) :
    Finset.univ.sup (vectorTensorToGraphTensor P).bondDim = P.maxBondDim := by
  apply le_antisymm
  · simp only [Finset.sup_le_iff, Finset.mem_univ, forall_const]
    intro e
    exact Finset.le_sup (f := P.bondDim) (Finset.mem_univ ((forwardSquareEdgeEquiv L).symm e))
  · rw [P.maxBondDim_le_iff]
    intro e
    exact Finset.le_sup (f := (vectorTensorToGraphTensor P).bondDim)
      (Finset.mem_univ (forwardSquareEdgeEquiv L e))

/-- Positivity and any real per-edge bound are preserved in both directions. -/
theorem pinnedTensorToGraphTensor_bond_bounds (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v) (B : ℝ) :
    ((∀ e, 0 < (pinnedTensorToGraphTensor D A).bondDim e) ↔ ∀ e, 0 < D e) ∧
      ((∀ e, ((pinnedTensorToGraphTensor D A).bondDim e : ℝ) ≤ B) ↔
        ∀ e, (D e : ℝ) ≤ B) := by
  constructor <;> exact
    ⟨fun h e => h (forwardSquareEdgeEquiv L e),
      fun h e => h ((forwardSquareEdgeEquiv L).symm e)⟩

/-- Conversion preserves the Euclidean norm, including for zero contraction. -/
theorem norm_stateVector_pinnedTensorToGraphTensor (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v) :
    ‖WithLp.toLp 2 (stateCoeff (pinnedTensorToGraphTensor D A))‖ =
      ‖Pinned.contractPEPS D A‖ := by
  rw [stateVector_pinnedTensorToGraphTensor]

/-- A nonzero source contraction has a unit normalized native vector and exactly
the same error for every chosen phase. -/
theorem pinnedTensorToGraphTensor_normalized (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v)
    (hA : Pinned.contractPEPS D A ≠ 0) (Ω : Pinned.State L q) (θ : ℝ) :
    let Φ := WithLp.toLp 2 (stateCoeff (pinnedTensorToGraphTensor D A))
    Φ ≠ 0 ∧ ‖(‖Φ‖ : ℂ)⁻¹ • Φ‖ = 1 ∧
      ‖(‖Φ‖ : ℂ)⁻¹ • Φ - Complex.exp ((θ : ℂ) * Complex.I) • Ω‖ =
        ‖((‖Pinned.contractPEPS D A‖⁻¹ : ℝ) : ℂ) • Pinned.contractPEPS D A -
          Complex.exp ((θ : ℂ) * Complex.I) • Ω‖ := by
  dsimp only
  rw [stateVector_pinnedTensorToGraphTensor]
  refine ⟨hA, ?_, by rw [Complex.ofReal_inv]⟩
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hA)]

/-- Every physical-first approximation gives a native tensor with the same bonds,
nonzero contraction, and the same phase and error bound. -/
theorem pinnedTensorToGraphTensor_approximation (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor q D v)
    (Ω : Pinned.State L q) (B ε θ : ℝ)
    (hpos : ∀ e, 0 < D e) (hbound : ∀ e, (D e : ℝ) ≤ B)
    (hne : Pinned.contractPEPS D A ≠ 0)
    (herr : ‖((‖Pinned.contractPEPS D A‖⁻¹ : ℝ) : ℂ) • Pinned.contractPEPS D A -
      Complex.exp ((θ : ℂ) * Complex.I) • Ω‖ ≤ ε) :
    let T := pinnedTensorToGraphTensor D A
    let Φ := WithLp.toLp 2 (stateCoeff T)
    (∀ e, 0 < T.bondDim e) ∧ (∀ e, (T.bondDim e : ℝ) ≤ B) ∧ Φ ≠ 0 ∧
      ‖(‖Φ‖ : ℂ)⁻¹ • Φ - Complex.exp ((θ : ℂ) * Complex.I) • Ω‖ ≤ ε := by
  obtain ⟨hΦ, _, he⟩ := pinnedTensorToGraphTensor_normalized D A hne Ω θ
  exact ⟨(pinnedTensorToGraphTensor_bond_bounds D A B).1.mpr hpos,
    (pinnedTensorToGraphTensor_bond_bounds D A B).2.mpr hbound, hΦ, he.trans_le herr⟩

/-- A virtual-first approximation gives a native tensor with the same maximum-bond
bound and normalized phase error. The source structure supplies positivity. -/
theorem vectorTensorToGraphTensor_approximation (P : Vector.Tensor q L)
    (Ω : Pinned.State L q) (N : ℕ) (ε θ : ℝ)
    (hbound : P.maxBondDim ≤ N) (hne : P.contract ≠ 0)
    (herr : ‖(‖P.contract‖ : ℂ)⁻¹ • P.contract -
      Complex.exp ((θ : ℂ) * Complex.I) • Ω‖ ≤ ε) :
    let T := vectorTensorToGraphTensor P
    let Φ := WithLp.toLp 2 (stateCoeff T)
    (∀ e, 0 < T.bondDim e) ∧ Finset.univ.sup T.bondDim ≤ N ∧ Φ ≠ 0 ∧
      ‖(‖Φ‖ : ℂ)⁻¹ • Φ - Complex.exp ((θ : ℂ) * Complex.I) • Ω‖ ≤ ε := by
  dsimp only
  rw [maxBondDim_vectorTensorToGraphTensor, stateVector_vectorTensorToGraphTensor]
  exact ⟨fun e => P.bondDim_pos ((forwardSquareEdgeEquiv L).symm e), hbound, hne, herr⟩

end

end TNLean.PEPS.Approximation
