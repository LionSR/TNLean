/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.DependentNetworkColumn
import TNLean.PEPS.Defs

/-!
# Extracting one ket column from an operator tensor network

An operator tensor network carries an output and an input physical index at
every vertex. Fixing the input index separately at every vertex gives a ket
tensor network on the same graph, with the same virtual alphabet on every
edge and the same inserted bond matrices. Its contraction is the column
`σ|z⟩` of the contracted operator `σ` at the product-basis vector `|z⟩`.

Combined with the vector part of Lemma 8.1, an operator network `σ` with
`‖σ - |Ω⟩⟨Ω|‖₁ ≤ η < 1` yields a nonzero ket network, with unchanged virtual
alphabets and bond dimensions, whose normalized contraction lies within `2η`
of `Ω` up to a phase.

The extraction for the edge-dependent networks of
`TNLean.PEPS.DependentBondNetwork` is in
`TNLean.Lattice.Compression.DependentNetworkColumn`. This file treats the
tensors `TNLean.PEPS.Tensor` on a finite simple graph with edge-dependent bond
dimensions, where an operator tensor has the physical alphabet `Fin (d * d)`
read as output-input pairs. No positivity or Hermiticity of the contracted
operator is assumed.

## Main results

* `TNLean.PEPS.Approximation.exists_fixInput_stateCoeff_of_traceNorm_sub_pure_le`
  — Lemma 8.1 for operator tensors on a simple graph.

## References

Polynomial-PEPS approximation manuscript (September 24, 2026), Lemma 8.1
`lem:columns`, `07-assembly.tex`, lines 67–94, in particular the final
sentence of the statement (lines 76–77) and of the proof (lines 91–93);
openai/math commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open scoped BigOperators Matrix

namespace TNLean.PEPS.Approximation

section SimpleGraph

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- The operator contracted from an operator tensor on a finite simple graph.
The physical alphabet `Fin (d * d)` at each vertex is read as output-input
pairs through `finProdFinEquiv`.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 76–77. -/
def operatorCoeff (A : Tensor G (d * d)) : Matrix (V → Fin d) (V → Fin d) ℂ :=
  fun τ ρ ↦ stateCoeff A fun v ↦ finProdFinEquiv (τ v, ρ v)

/-- The ket tensor obtained from an operator tensor by fixing the input index
`z v` at every vertex `v`. Its bond dimensions are those of the operator tensor.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 91–92. -/
def _root_.TNLean.PEPS.Tensor.fixInput (A : Tensor G (d * d)) (z : V → Fin d) : Tensor G d where
  bondDim := A.bondDim
  component v η s := A.component v η (finProdFinEquiv (s, z v))

omit [Fintype V] in
/-- Fixing the input indices leaves every bond dimension unchanged.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 76–77. -/
@[simp]
theorem _root_.TNLean.PEPS.Tensor.bondDim_fixInput (A : Tensor G (d * d)) (z : V → Fin d) :
    (A.fixInput z).bondDim = A.bondDim :=
  rfl

/-- Fixing the input indices locally selects the corresponding entry of the
contracted operator.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 91–92. -/
theorem stateCoeff_fixInput (A : Tensor G (d * d)) (z τ : V → Fin d) :
    stateCoeff (A.fixInput z) τ = operatorCoeff A τ z :=
  rfl

/-- The state of the input-fixed tensor is the column `σ|z⟩` of the contracted
operator `σ` at the product-basis vector `|z⟩`.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 91–92. -/
theorem operatorCoeff_mulVec_single (A : Tensor G (d * d)) (z : V → Fin d) :
    operatorCoeff A *ᵥ Pi.single z 1 = stateCoeff (A.fixInput z) := by
  ext τ
  simp [stateCoeff_fixInput]

/-- **Polynomial-PEPS Lemma 8.1 for operator tensors on a simple graph.**

Let `σ` be the operator contracted from an operator tensor `A` on a finite
simple graph, and let `Ω` be a unit vector with `‖σ - |Ω⟩⟨Ω|‖₁ ≤ η < 1`, the
trace norm being evaluated along an arbitrary enumeration `e` of the product
basis. Then some product-basis input `z` gives a ket tensor `A.fixInput z`,
with the bond dimensions of `A` on every edge, whose state `ψ = σ|z⟩` is
nonzero and satisfies `‖ψ / ‖ψ‖ - e^{iθ} Ω‖ ≤ 2η` for some real `θ`.

The operator `σ` is not assumed positive or Hermitian.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 8.1 `lem:columns`,
`07-assembly.tex`, lines 67–94. -/
theorem exists_fixInput_stateCoeff_of_traceNorm_sub_pure_le (A : Tensor G (d * d))
    {n : ℕ} (e : (V → Fin d) ≃ Fin n) (Ω : EuclideanSpace ℂ (V → Fin d)) (hΩ : ‖Ω‖ = 1)
    {η : ℝ}
    (hσ : Matrix.traceNorm (Matrix.reindex e e
      (operatorCoeff A - Matrix.vecMulVec (⇑Ω) (star ⇑Ω))) ≤ η)
    (hη : η < 1) :
    ∃ z : V → Fin d, (A.fixInput z).bondDim = A.bondDim ∧
      ∃ ψ : EuclideanSpace ℂ (V → Fin d),
        (∀ τ, ψ τ = stateCoeff (A.fixInput z) τ) ∧
        ψ = Matrix.toEuclideanLin (operatorCoeff A) (EuclideanSpace.single z 1) ∧
        ψ ≠ 0 ∧
        ∃ θ : ℝ, ‖((‖ψ‖ : ℂ)⁻¹) • ψ - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * η := by
  obtain ⟨z, hz, θ, hθ⟩ :=
    exists_column_ne_zero_of_traceNorm_sub_pure_le e _ Ω hΩ hσ hη
  refine ⟨z, rfl, _, fun τ ↦ ?_, rfl, hz, θ, hθ⟩
  rw [Matrix.toEuclideanLin_single_one_apply, stateCoeff_fixInput]

end SimpleGraph

end TNLean.PEPS.Approximation
