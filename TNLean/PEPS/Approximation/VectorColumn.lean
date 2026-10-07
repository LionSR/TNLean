/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ColumnSelection
import TNLean.PEPS.DependentBondNetwork

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

Two network models are treated.

* The edge-dependent contraction on directed multigraphs of
  `TNLean.PEPS.DependentBondNetwork`, which allows parallel edges,
  heterogeneous physical spaces, edge-dependent virtual alphabets, and
  arbitrary inserted bond matrices.
* The tensors `TNLean.PEPS.Tensor` on a finite simple graph with
  edge-dependent bond dimensions, where an operator tensor has the physical
  alphabet `Fin (d * d)` read as output-input pairs.

Neither model assumes positivity or Hermiticity of the contracted operator.

## Main results

* `TNLean.PEPS.Approximation.network_fixInput` and
  `TNLean.PEPS.Approximation.operatorNetworkMatrix_mulVec_single` — fixing the
  input indices selects the column of the contracted operator.
* `TNLean.PEPS.Approximation.exists_fixInput_network_of_traceNorm_sub_pure_le`
  — Lemma 8.1 for edge-dependent operator networks.
* `TNLean.PEPS.Approximation.exists_fixInput_stateCoeff_of_traceNorm_sub_pure_le`
  — Lemma 8.1 for operator tensors on a simple graph.

## References

Polynomial-PEPS approximation manuscript (September 24, 2026), Lemma 8.1
`lem:columns`, `07-assembly.tex`, lines 67–99, in particular the final
sentence of the statement (line 78) and of the proof (lines 91–93);
openai/math commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open scoped BigOperators Matrix

namespace TNLean.PEPS.Approximation

open TNLean.PEPS.DependentBondNetwork

section Dependent

variable {Vertex Edge : Type*} (tail head : Edge → Vertex) (D : Edge → Type*)
variable [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex] [DecidableEq Edge]
  [∀ e, Fintype (D e)]
variable {Out In : Vertex → Type*}

/-- The operator contracted from an edge-dependent operator tensor network.
The local physical index at `v` is an output-input pair, and the operator has
rows indexed by output configurations and columns by input configurations.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, line 78. -/
def operatorNetworkMatrix (A : (v : Vertex) → LocalConfig tail head D v → Out v × In v → ℂ)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ) :
    Matrix ((v : Vertex) → Out v) ((v : Vertex) → In v) ℂ :=
  fun τ ρ ↦ network tail head D A B fun v ↦ (τ v, ρ v)

/-- The ket tensors obtained by fixing the input index `z v` at every vertex `v`.
The local virtual configurations, hence all virtual alphabets, are those of
the operator tensors.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 91–92. -/
def fixInput (A : (v : Vertex) → LocalConfig tail head D v → Out v × In v → ℂ)
    (z : (v : Vertex) → In v) : (v : Vertex) → LocalConfig tail head D v → Out v → ℂ :=
  fun v η s ↦ A v η (s, z v)

/-- Fixing the input index locally selects the corresponding entry of the
contracted operator, with the same graph, virtual alphabets and bond matrices.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 91–92. -/
theorem network_fixInput
    (A : (v : Vertex) → LocalConfig tail head D v → Out v × In v → ℂ)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ) (z : (v : Vertex) → In v)
    (τ : (v : Vertex) → Out v) :
    network tail head D (fixInput tail head D A z) B τ =
      operatorNetworkMatrix tail head D A B τ z :=
  rfl

/-- The contraction of the input-fixed network is the column `σ|z⟩` of the
contracted operator `σ` at the product-basis vector `|z⟩`.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 91–92. -/
theorem operatorNetworkMatrix_mulVec_single [∀ v, Fintype (In v)] [∀ v, DecidableEq (In v)]
    (A : (v : Vertex) → LocalConfig tail head D v → Out v × In v → ℂ)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ) (z : (v : Vertex) → In v) :
    (operatorNetworkMatrix tail head D A B) *ᵥ Pi.single z 1 =
      network tail head D (fixInput tail head D A z) B := by
  ext τ
  simp [Matrix.mulVec_single_one, network_fixInput]

variable {P : Vertex → Type*} [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

/-- **Polynomial-PEPS Lemma 8.1 for edge-dependent operator networks.**

Let `σ` be the operator contracted from an edge-dependent operator tensor
network on a directed multigraph, with local physical space `P v` at each
vertex, and let `Ω` be a unit vector with `‖σ - |Ω⟩⟨Ω|‖₁ ≤ η < 1`, the trace
norm being evaluated along an arbitrary enumeration `e` of the product basis.
Then fixing a suitable product-basis input `z` locally at every vertex gives a
ket network, on the same multigraph with the same virtual alphabets `D` and
bond matrices `B`, whose contraction `ψ = σ|z⟩` is nonzero and satisfies
`‖ψ / ‖ψ‖ - e^{iθ} Ω‖ ≤ 2η` for some real `θ`.

The operator `σ` is not assumed positive or Hermitian.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 8.1 `lem:columns`,
`07-assembly.tex`, lines 67–94. -/
theorem exists_fixInput_network_of_traceNorm_sub_pure_le
    (A : (v : Vertex) → LocalConfig tail head D v → P v × P v → ℂ)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ) {n : ℕ} (e : ((v : Vertex) → P v) ≃ Fin n)
    (Ω : EuclideanSpace ℂ ((v : Vertex) → P v)) (hΩ : ‖Ω‖ = 1) {η : ℝ}
    (hσ : Matrix.traceNorm (Matrix.reindex e e
      (operatorNetworkMatrix tail head D A B - Matrix.vecMulVec (⇑Ω) (star ⇑Ω))) ≤ η)
    (hη : η < 1) :
    ∃ z : (v : Vertex) → P v, ∃ ψ : EuclideanSpace ℂ ((v : Vertex) → P v),
      (∀ τ, ψ τ = network tail head D (fixInput tail head D A z) B τ) ∧
      ψ = Matrix.toEuclideanLin (operatorNetworkMatrix tail head D A B)
        (EuclideanSpace.single z 1) ∧
      ψ ≠ 0 ∧ ∃ θ : ℝ, ‖((‖ψ‖ : ℂ)⁻¹) • ψ - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * η := by
  obtain ⟨z, hz, θ, hθ⟩ :=
    exists_column_ne_zero_of_traceNorm_sub_pure_le e _ Ω hΩ hσ hη
  refine ⟨z, _, fun τ ↦ ?_, rfl, hz, θ, hθ⟩
  rw [toEuclideanLin_single_one_apply, network_fixInput]

end Dependent

section SimpleGraph

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- The operator contracted from an operator tensor on a finite simple graph.
The physical alphabet `Fin (d * d)` at each vertex is read as output-input
pairs through `finProdFinEquiv`.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, line 78. -/
def operatorCoeff (A : Tensor G (d * d)) : Matrix (V → Fin d) (V → Fin d) ℂ :=
  fun τ ρ ↦ stateCoeff A fun v ↦ finProdFinEquiv (τ v, ρ v)

/-- The ket tensor obtained from an operator tensor by fixing the input index
`z v` at every vertex `v`. Its bond dimensions are those of the operator tensor.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 91–92. -/
def Tensor.fixInput (A : Tensor G (d * d)) (z : V → Fin d) : Tensor G d where
  bondDim := A.bondDim
  component v η s := A.component v η (finProdFinEquiv (s, z v))

/-- Fixing the input indices leaves every bond dimension unchanged.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, line 78. -/
@[simp]
theorem Tensor.bondDim_fixInput (A : Tensor G (d * d)) (z : V → Fin d) :
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
  simp [Matrix.mulVec_single_one, stateCoeff_fixInput]

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
  rw [toEuclideanLin_single_one_apply, stateCoeff_fixInput]

end SimpleGraph

end TNLean.PEPS.Approximation
