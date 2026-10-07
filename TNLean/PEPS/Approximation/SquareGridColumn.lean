/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareGridContraction
import TNLean.PEPS.Approximation.VectorColumn

/-!
# One ket column of an operator network on the open square

The assembly of the polynomial PEPS approximation produces an operator tensor
network `σ` with `‖σ - |Ω⟩⟨Ω|‖₁ ≤ η < 1` and then extracts one ket column of it
(Lemma 8.1). This file instantiates that lemma on the open `L × L` square in the
two source presentations of `TNLean.PEPS.Approximation.SquareGridSource` and on
the native graph tensors they are transported to.

An operator tensor on the open square is a square-grid tensor whose physical
alphabet `Fin (q * q)` is read as output-input pairs through `finProdFinEquiv`,
the convention of `TNLean.PEPS.Tensor.fixInput`. Fixing the input index `z v`
at every vertex `v` gives a ket tensor on the same grid with the same bond
dimension on every edge, whose contraction is exactly the column `σ|z⟩`. The
operator `σ` is not assumed positive or Hermitian.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.

## Main results

* `TNLean.PEPS.Approximation.Pinned.contractPEPS_fixInput` and
  `TNLean.PEPS.Approximation.Vector.Tensor.contract_fixInput` — fixing the input
  indices sitewise gives exactly the column of the contracted operator.
* `TNLean.PEPS.Approximation.pinnedTensorToGraphTensor_fixInput` and
  `TNLean.PEPS.Approximation.vectorTensorToGraphTensor_fixInput` — column fixing
  commutes with the transport to native graph tensors.
* `TNLean.PEPS.Approximation.Pinned.exists_fixInput_contractPEPS_of_traceNorm_sub_pure_le`
  and `TNLean.PEPS.Approximation.Vector.Tensor.exists_fixInput_contract_of_traceNorm_sub_pure_le`
  — Lemma 8.1 on the open square.
* `TNLean.PEPS.Approximation.Pinned.exists_peps_of_traceNorm_sub_pure_le` — the
  form consumed by the final theorem: a nonzero PEPS whose bond dimensions obey
  every bound the operator network obeys, with normalized phase error at most
  any `ε ≥ 2η`.

## References

Polynomial-PEPS approximation manuscript (September 24, 2026),
openai/math commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`:
Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 67–94, and its use in
§8.1–8.2, `07-assembly.tex`, lines 9–99; the PEPS convention and
Theorem 1.1 `thm:main`, `00-introduction.tex`, lines 20–57.
-/

noncomputable section

open scoped BigOperators Matrix

namespace TNLean.PEPS.Approximation

variable {L q : ℕ}

/-! ### Physical-first presentation -/

namespace Pinned

/-- The operator contracted from a physical-first operator network on the open
square. The physical index `finProdFinEquiv (τ v, ρ v)` at `v` carries the
output `τ v` and the input `ρ v`; rows are output and columns input
configurations.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 76–77;
the operator network of `07-assembly.tex`, lines 56–63. -/
def operatorMatrix (D : ForwardEdge L → ℕ) (A : (v : Vertex L) → LocalTensor (q * q) D v) :
    Matrix (Vertex L → Fin q) (Vertex L → Fin q) ℂ :=
  fun τ ρ ↦ contractPEPS D A fun v ↦ finProdFinEquiv (τ v, ρ v)

/-- The ket tensors obtained by fixing the input index `z v` at every vertex `v`.
They have the same edge dimensions `D` as the operator tensors.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 91–92. -/
def fixInput (D : ForwardEdge L → ℕ) (A : (v : Vertex L) → LocalTensor (q * q) D v)
    (z : Vertex L → Fin q) : (v : Vertex L) → LocalTensor q D v :=
  fun v p ↦ A v (finProdFinEquiv (p, z v))

/-- Fixing the input indices selects the corresponding entry of the contracted
operator.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 91–92. -/
theorem contractPEPS_fixInput_apply (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → LocalTensor (q * q) D v) (z τ : Vertex L → Fin q) :
    contractPEPS D (fixInput D A z) τ = operatorMatrix D A τ z :=
  rfl

/-- The contraction of the input-fixed network on the open square is the column
`σ|z⟩` of the contracted operator `σ`.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 91–92. -/
theorem contractPEPS_fixInput (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → LocalTensor (q * q) D v) (z : Vertex L → Fin q) :
    contractPEPS D (fixInput D A z) =
      Matrix.toEuclideanLin (operatorMatrix D A) (EuclideanSpace.single z 1) := by
  ext τ
  rw [Matrix.toEuclideanLin_single_one_apply, contractPEPS_fixInput_apply]

/-- **Polynomial-PEPS Lemma 8.1 on the open square, physical-first presentation.**

Let `σ` be the operator contracted from an operator network on the open `L × L`
square with edge dimensions `D`, and let `Ω` be a unit vector with
`‖σ - |Ω⟩⟨Ω|‖₁ ≤ η < 1`, the trace norm being evaluated along an arbitrary
enumeration `e` of the product basis. Then fixing a suitable input `z`
sitewise gives ket tensors with the same edge dimensions `D`, whose contraction
`Φ = σ|z⟩` is nonzero and satisfies `‖Φ / ‖Φ‖ - e^{iθ} Ω‖ ≤ 2η` for some real
`θ`. The operator `σ` is not assumed positive or Hermitian.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 8.1 `lem:columns`,
`07-assembly.tex`, lines 67–94. -/
theorem exists_fixInput_contractPEPS_of_traceNorm_sub_pure_le (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → LocalTensor (q * q) D v) {n : ℕ} (e : (Vertex L → Fin q) ≃ Fin n)
    (Ω : State L q) (hΩ : ‖Ω‖ = 1) {η : ℝ}
    (hσ : Matrix.traceNorm (Matrix.reindex e e
      (operatorMatrix D A - Matrix.vecMulVec (⇑Ω) (star ⇑Ω))) ≤ η)
    (hη : η < 1) :
    ∃ z : Vertex L → Fin q,
      contractPEPS D (fixInput D A z) =
        Matrix.toEuclideanLin (operatorMatrix D A) (EuclideanSpace.single z 1) ∧
      contractPEPS D (fixInput D A z) ≠ 0 ∧
      ∃ θ : ℝ, ‖((‖contractPEPS D (fixInput D A z)‖ : ℂ)⁻¹) • contractPEPS D (fixInput D A z) -
        Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * η := by
  obtain ⟨z, hz, θ, hθ⟩ :=
    exists_column_ne_zero_of_traceNorm_sub_pure_le e _ Ω hΩ hσ hη
  rw [← contractPEPS_fixInput] at hz hθ
  exact ⟨z, contractPEPS_fixInput D A z, hz, θ, hθ⟩

/-- **Column extraction in the form used by the final theorem.**

Let an operator network on the open `L × L` square have positive edge
dimensions `D e ≤ B`, and let its operator `σ` satisfy
`‖σ - |Ω⟩⟨Ω|‖₁ ≤ η < 1` for a unit vector `Ω`. Then for every `ε ≥ 2η` there is
a nonzero PEPS on the same grid, with positive edge dimensions at most `B`,
whose normalized contraction is within `ε` of `Ω` up to a phase. With
`B = C L^c` and `ε = L⁻¹` this is the conclusion of Theorem 1.1, so the last
step of the assembly reduces to the bound `2η ≤ L⁻¹`.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 8.1 `lem:columns`,
`07-assembly.tex`, lines 67–99, and its use in the proof of Theorem 1.1
`thm:main`, `07-assembly.tex`, lines 203–214; the PEPS convention and the
target error of `00-introduction.tex`, lines 27–56. -/
theorem exists_peps_of_traceNorm_sub_pure_le (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → LocalTensor (q * q) D v) {B : ℝ} (hDpos : ∀ e, 0 < D e)
    (hDB : ∀ e, (D e : ℝ) ≤ B) {n : ℕ} (e : (Vertex L → Fin q) ≃ Fin n)
    (Ω : State L q) (hΩ : ‖Ω‖ = 1) {η ε : ℝ}
    (hσ : Matrix.traceNorm (Matrix.reindex e e
      (operatorMatrix D A - Matrix.vecMulVec (⇑Ω) (star ⇑Ω))) ≤ η)
    (hη : η < 1) (hε : 2 * η ≤ ε) :
    ∃ (D' : ForwardEdge L → ℕ) (A' : (v : Vertex L) → LocalTensor q D' v),
      (∀ e, 0 < D' e) ∧ (∀ e, (D' e : ℝ) ≤ B) ∧ contractPEPS D' A' ≠ 0 ∧
      ∃ θ : ℝ, ‖((‖contractPEPS D' A'‖⁻¹ : ℝ) : ℂ) • contractPEPS D' A' -
        Complex.exp (θ * Complex.I) • Ω‖ ≤ ε := by
  obtain ⟨z, -, hz, θ, hθ⟩ :=
    exists_fixInput_contractPEPS_of_traceNorm_sub_pure_le D A e Ω hΩ hσ hη
  refine ⟨D, fixInput D A z, hDpos, hDB, hz, θ, ?_⟩
  rw [Complex.ofReal_inv]
  exact hθ.trans hε

end Pinned

/-- Column fixing commutes with the transport of physical-first tensors to
native graph tensors on the square lattice; in particular every native bond
dimension is unchanged.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 76–77. -/
theorem pinnedTensorToGraphTensor_fixInput (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor (q * q) D v) (z : Vertex L → Fin q) :
    pinnedTensorToGraphTensor D (Pinned.fixInput D A z) =
      (pinnedTensorToGraphTensor D A).fixInput z :=
  rfl

/-- The operator of a physical-first operator network is the operator of its
native graph tensor.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 76–77. -/
theorem operatorCoeff_pinnedTensorToGraphTensor (D : ForwardEdge L → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor (q * q) D v) :
    operatorCoeff (pinnedTensorToGraphTensor D A) = Pinned.operatorMatrix D A := by
  ext τ ρ
  exact stateCoeff_pinnedTensorToGraphTensor D A _

/-! ### Virtual-first presentation -/

namespace Vector

/-- The operator contracted from a virtual-first operator network on the open
square, with output-input pairs read through `finProdFinEquiv`.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 76–77. -/
def Tensor.operatorMatrix (P : Tensor (q * q) L) :
    Matrix (Vertex L → Fin q) (Vertex L → Fin q) ℂ :=
  fun τ ρ ↦ P.contract fun v ↦ finProdFinEquiv (τ v, ρ v)

/-- The ket tensor obtained by fixing the input index `z v` at every vertex `v`.
It keeps the bond dimensions, and hence their positivity, of the operator
tensor.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 91–92. -/
def Tensor.fixInput (P : Tensor (q * q) L) (z : Vertex L → Fin q) : Tensor q L where
  bondDim := P.bondDim
  bondDim_pos := P.bondDim_pos
  tensor v a p := P.tensor v a (finProdFinEquiv (p, z v))

/-- Fixing the input indices leaves every bond dimension unchanged.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 76–77. -/
@[simp]
theorem Tensor.bondDim_fixInput (P : Tensor (q * q) L) (z : Vertex L → Fin q) :
    (P.fixInput z).bondDim = P.bondDim :=
  rfl

/-- Fixing the input indices leaves the maximum bond dimension unchanged.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 76–77. -/
@[simp]
theorem Tensor.maxBondDim_fixInput (P : Tensor (q * q) L) (z : Vertex L → Fin q) :
    (P.fixInput z).maxBondDim = P.maxBondDim :=
  rfl

/-- Fixing the input indices selects the corresponding entry of the contracted
operator.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 91–92. -/
theorem Tensor.contract_fixInput_apply (P : Tensor (q * q) L) (z τ : Vertex L → Fin q) :
    (P.fixInput z).contract τ = P.operatorMatrix τ z :=
  rfl

/-- The contraction of the input-fixed tensor is the column `σ|z⟩` of the
contracted operator `σ`.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 91–92. -/
theorem Tensor.contract_fixInput (P : Tensor (q * q) L) (z : Vertex L → Fin q) :
    (P.fixInput z).contract =
      Matrix.toEuclideanLin P.operatorMatrix (EuclideanSpace.single z 1) := by
  ext τ
  rw [Matrix.toEuclideanLin_single_one_apply, Tensor.contract_fixInput_apply]

/-- **Polynomial-PEPS Lemma 8.1 on the open square, virtual-first presentation.**

Let `σ` be the operator contracted from an operator tensor `P` on the open
`L × L` square, and let `Ω` be a unit vector with `‖σ - |Ω⟩⟨Ω|‖₁ ≤ η < 1`, the
trace norm being evaluated along an arbitrary enumeration `e` of the product
basis. Then some input `z` gives a ket tensor `P.fixInput z`, with the bond
dimensions of `P` on every edge, whose contraction `Φ = σ|z⟩` is nonzero and
satisfies `‖Φ / ‖Φ‖ - e^{iθ} Ω‖ ≤ 2η` for some real `θ`. The operator `σ` is not
assumed positive or Hermitian.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 8.1 `lem:columns`,
`07-assembly.tex`, lines 67–94. -/
theorem Tensor.exists_fixInput_contract_of_traceNorm_sub_pure_le (P : Tensor (q * q) L)
    {n : ℕ} (e : (Vertex L → Fin q) ≃ Fin n) (Ω : State q L) (hΩ : ‖Ω‖ = 1) {η : ℝ}
    (hσ : Matrix.traceNorm (Matrix.reindex e e
      (P.operatorMatrix - Matrix.vecMulVec (⇑Ω) (star ⇑Ω))) ≤ η)
    (hη : η < 1) :
    ∃ z : Vertex L → Fin q, (P.fixInput z).bondDim = P.bondDim ∧
      (P.fixInput z).contract =
        Matrix.toEuclideanLin P.operatorMatrix (EuclideanSpace.single z 1) ∧
      (P.fixInput z).contract ≠ 0 ∧
      ∃ θ : ℝ, ‖((‖(P.fixInput z).contract‖ : ℂ)⁻¹) • (P.fixInput z).contract -
        Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * η := by
  obtain ⟨z, hz, θ, hθ⟩ :=
    exists_column_ne_zero_of_traceNorm_sub_pure_le e _ Ω hΩ hσ hη
  rw [← Tensor.contract_fixInput] at hz hθ
  exact ⟨z, rfl, Tensor.contract_fixInput P z, hz, θ, hθ⟩

end Vector

/-- Column fixing commutes with the transport of virtual-first tensors to native
graph tensors on the square lattice.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 76–77. -/
theorem vectorTensorToGraphTensor_fixInput (P : Vector.Tensor (q * q) L)
    (z : Vertex L → Fin q) :
    vectorTensorToGraphTensor (P.fixInput z) = (vectorTensorToGraphTensor P).fixInput z :=
  rfl

/-- The operator of a virtual-first operator network is the operator of its
native graph tensor.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 76–77. -/
theorem operatorCoeff_vectorTensorToGraphTensor (P : Vector.Tensor (q * q) L) :
    operatorCoeff (vectorTensorToGraphTensor P) = P.operatorMatrix := by
  ext τ ρ
  exact stateCoeff_vectorTensorToGraphTensor P _

end TNLean.PEPS.Approximation
