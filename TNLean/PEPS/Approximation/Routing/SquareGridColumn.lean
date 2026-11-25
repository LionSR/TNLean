/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Tensor.SquareLattice.SquareGridContraction
import TNLean.PEPS.Approximation.Routing.VectorColumn
import QICLean.Channel.PartialTrace.ProductReferenceDensityError

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
* `TNLean.PEPS.Approximation.Pinned.exists_peps_of_traceNorm_sub_pure_le` and
  `TNLean.PEPS.Approximation.Vector.Tensor.exists_peps_of_traceNorm_sub_pure_le`
  — the form used by the final theorem: a nonzero PEPS whose bond dimensions
  obey every bound the operator network obeys, with normalized phase error at
  most any `ε ≥ 2η`.

## References

Polynomial-PEPS approximation manuscript (September 24, 2026),
openai/math commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`:
Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 67–94, and its use in
§8.1–8.2, `07-assembly.tex`, lines 9–99; the PEPS convention and
Theorem 1.1 `thm:main`, `00-introduction.tex`, lines 20–57.

## A PEPS column from a subnormalized product reference

Let the actual joint vector `Ψ` be contractive and close to `Ω ⊗ Ξ`, where
`Ω` is the unit target and the private factor `Ξ` has norm in `[1 - δ, 1]`.
An operator network approximating the physical density of this same `Ψ`
within `κ` has error at most `κ + 2ε + 2δ` from `|Ω⟩⟨Ω|`. If that error is
less than one, a nonzero input-fixed column of the supplied network has
normalized phase error at most twice that bound. Every bond dimension and
the exact contracted column are retained.

The joint vector, its product-reference estimate, and the compressed operator
network are hypotheses. No protocol, compression theorem, or grid routing
is constructed here.

**Scope restriction (supplied product reference and square network):**
The estimates for the actual protocol vectors and its compressed operator
are assumed, and the operator network is already on the open square.
The source selects a column on the party network before routing it.
The present statement takes the square network first and preserves its
individual edge dimensions. For the protocol, the estimates are verified in
`dyadicOperatorNetworkAt_of_dyadicProtocolBoundsAt`, and the
source order of column selection then routing is carried out in
`hasPEPSApproximation_of_dyadicOperatorNetworkAt`; see
`docs/paper-gaps/polypeps_product_reference_column.tex`.

Source: *Polynomial PEPS approximation of gapped square-grid ground states*,
§8.1, `eq:reference-junk`, `eq:protocol-density`, `eq:compressed-density`, and
Lemma 8.1 `lem:columns`, `07-assembly.tex:21–99`, immutable revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
These are original proofs; no OpenAI Lean code is copied or adapted.
-/

section

open ManyBody (Edge squareLatticeGraph)

noncomputable section

open scoped BigOperators Matrix

namespace TNLean.PEPS.Approximation
open TNLean.Network

variable {L q : ℕ}

/-! ### Physical-first presentation -/

namespace Pinned

/-- The operator contracted from a physical-first operator network on the open
square. The physical index `finProdFinEquiv (τ v, ρ v)` at `v` carries the
output `τ v` and the input `ρ v`; rows are output and columns input
configurations.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 76–77;
the operator network of `07-assembly.tex`, lines 56–63. -/
def operatorMatrix (D : Edge (squareLatticeGraph L L) → ℕ)
    (A : (v : Vertex L) → LocalTensor (q * q) D v) :
    Matrix (Vertex L → Fin q) (Vertex L → Fin q) ℂ :=
  fun τ ρ ↦ contractPEPS D A fun v ↦ finProdFinEquiv (τ v, ρ v)

/-- The ket tensors obtained by fixing the input index `z v` at every vertex `v`.
They have the same edge dimensions `D` as the operator tensors.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 91–92. -/
def fixInput (D : Edge (squareLatticeGraph L L) → ℕ) (A : (v : Vertex L) → LocalTensor (q * q) D v)
    (z : Vertex L → Fin q) : (v : Vertex L) → LocalTensor q D v :=
  fun v p ↦ A v (finProdFinEquiv (p, z v))

/-- Fixing the input indices selects the corresponding entry of the contracted
operator.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 91–92. -/
theorem contractPEPS_fixInput_apply (D : Edge (squareLatticeGraph L L) → ℕ)
    (A : (v : Vertex L) → LocalTensor (q * q) D v) (z τ : Vertex L → Fin q) :
    contractPEPS D (fixInput D A z) τ = operatorMatrix D A τ z :=
  rfl

/-- The contraction of the input-fixed network on the open square is the column
`σ|z⟩` of the contracted operator `σ`.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 91–92. -/
theorem contractPEPS_fixInput (D : Edge (squareLatticeGraph L L) → ℕ)
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
theorem exists_fixInput_contractPEPS_of_traceNorm_sub_pure_le
    (D : Edge (squareLatticeGraph L L) → ℕ)
    (A : (v : Vertex L) → LocalTensor (q * q) D v) {n : ℕ} (e : (Vertex L → Fin q) ≃ Fin n)
    (Ω : State L q) (hΩ : ‖Ω‖ = 1) {η : ℝ}
    (hσ : Matrix.traceNorm (Matrix.reindex e e
      (operatorMatrix D A - Matrix.vecMulVec (⇑Ω) (star ⇑Ω))) ≤ η)
    (hη : η < 1) :
    ∃ z : Vertex L → Fin q,
      contractPEPS D (fixInput D A z) =
        Matrix.toEuclideanLin (operatorMatrix D A) (EuclideanSpace.single z 1) ∧
      contractPEPS D (fixInput D A z) ≠ 0 ∧
      ∃ θ : ℝ, ‖((‖contractPEPS D (fixInput D A z)‖ : ℂ)⁻¹) •
        contractPEPS D (fixInput D A z) - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * η :=
  Matrix.exists_eq_column_ne_zero_of_rectangularTraceNorm_sub_pure_le Ω hΩ
    (by rwa [← Matrix.rectangularTraceNorm_reindex e e, Matrix.rectangularTraceNorm_square]) hη
    (contractPEPS_fixInput D A)

/-- A nonzero contraction on the open square forces every edge dimension to be
positive: if some `D e` were zero, the sum over virtual configurations would be
empty. Theorem 1.1 `thm:main` asks for a nonzero PEPS
(`00-introduction.tex`, lines 50–51), so positive bond dimensions are part of
its conclusion and need not be assumed of the operator network. -/
theorem pos_of_contractPEPS_ne_zero (D : Edge (squareLatticeGraph L L) → ℕ)
    (A : (v : Vertex L) → LocalTensor q D v) (h : contractPEPS D A ≠ 0)
    (e : Edge (squareLatticeGraph L L)) : 0 < D e := by
  refine Nat.pos_of_ne_zero fun hD ↦ h ?_
  have : IsEmpty ((e : Edge (squareLatticeGraph L L)) → Fin (D e)) :=
    ⟨fun a ↦ absurd (a e).isLt (by omega)⟩
  ext x
  simp [contractPEPS]

/-- **Column extraction in the form used by the final theorem.**

Let an operator network on the open `L × L` square have edge dimensions
`D e ≤ B`, and let its operator `σ` satisfy `‖σ - |Ω⟩⟨Ω|‖₁ ≤ η < 1` for a unit
vector `Ω`. Then for every `ε ≥ 2η` there is a nonzero PEPS on the same grid,
with positive edge dimensions at most `B`, whose normalized contraction is
within `ε` of `Ω` up to a phase. Positivity of the edge dimensions is not a
hypothesis: it follows from the contraction being nonzero.

With `B = C L^c` and `ε = L⁻¹` the conclusion is that of Theorem 1.1 for one
lattice size. The source applies Lemma 8.1 on the party graph and then routes
the resulting ket network onto the grid (`07-assembly.tex`, lines 96–177).
To use this statement instead, the routing must be applied to the operator
network before the column is fixed; the two steps commute, since column
fixing acts sitewise on physical indices and routing leaves physical
coordinates unchanged (`07-assembly.tex`, lines 125–126 and 159–160). Sizes
`L < L_0` are handled separately in the source by an exact spanning-tree PEPS
(`07-assembly.tex`, lines 205–212) and do not pass through this statement.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 8.1 `lem:columns`,
`07-assembly.tex`, lines 67–94; the PEPS convention and the target error of
Theorem 1.1 `thm:main`, `00-introduction.tex`, lines 27–56. -/
theorem exists_peps_of_traceNorm_sub_pure_le (D : Edge (squareLatticeGraph L L) → ℕ)
    (A : (v : Vertex L) → LocalTensor (q * q) D v) {B : ℝ}
    (hDB : ∀ e, (D e : ℝ) ≤ B) {n : ℕ} (e : (Vertex L → Fin q) ≃ Fin n)
    (Ω : State L q) (hΩ : ‖Ω‖ = 1) {η ε : ℝ}
    (hσ : Matrix.traceNorm (Matrix.reindex e e
      (operatorMatrix D A - Matrix.vecMulVec (⇑Ω) (star ⇑Ω))) ≤ η)
    (hη : η < 1) (hε : 2 * η ≤ ε) :
    ∃ (D' : Edge (squareLatticeGraph L L) → ℕ) (A' : (v : Vertex L) → LocalTensor q D' v),
      (∀ e, 0 < D' e) ∧ (∀ e, (D' e : ℝ) ≤ B) ∧ contractPEPS D' A' ≠ 0 ∧
      ∃ θ : ℝ, ‖((‖contractPEPS D' A'‖⁻¹ : ℝ) : ℂ) • contractPEPS D' A' -
        Complex.exp (θ * Complex.I) • Ω‖ ≤ ε := by
  obtain ⟨z, -, hz, θ, hθ⟩ :=
    exists_fixInput_contractPEPS_of_traceNorm_sub_pure_le D A e Ω hΩ hσ hη
  refine ⟨D, fixInput D A z, pos_of_contractPEPS_ne_zero D _ hz, hDB, hz, θ, ?_⟩
  rw [Complex.ofReal_inv]
  exact hθ.trans hε

end Pinned

/-- Column fixing commutes with the transport of physical-first tensors to
native graph tensors on the square lattice; in particular every native bond
dimension is unchanged.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 76–77. -/
theorem pinnedTensorToGraphTensor_fixInput (D : Edge (squareLatticeGraph L L) → ℕ)
    (A : (v : Vertex L) → Pinned.LocalTensor (q * q) D v) (z : Vertex L → Fin q) :
    pinnedTensorToGraphTensor D (Pinned.fixInput D A z) =
      (pinnedTensorToGraphTensor D A).fixInput z :=
  rfl

/-- The operator of a physical-first operator network is the operator of its
native graph tensor.

Polynomial-PEPS Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 76–77. -/
theorem operatorCoeff_pinnedTensorToGraphTensor (D : Edge (squareLatticeGraph L L) → ℕ)
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
  obtain ⟨z, h⟩ :=
    Matrix.exists_eq_column_ne_zero_of_rectangularTraceNorm_sub_pure_le Ω hΩ
      (by rwa [← Matrix.rectangularTraceNorm_reindex e e, Matrix.rectangularTraceNorm_square]) hη
      (Tensor.contract_fixInput P)
  exact ⟨z, rfl, h⟩

/-- **Column extraction in the form used by the final theorem, virtual-first
presentation.**

If the bond dimensions of an operator tensor `P` on the open `L × L` square are
at most `B` and its operator `σ` satisfies `‖σ - |Ω⟩⟨Ω|‖₁ ≤ η < 1` for a unit
vector `Ω`, then for every `ε ≥ 2η` there is a nonzero PEPS on the same grid,
with bond dimensions at most `B`, whose normalized contraction is within `ε`
of `Ω` up to a phase. The bond dimensions are positive by the definition of
the virtual-first presentation. The remarks on routing and small sizes made
for `Pinned.exists_peps_of_traceNorm_sub_pure_le` apply unchanged.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 8.1 `lem:columns`,
`07-assembly.tex`, lines 67–94; the PEPS convention and the target error of
Theorem 1.1 `thm:main`, `00-introduction.tex`, lines 27–56. -/
theorem Tensor.exists_peps_of_traceNorm_sub_pure_le (P : Tensor (q * q) L) {B : ℝ}
    (hPB : ∀ e, (P.bondDim e : ℝ) ≤ B) {n : ℕ} (e : (Vertex L → Fin q) ≃ Fin n)
    (Ω : State q L) (hΩ : ‖Ω‖ = 1) {η ε : ℝ}
    (hσ : Matrix.traceNorm (Matrix.reindex e e
      (P.operatorMatrix - Matrix.vecMulVec (⇑Ω) (star ⇑Ω))) ≤ η)
    (hη : η < 1) (hε : 2 * η ≤ ε) :
    ∃ P' : Tensor q L, (∀ e, (P'.bondDim e : ℝ) ≤ B) ∧ P'.contract ≠ 0 ∧
      ∃ θ : ℝ, ‖((‖P'.contract‖⁻¹ : ℝ) : ℂ) • P'.contract -
        Complex.exp (θ * Complex.I) • Ω‖ ≤ ε := by
  obtain ⟨z, -, -, hz, θ, hθ⟩ :=
    P.exists_fixInput_contract_of_traceNorm_sub_pure_le e Ω hΩ hσ hη
  refine ⟨P.fixInput z, hPB, hz, θ, ?_⟩
  rw [Complex.ofReal_inv]
  exact hθ.trans hε

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
end

end

section

open ManyBody (Edge squareLatticeGraph)

open scoped Matrix

noncomputable section

namespace TNLean.PEPS.Approximation.Pinned
open TNLean.Network

variable {L q : ℕ} {b : Type*} [Fintype b]

/-- Fixing an input column of the supplied operator network produces a
nonzero ket with the same virtual dimensions. The two error hypotheses
refer to the same joint vector `Ψ`, before and after discarding its private
coordinates. No positivity or Hermiticity is required of the operator
network. Source: §8.1 and Lemma 8.1 `lem:columns`. -/
theorem exists_fixInput_contractPEPS_of_product_reference
    (D : Edge (squareLatticeGraph L L) → ℕ) (A : (v : Vertex L) → LocalTensor (q * q) D v)
    {n : ℕ} (e : (Vertex L → Fin q) ≃ Fin n)
    (Ψ : EuclideanSpace ℂ ((Vertex L → Fin q) × b))
    (Ω : State L q) (Ξ : EuclideanSpace ℂ b)
    (hΨ : ‖Ψ‖ ≤ 1) (hΩ : ‖Ω‖ = 1) (hΞ : ‖Ξ‖ ≤ 1) {ε δ κ : ℝ}
    (herror : ‖Ψ - Matrix.euclideanTensorVector Ω Ξ‖ ≤ ε)
    (hlower : 1 - δ ≤ ‖Ξ‖)
    (hcompression : Matrix.traceNorm (Matrix.reindex e e
      (operatorMatrix D A - Matrix.partialTraceRight (Matrix.euclideanOuterProduct Ψ Ψ))) ≤ κ)
    (hsmall : κ + 2 * ε + 2 * δ < 1) :
    ∃ z : Vertex L → Fin q,
      contractPEPS D (fixInput D A z) =
        Matrix.toEuclideanLin (operatorMatrix D A) (EuclideanSpace.single z 1) ∧
      contractPEPS D (fixInput D A z) ≠ 0 ∧
      ∃ θ : ℝ, ‖((‖contractPEPS D (fixInput D A z)‖ : ℂ)⁻¹) •
        contractPEPS D (fixInput D A z) - Complex.exp (θ * Complex.I) • Ω‖ ≤
          2 * (κ + 2 * ε + 2 * δ) := by
  classical
  have htrace (M : Matrix (Vertex L → Fin q) (Vertex L → Fin q) ℂ) :
      Matrix.traceNorm (Matrix.reindex e e M) = Matrix.rectangularTraceNorm M := by
    simpa only [Matrix.rectangularTraceNorm_square] using
      Matrix.rectangularTraceNorm_reindex e e M
  have hcompression' : Matrix.rectangularTraceNorm
      (operatorMatrix D A - Matrix.partialTraceRight (Matrix.euclideanOuterProduct Ψ Ψ)) ≤ κ := by
    rwa [htrace] at hcompression
  have hσ := Matrix.rectangularTraceNorm_sub_pure_le_of_product_reference
    (operatorMatrix D A) Ψ Ω Ξ hΨ hΩ hΞ herror hlower hcompression'
  apply exists_fixInput_contractPEPS_of_traceNorm_sub_pure_le D A e Ω hΩ _ hsmall
  rw [htrace]
  exact hσ

/-- The selected ket is a nonzero PEPS with the original edge dimensions,
which are therefore positive and retain every bound satisfied by the
operator network. Source: §8.1 and Lemma 8.1, in the form required for the
one-size conclusion of Theorem 1.1. -/
theorem exists_peps_of_product_reference
    (D : Edge (squareLatticeGraph L L) → ℕ) (A : (v : Vertex L) → LocalTensor (q * q) D v)
    {B : ℝ} (hDB : ∀ f, (D f : ℝ) ≤ B)
    {n : ℕ} (e : (Vertex L → Fin q) ≃ Fin n)
    (Ψ : EuclideanSpace ℂ ((Vertex L → Fin q) × b))
    (Ω : State L q) (Ξ : EuclideanSpace ℂ b)
    (hΨ : ‖Ψ‖ ≤ 1) (hΩ : ‖Ω‖ = 1) (hΞ : ‖Ξ‖ ≤ 1) {ε δ κ η : ℝ}
    (herror : ‖Ψ - Matrix.euclideanTensorVector Ω Ξ‖ ≤ ε)
    (hlower : 1 - δ ≤ ‖Ξ‖)
    (hcompression : Matrix.traceNorm (Matrix.reindex e e
      (operatorMatrix D A - Matrix.partialTraceRight (Matrix.euclideanOuterProduct Ψ Ψ))) ≤ κ)
    (hsmall : κ + 2 * ε + 2 * δ < 1) (hη : 2 * (κ + 2 * ε + 2 * δ) ≤ η) :
    ∃ z : Vertex L → Fin q,
      (∀ f, 0 < D f) ∧ (∀ f, (D f : ℝ) ≤ B) ∧
      contractPEPS D (fixInput D A z) ≠ 0 ∧
      ∃ θ : ℝ, ‖((‖contractPEPS D (fixInput D A z)‖⁻¹ : ℝ) : ℂ) •
        contractPEPS D (fixInput D A z) - Complex.exp (θ * Complex.I) • Ω‖ ≤ η := by
  obtain ⟨z, -, hz, θ, hθ⟩ := exists_fixInput_contractPEPS_of_product_reference
    D A e Ψ Ω Ξ hΨ hΩ hΞ herror hlower hcompression hsmall
  refine ⟨z, pos_of_contractPEPS_ne_zero D _ hz, hDB, hz, θ, ?_⟩
  rw [Complex.ofReal_inv]
  exact hθ.trans hη

end TNLean.PEPS.Approximation.Pinned
end

end
