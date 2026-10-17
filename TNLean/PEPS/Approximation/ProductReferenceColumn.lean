/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ProductReferenceDensityError
import TNLean.PEPS.Approximation.SquareGridColumn

/-!
# A PEPS column from a subnormalized product reference

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
individual edge dimensions. The source order, with the estimates verified for
the protocol, is followed in
`largeSizeDyadicOperatorNetwork_of_largeSizeDyadicProtocolConsequences`; see
`docs/paper-gaps/polypeps_product_reference_column.tex`.

Source: *Polynomial PEPS approximation of gapped square-grid ground states*,
§8.1, `eq:reference-junk`, `eq:protocol-density`, `eq:compressed-density`, and
Lemma 8.1 `lem:columns`, `07-assembly.tex:21–99`, immutable revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
These are original proofs; no OpenAI Lean code is copied or adapted.
-/

open scoped Matrix

noncomputable section

namespace TNLean.PEPS.Approximation.Pinned

variable {L q : ℕ} {b : Type*} [Fintype b]

/-- Fixing an input column of the supplied operator network produces a
nonzero ket with the same virtual dimensions. The two error hypotheses
refer to the same joint vector `Ψ`, before and after discarding its private
coordinates. No positivity or Hermiticity is required of the operator
network. Source: §8.1 and Lemma 8.1 `lem:columns`. -/
theorem exists_fixInput_contractPEPS_of_product_reference
    (D : ForwardEdge L → ℕ) (A : (v : Vertex L) → LocalTensor (q * q) D v)
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
    (D : ForwardEdge L → ℕ) (A : (v : Vertex L) → LocalTensor (q * q) D v)
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
