/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ProductReferenceDensityError
import TNLean.Lattice.Compression.ColumnSelection
import TNLean.Lattice.Compression.PartyNetwork

/-!
# A product-basis input column of a party network

An operator party network has the physical alphabet `Fin (q * q)` at every party, read as
output-input pairs through `finProdFinEquiv`. Its operator has rows indexed by output
configurations and columns by input configurations; each party reads its pair at its site.
Fixing the input `z` sitewise gives a ket party network with the same links and link
dimensions, whose coefficients are the column `σ|z⟩`. If `‖σ - |Ω⟩⟨Ω|‖₁ ≤ η < 1`, a column
is nonzero and within `2 η` of `Ω` after normalization, up to a phase. This is Lemma 8.1 of
the source, stated for an arbitrary finite set of parties; the routing of the column onto
the square is in `TNLean.PEPS.Approximation.PartyColumnRouting`.

## Main results

* `TNLean.Lattice.Compression.PartyNetwork.operatorCoeff`,
  `TNLean.Lattice.Compression.PartyNetwork.fixInput`: the operator of an operator party
  network and its input-fixed ket network.
* `TNLean.Lattice.Compression.PartyNetwork.exists_fixInput_of_rectangularTraceNorm_sub_pure_le`:
  Lemma 8.1 on the party network.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §8.1, Lemma 8.1 `lem:columns`,
  `07-assembly.tex:21–99`, immutable revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
  These are original proofs; no OpenAI Lean code is copied or adapted.
-/

noncomputable section

open scoped BigOperators Matrix

namespace TNLean.Lattice.Compression

namespace PartyNetwork

variable {P Λ V : Type*} [Fintype P] [Fintype Λ] [DecidableEq Λ] {q : ℕ}

/-- The operator contracted from an operator party network, each party reading its
output-input pair at its site. Rows are output configurations and columns are input
configurations.

Source: Polynomial-PEPS manuscript (Sept 24 2026), the party operator network `σ` of
`eq:compressed-density` and Lemma 8.1 `lem:columns`, `07-assembly.tex:57–78`. -/
def operatorCoeff (N : PartyNetwork P Λ (q * q)) (site : P → V) :
    Matrix (V → Fin q) (V → Fin q) ℂ :=
  fun τ ρ ↦ N.coeff site fun v ↦ finProdFinEquiv (τ v, ρ v)

/-- The ket party network obtained by fixing the input index `z (site p)` of every party
`p`. The links and their dimensions are those of the operator network.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 8.1 `lem:columns`,
`07-assembly.tex:77–78` and `91–92`. -/
def fixInput (N : PartyNetwork P Λ (q * q)) (site : P → V) (z : V → Fin q) :
    PartyNetwork P Λ q where
  dim := N.dim
  src := N.src
  tgt := N.tgt
  tensor p η s := N.tensor p η (finProdFinEquiv (s, z (site p)))

omit [Fintype P] [Fintype Λ] [DecidableEq Λ] in
/-- Fixing the input leaves every link dimension unchanged.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:77–78`. -/
@[simp]
theorem dim_fixInput (N : PartyNetwork P Λ (q * q)) (site : P → V) (z : V → Fin q) :
    (N.fixInput site z).dim = N.dim :=
  rfl

/-- The coefficients of the input-fixed network are the column `σ|z⟩`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:91–92`. -/
theorem coeff_fixInput (N : PartyNetwork P Λ (q * q)) (site : P → V) (z τ : V → Fin q) :
    (N.fixInput site z).coeff site τ = N.operatorCoeff site τ z :=
  rfl

/-- **Lemma 8.1 on the party network.** If the operator `σ` of an operator party network
satisfies `‖σ - |Ω⟩⟨Ω|‖₁ ≤ η < 1` for a unit vector `Ω`, then fixing a suitable
product-basis input `z` gives a ket party network with the same link dimensions, whose
coefficient vector `ψ = σ|z⟩` is nonzero and satisfies `‖ψ / ‖ψ‖ - e^{iθ} Ω‖ ≤ 2 η` for some
real `θ`. No positivity or Hermiticity of `σ` is assumed.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 8.1 `lem:columns`,
`07-assembly.tex:67–94`. -/
theorem exists_fixInput_of_rectangularTraceNorm_sub_pure_le [Fintype V] [DecidableEq V]
    (N : PartyNetwork P Λ (q * q)) (site : P → V) (Ω : EuclideanSpace ℂ (V → Fin q))
    (hΩ : ‖Ω‖ = 1) {η : ℝ}
    (hσ : Matrix.rectangularTraceNorm (N.operatorCoeff site - Matrix.euclideanOuterProduct Ω Ω)
      ≤ η)
    (hη : η < 1) :
    ∃ z : V → Fin q, ∃ ψ : EuclideanSpace ℂ (V → Fin q),
      (∀ τ, ψ τ = (N.fixInput site z).coeff site τ) ∧ ψ ≠ 0 ∧
      ∃ θ : ℝ, ‖((‖ψ‖ : ℂ)⁻¹) • ψ - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * η := by
  classical
  let e := Fintype.equivFin (V → Fin q)
  have htrace : Matrix.traceNorm (Matrix.reindex e e
      (N.operatorCoeff site - Matrix.vecMulVec (⇑Ω) (star ⇑Ω))) ≤ η := by
    rw [← Matrix.rectangularTraceNorm_square, Matrix.rectangularTraceNorm_reindex]
    exact hσ
  obtain ⟨z, hz, θ, hθ⟩ :=
    exists_column_ne_zero_of_traceNorm_sub_pure_le e _ Ω hΩ htrace hη
  refine ⟨z, _, fun τ ↦ ?_, hz, θ, hθ⟩
  rw [Matrix.toEuclideanLin_single_one_apply, coeff_fixInput]

end PartyNetwork

end TNLean.Lattice.Compression
