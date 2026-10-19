/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LocalHamiltonian
import QICLean.Analysis.Entropy

/-!
# Regional states and regional entropy on finite lattice domains

Regional entropy is the existing von Neumann entropy of the partial trace, after
splitting configuration coordinates.

## Main definitions

* `reducedState`: the reduced pure state on a region.
* `regionalEntropy`: its von Neumann entropy, in natural logarithms.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 1.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped ComplexOrder

namespace TNLean.Lattice

/-- The reduced pure-state matrix obtained by tracing over complementary
configuration coordinates. Source: area-law Section 1, definition of `ρ_A`. -/
noncomputable def reducedState (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    Matrix ({x : Site Λ // x ∈ A} → Fin q) ({x : Site Λ // x ∈ A} → Fin q) ℂ :=
  Matrix.partialTraceRight
    ((Matrix.vecMulVec (fun x ↦ Ω x) (star (fun x ↦ Ω x))).submatrix
      (configurationSplit Λ q A).symm (configurationSplit Λ q A).symm)

/-- Regional reductions of a pure vector are positive semidefinite.
Source: area-law `sec:prelim`, lines 10–25, normalized density operators
and partial trace; the positivity statement does not require normalization. -/
theorem reducedState_posSemidef (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    (reducedState Λ q Ω A).PosSemidef :=
  ((Matrix.posSemidef_vecMulVec_self_star (fun x ↦ Ω x)).submatrix
    (configurationSplit Λ q A).symm).partialTraceRight

/-- Regional pure-state matrices are Hermitian, also for empty regions and
singular marginals. -/
theorem reducedState_isHermitian (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    (reducedState Λ q Ω A).IsHermitian :=
  (reducedState_posSemidef Λ q Ω A).isHermitian

/-- Entanglement entropy with natural logarithms and the convention `0 log 0 = 0`.
Source: area-law Section 1, definition of `SΩ(A)`. -/
noncomputable def regionalEntropy (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (A : Finset (Site Λ)) : ℝ :=
  vonNeumannEntropy (reducedState Λ q Ω A) (reducedState_isHermitian Λ q Ω A)

end TNLean.Lattice
