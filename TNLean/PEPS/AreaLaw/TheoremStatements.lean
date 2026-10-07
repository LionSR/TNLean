/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.LocalHamiltonian
import QICLean.Analysis.Entropy

/-!
# The uniform finite-domain area-law statement

The constant is chosen before the finite domain, interaction family, ground
vector, and cut. Regional entropy is the existing von Neumann entropy of the
partial trace, after splitting configuration coordinates. The target is a
proposition; this module does not assert that the area law has been proved.

## Main definitions

* `reducedState`: the reduced pure state on a region.
* `regionalEntropy`: its von Neumann entropy, in natural logarithms.
* `UniformAreaLaw`: the complete arbitrary-domain, finite-range target.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Theorem 1.1 and `eq:area-law`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped ComplexOrder

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript:
  preprints/
  A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
  build/
  sections/
  00-introduction.tex
Labels: thm:area, eq:area-law.
Provenance-ID: 8738-tnlean.peps.arealaw.reducedstate
Downstream declaration: TNLean.PEPS.AreaLaw.reducedState
Provenance-ID: 8738-tnlean.peps.arealaw.reducedstate_ishermitian
Downstream declaration: TNLean.PEPS.AreaLaw.reducedState_isHermitian
Provenance-ID: 8738-tnlean.peps.arealaw.regionalentropy
Downstream declaration: TNLean.PEPS.AreaLaw.regionalEntropy
Provenance-ID: 8738-tnlean.peps.arealaw.uniformarealaw
Downstream declaration: TNLean.PEPS.AreaLaw.UniformAreaLaw
-/

namespace TNLean.PEPS.AreaLaw

/-- The reduced pure-state matrix obtained by tracing over complementary
configuration coordinates. Source: area-law Section 1, definition of `ρ_A`. -/
noncomputable def reducedState (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    Matrix ({x : Site Λ // x ∈ A} → Fin q) ({x : Site Λ // x ∈ A} → Fin q) ℂ :=
  Matrix.partialTraceRight
    ((Matrix.vecMulVec (fun x ↦ Ω x) (star (fun x ↦ Ω x))).submatrix
      (configurationSplit Λ q A).symm (configurationSplit Λ q A).symm)

/-- Regional pure-state matrices are Hermitian, also for empty regions and
singular marginals. -/
theorem reducedState_isHermitian (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    (reducedState Λ q Ω A).IsHermitian :=
  ((Matrix.posSemidef_vecMulVec_self_star (fun x ↦ Ω x)).submatrix
    (configurationSplit Λ q A).symm).partialTraceRight.isHermitian

/-- Entanglement entropy with natural logarithms and the convention `0 log 0 = 0`.
Source: area-law Section 1, definition of `SΩ(A)`. -/
noncomputable def regionalEntropy (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (A : Finset (Site Λ)) : ℝ :=
  vonNeumannEntropy (reducedState Λ q Ω A) (reducedState_isHermitian Λ q Ω A)

/-- The uniform area-law target, with its constant chosen before all physical
instances. Source: area-law Theorem 1.1 (`thm:area`, `eq:area-law`).
This proposition is a theorem statement, not a proof of that theorem. -/
def UniformAreaLaw : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ R : ℕ, ∀ J Δ : ℝ, 0 < J → 0 < Δ →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ Λ : Finset (ℤ × ℤ), ∀ h : LocalHamiltonian Λ q R J,
        ∀ E₀ : ℝ, ∀ Ω : StateSpace Λ q,
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
            ∀ A : Finset (Site Λ), regionalEntropy Λ q Ω A ≤ C * (edgeBoundary Λ A).card

end TNLean.PEPS.AreaLaw
