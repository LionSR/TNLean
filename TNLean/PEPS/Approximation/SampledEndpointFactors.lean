/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceGaussianLaw

/-! # The two endpoint factors of a sampled source

Each original source occurrence and ordered ket–bra branch pair determine the
left and right endpoint matrices. Both matrices use the same Gaussian array
and sample index. Their averaged Kronecker product is the actual sampled source
matrix, including when the sample set is empty.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 279–309 and 565–588.
-/

noncomputable section
open QICLean.ComplexGaussian
open scoped Kronecker
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type} {a b : Layout P}

variable (w : SourceCircuit a b) (k : ℕ)
  (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
    Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
  (E : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
  (F : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)

/-- The left endpoint operator retains the original source occurrence, the ordered
ket–bra branch pair, and the shared sample index. Source: polynomial-PEPS,
`04-compression.tex:279–309`. -/
def sampledEndpointLeft (e : sourceLocations w)
    (ξζ : branchLabels w e.1 × branchLabels w e.1) (j : Fin k)
    (ω : SourceGaussianSamples w k) :
    Matrix (Fin (sourceDims w e).1) (Fin (sourceDims w e).1) ℂ :=
  ambientSourceU k (lam e ξζ.1) (lam e ξζ.2) (E e ξζ.1) (E e ξζ.2)
    j (ω e ξζ)

/-- The right endpoint uses the conjugate of precisely the same Gaussian array
and the same sample index as the left endpoint. Source: polynomial-PEPS,
`04-compression.tex:279–309`. -/
def sampledEndpointRight (e : sourceLocations w)
    (ξζ : branchLabels w e.1 × branchLabels w e.1) (j : Fin k)
    (ω : SourceGaussianSamples w k) :
    Matrix (Fin (sourceDims w e).2) (Fin (sourceDims w e).2) ℂ :=
  ambientSourceV k (lam e ξζ.1) (lam e ξζ.2) (F e ξζ.1) (F e ξζ.2)
    j (ω e ξζ)

/-- The actual sampled source is the average of its two endpoint factors;
the factorization follows from the constructed matrices. Source: polynomial-PEPS,
`04-compression.tex:279–309`. -/
theorem sampledSourceMatrix_eq_endpoint_average (e : sourceLocations w)
    (ξ ζ : branchLabels w e.1) (ω : SourceGaussianSamples w k) :
    sampledSourceMatrix w k lam E F e ξ ζ ω =
      (k : ℂ)⁻¹ • ∑ j : Fin k,
        sampledEndpointLeft w k lam E e (ξ, ζ) j ω ⊗ₖ
          sampledEndpointRight w k lam F e (ξ, ζ) j ω := rfl

end TNLean.PEPS.PairEffect.SourceCircuit
