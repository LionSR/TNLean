/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.OpenMPS
import QICLean.Analysis.SubnormalizedPureStateError

/-!
# Efficient approximation of families by matrix product states

The accuracy is fixed before the polynomial bond bound is chosen. Its constants
are uniform over the set of chain lengths. No consistency between different
chain lengths is required. Both states in the approximation are interpreted as
pure density matrices, and the error uses the full trace norm.

Source: Schuch–Wolf–Verstraete–Cirac, arXiv:0705.0292v2,
`paper_v2.tex`, lines 198–210.
-/

namespace TNLean.MPS.AreaLaw

/-- Efficient MPS approximation in the sense of Schuch–Wolf–Verstraete–Cirac,
arXiv:0705.0292v2, lines 198–210. For each fixed positive accuracy, normalized
approximants have a polynomial bond bound uniform in the chain length. Writing
the polynomial as `C * (N + 1) ^ m` allows finite exceptional lengths to be
absorbed into its constant. The error is the full trace norm, without a factor
of one half. -/
def IsEfficientlyApproximableByMPS {q : ℕ} {lengths : Set ℕ}
    (ψ : ∀ N : lengths, EuclideanSpace ℂ (Fin N.val → Fin q)) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∃ m : ℕ,
    ∀ N : lengths, ∃ D : ℕ, ∃ φ : EuclideanSpace ℂ (Fin N.val → Fin q),
      (D : ℝ) ≤ C * ((N.val : ℝ) + 1) ^ m ∧ ‖φ‖ = 1 ∧
      IsOpenMPS N.val q D (fun x ↦ φ x) ∧
      Matrix.rectangularTraceNorm
        (Matrix.euclideanOuterProduct (ψ N) (ψ N) - Matrix.euclideanOuterProduct φ φ) ≤ δ

end TNLean.MPS.AreaLaw
