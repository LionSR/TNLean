/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.CanonicalOneCopyState

/-!
# Actual canonical fixed-point regressions

The signatures require only canonical-form data, retained copy choices and the stated
length/nonvanishing conditions. The physical comparison uses the assembled tensor itself.
A multiplicity-one regression preserves the absolute-value correction for complex weights.
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix MPSTensor

variable {d : ℕ} {P : SectorDecomposition d} (h : IsBNTCanonicalForm P)
  (κ : (j : Fin P.basisCount) → Fin (P.copies j))

example (j : Fin P.basisCount) :
    (h.basisFixedPoint j).PosDef ∧ (h.basisFixedPoint j).trace = 1 ∧
      Kraus.transferMap (P.basis j) (h.basisFixedPoint j) = h.basisFixedPoint j :=
  ⟨(h.basisFixedPoint_spec j).1, (h.basisFixedPoint_spec j).2.1,
    (h.basisFixedPoint_spec j).2.2.1⟩

example (j : Fin P.basisCount) (τ : Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ)
    (hτ : τ.PosSemidef) (htr : τ.trace = 1) (hfix : Kraus.transferMap (P.basis j) τ = τ) :
    τ = h.basisFixedPoint j :=
  (h.basisFixedPoint_spec j).2.2.2 τ ⟨hτ, htr⟩ hfix

example (j : Fin P.basisCount) :
    ∑ p, star (h.basisFixedPointPair κ j p) * h.basisFixedPointPair κ j p = 1 := by
  simpa using h.inner_basisFixedPointPair κ j j

example {q M : ℕ} (hM : M ≠ 0) (hβ : P.coeff (q * M) ≠ 0) :
    ∑ c : Fin M → Fin P.totalDim × Fin P.totalDim,
      star (h.oneCopyFixedPointState κ q M c) * h.oneCopyFixedPointState κ q M c = 1 :=
  h.oneCopyFixedPointState_norm_sq κ hM hβ

example {q : ℕ} (hq : q ≠ 0) (M : ℕ) :
    nonNormalApproxVector P.toTensor q M (oneCopyWeight P.copyWeights κ q M)
        (h.basisFixedPointPair κ) =
      copyApproxVector P.toTensor q M (P.coeff (q * M))
        (copyIsometry P.copyCoord P.copyWeights q) h.basisFixedPoint :=
  h.nonNormalApproxVector_oneCopyFixedPoint κ hq M

example (j : Fin P.basisCount) (hj : ∀ k : Fin (P.copies j), k = κ j) (q M : ℕ) :
    oneCopyWeight P.copyWeights κ q M j = ((‖P.weight j (κ j)‖ ^ (q * M) : ℝ) : ℂ) := by
  simpa only [Nat.mul_comm] using oneCopyWeight_of_subsingleton P.copyWeights κ hj q M

section AxiomChecks
set_option linter.hashCommand false

/-- info: 'MPSTensor.IsBNTCanonicalForm.basisFixedPoint_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.IsBNTCanonicalForm.basisFixedPoint_spec

/-- info: 'MPSTensor.IsBNTCanonicalForm.inner_basisFixedPointPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.IsBNTCanonicalForm.inner_basisFixedPointPair

/-- info: 'MPSTensor.IsBNTCanonicalForm.oneCopyFixedPointState_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.IsBNTCanonicalForm.oneCopyFixedPointState_norm_sq

/-- info: 'MPSTensor.IsBNTCanonicalForm.nonNormalApproxVector_oneCopyFixedPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.IsBNTCanonicalForm.nonNormalApproxVector_oneCopyFixedPoint

/-- info: 'MPSTensor.IsBNTCanonicalForm.nonNormalApproxOverlap_oneCopyFixedPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.IsBNTCanonicalForm.nonNormalApproxOverlap_oneCopyFixedPoint

end AxiomChecks
