/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.HermitianHelpers
import TNLean.Channel.PartialTrace
import TNLean.Channel.PositiveFunctional
import TNLean.Channel.WolfProps

/-!
# Positive conditional expectations onto one matrix factor

This file determines the form of a positive linear retraction from a matrix algebra onto
the unital subalgebra consisting of the identity on the left tensor factor and an arbitrary
matrix on the right tensor factor.

## Main results

* `Matrix.extractRightFactorMap`: the right matrix factor of the image of a linear map.
* `Matrix.exists_density_of_positive_retraction_onto_right_factor`: the one-factor form of
  a positive conditional expectation.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 1.5 and
  Equation (1.40)][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

namespace Matrix

variable {m d : ℕ} [NeZero m]

/-- Extract the right matrix factor from the image of a linear map by restricting to one
diagonal block in the left tensor factor.

For maps whose image consists of matrices of the form $1_m\otimes X$, this restriction is
the unique matrix $X$. This is the factor restriction used in Wolf, Proposition 1.5. -/
noncomputable def extractRightFactorMap
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) :
    Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun A := (E A).submatrix (fun j ↦ (0, j)) (fun j ↦ (0, j))
  map_add' A B := by
    ext i j
    simp
  map_smul' c A := by
    ext i j
    simp

@[simp]
theorem extractRightFactorMap_apply
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (A : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) (i j : Fin d) :
    extractRightFactorMap E A i j = E A (0, i) (0, j) :=
  rfl

/-- If the image of $E$ lies in $1_m\otimes M_d(\mathbb C)$, then the extracted right
factor reconstructs the whole image.

This is the one-factor range restriction in Wolf, Proposition 1.5. -/
theorem eq_one_kronecker_extractRightFactorMap
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (hRange : ∀ A, ∃ X : Matrix (Fin d) (Fin d) ℂ,
      E A = (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X)
    (A : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) :
    E A = (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ extractRightFactorMap E A := by
  obtain ⟨X, hX⟩ := hRange A
  have hExtract : extractRightFactorMap E A = X := by
    ext i j
    simp [hX]
  rw [hX, hExtract]

/-- Positivity passes from a map with range in $1_m\otimes M_d(\mathbb C)$ to its
extracted right-factor map.

This is the positivity restriction used in Wolf, Proposition 1.5. -/
theorem extractRightFactorMap_posSemidef
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (hE : IsPositiveMap E) (A : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (hA : A.PosSemidef) :
    (extractRightFactorMap E A).PosSemidef := by
  exact (hE A hA).submatrix (fun j ↦ (0, j))

/-- If $E$ fixes $1_m\otimes M_d(\mathbb C)$ pointwise, then its extracted right-factor
map sends $1_m\otimes X$ to $X$.

This is the one-factor retraction condition in Wolf, Proposition 1.5. -/
theorem extractRightFactorMap_one_kronecker
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (hFix : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      E ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X) =
        (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    extractRightFactorMap E
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X) = X := by
  ext i j
  simp [hFix]

/-- For a positive matrix in the left factor, positivity and the retraction property force
the induced action on the right factor to be a scalar multiple of the identity map.

This is the rank-one order argument in the proof of Wolf, Proposition 1.5. -/
theorem exists_extractRightFactorMap_kronecker_eq_smul_of_posSemidef
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (hE : IsPositiveMap E)
    (hFix : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      E ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X) =
        (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X)
    (Y : Matrix (Fin m) (Fin m) ℂ) (hY : Y.PosSemidef) :
    ∃ c : ℂ, ∀ X : Matrix (Fin d) (Fin d) ℂ,
      extractRightFactorMap E (Y ⊗ₖ X) = c • X := by
  classical
  let T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
    { toFun := fun X ↦ extractRightFactorMap E (Y ⊗ₖ X)
      map_add' := by
        intro X Z
        simp [Matrix.kronecker_add]
      map_smul' := by
        intro c X
        simp [Matrix.kronecker_smul] }
  have hT : ∀ v : Fin d → ℂ, ∃ c : ℂ,
      T (Matrix.vecMulVec v (star v)) =
        c • Matrix.vecMulVec v (star v) := by
    intro v
    let P : Matrix (Fin d) (Fin d) ℂ := Matrix.vecMulVec v (star v)
    have hP : P.PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
    have hYP : (Y ⊗ₖ P).PosSemidef := hY.kronecker hP
    have hOut : (T P).PosSemidef := by
      exact extractRightFactorMap_posSemidef E hE (Y ⊗ₖ P) hYP
    have hBound :
        (Y.trace • (1 : Matrix (Fin m) (Fin m) ℂ) - Y).PosSemidef :=
      hY.trace_smul_one_sub_self_posSemidef
    have hNeg : (-Y) ⊗ₖ P = -(Y ⊗ₖ P) := by
      rw [show -Y = (-1 : ℂ) • Y by simp, Matrix.smul_kronecker]
      simp
    have hInputDiff :
        ((Y.trace • (1 : Matrix (Fin m) (Fin m) ℂ)) ⊗ₖ P - Y ⊗ₖ P).PosSemidef := by
      simpa [sub_eq_add_neg, Matrix.add_kronecker, Matrix.smul_kronecker, hNeg] using
        hBound.kronecker hP
    have hOutputDiff := extractRightFactorMap_posSemidef E hE _ hInputDiff
    have hDom : T P ≤ Y.trace • P := by
      rw [Matrix.le_iff]
      simpa [T, Matrix.smul_kronecker,
        extractRightFactorMap_one_kronecker E hFix] using hOutputDiff
    obtain ⟨c, _, hc⟩ :=
      Matrix.PosSemidef.eq_nonneg_smul_vecMulVec_of_le_smul_vecMulVec hOut v hDom
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := WolfProps.exists_eq_smul_id_of_maps_rankOne_to_span T hT
  refine ⟨c, fun X ↦ ?_⟩
  have hApply := LinearMap.congr_fun hc X
  simpa [T] using hApply

/-- If the extracted action has scalar form on every rank-one positive matrix in the
left factor, then it has scalar form on every left-factor matrix.

The extension uses the rank-one polarization identity from Wolf, Proposition 2.2. -/
theorem extractRightFactorMap_kronecker_eq_smul_of_rankOne
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (f : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] ℂ)
    (hRankOne : ∀ (v : Fin m → ℂ) (X : Matrix (Fin d) (Fin d) ℂ),
      extractRightFactorMap E (Matrix.vecMulVec v (star v) ⊗ₖ X) =
        f (Matrix.vecMulVec v (star v)) • X)
    (Y : Matrix (Fin m) (Fin m) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    extractRightFactorMap E (Y ⊗ₖ X) = f Y • X := by
  classical
  let L : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
    { toFun := fun Z ↦ extractRightFactorMap E (Z ⊗ₖ X)
      map_add' := by
        intro Z W
        simp [Matrix.add_kronecker]
      map_smul' := by
        intro c Z
        simp [Matrix.smul_kronecker] }
  have hOuter (u v : Fin m → ℂ) :
      L (Matrix.vecMulVec u (star v)) =
        f (Matrix.vecMulVec u (star v)) • X := by
    have hPolarization := WolfProps.vecMulVec_star_eq_polarization u v
    have hL :
        (4 : ℂ) • L (Matrix.vecMulVec u (star v)) =
          L (Matrix.vecMulVec (u + v) (star (u + v))) -
              L (Matrix.vecMulVec (u - v) (star (u - v))) +
            Complex.I • L (Matrix.vecMulVec (u + Complex.I • v)
              (star (u + Complex.I • v))) -
            Complex.I • L (Matrix.vecMulVec (u - Complex.I • v)
              (star (u - Complex.I • v))) := by
      simpa only [map_smul, map_sub, map_add] using congrArg L hPolarization
    have hf :
        (4 : ℂ) • f (Matrix.vecMulVec u (star v)) =
          f (Matrix.vecMulVec (u + v) (star (u + v))) -
              f (Matrix.vecMulVec (u - v) (star (u - v))) +
            Complex.I • f (Matrix.vecMulVec (u + Complex.I • v)
              (star (u + Complex.I • v))) -
            Complex.I • f (Matrix.vecMulVec (u - Complex.I • v)
              (star (u - Complex.I • v))) := by
      simpa only [map_smul, map_sub, map_add] using congrArg f hPolarization
    have hLRankOne (w : Fin m → ℂ) :
        L (Matrix.vecMulVec w (star w)) =
          f (Matrix.vecMulVec w (star w)) • X := by
      exact hRankOne w X
    rw [hLRankOne (u + v), hLRankOne (u - v),
      hLRankOne (u + Complex.I • v), hLRankOne (u - Complex.I • v)] at hL
    have hFour :
        (4 : ℂ) • L (Matrix.vecMulVec u (star v)) =
          (4 : ℂ) • (f (Matrix.vecMulVec u (star v)) • X) := by
      rw [hL]
      calc
        _ = ((4 : ℂ) • f (Matrix.vecMulVec u (star v))) • X := by
          rw [hf]
          module
        _ = (4 : ℂ) • (f (Matrix.vecMulVec u (star v)) • X) := by
          simp [smul_smul, smul_eq_mul]
    exact smul_right_injective _ (by norm_num : (4 : ℂ) ≠ 0) hFour
  change L Y = f Y • X
  refine Matrix.induction_on' Y ?_ ?_ ?_
  · simp
  · intro Z W hZ hW
    rw [map_add, map_add, hZ, hW, add_smul]
  · intro i j c
    have hSingle : (Matrix.single i j c : Matrix (Fin m) (Fin m) ℂ) =
        c • Matrix.vecMulVec (Pi.single i 1) (star (Pi.single j 1)) := by
      have hStar : (star (Pi.single j (1 : ℂ)) : Fin m → ℂ) = Pi.single j 1 := by
        ext k
        simp [Pi.single_apply, Pi.star_apply]
      rw [hStar]
      rw [← Matrix.single_eq_single_vecMulVec_single (i := i) (j := j)]
      ext k l
      simp [Matrix.single_apply]
    rw [hSingle, map_smul, map_smul, hOuter, smul_smul]
    simp [smul_eq_mul]

section NontrivialRightFactor

variable [NeZero d]

/-- The left-factor functional associated with a conditional expectation is obtained by
testing its right-factor action on one fixed rank-one coordinate projection.

This is the normalized functional appearing in the proof of Wolf, Proposition 1.5. -/
noncomputable def conditionalExpectationLeftFunctional
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) :
    Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] ℂ where
  toFun Y := extractRightFactorMap E
    (Y ⊗ₖ Matrix.single (0 : Fin d) 0 1) 0 0
  map_add' Y Z := by
    simp [Matrix.add_kronecker]
  map_smul' c Y := by
    simp [Matrix.smul_kronecker]

@[simp]
theorem conditionalExpectationLeftFunctional_apply
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (Y : Matrix (Fin m) (Fin m) ℂ) :
    conditionalExpectationLeftFunctional E Y =
      extractRightFactorMap E (Y ⊗ₖ Matrix.single (0 : Fin d) 0 1) 0 0 :=
  rfl

/-- The left-factor functional of a positive conditional expectation is positive. -/
theorem conditionalExpectationLeftFunctional_nonneg
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (hE : IsPositiveMap E) (Y : Matrix (Fin m) (Fin m) ℂ)
    (hY : Y.PosSemidef) :
    (0 : ℂ) ≤ conditionalExpectationLeftFunctional E Y := by
  let P : Matrix (Fin d) (Fin d) ℂ := Matrix.single 0 0 1
  have hP : P.PosSemidef := by
    have hSingle : P = Matrix.vecMulVec (Pi.single (0 : Fin d) (1 : ℂ))
        (star (Pi.single (0 : Fin d) (1 : ℂ))) := by
      ext i j
      by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
        simp [P, Matrix.vecMulVec_apply, hi, hj, eq_comm]
    rw [hSingle]
    exact Matrix.posSemidef_vecMulVec_self_star _
  have hOut := extractRightFactorMap_posSemidef E hE (Y ⊗ₖ P) (hY.kronecker hP)
  simpa [conditionalExpectationLeftFunctional, P] using
    (Matrix.PosSemidef.diag_nonneg hOut (i := (0 : Fin d)))

/-- The left-factor functional of a retraction fixing $1_m\otimes M_d(\mathbb C)$ is
normalized. -/
theorem conditionalExpectationLeftFunctional_one
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (hFix : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      E ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X) =
        (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X) :
    conditionalExpectationLeftFunctional E 1 = 1 := by
  have h := extractRightFactorMap_one_kronecker E hFix
    (Matrix.single (0 : Fin d) 0 1)
  exact congrFun (congrFun h 0) 0

/-- On every simple tensor, the extracted right factor is multiplication by the
left-factor functional.

This is the scalar-factor conclusion in the proof of Wolf, Proposition 1.5. -/
theorem extractRightFactorMap_kronecker_eq_functional_smul
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (hE : IsPositiveMap E)
    (hFix : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      E ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X) =
        (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X)
    (Y : Matrix (Fin m) (Fin m) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    extractRightFactorMap E (Y ⊗ₖ X) =
      conditionalExpectationLeftFunctional E Y • X := by
  apply extractRightFactorMap_kronecker_eq_smul_of_rankOne
    E (conditionalExpectationLeftFunctional E)
  intro v Z
  let P : Matrix (Fin m) (Fin m) ℂ := Matrix.vecMulVec v (star v)
  have hP : P.PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  obtain ⟨c, hc⟩ :=
    exists_extractRightFactorMap_kronecker_eq_smul_of_posSemidef E hE hFix P hP
  have hCoefficient : c = conditionalExpectationLeftFunctional E P := by
    have hEntry := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ ↦ M 0 0)
      (hc (Matrix.single (0 : Fin d) 0 1))
    simpa [conditionalExpectationLeftFunctional, Matrix.single_apply] using hEntry.symm
  rw [hc Z, hCoefficient]

end NontrivialRightFactor

/-- A scalar action on simple tensors determines the extracted map on every matrix as a
weighted partial trace.

The calculation is the one-factor part of Equation (1.40) following Wolf,
Proposition 1.5. -/
theorem extractRightFactorMap_eq_weighted_partialTrace
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (f : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] ℂ) (ρ : Matrix (Fin m) (Fin m) ℂ)
    (hρ : ∀ Y : Matrix (Fin m) (Fin m) ℂ, f Y = (ρ * Y).trace)
    (hScalar : ∀ (Y : Matrix (Fin m) (Fin m) ℂ)
      (X : Matrix (Fin d) (Fin d) ℂ),
      extractRightFactorMap E (Y ⊗ₖ X) = f Y • X)
    (A : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) :
    extractRightFactorMap E A =
      Matrix.partialTraceLeft
        ((ρ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * A) := by
  classical
  refine Matrix.induction_on' A ?_ ?_ ?_
  · ext i j
    simp [Matrix.partialTraceLeft_apply]
  · intro A B hA hB
    rw [map_add, hA, hB]
    ext i j
    simp [Matrix.partialTraceLeft_apply, Matrix.mul_add, Finset.sum_add_distrib]
  · rintro ⟨i, j⟩ ⟨k, l⟩ c
    have hSingle :
        (Matrix.single (i, j) (k, l) c :
          Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) =
          Matrix.single i k c ⊗ₖ Matrix.single j l 1 := by
      rw [Matrix.single_kronecker_single]
      simp
    rw [hSingle]
    rw [hScalar, hρ]
    rw [← Matrix.traceLeft_kronecker]
    simp only [Matrix.traceLeft]
    rw [← Matrix.mul_kronecker_mul]
    simp

/-- A normalized positive scalar action on simple tensors is represented by a density
matrix and gives the weighted-partial-trace form of the whole map.

This is the final functional representation step in Wolf, Proposition 1.5 and
Equation (1.40). -/
theorem exists_density_of_scalar_action
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (hRange : ∀ A, ∃ X : Matrix (Fin d) (Fin d) ℂ,
      E A = (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X)
    (f : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] ℂ)
    (hPositive : ∀ Y : Matrix (Fin m) (Fin m) ℂ,
      Y.PosSemidef → (0 : ℂ) ≤ f Y)
    (hOne : f 1 = 1)
    (hScalar : ∀ (Y : Matrix (Fin m) (Fin m) ℂ)
      (X : Matrix (Fin d) (Fin d) ℂ),
      extractRightFactorMap E (Y ⊗ₖ X) = f Y • X) :
    ∃ ρ : Matrix (Fin m) (Fin m) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ A : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ,
        E A = (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ
          Matrix.partialTraceLeft
            ((ρ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * A) := by
  obtain ⟨ρ, hρ, hρtrace, hRepresentation⟩ :=
    Matrix.exists_density_of_positive_functional f hPositive hOne
  refine ⟨ρ, hρ, hρtrace, fun A ↦ ?_⟩
  rw [eq_one_kronecker_extractRightFactorMap E hRange A]
  rw [extractRightFactorMap_eq_weighted_partialTrace E f ρ hRepresentation hScalar A]

/-- A positive linear retraction onto $1_m\otimes M_d(\mathbb C)$ is a weighted partial
trace on the left factor, followed by the canonical embedding of the right factor.

More precisely, there is a positive semidefinite matrix $\rho$ of trace one such that
\[
  E(A)=1_m\otimes
    \operatorname{tr}_m\bigl((\rho\otimes 1_d)A\bigr).
\]
This is the one-factor case of Wolf, Proposition 1.5 and Equation (1.40). -/
theorem exists_density_of_positive_retraction_onto_right_factor [NeZero d]
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (hE : IsPositiveMap E)
    (hRange : ∀ A, ∃ X : Matrix (Fin d) (Fin d) ℂ,
      E A = (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X)
    (hFix : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      E ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X) =
        (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X) :
    ∃ ρ : Matrix (Fin m) (Fin m) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ A : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ,
        E A = (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ
          Matrix.partialTraceLeft
            ((ρ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * A) := by
  let f := conditionalExpectationLeftFunctional E
  apply exists_density_of_scalar_action E hRange f
  · intro Y hY
    exact conditionalExpectationLeftFunctional_nonneg E hE Y hY
  · exact conditionalExpectationLeftFunctional_one E hFix
  · exact extractRightFactorMap_kronecker_eq_functional_smul E hE hFix

end Matrix
