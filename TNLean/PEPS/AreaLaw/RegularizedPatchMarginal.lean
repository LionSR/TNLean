/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchMinimum
import QICLean.Channel.FiniteProduct

/-!
# Canonical marginals of regularized patch outputs

The normalized output of the regularized patch problem has its regional density
matrices given by the existing finite-product partial trace. The only coordinate
change removes the redundant membership witness in the full-region index.
Expectations of arbitrary complex regional matrices agree with the complex trace
pairing against these marginals. Local dimensions may vary, and regions may be
empty.

Source: OpenAI `03-patches.tex`, lines 68–99, commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators Matrix Kronecker ComplexOrder
open Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*}

/-- Forget the redundant full-region membership witness in a configuration. -/
def dependentGlobalConfigEquiv :
    ((v : (Finset.univ : Finset V)) → Out v.1) ≃ ((v : V) → Out v) where
  toFun σ v := σ ⟨v, Finset.mem_univ v⟩
  invFun σ v := σ v.1
  left_inv σ := by funext v; rfl
  right_inv σ := rfl

variable [∀ v, Fintype (Out v)]

/-- The canonical unitary identification of the full-region and global
configuration Hilbert spaces. -/
noncomputable def dependentGlobalConfigIsometry :
    EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((v : V) → Out v) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ dependentGlobalConfigEquiv

@[simp]
theorem dependentGlobalConfigIsometry_apply
    (ξ : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (σ : (v : V) → Out v) :
    dependentGlobalConfigIsometry ξ σ = ξ (fun v ↦ σ v.1) := rfl

/-- The actual regional lift pairs with the canonical finite-product marginal.
This equality is complex-valued and requires no Hermiticity assumption on the
regional matrix. -/
theorem inner_dependentRegionOperatorLift_eq_trace_reducedPure (R : Finset V)
    (K : Matrix ((v : R) → Out v.1) ((v : R) → Out v.1) ℂ)
    (ξ : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) :
    inner ℂ ξ (WithLp.toLp 2 (dependentRegionOperatorLift R K *ᵥ ξ)) =
      Matrix.trace (FiniteProduct.reducedPure Out (dependentGlobalConfigIsometry ξ) R * K) := by
  classical
  let e := dependentRegionConfigEquiv (Out := Out) R
  let P := Matrix.vecMulVec (WithLp.ofLp ξ) (star (WithLp.ofLp ξ))
  let Y := P.submatrix e.symm e.symm
  have hρ : FiniteProduct.reducedPure Out (dependentGlobalConfigIsometry ξ) R =
      Matrix.partialTraceRight Y := by
    rfl
  have hpair : Matrix.trace (Matrix.partialTraceRight Y * K) =
      Matrix.trace (Y * (K ⊗ₖ 1)) := by
    let s := Equiv.prodComm (FiniteProduct.Configuration Out Rᶜ)
      (FiniteProduct.Configuration Out R)
    have hswap : (K ⊗ₖ (1 : Matrix (FiniteProduct.Configuration Out Rᶜ)
        (FiniteProduct.Configuration Out Rᶜ) ℂ)).submatrix s s = 1 ⊗ₖ K := by
      ext p q
      exact mul_comm _ _
    calc
      _ = Matrix.trace (Matrix.partialTraceLeft (Y.submatrix s s) * K) := rfl
      _ = Matrix.trace (Y.submatrix s s * (1 ⊗ₖ K)) :=
        Matrix.trace_partialTraceLeft_mul K _
      _ = Matrix.trace ((Y * (K ⊗ₖ 1)).submatrix s s) := by
        rw [← hswap, Matrix.submatrix_mul_equiv]
      _ = Matrix.trace (Y * (K ⊗ₖ 1)) := Matrix.trace_submatrix_equiv s _
  have hLift : (dependentRegionOperatorLift R K).submatrix e.symm e.symm =
      K ⊗ₖ 1 := by
    ext p q
    change (K ⊗ₖ 1) (e (e.symm p)) (e (e.symm q)) = _
    simp only [Equiv.apply_symm_apply]
  rw [hρ, hpair]
  calc
    _ = Matrix.trace (P * dependentRegionOperatorLift R K) := by
      rw [Matrix.trace_mul_comm, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
      exact EuclideanSpace.inner_eq_star_dotProduct ξ _
    _ = Matrix.trace ((P * dependentRegionOperatorLift R K).submatrix e.symm e.symm) :=
      (Matrix.trace_submatrix_equiv e.symm _).symm
    _ = Matrix.trace (Y * (K ⊗ₖ 1)) := by
      rw [← Matrix.submatrix_mul_equiv P (dependentRegionOperatorLift R K)
        e.symm e.symm e.symm, hLift]

variable {m : ℕ} (regions : Fin m → Finset V)

/-- The canonical regional density of the same normalized vector used in the
regularized patch minimum problem. Source: OpenAI `03-patches.tex`, lines 68–99. -/
noncomputable def normalizedRegularizedPatchMarginal (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (R : Finset V) : Matrix ((v : R) → Out v.1) ((v : R) → Out v.1) ℂ :=
  FiniteProduct.reducedPure Out
    (dependentGlobalConfigIsometry (normalizedRegularizedPatchOutput regions a b Ω x)) R

/-- Canonical regularized patch marginals are positive semidefinite. -/
theorem normalizedRegularizedPatchMarginal_posSemidef (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (R : Finset V) :
    (normalizedRegularizedPatchMarginal regions a b Ω x R).PosSemidef :=
  FiniteProduct.reducedPure_posSemidef Out _ R

/-- Every feasible regularized output has trace-one canonical marginals,
including the marginal on the empty region. -/
theorem trace_normalizedRegularizedPatchMarginal (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) (hΩ : ‖Ω‖ = 1)
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions) (R : Finset V) :
    (normalizedRegularizedPatchMarginal regions a b Ω x R).trace = 1 := by
  apply FiniteProduct.trace_reducedPure
  rw [dependentGlobalConfigIsometry.norm_map]
  exact norm_normalizedRegularizedPatchOutput regions a ha hb Ω hΩ hx

/-- Regional expectations in the normalized regularized output are precisely
the complex trace pairings with its canonical reduced state. -/
theorem inner_normalizedRegularizedPatchOutput_lift_eq_trace (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (R : Finset V) (K : Matrix ((v : R) → Out v.1) ((v : R) → Out v.1) ℂ) :
    inner ℂ (normalizedRegularizedPatchOutput regions a b Ω x)
        (WithLp.toLp 2 (dependentRegionOperatorLift R K *ᵥ
          normalizedRegularizedPatchOutput regions a b Ω x)) =
      Matrix.trace (normalizedRegularizedPatchMarginal regions a b Ω x R * K) :=
  inner_dependentRegionOperatorLift_eq_trace_reducedPure R K _

end TNLean.PEPS
