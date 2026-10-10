/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.DependentRegionOperatorLift
import QICLean.Channel.FiniteProduct
import QICLean.Entropy.LocalLift

/-!
# Regional operators and marginals under local basis relabelling

A family of equivalences from arbitrary finite site alphabets to `Fin` alphabets
identifies the native regional lift with `Entropy.localLift` and the canonical
finite-product marginal with `Entropy.regionState`. All identities are exact,
including for complex matrices that are not Hermitian. Empty regions, empty site
sets and empty local alphabets need no separate hypotheses.

The native full-region configuration identification and its expectation formula
are owned here. Variational outputs and their normalization remain in
`RegularizedPatchMarginal`; no optimization or commutation statement is used.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `03-patches.tex`, lines 68–99, commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
* `QICLean.Channel.FiniteProduct` and `QICLean.Entropy.LocalLift` for the
  canonical partial traces and regional operators.
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

/-- The regional identity extension pairs with the canonical finite-product
marginal of the same vector.
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

variable {n : V → ℕ}

/-- Relabel each local alphabet in a regional configuration. -/
def dependentRegionFinEquiv (e : ∀ v, Out v ≃ Fin (n v)) (R : Finset V) :
    ((v : R) → Out v.1) ≃ Entropy.RegionConfig n R :=
  Equiv.piCongrRight fun v ↦ e v.1

/-- Relabel a native full-region configuration in the global `Fin` coordinates. -/
def dependentGlobalFinEquiv (e : ∀ v, Out v ≃ Fin (n v)) :
    ((v : (Finset.univ : Finset V)) → Out v.1) ≃ Entropy.SiteConfig n :=
  dependentGlobalConfigEquiv.trans (Equiv.piCongrRight e)

/-- The unitary basis relabelling, composed with the canonical full-region
identification rather than a new choice of global Hilbert space. -/
noncomputable def dependentGlobalFinIsometry (e : ∀ v, Out v ≃ Fin (n v)) :
    EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Entropy.SiteConfig n) :=
  dependentGlobalConfigIsometry.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.piCongrRight e))

@[simp]
theorem dependentGlobalFinIsometry_apply (e : ∀ v, Out v ≃ Fin (n v))
    (ξ : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (σ : Entropy.SiteConfig n) :
    dependentGlobalFinIsometry e ξ σ = ξ (fun v ↦ (e v.1).symm (σ v.1)) := rfl

omit [∀ v, Fintype (Out v)] in
/-- Native regional operators become the QIC local lifts under the same local
basis relabelling on their input and output indices. -/
theorem reindex_dependentRegionOperatorLift (e : ∀ v, Out v ≃ Fin (n v))
    (R : Finset V) (K : Matrix ((v : R) → Out v.1) ((v : R) → Out v.1) ℂ) :
    Matrix.reindex (dependentGlobalFinEquiv e) (dependentGlobalFinEquiv e)
        (dependentRegionOperatorLift R K) =
      Entropy.localLift R
        (Matrix.reindex (dependentRegionFinEquiv e R) (dependentRegionFinEquiv e R) K) := by
  classical
  let eC := (FiniteProduct.complementEquiv Out R).symm.trans
    (Equiv.piCongrRight fun v : {v // v ∉ R} ↦ e v.1)
  ext σ τ
  change K _ _ * (1 : Matrix _ _ ℂ) (eC.symm ((Entropy.cutEquiv n R) σ).2)
      (eC.symm ((Entropy.cutEquiv n R) τ).2) = K _ _ * (1 : Matrix _ _ ℂ) _ _
  simp only [Matrix.one_apply, Equiv.symm_apply_eq, Equiv.apply_symm_apply]
  rfl

/-- The coordinate isometry intertwines the actions of the native and QIC
regional operators on every vector. -/
theorem dependentGlobalFinIsometry_lift (e : ∀ v, Out v ≃ Fin (n v))
    (R : Finset V) (K : Matrix ((v : R) → Out v.1) ((v : R) → Out v.1) ℂ)
    (ξ : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) :
    dependentGlobalFinIsometry e
        (WithLp.toLp 2 (dependentRegionOperatorLift R K *ᵥ ξ)) =
      Matrix.toEuclideanLin (Entropy.localLift R
        (Matrix.reindex (dependentRegionFinEquiv e R) (dependentRegionFinEquiv e R) K))
          (dependentGlobalFinIsometry e ξ) := by
  rw [← reindex_dependentRegionOperatorLift]
  ext σ
  change (dependentRegionOperatorLift R K *ᵥ ξ) ((dependentGlobalFinEquiv e).symm σ) =
    ((dependentRegionOperatorLift R K).submatrix (dependentGlobalFinEquiv e).symm
      (dependentGlobalFinEquiv e).symm *ᵥ
        (fun τ ↦ ξ ((dependentGlobalFinEquiv e).symm τ))) σ
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply]

/-- The canonical native marginal, with its regional basis relabelled, is
exactly the QIC regional state of the relabelled global vector. -/
theorem reindex_reducedPure_eq_regionState (e : ∀ v, Out v ≃ Fin (n v))
    (R : Finset V)
    (ξ : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) :
    Matrix.reindex (dependentRegionFinEquiv e R) (dependentRegionFinEquiv e R)
        (FiniteProduct.reducedPure Out (dependentGlobalConfigIsometry ξ) R) =
      Entropy.regionState R (dependentGlobalFinIsometry e ξ) := by
  classical
  let eR := dependentRegionFinEquiv e R
  let eC := (FiniteProduct.complementEquiv Out R).symm.trans
    (Equiv.piCongrRight fun v : {v // v ∉ R} ↦ e v.1)
  let P := Matrix.vecMulVec (WithLp.ofLp ξ) (star (WithLp.ofLp ξ))
  let Y := P.submatrix (dependentRegionConfigEquiv R).symm
    (dependentRegionConfigEquiv R).symm
  change (Matrix.partialTraceRight Y).submatrix eR.symm eR.symm = _
  rw [← Matrix.partialTraceRight_submatrix_prod_equiv eR eC]
  unfold Entropy.regionState
  congr 1
  ext p q
  change ξ ((dependentRegionConfigEquiv R).symm ((eR.prodCongr eC).symm p)) *
      star (ξ ((dependentRegionConfigEquiv R).symm ((eR.prodCongr eC).symm q))) =
    ξ ((dependentGlobalFinEquiv e).symm ((Entropy.cutEquiv n R).symm p)) *
      star (ξ ((dependentGlobalFinEquiv e).symm ((Entropy.cutEquiv n R).symm q)))
  have h (z : Entropy.RegionConfig n R × ((v : {v // v ∉ R}) → Fin (n v))) :
      (dependentRegionConfigEquiv R).symm ((eR.prodCongr eC).symm z) =
        (dependentGlobalFinEquiv e).symm ((Entropy.cutEquiv n R).symm z) := by
    funext v
    by_cases hv : v.1 ∈ R <;>
      simp [dependentRegionConfigEquiv, assembleDependentRegionConfig, eR, eC,
        dependentRegionFinEquiv, dependentGlobalFinEquiv, dependentGlobalConfigEquiv,
        FiniteProduct.complementEquiv, Equiv.piEquivPiSubtypeProd, hv]
  rw [h p, h q]

end TNLean.PEPS
