/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Basic
import TNLean.QCA.LocalLimit
import Mathlib.Data.Finset.Sort

/-!
# Finite-chain conjugation by a matrix product unitary

This file isolates the finite-size expression
\(U^{(N)} A_L U^{(N)\dagger}\) that occurs before the stabilization limit in
`eq:appendix-1`.  A periodic MPU matrix is reindexed from the cyclic sites
`Fin N` to an integer interval of length `N`; a local observable is extended to
that interval by tensoring with the identity and then conjugated by the
reindexed unitary.

No stabilization, propagation bound, translation covariance, quasi-local
automorphism, or QCA is asserted here.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188,
  equation `eq:appendix-1`, lines 2300--2306.
-/

open scoped Matrix

namespace SpinChain

/-- The half-open integer interval of `N` consecutive sites beginning at `a`.

This is the chosen finite chain used to interpret the finite-size operator
\(U^{(N)}\) in arXiv:1703.09188, equation `eq:appendix-1`, lines 2300--2306. -/
noncomputable def finiteChainRegion (a : ℤ) (N : ℕ) : Finset ℤ :=
  Finset.Ico a (a + N)

@[simp]
lemma card_finiteChainRegion (a : ℤ) (N : ℕ) : (finiteChainRegion a N).card = N := by
  simp [finiteChainRegion, Int.card_Ico]

/-- The increasing identification of the cyclic site labels `Fin N` with the
chosen integer interval of length `N`.

Source: arXiv:1703.09188, equation `eq:appendix-1`, lines 2300--2306. -/
noncomputable def finiteChainSiteEquiv (a : ℤ) (N : ℕ) :
    Fin N ≃ finiteChainRegion a N :=
  ((finiteChainRegion a N).orderIsoOfFin (card_finiteChainRegion a N)).toEquiv

/-- Reindex a periodic length-`N` configuration as a configuration on the
chosen integer interval.

Source: arXiv:1703.09188, equation `eq:appendix-1`, lines 2300--2306. -/
noncomputable def finiteChainConfigEquiv (d N : ℕ) (a : ℤ) :
    (Fin N → Fin d) ≃ Config d (finiteChainRegion a N) :=
  Equiv.arrowCongr (finiteChainSiteEquiv a N) (Equiv.refl (Fin d))

/-- The periodic matrix-product operator \(U^{(N)}\), reindexed to the
configuration basis of the chosen finite integer interval.

Source: arXiv:1703.09188, equation `eq:appendix-1`, lines 2300--2306. -/
noncomputable def finiteChainMPOMatrix {d D : ℕ} (U : MPOTensor d D)
    (N : ℕ) (a : ℤ) : LocalAlgebra d (finiteChainRegion a N) :=
  CStarMatrix.ofMatrixStarAlgEquiv
    (Matrix.reindex (finiteChainConfigEquiv d N a) (finiteChainConfigEquiv d N a)
      (MPOTensor.mpo U N))

/-- For the paper's explicit convention `N > 1`, the reindexed finite-chain
operator \(U^{(N)}\) is unitary.

Source: arXiv:1703.09188, equations `UisUnitary` and `eq:appendix-1`,
lines 327--335 and 2300--2306. -/
noncomputable def finiteChainMPUUnitary {d D : ℕ} {U : MPOTensor d D}
    (hU : U.IsMPU) {N : ℕ} (hN : 1 < N) (a : ℤ) :
    unitary (LocalAlgebra d (finiteChainRegion a N)) := by
  let e := finiteChainConfigEquiv d N a
  let M := Matrix.reindex e e (MPOTensor.mpo U N)
  have hM : M ∈ Matrix.unitaryGroup (Config d (finiteChainRegion a N)) ℂ :=
    Matrix.reindex_mem_unitaryGroup e (MPOTensor.mpo U N) (hU.mpo_mem_unitaryGroup hN)
  refine ⟨finiteChainMPOMatrix U N a, ?_⟩
  change star M * M = 1 ∧ M * star M = 1
  exact ⟨Matrix.mem_unitaryGroup_iff'.mp hM, Matrix.mem_unitaryGroup_iff.mp hM⟩

/-- Conjugation by the finite-chain MPU unitary, in the source order
\(A\mapsto U^{(N)} A U^{(N)\dagger}\).

Source: arXiv:1703.09188, equation `eq:appendix-1`, lines 2300--2306. -/
noncomputable def finiteChainConjugation {d D : ℕ} {U : MPOTensor d D}
    (hU : U.IsMPU) {N : ℕ} (hN : 1 < N) (a : ℤ) :
    LocalAlgebra d (finiteChainRegion a N) ≃⋆ₐ[ℂ]
      LocalAlgebra d (finiteChainRegion a N) :=
  Unitary.conjStarAlgAut ℂ _ (finiteChainMPUUnitary hU hN a)

/-- Finite-chain conjugation has the pointwise formula
\(U^{(N)} A U^{(N)\dagger}\), with the factors in the order used in
`eq:appendix-1`.

Source: arXiv:1703.09188, equation `eq:appendix-1`, lines 2300--2306. -/
@[simp]
lemma finiteChainConjugation_apply {d D : ℕ} {U : MPOTensor d D}
    (hU : U.IsMPU) {N : ℕ} (hN : 1 < N) (a : ℤ)
    (A : LocalAlgebra d (finiteChainRegion a N)) :
    finiteChainConjugation hU hN a A =
      finiteChainMPOMatrix U N a * A * star (finiteChainMPOMatrix U N a) :=
  rfl

/-- Include an observable `A` supported on `Λ` into the chosen finite interval,
apply the finite-chain conjugation \(U^{(N)} A_L U^{(N)\dagger}\), and regard the
result as an algebraic local observable.

Source: arXiv:1703.09188, equation `eq:appendix-1`, lines 2300--2306. -/
noncomputable def finiteChainLocalObservable {d D : ℕ} {U : MPOTensor d D}
    (hU : U.IsMPU) {N : ℕ} (hN : 1 < N) (a : ℤ) {Λ : Finset ℤ}
    (hΛ : Λ ⊆ finiteChainRegion a N) :
    LocalAlgebra d Λ →⋆ₐ[ℂ] AlgebraicLocalAlgebra d :=
  (localObservable d (finiteChainRegion a N)).comp
    ((finiteChainConjugation hU hN a).toStarAlgHom.comp (localInclusion hΛ))

/-- The local-observable map is exactly the finite-`N` term
\(U^{(N)} A_L U^{(N)\dagger}\) from `eq:appendix-1`.

Source: arXiv:1703.09188, equation `eq:appendix-1`, lines 2300--2306. -/
@[simp]
lemma finiteChainLocalObservable_apply {d D : ℕ} {U : MPOTensor d D}
    (hU : U.IsMPU) {N : ℕ} (hN : 1 < N) (a : ℤ) {Λ : Finset ℤ}
    (hΛ : Λ ⊆ finiteChainRegion a N) (A : LocalAlgebra d Λ) :
    finiteChainLocalObservable hU hN a hΛ A =
      localObservable d (finiteChainRegion a N)
        (finiteChainMPOMatrix U N a * localInclusion hΛ A *
          star (finiteChainMPOMatrix U N a)) :=
  rfl

end SpinChain
