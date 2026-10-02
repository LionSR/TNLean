/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LocalObservableQuasiLocalState
import TNLean.QCA.QuasiLocalInterval
import TNLean.MPS.ParentHamiltonian.PhysicalDeformation

/-!
# Exact local support of the quasi-local MPS state

An observable that annihilates the finite-interval MPS space has zero
insertion transfer map, since its boundary-map compression is the Choi
reshuffling of that map. Its trace insertion expectation therefore vanishes.
The compatible quasi-local state inherits this support property at every
interval position. In particular, every local positive parent interaction
has expectation zero. No primitivity or purity is assumed.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1 and equations
(3.1)--(3.2b); CPGSV21, arXiv:2011.12127, lines 1996--1999.
-/

open scoped Matrix ComplexOrder BigOperators
open SpinChain
namespace MPSTensor
variable {d D k : ℕ}

/-- An observable annihilating the local MPS space has zero insertion map.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b)
and the local support definition in Theorem 1.1. -/
private theorem physicalObservableTransfer_eq_zero_of_groundSpaceES_le_ker
    (A : MPSTensor d D) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hX : groundSpaceES A k ≤ LinearMap.ker (Matrix.toEuclideanLin X)) :
    physicalObservableTransfer A k X = 0 := by
  have hcomp : (Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ) X).comp
      (groundSpaceMapES A k) = 0 := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact LinearMap.mem_ker.mp (hX ((range_groundSpaceMapES A k).le ⟨v, rfl⟩))
  have hR : Matrix.gramReshuffle (physicalObservableTransfer A k X) = 0 := by
    rw [← adjoint_groundSpaceMapES_observable_groundSpaceMapES, hcomp]
    simp
  apply (Matrix.stdBasis ℂ (Fin D) (Fin D)).ext
  rintro ⟨c, a⟩
  ext e b
  simpa [Matrix.stdBasis_eq_single] using
    congrArg (fun T => inner ℂ (EuclideanSpace.single (b, a) 1)
      (T (EuclideanSpace.single (e, c) 1))) hR

/-- The trace insertion expectation vanishes on an observable that annihilates
the local MPS space. No normalization or positivity assumption is needed.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b)
and Theorem 1.1, local support spaces. -/
theorem observableInsertionExpectation_eq_zero_of_groundSpaceES_le_ker
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hX : groundSpaceES A k ≤ LinearMap.ker (Matrix.toEuclideanLin X)) :
    observableInsertionExpectation A ρ X = 0 := by
  simp [observableInsertionExpectation,
    physicalObservableTransfer_eq_zero_of_groundSpaceES_le_ker A X hX]

/-- The completed state vanishes on every consecutive observable annihilating
its local MPS support. Source: Nachtergaele, arXiv:cond-mat/9410110,
Theorem 1.1 and equations (3.1)--(3.2b). -/
theorem quasiLocalExpectation_interval_eq_zero_of_groundSpaceES_le_ker [NeZero d]
    (A : MPSTensor d D) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (hfix : Kraus.transferMap A ρ = ρ) (htr : Matrix.trace ρ ≠ 0)
    (a : ℤ) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hX : groundSpaceES A k ≤ LinearMap.ker (Matrix.toEuclideanLin X)) :
    quasiLocalExpectation A hTP hρ hfix htr
      (quasiLocalIntervalObservable d a k X) = 0 := by
  rw [quasiLocalIntervalObservable_apply, quasiLocalExpectation_interval,
    StarAlgEquiv.apply_symm_apply]
  exact observableInsertionExpectation_eq_zero_of_groundSpaceES_le_ker A ρ X hX

/-- The constructed quasi-local state has zero expectation for every translate
of a positive parent interaction. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.1; CPGSV21, arXiv:2011.12127,
lines 1996--1999. -/
theorem IsParentInteraction.quasiLocalExpectation_interval_eq_zero [NeZero d]
    {A : MPSTensor d D} (hTP : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (hfix : Kraus.transferMap A ρ = ρ) (htr : Matrix.trace ρ ≠ 0)
    {X : Matrix (Cfg d k) (Cfg d k) ℂ}
    (hX : IsParentInteraction A k (Matrix.toEuclideanLin X)) (a : ℤ) :
    quasiLocalExpectation A hTP hρ hfix htr
      (quasiLocalIntervalObservable d a k X) = 0 := by
  exact quasiLocalExpectation_interval_eq_zero_of_groundSpaceES_le_ker
    A hTP hρ hfix htr a X hX.ker_eq.ge

end MPSTensor
