/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LocalObservableRegionExpectation
import TNLean.QCA.CompatibleLocalState

/-!
# The quasi-local MPS expectation

A trace-preserving tensor and a positive invariant virtual matrix of nonzero
trace determine compatible normalized positive expectations on every finite
region. Their uniform operator-norm bound gives a unique continuous extension
to the quasi-local observable algebra. The construction does not require
primitivity and makes no assertion of purity.

Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3,
equations (3.1)--(3.2b), interpreted as compatible local expectations.
-/

open scoped Matrix BigOperators ComplexOrder
open SpinChain

namespace MPSTensor

variable {d D : ℕ}

private theorem localObservableExpectation_norm_le (A : MPSTensor d D)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (hfix : Kraus.transferMap A ρ = ρ) (htr : Matrix.trace ρ ≠ 0)
    (Λ : Finset ℤ) (X : LocalAlgebra d Λ) :
    ‖localObservableExpectation A ρ Λ X‖ ≤ ‖X‖ := by
  let a := -((Λ.sup Int.natAbs : ℕ) : ℤ)
  let N := 2 * Λ.sup Int.natAbs + 1
  let hΛ : Λ ⊆ intervalRegion a N := by
    intro x hx
    have hr := Finset.le_sup (f := Int.natAbs) hx
    have hxpos := Int.le_natAbs (a := x)
    have hxneg := Int.le_natAbs (a := -x)
    simp only [Int.natAbs_neg] at hxneg
    dsimp [a, N, intervalRegion]
    simp only [Finset.mem_Ico]
    omega
  change ‖observableInsertionExpectation A ρ
    (intervalCoordinates d a N (localInclusion hΛ X))‖ ≤ ‖X‖
  refine (norm_observableInsertionExpectation_le A hρ hfix htr _).trans ?_
  change ‖((intervalCoordinates d a N).trans CStarMatrix.ofMatrixStarAlgEquiv)
    (localInclusion hΛ X)‖ ≤ ‖X‖
  exact (NonUnitalStarAlgHom.norm_apply_le _ _).trans
    (NonUnitalStarAlgHom.norm_apply_le (localInclusion hΛ) X)

private theorem localObservableExpectation_one (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hfix : Kraus.transferMap A ρ = ρ)
    (htr : Matrix.trace ρ ≠ 0) (Λ : Finset ℤ) :
    localObservableExpectation A ρ Λ 1 = 1 := by
  change observableInsertionExpectation A ρ
    (intervalCoordinates d _ _ (localInclusion _ 1)) = 1
  simp only [map_one]
  exact observableInsertionExpectation_one A ρ hfix htr _

private theorem localObservableExpectation_nonneg_star_mul_self (A : MPSTensor d D)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (Λ : Finset ℤ) (X : LocalAlgebra d Λ) :
    0 ≤ localObservableExpectation A ρ Λ (star X * X) := by
  change 0 ≤ observableInsertionExpectation A ρ
    (intervalCoordinates d _ _ (localInclusion _ (star X * X)))
  simp only [map_mul, map_star]
  exact observableInsertionExpectation_nonneg A hρ
    (Matrix.posSemidef_conjTranspose_mul_self _)

/-- The compatible normalized positive local state determined by a
trace-preserving tensor and a positive invariant virtual matrix of nonzero
trace. Source: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b). -/
noncomputable def localMPSState (A : MPSTensor d D)
    (hTP : ∑ i, (A i)ᴴ * A i = 1) {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ.PosSemidef) (hfix : Kraus.transferMap A ρ = ρ)
    (htr : Matrix.trace ρ ≠ 0) : CompatibleLocalState d where
  functional := localObservableExpectation A ρ
  compatible := fun _ _ h X => localObservableExpectation_localInclusion A ρ hTP hfix h X
  norm_le := localObservableExpectation_norm_le A hρ hfix htr
  map_one := localObservableExpectation_one A ρ hfix htr
  nonneg_star_mul_self := localObservableExpectation_nonneg_star_mul_self A hρ

/-- On a consecutive interval the local state is the trace insertion
expectation in numbered coordinates. Source: Nachtergaele,
arXiv:cond-mat/9410110, equations (3.1)--(3.2b). -/
theorem localMPSState_functional_interval (A : MPSTensor d D)
    (hTP : ∑ i, (A i)ᴴ * A i = 1) {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ.PosSemidef) (hfix : Kraus.transferMap A ρ = ρ)
    (htr : Matrix.trace ρ ≠ 0) (a : ℤ) (N : ℕ)
    (X : LocalAlgebra d (intervalRegion a N)) :
    (localMPSState A hTP hρ hfix htr).functional (intervalRegion a N) X =
      observableInsertionExpectation A ρ (intervalCoordinates d a N X) := by
  have h := localObservableExpectation_eq_of_subset_interval A ρ hTP hfix a N (by rfl) X
  rw [localInclusion_refl] at h
  exact h

/-- The continuous quasi-local expectation extending the finite-region MPS
state. Source: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), extension of compatible local expectations. -/
noncomputable def quasiLocalExpectation [NeZero d] (A : MPSTensor d D)
    (hTP : ∑ i, (A i)ᴴ * A i = 1) {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ.PosSemidef) (hfix : Kraus.transferMap A ρ = ρ)
    (htr : Matrix.trace ρ ≠ 0) : QuasiLocalAlgebra d →L[ℂ] ℂ :=
  (localMPSState A hTP hρ hfix htr).quasiLocalFunctional

/-- The completed MPS expectation agrees with its finite-region restriction.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b). -/
@[simp] theorem quasiLocalExpectation_quasiLocalObservable [NeZero d]
    (A : MPSTensor d D) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (hfix : Kraus.transferMap A ρ = ρ) (htr : Matrix.trace ρ ≠ 0)
    (Λ : Finset ℤ) (X : LocalAlgebra d Λ) :
    quasiLocalExpectation A hTP hρ hfix htr (quasiLocalObservable d Λ X) =
      localObservableExpectation A ρ Λ X :=
  (localMPSState A hTP hρ hfix htr).quasiLocalFunctional_quasiLocalObservable Λ X

/-- On every finite interval the quasi-local expectation is the original
trace insertion formula. Source: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b). -/
theorem quasiLocalExpectation_interval [NeZero d] (A : MPSTensor d D)
    (hTP : ∑ i, (A i)ᴴ * A i = 1) {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ.PosSemidef) (hfix : Kraus.transferMap A ρ = ρ)
    (htr : Matrix.trace ρ ≠ 0) (a : ℤ) (N : ℕ)
    (X : LocalAlgebra d (intervalRegion a N)) :
    quasiLocalExpectation A hTP hρ hfix htr
      (quasiLocalObservable d (intervalRegion a N) X) =
        observableInsertionExpectation A ρ (intervalCoordinates d a N X) :=
  ((localMPSState A hTP hρ hfix htr).quasiLocalFunctional_quasiLocalObservable
    (intervalRegion a N) X).trans (localMPSState_functional_interval A hTP hρ hfix htr a N X)

/-- The completed MPS expectation is normalized, positive on adjoint squares,
and has norm one. Source: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), the local GVBS state. -/
theorem quasiLocalExpectation_isState [NeZero d] (A : MPSTensor d D)
    (hTP : ∑ i, (A i)ᴴ * A i = 1) {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ.PosSemidef) (hfix : Kraus.transferMap A ρ = ρ)
    (htr : Matrix.trace ρ ≠ 0) :
    ‖quasiLocalExpectation A hTP hρ hfix htr‖ = 1 ∧
      quasiLocalExpectation A hTP hρ hfix htr 1 = 1 ∧
        ∀ X, 0 ≤ quasiLocalExpectation A hTP hρ hfix htr (star X * X) := by
  exact ⟨(localMPSState A hTP hρ hfix htr).norm_quasiLocalFunctional,
    (localMPSState A hTP hρ hfix htr).quasiLocalFunctional_one,
    (localMPSState A hTP hρ hfix htr).quasiLocalFunctional_nonneg_star_mul_self⟩

end MPSTensor
