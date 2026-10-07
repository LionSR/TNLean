/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.QuasiLocal
import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# Extension of compatible finite-region states

A family of complex-linear functionals on all finite-region observable algebras,
compatible under identity-tensor inclusions and uniformly contractive, induces
a bounded linear functional on the algebraic local algebra. It therefore
extends uniquely to the quasi-local completion. If the finite-region
functionals are normalized and positive on adjoint squares, their extension
has norm one and remains positive on adjoint squares.

This is an extension theorem with an explicit compatibility hypothesis. It
makes no assertion that a particular tensor supplies such a family.

Source: the inductive limit of finite-region observable algebras and its norm
completion in arXiv:1703.09188, Appendix, lines 2292--2300, together with the
state conventions of Nachtergaele, arXiv:cond-mat/9410110, lines 854--887.
-/

open scoped ComplexOrder

namespace SpinChain

-- The algebraic limit is equipped with its operator-norm topology.
noncomputable local instance (d : ℕ) [NeZero d] : TopologicalSpace (AlgebraicLocalAlgebra d) :=
  (inferInstance : MetricSpace (AlgebraicLocalAlgebra d)).toUniformSpace.toTopologicalSpace
attribute [local instance] CStarMatrix.instNorm CStarMatrix.instNormedAddCommGroup
  CStarMatrix.instNormedRing CStarMatrix.instCStarRing

/-- A compatible family of normalized positive contractive linear functionals
on the finite-region observable algebras. Compatibility under region enlargement
is part of the data. Source: arXiv:1703.09188, Appendix, lines 2292--2296;
Nachtergaele, arXiv:cond-mat/9410110, lines 854--887. -/
structure CompatibleLocalState (d : ℕ) where
  /-- The functional on each finite region. -/
  functional : (Λ : Finset ℤ) → LocalAlgebra d Λ →ₗ[ℂ] ℂ
  /-- Enlarging a region preserves expectation values. -/
  compatible : ∀ (Λ Γ : Finset ℤ) (h : Λ ⊆ Γ) (X : LocalAlgebra d Λ),
    functional Γ (localInclusion h X) = functional Λ X
  /-- Every finite-region functional is contractive. -/
  norm_le : ∀ (Λ : Finset ℤ) (X : LocalAlgebra d Λ), ‖functional Λ X‖ ≤ ‖X‖
  /-- Every finite-region functional is normalized. -/
  map_one : ∀ Λ : Finset ℤ, functional Λ 1 = 1
  /-- Every finite-region functional is positive on adjoint squares. -/
  nonneg_star_mul_self : ∀ (Λ : Finset ℤ) (X : LocalAlgebra d Λ),
    0 ≤ functional Λ (star X * X)

namespace CompatibleLocalState
variable {d : ℕ} (f : CompatibleLocalState d)

/-- The linear functional induced on the algebraic direct limit.
Source: arXiv:1703.09188, Appendix, lines 2292--2296. -/
noncomputable def algebraicFunctional : AlgebraicLocalAlgebra d →ₗ[ℂ] ℂ :=
  DirectLimit.Module.lift ℂ (Finset ℤ) (LocalAlgebra d) (localAlgebraMap d)
    f.functional f.compatible

/-- The algebraic extension agrees with the supplied finite-region functional.
Source: arXiv:1703.09188, Appendix, lines 2292--2296. -/
@[simp] theorem algebraicFunctional_localObservable (Λ : Finset ℤ)
    (X : LocalAlgebra d Λ) :
    f.algebraicFunctional (localObservable d Λ X) = f.functional Λ X := rfl

/-- The algebraic extension is contractive in the operator norm.
Source: arXiv:1703.09188, Appendix, lines 2292--2300. -/
theorem algebraicFunctional_norm_le [NeZero d] (X : AlgebraicLocalAlgebra d) :
    ‖f.algebraicFunctional X‖ ≤ ‖X‖ := by
  induction X using DirectLimit.induction with
  | _ Λ X => exact f.norm_le Λ X

/-- The continuous linear functional on the algebraic local algebra.
Source: arXiv:1703.09188, Appendix, lines 2292--2300. -/
noncomputable def algebraicContinuousFunctional [NeZero d] :
    AlgebraicLocalAlgebra d →L[ℂ] ℂ :=
  f.algebraicFunctional.mkContinuous 1
    (fun X => by simpa only [one_mul] using f.algebraicFunctional_norm_le X)

/-- The continuous linear extension to the quasi-local algebra.
Source: arXiv:1703.09188, Appendix, lines 2292--2300. -/
noncomputable def quasiLocalFunctional [NeZero d] : QuasiLocalAlgebra d →L[ℂ] ℂ :=
  f.algebraicContinuousFunctional.fromCompletion

/-- The completed extension agrees with its algebraic restriction.
Source: arXiv:1703.09188, Appendix, lines 2292--2300. -/
@[simp] theorem quasiLocalFunctional_algebraicToQuasiLocal [NeZero d]
    (X : AlgebraicLocalAlgebra d) :
    f.quasiLocalFunctional (algebraicToQuasiLocal d X) = f.algebraicFunctional X :=
  ContinuousLinearMap.fromCompletion_apply_coe f.algebraicContinuousFunctional X

/-- The completed extension agrees with every finite-region functional.
Source: arXiv:1703.09188, Appendix, lines 2292--2300. -/
@[simp] theorem quasiLocalFunctional_quasiLocalObservable [NeZero d]
    (Λ : Finset ℤ) (X : LocalAlgebra d Λ) :
    f.quasiLocalFunctional (quasiLocalObservable d Λ X) = f.functional Λ X :=
  f.quasiLocalFunctional_algebraicToQuasiLocal (localObservable d Λ X)

/-- Positivity on adjoint squares extends from finite regions to the completion.
Source: arXiv:1703.09188, Appendix, lines 2292--2300; Nachtergaele,
arXiv:cond-mat/9410110, lines 854--887. -/
theorem quasiLocalFunctional_nonneg_star_mul_self [NeZero d]
    (X : QuasiLocalAlgebra d) : 0 ≤ f.quasiLocalFunctional (star X * X) := by
  refine UniformSpace.Completion.induction_on X ?_ ?_
  · exact isClosed_le continuous_const
      (f.quasiLocalFunctional.continuous.comp (continuous_star.mul continuous_id))
  · intro a
    induction a using DirectLimit.induction with
    | _ Λ a =>
      change 0 ≤ f.quasiLocalFunctional
        (star (quasiLocalObservable d Λ a) * quasiLocalObservable d Λ a)
      simpa only [← map_star, ← map_mul, quasiLocalFunctional_quasiLocalObservable]
        using f.nonneg_star_mul_self Λ a

/-- The completed functional preserves normalization.
Source: arXiv:1703.09188, Appendix, lines 2292--2300. -/
@[simp] theorem quasiLocalFunctional_one [NeZero d] : f.quasiLocalFunctional 1 = 1 := by
  rw [← (quasiLocalObservable d ∅).map_one]
  exact (f.quasiLocalFunctional_quasiLocalObservable ∅ 1).trans (f.map_one ∅)

/-- The completed extension is contractive.
Source: arXiv:1703.09188, Appendix, lines 2292--2300. -/
theorem quasiLocalFunctional_norm_le [NeZero d] (X : QuasiLocalAlgebra d) :
    ‖f.quasiLocalFunctional X‖ ≤ ‖X‖ := by
  refine UniformSpace.Completion.induction_on X ?_ ?_
  · exact isClosed_le (f.quasiLocalFunctional.continuous.norm) continuous_norm
  · intro a
    simpa only [quasiLocalFunctional, ContinuousLinearMap.fromCompletion_apply_coe,
      UniformSpace.Completion.norm_coe, algebraicContinuousFunctional,
      LinearMap.mkContinuous_apply] using f.algebraicFunctional_norm_le a

/-- The completed normalized functional has norm one.
Source: arXiv:1703.09188, Appendix, lines 2292--2300. -/
theorem norm_quasiLocalFunctional [NeZero d] : ‖f.quasiLocalFunctional‖ = 1 := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun X => by simpa only [one_mul] using f.quasiLocalFunctional_norm_le X)
  · have h := f.quasiLocalFunctional.le_opNorm
      (quasiLocalObservable d ∅ (1 : LocalAlgebra d ∅))
    simpa only [quasiLocalFunctional_quasiLocalObservable, f.map_one,
      norm_quasiLocalObservable, norm_one, mul_one] using h

/-- A continuous linear functional is determined by its finite-region values.
Source: arXiv:1703.09188, Appendix, lines 2292--2300. -/
theorem quasiLocalFunctional_unique [NeZero d]
    (ω : QuasiLocalAlgebra d →L[ℂ] ℂ)
    (hω : ∀ (Λ : Finset ℤ) (X : LocalAlgebra d Λ),
      ω (quasiLocalObservable d Λ X) = f.functional Λ X) :
    ω = f.quasiLocalFunctional := by
  apply ContinuousLinearMap.ext
  intro X
  refine UniformSpace.Completion.induction_on X ?_ ?_
  · exact isClosed_eq ω.continuous f.quasiLocalFunctional.continuous
  · intro a
    induction a using DirectLimit.induction with
    | _ Λ a =>
      exact (hω Λ a).trans (f.quasiLocalFunctional_quasiLocalObservable Λ a).symm

/-- There is a unique normalized positive norm-one continuous linear extension
of the compatible finite-region functionals.
Source: arXiv:1703.09188, Appendix, lines 2292--2300; Nachtergaele,
arXiv:cond-mat/9410110, lines 854--887. -/
theorem existsUnique_quasiLocalFunctional [NeZero d] :
    ∃! ω : QuasiLocalAlgebra d →L[ℂ] ℂ,
      (∀ (Λ : Finset ℤ) (X : LocalAlgebra d Λ),
        ω (quasiLocalObservable d Λ X) = f.functional Λ X) ∧
      ‖ω‖ = 1 ∧ ω 1 = 1 ∧ ∀ X, 0 ≤ ω (star X * X) := by
  refine ⟨f.quasiLocalFunctional, ?_, ?_⟩
  · exact ⟨f.quasiLocalFunctional_quasiLocalObservable, f.norm_quasiLocalFunctional,
      f.quasiLocalFunctional_one, f.quasiLocalFunctional_nonneg_star_mul_self⟩
  · exact fun ω hω => f.quasiLocalFunctional_unique ω hω.1

end CompatibleLocalState
end SpinChain
