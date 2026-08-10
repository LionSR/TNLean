/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.CStarCompletion
import TNLean.QCA.LocalNorm

/-!
# The quasi-local algebra of a one-dimensional spin chain

The quasi-local algebra is the norm completion of the algebraic local observable algebra. Its
canonical algebraic and finite-region maps preserve the operator norm. The algebraic map has dense
range, and the union of the ranges of all finite-region maps is dense.

No single finite-region algebra has dense image in the quasi-local algebra.

## Main definitions

* `SpinChain.QuasiLocalAlgebra` — the completed local observable C-star algebra.
* `SpinChain.algebraicToQuasiLocal` — the dense algebraic star-algebra map.
* `SpinChain.quasiLocalObservable` — the canonical map from a finite region.

## Main results

* `SpinChain.quasiLocalObservable_isometry` — finite-region maps preserve distance.
* `SpinChain.denseRange_algebraicToQuasiLocal` — algebraic local observables are dense.
* `SpinChain.dense_iUnion_range_quasiLocalObservable` — the union over all finite regions is dense.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2285--2300.
-/

open scoped ComplexOrder

namespace SpinChain

attribute [local instance] CStarMatrix.instNorm CStarMatrix.instNormedAddCommGroup
  CStarMatrix.instNormedRing CStarMatrix.instCStarRing

/-- The quasi-local observable algebra is the operator-norm completion of the algebraic local
algebra.

Source: arXiv:1703.09188, Appendix, lines 2292--2300. -/
abbrev QuasiLocalAlgebra (d : ℕ) [NeZero d] :=
  UniformSpace.Completion (AlgebraicLocalAlgebra d)

/-- The canonical star-algebra homomorphism from algebraic local observables to quasi-local
observables.

Source: arXiv:1703.09188, Appendix, lines 2296--2300. -/
noncomputable def algebraicToQuasiLocal (d : ℕ) [NeZero d] :
    AlgebraicLocalAlgebra d →⋆ₐ[ℂ] QuasiLocalAlgebra d :=
  UniformSpace.Completion.toComplStarAlgHom

/-- The canonical map from the finite-region observable algebra into the quasi-local algebra.

Source: arXiv:1703.09188, Appendix, lines 2285--2300. -/
noncomputable def quasiLocalObservable (d : ℕ) [NeZero d] (Λ : Finset ℤ) :
    LocalAlgebra d Λ →⋆ₐ[ℂ] QuasiLocalAlgebra d :=
  (algebraicToQuasiLocal d).comp (localObservable d Λ)

/-- The algebraic embedding into the quasi-local algebra preserves norm. -/
@[simp]
theorem norm_algebraicToQuasiLocal (d : ℕ) [NeZero d] (A : AlgebraicLocalAlgebra d) :
    ‖algebraicToQuasiLocal d A‖ = ‖A‖ :=
  UniformSpace.Completion.norm_coe A

/-- Every finite-region map into the quasi-local algebra preserves the operator norm.

Source: arXiv:1703.09188, Appendix, lines 2292--2300. -/
@[simp]
theorem norm_quasiLocalObservable (d : ℕ) [NeZero d] (Λ : Finset ℤ)
    (A : LocalAlgebra d Λ) :
    ‖quasiLocalObservable d Λ A‖ = ‖A‖ := by
  rw [quasiLocalObservable, StarAlgHom.comp_apply, norm_algebraicToQuasiLocal,
    norm_localObservable]

/-- Every finite-region map into the quasi-local algebra is an isometry.

Source: arXiv:1703.09188, Appendix, lines 2292--2300. -/
theorem quasiLocalObservable_isometry (d : ℕ) [NeZero d] (Λ : Finset ℤ) :
    Isometry (quasiLocalObservable d Λ) := by
  rw [isometry_iff_dist_eq]
  intro A B
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_quasiLocalObservable]

/-- Every finite-region map into the quasi-local algebra is injective. -/
theorem quasiLocalObservable_injective (d : ℕ) [NeZero d] (Λ : Finset ℤ) :
    Function.Injective (quasiLocalObservable d Λ) :=
  (quasiLocalObservable_isometry d Λ).injective

/-- Enlarging a finite region does not change the associated quasi-local observable. -/
@[simp]
theorem quasiLocalObservable_localInclusion (d : ℕ) [NeZero d]
    {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ) (A : LocalAlgebra d Λ) :
    quasiLocalObservable d Γ (localInclusion h A) = quasiLocalObservable d Λ A := by
  simp only [quasiLocalObservable, StarAlgHom.comp_apply,
    localObservable_localInclusion]

/-- Algebraic local observables have dense image in the quasi-local algebra.

Source: arXiv:1703.09188, Appendix, lines 2296--2300. -/
theorem denseRange_algebraicToQuasiLocal (d : ℕ) [NeZero d] :
    DenseRange (algebraicToQuasiLocal d) :=
  UniformSpace.Completion.denseRange_toComplStarAlgHom

/-- The union of the images of all finite-region observable algebras is dense in the quasi-local
algebra.

The union ranges over every finite region; no fixed finite-region image is asserted to be dense.
Source: arXiv:1703.09188, Appendix, lines 2285--2300. -/
theorem dense_iUnion_range_quasiLocalObservable (d : ℕ) [NeZero d] :
    Dense (⋃ Λ : Finset ℤ, Set.range (quasiLocalObservable d Λ)) := by
  apply Dense.mono _ (denseRange_algebraicToQuasiLocal d)
  rintro x ⟨A, rfl⟩
  obtain ⟨Λ, a, ha⟩ := exists_supportedIn A
  rw [← ha]
  exact Set.mem_iUnion.2 ⟨Λ, ⟨a, rfl⟩⟩

end SpinChain
