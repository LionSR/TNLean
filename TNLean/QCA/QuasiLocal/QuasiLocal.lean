/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Norm.CStarCompletion
import TNLean.QCA.QuasiLocal.LocalNorm

/-!
# The quasi-local algebra of a one-dimensional spin chain

The quasi-local algebra is the norm completion of the algebraic local observable algebra. Its
canonical algebraic and finite-region maps preserve the operator norm. The algebraic map has dense
range, and the union of the ranges of all finite-region maps is dense.

The finite-region density result concerns the union of all finite-region images; it makes no
claim about the image of a fixed region.

## Main definitions

* `SpinChain.QuasiLocalAlgebra` — the completed local observable C-star algebra.
* `SpinChain.algebraicToQuasiLocal` — the dense algebraic star-algebra map.
* `SpinChain.quasiLocalObservable` — the canonical map from a finite region.
* `SpinChain.QuasiLocalSupportedIn` — membership in a finite-region observable algebra.
* `SpinChain.matrixToQuasiLocalObservable` — the canonical map from ordinary finite-region
  matrices.

## Main results

* `SpinChain.quasiLocalObservable_isometry` — finite-region maps preserve distance.
* `SpinChain.denseRange_algebraicToQuasiLocal` — algebraic local observables are dense.
* `SpinChain.dense_iUnion_range_quasiLocalObservable` — all finite-region images have dense
  union.
* `SpinChain.QuasiLocalSupportedIn.quasiLocalObservable` — every embedded finite-region
  observable is supported in its region.
* `SpinChain.QuasiLocalSupportedIn.mono` — support is monotone under region enlargement.
* `SpinChain.matrixToQuasiLocalObservable_supportedIn` — an embedded matrix is supported in its
  region.

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

/-- A quasi-local observable is supported in the finite region \(\Lambda\) when it belongs to the
range of the canonical map from \(\mathcal A_\Lambda\).

Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
def QuasiLocalSupportedIn {d : ℕ} [NeZero d] (x : QuasiLocalAlgebra d)
    (Λ : Finset ℤ) : Prop :=
  x ∈ Set.range (quasiLocalObservable d Λ)

namespace QuasiLocalSupportedIn

variable {d : ℕ} [NeZero d] {x : QuasiLocalAlgebra d} {Λ Γ : Finset ℤ}

/-- Every finite-region observable, embedded in the quasi-local algebra, is supported in its
region.

Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
lemma quasiLocalObservable (A : LocalAlgebra d Λ) :
    QuasiLocalSupportedIn (SpinChain.quasiLocalObservable d Λ A) Λ :=
  ⟨A, rfl⟩

/-- A quasi-local observable is supported in a region exactly when it has a representative in
that region's finite observable algebra.

Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
lemma iff_exists :
    QuasiLocalSupportedIn x Λ ↔
      ∃ A : LocalAlgebra d Λ, SpinChain.quasiLocalObservable d Λ A = x :=
  Iff.rfl

/-- Quasi-local support is monotone under enlargement of the finite region.

Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
lemma mono (hx : QuasiLocalSupportedIn x Λ) (hΛΓ : Λ ⊆ Γ) :
    QuasiLocalSupportedIn x Γ := by
  obtain ⟨A, rfl⟩ := hx
  exact ⟨localInclusion hΛΓ A, quasiLocalObservable_localInclusion d hΛΓ A⟩

end QuasiLocalSupportedIn

/-! ### Canonical matrix observables -/

/-- The canonical star-algebra homomorphism from ordinary matrices in finite-region coordinates
to the quasi-local algebra.

It first identifies a matrix with the corresponding element of the finite local C*-algebra and
then applies the canonical quasi-local inclusion. Under this identification, it is the
finite-region inclusion used by Cirac et al., arXiv:1703.09188, lines 2292--2298. It also realizes
the finite-cell inclusions surrounding GNVW equation `RR2x`, arXiv:0910.3675v2,
lines 1251--1274; neither source names the composition separately. -/
noncomputable def matrixToQuasiLocalObservable (d : ℕ) [NeZero d] (Λ : Finset ℤ) :
    Matrix (Config d Λ) (Config d Λ) ℂ →⋆ₐ[ℂ] QuasiLocalAlgebra d :=
  (quasiLocalObservable d Λ).comp CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom

/-- A matrix embedded by `matrixToQuasiLocalObservable` is supported in its defining finite
region.

This is the support property of the canonical finite-region inclusion used by Cirac et al.,
arXiv:1703.09188, lines 2292--2298; it is not a separately stated source theorem. -/
theorem matrixToQuasiLocalObservable_supportedIn (d : ℕ) [NeZero d] (Λ : Finset ℤ)
    (a : Matrix (Config d Λ) (Config d Λ) ℂ) :
    QuasiLocalSupportedIn (matrixToQuasiLocalObservable d Λ a) Λ := by
  change QuasiLocalSupportedIn
    (quasiLocalObservable d Λ (CStarMatrix.ofMatrixStarAlgEquiv a)) Λ
  exact QuasiLocalSupportedIn.quasiLocalObservable _

end SpinChain
