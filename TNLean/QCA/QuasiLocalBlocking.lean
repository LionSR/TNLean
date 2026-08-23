/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.AlgebraicBlocking
import TNLean.QCA.FinitePropagation

/-!
# Blocking quasi-local observables

The algebraic-local site-blocking equivalence and its inverse are operator-norm isometries, so they
extend to an equivalence of quasi-local completions.  On finite observables, forward blocking
expands a blocked region, while reverse blocking uses the block hull of an arbitrary original
region.  Consequently finite support transports in both directions, and support on an exactly
expanded region is equivalent before and after blocking.

This file only constructs the quasi-local completion and transports finite support.  It does not
introduce scaled translations, blocked neighborhoods, propagation estimates, automorphism
conjugation, or transport of the QCA predicate.

## Main definitions

* `SpinChain.quasiLocalBlocking` — site blocking on quasi-local observable algebras.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2308 and
  2313--2320.
-/

open scoped ComplexOrder

namespace SpinChain

attribute [local instance] CStarMatrix.instNorm CStarMatrix.instNormedAddCommGroup
  CStarMatrix.instNormedRing CStarMatrix.instCStarRing

/-- Blocking consecutive groups of `L` sites extends to an equivalence between the blocked and
original quasi-local observable algebras.

This is the quasi-local completion of the site grouping used in
Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2308 and 2313--2320. -/
noncomputable def quasiLocalBlocking (d L : ℕ) [NeZero d] [NeZero L] :
    QuasiLocalAlgebra (MPSTensor.blockPhysDim d L) ≃⋆ₐ[ℂ] QuasiLocalAlgebra d :=
  UniformSpace.Completion.mapStarAlgEquiv
    (algebraicLocalBlocking d L)
    (algebraicLocalBlocking_isometry d L).continuous
    (algebraicLocalBlocking_symm_isometry d L).continuous

/-- Quasi-local blocking acts by the completion map of algebraic-local blocking. -/
lemma quasiLocalBlocking_apply (d L : ℕ) [NeZero d] [NeZero L]
    (A : QuasiLocalAlgebra (MPSTensor.blockPhysDim d L)) :
    quasiLocalBlocking d L A =
      UniformSpace.Completion.map (algebraicLocalBlocking d L) A :=
  rfl

/-- Quasi-local blocking agrees with algebraic-local blocking on the dense algebraic subalgebra. -/
@[simp]
lemma quasiLocalBlocking_algebraicToQuasiLocal (d L : ℕ) [NeZero d] [NeZero L]
    (A : AlgebraicLocalAlgebra (MPSTensor.blockPhysDim d L)) :
    quasiLocalBlocking d L (algebraicToQuasiLocal _ A) =
      algebraicToQuasiLocal d (algebraicLocalBlocking d L A) :=
  UniformSpace.Completion.mapStarAlgEquiv_coe _ _ _ A

/-- Inverse quasi-local blocking agrees with inverse algebraic-local blocking on the dense
algebraic subalgebra. -/
@[simp]
lemma quasiLocalBlocking_symm_algebraicToQuasiLocal (d L : ℕ) [NeZero d] [NeZero L]
    (A : AlgebraicLocalAlgebra d) :
    (quasiLocalBlocking d L).symm (algebraicToQuasiLocal d A) =
      algebraicToQuasiLocal _ ((algebraicLocalBlocking d L).symm A) :=
  UniformSpace.Completion.mapStarAlgEquiv_coe
    (algebraicLocalBlocking d L).symm
    (algebraicLocalBlocking_symm_isometry d L).continuous
    (algebraicLocalBlocking_isometry d L).continuous A

/-- Quasi-local blocking sends a finite blocked representative to its finite blocking on the
expanded original region. -/
lemma quasiLocalBlocking_quasiLocalObservable (d L : ℕ) [NeZero d] [NeZero L]
    (Λ : Finset ℤ) (A : LocalAlgebra (MPSTensor.blockPhysDim d L) Λ) :
    quasiLocalBlocking d L (quasiLocalObservable _ Λ A) =
      quasiLocalObservable d (expandedRegion L Λ) (localBlocking d L Λ A) := by
  simp only [quasiLocalObservable, StarAlgHom.comp_apply,
    quasiLocalBlocking_algebraicToQuasiLocal, algebraicLocalBlocking_localObservable]

/-- Inverse quasi-local blocking enlarges an arbitrary finite original region to its block hull and
then applies inverse finite blocking. -/
lemma quasiLocalBlocking_symm_quasiLocalObservable (d L : ℕ) [NeZero d] [NeZero L]
    (Δ : Finset ℤ) (A : LocalAlgebra d Δ) :
    (quasiLocalBlocking d L).symm (quasiLocalObservable d Δ A) =
      quasiLocalObservable _ (blockHull L Δ)
        ((localBlocking d L (blockHull L Δ)).symm
          (localInclusion (subset_expandedRegion_blockHull L Δ) A)) := by
  simp only [quasiLocalObservable, StarAlgHom.comp_apply,
    quasiLocalBlocking_symm_algebraicToQuasiLocal,
    algebraicLocalBlocking_symm_localObservable]

/-- On an expanded region, inverse quasi-local blocking is exactly inverse finite blocking. -/
lemma quasiLocalBlocking_symm_quasiLocalObservable_expandedRegion
    (d L : ℕ) [NeZero d] [NeZero L] (Λ : Finset ℤ)
    (A : LocalAlgebra d (expandedRegion L Λ)) :
    (quasiLocalBlocking d L).symm
        (quasiLocalObservable d (expandedRegion L Λ) A) =
      quasiLocalObservable _ Λ ((localBlocking d L Λ).symm A) := by
  simp only [quasiLocalObservable, StarAlgHom.comp_apply,
    quasiLocalBlocking_symm_algebraicToQuasiLocal,
    algebraicLocalBlocking_symm_localObservable_expandedRegion]

/-- Quasi-local blocking preserves the operator norm. -/
@[simp]
lemma norm_quasiLocalBlocking (d L : ℕ) [NeZero d] [NeZero L]
    (A : QuasiLocalAlgebra (MPSTensor.blockPhysDim d L)) :
    ‖quasiLocalBlocking d L A‖ = ‖A‖ :=
  StarAlgEquiv.norm_map (quasiLocalBlocking d L) A

/-- Quasi-local blocking is an operator-norm isometry. -/
lemma quasiLocalBlocking_isometry (d L : ℕ) [NeZero d] [NeZero L] :
    Isometry (quasiLocalBlocking d L) :=
  StarAlgEquiv.isometry (quasiLocalBlocking d L)

/-- Forward quasi-local blocking sends support in a blocked region to support in its expanded
original region. -/
lemma quasiLocalBlocking_supportedIn
    (d L : ℕ) [NeZero d] [NeZero L]
    {A : QuasiLocalAlgebra (MPSTensor.blockPhysDim d L)} {Λ : Finset ℤ}
    (hA : QuasiLocalSupportedIn A Λ) :
    QuasiLocalSupportedIn (quasiLocalBlocking d L A) (expandedRegion L Λ) := by
  obtain ⟨a, rfl⟩ := hA
  exact ⟨localBlocking d L Λ a, (quasiLocalBlocking_quasiLocalObservable d L Λ a).symm⟩

/-- Reverse quasi-local blocking sends support in an original region to support in its block
hull. -/
lemma quasiLocalBlocking_symm_supportedIn
    (d L : ℕ) [NeZero d] [NeZero L]
    {A : QuasiLocalAlgebra d} {Δ : Finset ℤ} (hA : QuasiLocalSupportedIn A Δ) :
    QuasiLocalSupportedIn ((quasiLocalBlocking d L).symm A) (blockHull L Δ) := by
  obtain ⟨a, rfl⟩ := hA
  exact ⟨_, (quasiLocalBlocking_symm_quasiLocalObservable d L Δ a).symm⟩

/-- A blocked observable is supported in `Λ` exactly when its quasi-local blocking is supported in
the expanded original region. -/
lemma quasiLocalBlocking_supportedIn_expandedRegion_iff
    (d L : ℕ) [NeZero d] [NeZero L]
    {A : QuasiLocalAlgebra (MPSTensor.blockPhysDim d L)} {Λ : Finset ℤ} :
    QuasiLocalSupportedIn (quasiLocalBlocking d L A) (expandedRegion L Λ) ↔
      QuasiLocalSupportedIn A Λ := by
  constructor
  · intro hA
    have h := quasiLocalBlocking_symm_supportedIn d L hA
    simpa only [StarAlgEquiv.symm_apply_apply, blockHull_expandedRegion] using h
  · exact quasiLocalBlocking_supportedIn d L

end SpinChain
