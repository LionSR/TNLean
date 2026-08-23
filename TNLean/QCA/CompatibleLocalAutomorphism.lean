/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.IsQCA

/-!
# Compatible finite-local actions on the quasi-local algebra

A pair of compatible families of finite-region star-algebra homomorphisms, inverse after passage to
algebraic-local observables, determines a star-algebra equivalence of the algebraic local algebra.
If the forward family preserves the local operator norm, mutual invertibility makes both induced
maps isometries, so the equivalence extends to the quasi-local completion. Finite-region support and
unit-translation formulas for the forward family then imply finite propagation, translation
covariance, and the QCA predicate for the completed automorphism.

The hypotheses in this file are deliberately stated for the supplied finite-local families. No
stabilization of finite-chain observables, quantitative propagation radius, standard-form theorem,
or MPU-to-QCA construction is asserted.

## Main definitions

* `SpinChain.CompatibleLocalAutomorphism` — mutually inverse compatible finite-local families.
* `SpinChain.CompatibleLocalAutomorphism.algebraicEquiv` — the induced algebraic-local
  star-algebra equivalence.
* `SpinChain.CompatibleLocalAutomorphism.quasiLocalEquiv` — its extension to the completion.
* `SpinChain.CompatibleLocalAutomorphism.ForwardNormPreserving` — the explicit local norm
  hypothesis; inverse norm preservation follows from mutual invertibility.
* `SpinChain.CompatibleLocalAutomorphism.MapsSupportWithin` — a finite-local support bound.
* `SpinChain.CompatibleLocalAutomorphism.CommutesWithUnitTranslation` — the finite-local unit
  translation formula.

## Main results

* Dense algebraic-local and finite-region evaluation formulas for the algebraic and completed
  equivalences and their inverses.
* Local norm preservation implies forward and inverse isometry.
* A finite-local support bound implies `SpinChain.PropagatesWithin` for the completion.
* The finite-local unit-translation formula implies `SpinChain.TranslationCovariant`.
* Together these hypotheses imply `SpinChain.IsQCA`.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2292--2306.
* Schumacher--Werner, quant-ph/0405174, Definition 1.
-/

open scoped ComplexOrder

namespace SpinChain

attribute [local instance] CStarMatrix.instNorm CStarMatrix.instNormedAddCommGroup
  CStarMatrix.instNormedRing CStarMatrix.instCStarRing

/-- Mutually inverse compatible finite-local actions on the algebraic local algebra.

Each family starts on every finite-region algebra and takes values in the algebraic direct limit.
Compatibility says that enlarging the source region does not change the resulting local observable.
The last two fields say that the compatible lifts are inverse on every finite-region representative;
the universal property then makes them inverse on the whole algebraic local algebra.

Source context: arXiv:1703.09188, Appendix, lines 2292--2306, where compatible local actions are
assembled on the local algebra and then extended to its norm completion. -/
structure CompatibleLocalAutomorphism (d : ℕ) where
  /-- The forward finite-local family. -/
  forward : (Λ : Finset ℤ) → LocalAlgebra d Λ →⋆ₐ[ℂ] AlgebraicLocalAlgebra d
  /-- The inverse finite-local family. -/
  inverse : (Λ : Finset ℤ) → LocalAlgebra d Λ →⋆ₐ[ℂ] AlgebraicLocalAlgebra d
  /-- The forward family is compatible with canonical inclusions. -/
  forward_compatible : ∀ (Λ Γ : Finset ℤ) (h : Λ ⊆ Γ) (A : LocalAlgebra d Λ),
    forward Γ (localInclusion h A) = forward Λ A
  /-- The inverse family is compatible with canonical inclusions. -/
  inverse_compatible : ∀ (Λ Γ : Finset ℤ) (h : Λ ⊆ Γ) (A : LocalAlgebra d Λ),
    inverse Γ (localInclusion h A) = inverse Λ A
  /-- Applying the lifted inverse after the forward family fixes every finite representative. -/
  inverse_forward : ∀ (Λ : Finset ℤ) (A : LocalAlgebra d Λ),
    algebraicLocalAlgebraLift inverse inverse_compatible (forward Λ A) =
      localObservable d Λ A
  /-- Applying the lifted forward map after the inverse family fixes every finite representative. -/
  forward_inverse : ∀ (Λ : Finset ℤ) (A : LocalAlgebra d Λ),
    algebraicLocalAlgebraLift forward forward_compatible (inverse Λ A) =
      localObservable d Λ A

namespace CompatibleLocalAutomorphism

variable {d : ℕ} (F : CompatibleLocalAutomorphism d)

/-- The star-algebra homomorphism induced by the compatible forward finite-local family. -/
noncomputable def forwardHom :
    AlgebraicLocalAlgebra d →⋆ₐ[ℂ] AlgebraicLocalAlgebra d :=
  algebraicLocalAlgebraLift F.forward F.forward_compatible

/-- The star-algebra homomorphism induced by the compatible inverse finite-local family. -/
noncomputable def inverseHom :
    AlgebraicLocalAlgebra d →⋆ₐ[ℂ] AlgebraicLocalAlgebra d :=
  algebraicLocalAlgebraLift F.inverse F.inverse_compatible

/-- The forward algebraic-local map agrees with the supplied finite-local family. -/
@[simp]
lemma forwardHom_localObservable (Λ : Finset ℤ) (A : LocalAlgebra d Λ) :
    F.forwardHom (localObservable d Λ A) = F.forward Λ A :=
  rfl

/-- The inverse algebraic-local map agrees with the supplied finite-local family. -/
@[simp]
lemma inverseHom_localObservable (Λ : Finset ℤ) (A : LocalAlgebra d Λ) :
    F.inverseHom (localObservable d Λ A) = F.inverse Λ A :=
  rfl

/-- Compatible mutually inverse finite-local families induce a star-algebra equivalence of the
algebraic local algebra. -/
noncomputable def algebraicEquiv :
    AlgebraicLocalAlgebra d ≃⋆ₐ[ℂ] AlgebraicLocalAlgebra d where
  toFun := F.forwardHom
  invFun := F.inverseHom
  left_inv A := by
    induction A using DirectLimit.induction with
    | _ Λ A => exact F.inverse_forward Λ A
  right_inv A := by
    induction A using DirectLimit.induction with
    | _ Λ A => exact F.forward_inverse Λ A
  map_add' A B := map_add F.forwardHom A B
  map_mul' A B := map_mul F.forwardHom A B
  map_smul' c A := map_smul F.forwardHom c A
  map_star' A := map_star F.forwardHom A

/-- The algebraic-local equivalence evaluates by the lifted forward homomorphism. -/
@[simp]
lemma algebraicEquiv_apply (A : AlgebraicLocalAlgebra d) :
    F.algebraicEquiv A = F.forwardHom A :=
  rfl

/-- The inverse algebraic-local equivalence evaluates by the lifted inverse homomorphism. -/
@[simp]
lemma algebraicEquiv_symm_apply (A : AlgebraicLocalAlgebra d) :
    F.algebraicEquiv.symm A = F.inverseHom A :=
  rfl

/-- The forward finite-local family preserves the operator norm on every finite region. -/
def ForwardNormPreserving [NeZero d] : Prop :=
  ∀ (Λ : Finset ℤ) (A : LocalAlgebra d Λ), ‖F.forward Λ A‖ = ‖A‖

variable [NeZero d]

/-- A local forward norm formula extends to every algebraic-local observable. -/
lemma norm_algebraicEquiv (hF : F.ForwardNormPreserving)
    (A : AlgebraicLocalAlgebra d) : ‖F.algebraicEquiv A‖ = ‖A‖ := by
  induction A using DirectLimit.induction with
  | _ Λ A =>
      change ‖F.forward Λ A‖ = ‖localObservable d Λ A‖
      rw [hF, norm_localObservable]

/-- The induced forward algebraic-local equivalence is an isometry when the forward finite-local
family preserves norm. -/
lemma algebraicEquiv_isometry (hF : F.ForwardNormPreserving) :
    Isometry F.algebraicEquiv := by
  rw [isometry_iff_dist_eq]
  intro A B
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_algebraicEquiv F hF]

/-- Mutual invertibility makes the inverse algebraic-local equivalence an isometry whenever the
forward family preserves norm. -/
lemma algebraicEquiv_symm_isometry (hF : F.ForwardNormPreserving) :
    Isometry F.algebraicEquiv.symm :=
  (F.algebraicEquiv_isometry hF).right_inv F.algebraicEquiv.apply_symm_apply

/-- The inverse algebraic-local equivalence preserves norm; no separate inverse norm hypothesis is
needed. -/
lemma norm_algebraicEquiv_symm (hF : F.ForwardNormPreserving)
    (A : AlgebraicLocalAlgebra d) : ‖F.algebraicEquiv.symm A‖ = ‖A‖ :=
  (F.algebraicEquiv_symm_isometry hF).norm_map_of_map_zero
    (map_zero F.algebraicEquiv.symm) A

/-- The algebraic-local equivalence extends to a star-algebra equivalence of the quasi-local
completion when its forward finite-local family preserves norm. -/
noncomputable def quasiLocalEquiv (hF : F.ForwardNormPreserving) :
    QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d :=
  UniformSpace.Completion.mapStarAlgEquiv F.algebraicEquiv
    (F.algebraicEquiv_isometry hF).continuous
    (F.algebraicEquiv_symm_isometry hF).continuous

/-- The completed equivalence agrees with the algebraic-local equivalence on the dense canonical
subalgebra. -/
@[simp]
lemma quasiLocalEquiv_algebraicToQuasiLocal
    (hF : F.ForwardNormPreserving) (A : AlgebraicLocalAlgebra d) :
    F.quasiLocalEquiv hF (algebraicToQuasiLocal d A) =
      algebraicToQuasiLocal d (F.algebraicEquiv A) :=
  UniformSpace.Completion.mapStarAlgEquiv_coe _ _ _ A

/-- The inverse completed equivalence agrees with the inverse algebraic-local equivalence on the
dense canonical subalgebra. -/
@[simp]
lemma quasiLocalEquiv_symm_algebraicToQuasiLocal
    (hF : F.ForwardNormPreserving) (A : AlgebraicLocalAlgebra d) :
    (F.quasiLocalEquiv hF).symm (algebraicToQuasiLocal d A) =
      algebraicToQuasiLocal d (F.algebraicEquiv.symm A) := by
  exact UniformSpace.Completion.mapStarAlgEquiv_coe
    F.algebraicEquiv.symm
    (F.algebraicEquiv_symm_isometry hF).continuous
    (F.algebraicEquiv_isometry hF).continuous A

/-- The completed equivalence evaluates on a finite-region observable by the supplied forward
finite-local family. -/
lemma quasiLocalEquiv_quasiLocalObservable
    (hF : F.ForwardNormPreserving) (Λ : Finset ℤ) (A : LocalAlgebra d Λ) :
    F.quasiLocalEquiv hF (quasiLocalObservable d Λ A) =
      algebraicToQuasiLocal d (F.forward Λ A) := by
  rw [quasiLocalObservable, StarAlgHom.comp_apply,
    quasiLocalEquiv_algebraicToQuasiLocal, algebraicEquiv_apply,
    forwardHom_localObservable]

/-- The inverse completed equivalence evaluates on a finite-region observable by the supplied
inverse finite-local family. -/
lemma quasiLocalEquiv_symm_quasiLocalObservable
    (hF : F.ForwardNormPreserving) (Λ : Finset ℤ) (A : LocalAlgebra d Λ) :
    (F.quasiLocalEquiv hF).symm (quasiLocalObservable d Λ A) =
      algebraicToQuasiLocal d (F.inverse Λ A) := by
  rw [quasiLocalObservable, StarAlgHom.comp_apply,
    quasiLocalEquiv_symm_algebraicToQuasiLocal, algebraicEquiv_symm_apply,
    inverseHom_localObservable]

/-- A finite-local support bound for the forward family: an observable initially represented in
`Λ` is sent to one represented in `Λ + 𝓝`. -/
def MapsSupportWithin (𝓝 : Finset ℤ) : Prop :=
  ∀ (Λ : Finset ℤ) (A : LocalAlgebra d Λ),
    SupportedIn (F.forward Λ A) (regionSumset Λ 𝓝)

/-- The forward family commutes with unit translation on every finite-region representative. -/
def CommutesWithUnitTranslation : Prop :=
  ∀ (Λ : Finset ℤ) (A : LocalAlgebra d Λ),
    F.forward (translateRegion 1 Λ) (localTranslation d 1 Λ A) =
      algebraicLocalTranslation d 1 (F.forward Λ A)

/-- A finite-local support bound gives the same propagation neighborhood for the completed
automorphism. -/
theorem propagatesWithin_quasiLocalEquiv
    (hF : F.ForwardNormPreserving) {𝓝 : Finset ℤ} (hsupp : F.MapsSupportWithin 𝓝) :
    PropagatesWithin (F.quasiLocalEquiv hF) 𝓝 := by
  intro Λ x hx
  obtain ⟨A, rfl⟩ := hx
  rw [quasiLocalEquiv_quasiLocalObservable]
  obtain ⟨B, hB⟩ := hsupp Λ A
  exact ⟨B, by rw [quasiLocalObservable, StarAlgHom.comp_apply, hB]⟩

omit [NeZero d] in
/-- The finite-local unit-translation formula implies commutation of the induced algebraic-local
map with unit translation. -/
lemma algebraicEquiv_commutes_unitTranslation (htrans : F.CommutesWithUnitTranslation)
    (A : AlgebraicLocalAlgebra d) :
    F.algebraicEquiv (algebraicLocalTranslation d 1 A) =
      algebraicLocalTranslation d 1 (F.algebraicEquiv A) := by
  induction A using DirectLimit.induction with
  | _ Λ A =>
      change F.algebraicEquiv
          (algebraicLocalTranslation d 1 (localObservable d Λ A)) =
        algebraicLocalTranslation d 1 (F.algebraicEquiv (localObservable d Λ A))
      rw [algebraicLocalTranslation_localObservable, algebraicEquiv_apply,
        forwardHom_localObservable, algebraicEquiv_apply, forwardHom_localObservable,
        htrans]

/-- The finite-local unit-translation formula implies translation covariance of the completed
automorphism. -/
theorem translationCovariant_quasiLocalEquiv
    (hF : F.ForwardNormPreserving) (htrans : F.CommutesWithUnitTranslation) :
    TranslationCovariant (F.quasiLocalEquiv hF) := by
  rw [translationCovariant_iff_commute_one]
  change F.quasiLocalEquiv hF * quasiLocalTranslation d 1 =
    quasiLocalTranslation d 1 * F.quasiLocalEquiv hF
  ext A
  simp only [StarAlgEquiv.mul_apply]
  induction A using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        ((StarAlgEquiv.isometry (F.quasiLocalEquiv hF)).continuous.comp
          (quasiLocalTranslation_isometry d 1).continuous)
        ((quasiLocalTranslation_isometry d 1).continuous.comp
          (StarAlgEquiv.isometry (F.quasiLocalEquiv hF)).continuous)
  | ih A =>
      change F.quasiLocalEquiv hF
          (quasiLocalTranslation d 1 (algebraicToQuasiLocal d A)) =
        quasiLocalTranslation d 1
          (F.quasiLocalEquiv hF (algebraicToQuasiLocal d A))
      simp only [quasiLocalTranslation_algebraicToQuasiLocal,
        quasiLocalEquiv_algebraicToQuasiLocal]
      rw [F.algebraicEquiv_commutes_unitTranslation htrans]

/-- Compatible finite-local actions satisfying local norm, support, and unit-translation formulas
assemble to a QCA of the quasi-local completion. -/
theorem isQCA_quasiLocalEquiv
    (hF : F.ForwardNormPreserving) {𝓝 : Finset ℤ} (hsupp : F.MapsSupportWithin 𝓝)
    (htrans : F.CommutesWithUnitTranslation) :
    IsQCA (F.quasiLocalEquiv hF) :=
  IsQCA.mk (F.translationCovariant_quasiLocalEquiv hF htrans)
    ⟨𝓝, F.propagatesWithin_quasiLocalEquiv hF hsupp⟩

end CompatibleLocalAutomorphism

end SpinChain
