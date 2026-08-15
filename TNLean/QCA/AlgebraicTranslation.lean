/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.LocalNorm
import TNLean.QCA.Translation

/-!
# Translations of algebraic-local observables

Finite-region translations are compatible with the canonical local inclusions, so they induce an
additive action of the lattice on the algebraic local algebra by star-algebra equivalences. This
action translates finite supports exactly and preserves the operator norm.

This file concerns the algebraic local algebra only. It does not extend translations to the
quasi-local completion or define finite propagation, inverse locality, or quantum cellular
automata.

## Main definitions

* `SpinChain.algebraicLocalTranslationHom` — translation as a star-algebra homomorphism.
* `SpinChain.algebraicLocalTranslation` — translation as a star-algebra equivalence.

## Main results

* `SpinChain.algebraicLocalTranslation_localObservable` — evaluation on a finite-region
  representative.
* `SpinChain.algebraicLocalTranslation_zero` and `SpinChain.algebraicLocalTranslation_add` — the
  additive action laws.
* `SpinChain.algebraicLocalTranslation_supportedIn_iff` — exact transport of finite support.
* `SpinChain.norm_algebraicLocalTranslation` — translation preserves the operator norm.
* `SpinChain.algebraicLocalTranslation_isometry` — translation is an isometry.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2292--2306,
  for the algebraic local algebra, its norm completion, and the translation requirement for QCA.
* Schumacher--Werner, quant-ph/0405174, Definition 1.
-/

open scoped ComplexOrder

namespace SpinChain

attribute [local instance] CStarMatrix.instNorm CStarMatrix.instNormedAddCommGroup
  CStarMatrix.instNormedRing CStarMatrix.instCStarRing

/-- Translation of finite-region representatives induces a star-algebra homomorphism on the
algebraic local algebra.

Context: arXiv:1703.09188, Appendix, lines 2292--2298, which introduce the algebraic local
algebra and use the lattice translation operator. -/
noncomputable def algebraicLocalTranslationHom (d : ℕ) (a : ℤ) :
    AlgebraicLocalAlgebra d →⋆ₐ[ℂ] AlgebraicLocalAlgebra d :=
  algebraicLocalAlgebraLift
    (fun Λ ↦ (localObservable d (translateRegion a Λ)).comp
      (localTranslation d a Λ).toStarAlgHom)
    (by
      intro Λ Γ h A
      change localObservable d (translateRegion a Γ)
          (localTranslation d a Γ (localInclusion h A)) =
        localObservable d (translateRegion a Λ) (localTranslation d a Λ A)
      calc
        _ = localObservable d (translateRegion a Γ)
            (localInclusion (translateRegion_mono a h) (localTranslation d a Λ A)) := by
              rw [localTranslation_localInclusion]
        _ = _ := localObservable_localInclusion d (translateRegion_mono a h) _)

/-- Algebraic-local translation sends a finite-region representative to its translated
representative.

Context: arXiv:1703.09188, Appendix, lines 2292--2298, which introduce the algebraic local
algebra and use the lattice translation operator. -/
@[simp]
lemma algebraicLocalTranslationHom_localObservable (d : ℕ) (a : ℤ)
    (Λ : Finset ℤ) (A : LocalAlgebra d Λ) :
    algebraicLocalTranslationHom d a (localObservable d Λ A) =
      localObservable d (translateRegion a Λ) (localTranslation d a Λ A) :=
  rfl

/-- Translation by zero gives the same element of the algebraic direct limit on every
finite-region representative. -/
private lemma algebraicLocalTranslation_zero_rep (d : ℕ) (Λ : Finset ℤ)
    (A : LocalAlgebra d Λ) :
    localObservable d (translateRegion 0 Λ) (localTranslation d 0 Λ A) =
      localObservable d Λ A := by
  let h : translateRegion 0 Λ ⊆ Λ := by simp
  rw [← localObservable_localInclusion d h]
  congr 1
  ext x y
  rw [localInclusion_apply]
  have hcomp : (Config.splitEquiv h x).2 = (Config.splitEquiv h y).2 := by
    funext i
    exact False.elim ((Finset.mem_sdiff.mp i.2).2 (by simpa using i.2))
  rw [if_pos hcomp, mul_one]
  let x₀ := (Config.translation d 0 Λ).symm (Config.restrict h x)
  let y₀ := (Config.translation d 0 Λ).symm (Config.restrict h y)
  change localTranslation d 0 Λ A (Config.restrict h x) (Config.restrict h y) = A x y
  rw [show Config.restrict h x = Config.translation d 0 Λ x₀ from
    (Equiv.apply_symm_apply _ _).symm]
  rw [show Config.restrict h y = Config.translation d 0 Λ y₀ from
    (Equiv.apply_symm_apply _ _).symm]
  rw [localTranslation_zero]
  congr 2 <;> funext i
  · change x _ = x i
    congr 1
    apply Subtype.ext
    simp
  · change y _ = y i
    congr 1
    apply Subtype.ext
    simp

/-- Successive finite-region translations give the same element of the algebraic direct limit as
translation by the sum. -/
private lemma algebraicLocalTranslation_add_rep (d : ℕ) (a b : ℤ) (Λ : Finset ℤ)
    (A : LocalAlgebra d Λ) :
    localObservable d (translateRegion b (translateRegion a Λ))
        (localTranslation d b (translateRegion a Λ) (localTranslation d a Λ A)) =
      localObservable d (translateRegion (a + b) Λ) (localTranslation d (a + b) Λ A) := by
  let h : translateRegion b (translateRegion a Λ) ⊆ translateRegion (a + b) Λ := by
    intro i hi
    simp only [mem_translateRegion] at hi ⊢
    ring_nf at hi ⊢
    exact hi
  rw [← localObservable_localInclusion d h]
  congr 1
  ext x y
  rw [localInclusion_apply]
  have hcomp : (Config.splitEquiv h x).2 = (Config.splitEquiv h y).2 := by
    funext i
    exact False.elim ((Finset.mem_sdiff.mp i.2).2 (by
      have hi := (Finset.mem_sdiff.mp i.2).1
      simp only [mem_translateRegion] at hi ⊢
      ring_nf at hi ⊢
      exact hi))
  rw [if_pos hcomp, mul_one]
  let x₀ := (Config.translation d (a + b) Λ).symm x
  let y₀ := (Config.translation d (a + b) Λ).symm y
  have hx : Config.restrict h x =
      Config.translation d b (translateRegion a Λ) (Config.translation d a Λ x₀) := by
    funext i
    change x _ = x _
    congr 1
    apply Subtype.ext
    simp only [siteTranslation_apply_val, siteTranslation_symm_apply_val]
    ring
  have hy : Config.restrict h y =
      Config.translation d b (translateRegion a Λ) (Config.translation d a Λ y₀) := by
    funext i
    change y _ = y _
    congr 1
    apply Subtype.ext
    simp only [siteTranslation_apply_val, siteTranslation_symm_apply_val]
    ring
  rw [hx, hy]
  have hx₀ : Config.translation d (a + b) Λ x₀ = x := Equiv.apply_symm_apply _ _
  have hy₀ : Config.translation d (a + b) Λ y₀ = y := Equiv.apply_symm_apply _ _
  simpa only [hx₀, hy₀] using localTranslation_add d a b Λ A x₀ y₀

/-- Translation by zero is the identity star-algebra homomorphism on algebraic-local
observables.

Context: arXiv:1703.09188, Appendix, lines 2292--2298, which introduce the algebraic local
algebra and use the lattice translation operator. -/
@[simp]
lemma algebraicLocalTranslationHom_zero (d : ℕ) :
    algebraicLocalTranslationHom d 0 = StarAlgHom.id ℂ (AlgebraicLocalAlgebra d) := by
  apply algebraicLocalAlgebra_starAlgHom_ext
  intro Λ
  ext A
  exact algebraicLocalTranslation_zero_rep d Λ A

/-- Successive algebraic-local translation homomorphisms compose by adding their displacements.

Context: arXiv:1703.09188, Appendix, lines 2292--2298, which introduce the algebraic local
algebra and use the lattice translation operator. -/
lemma algebraicLocalTranslationHom_add (d : ℕ) (a b : ℤ) :
    (algebraicLocalTranslationHom d b).comp (algebraicLocalTranslationHom d a) =
      algebraicLocalTranslationHom d (a + b) := by
  apply algebraicLocalAlgebra_starAlgHom_ext
  intro Λ
  ext A
  exact algebraicLocalTranslation_add_rep d a b Λ A

/-- Translation by a lattice displacement is a star-algebra equivalence of the algebraic local
algebra, with inverse given by the opposite displacement.

Context: arXiv:1703.09188, Appendix, lines 2292--2298, which introduce the algebraic local
algebra and use the lattice translation operator. -/
noncomputable def algebraicLocalTranslation (d : ℕ) (a : ℤ) :
    AlgebraicLocalAlgebra d ≃⋆ₐ[ℂ] AlgebraicLocalAlgebra d :=
  StarAlgEquiv.ofBijective (algebraicLocalTranslationHom d a) ⟨
    fun A B hAB ↦ by
      have h := congrArg (algebraicLocalTranslationHom d (-a)) hAB
      have hA : algebraicLocalTranslationHom d (-a)
          (algebraicLocalTranslationHom d a A) = A := by
        rw [← StarAlgHom.comp_apply, algebraicLocalTranslationHom_add,
          add_neg_cancel, algebraicLocalTranslationHom_zero]
        rfl
      have hB : algebraicLocalTranslationHom d (-a)
          (algebraicLocalTranslationHom d a B) = B := by
        rw [← StarAlgHom.comp_apply, algebraicLocalTranslationHom_add,
          add_neg_cancel, algebraicLocalTranslationHom_zero]
        rfl
      rwa [hA, hB] at h,
    fun A ↦ ⟨algebraicLocalTranslationHom d (-a) A, by
      rw [← StarAlgHom.comp_apply, algebraicLocalTranslationHom_add,
        neg_add_cancel, algebraicLocalTranslationHom_zero]
      rfl⟩⟩

/-- Algebraic-local translation as an equivalence has the same underlying map as the lifted
translation homomorphism. -/
@[simp]
lemma algebraicLocalTranslation_apply (d : ℕ) (a : ℤ) (A : AlgebraicLocalAlgebra d) :
    algebraicLocalTranslation d a A = algebraicLocalTranslationHom d a A :=
  StarAlgEquiv.ofBijective_apply _ _

/-- Algebraic-local translation sends a finite-region representative to its translated
representative.

Context: arXiv:1703.09188, Appendix, lines 2292--2298, which introduce the algebraic local
algebra and use the lattice translation operator. -/
lemma algebraicLocalTranslation_localObservable (d : ℕ) (a : ℤ)
    (Λ : Finset ℤ) (A : LocalAlgebra d Λ) :
    algebraicLocalTranslation d a (localObservable d Λ A) =
      localObservable d (translateRegion a Λ) (localTranslation d a Λ A) := by
  simpa only [algebraicLocalTranslation_apply] using
    algebraicLocalTranslationHom_localObservable d a Λ A

/-- Translation by zero is the identity star-algebra equivalence.

Context: arXiv:1703.09188, Appendix, lines 2292--2298, which introduce the algebraic local
algebra and use the lattice translation operator. -/
@[simp]
lemma algebraicLocalTranslation_zero (d : ℕ) :
    algebraicLocalTranslation d 0 = StarAlgEquiv.refl ℂ (AlgebraicLocalAlgebra d) := by
  ext A
  simp

/-- Successive algebraic-local translation equivalences compose by adding their displacements.

Context: arXiv:1703.09188, Appendix, lines 2292--2298, which introduce the algebraic local
algebra and use the lattice translation operator. -/
lemma algebraicLocalTranslation_add (d : ℕ) (a b : ℤ) :
    (algebraicLocalTranslation d a).trans (algebraicLocalTranslation d b) =
      algebraicLocalTranslation d (a + b) := by
  ext A
  change algebraicLocalTranslationHom d b (algebraicLocalTranslationHom d a A) =
    algebraicLocalTranslationHom d (a + b) A
  exact DFunLike.congr_fun (algebraicLocalTranslationHom_add d a b) A

/-- The inverse of translation by `a` is translation by `-a`.

Context: arXiv:1703.09188, Appendix, lines 2292--2298, which introduce the algebraic local
algebra and use the lattice translation operator. -/
@[simp]
lemma algebraicLocalTranslation_symm (d : ℕ) (a : ℤ) :
    (algebraicLocalTranslation d a).symm = algebraicLocalTranslation d (-a) := by
  apply StarAlgEquiv.ext
  intro A
  apply (algebraicLocalTranslation d a).symm_apply_eq.mpr
  change A = algebraicLocalTranslationHom d a (algebraicLocalTranslationHom d (-a) A)
  rw [← StarAlgHom.comp_apply, algebraicLocalTranslationHom_add,
    neg_add_cancel, algebraicLocalTranslationHom_zero]
  rfl

/-- Algebraic-local translation carries support in `Λ` to support in `Λ + a`.

Context: arXiv:1703.09188, Appendix, lines 2292--2298, which introduce the algebraic local
algebra and use the lattice translation operator. -/
lemma algebraicLocalTranslation_supportedIn (d : ℕ) (a : ℤ)
    {A : AlgebraicLocalAlgebra d} {Λ : Finset ℤ} (hA : SupportedIn A Λ) :
    SupportedIn (algebraicLocalTranslation d a A) (translateRegion a Λ) := by
  obtain ⟨B, rfl⟩ := hA
  exact ⟨localTranslation d a Λ B,
    (algebraicLocalTranslation_localObservable d a Λ B).symm⟩

/-- Algebraic-local translation carries support in `Λ` exactly to support in `Λ + a`.

Context: arXiv:1703.09188, Appendix, lines 2292--2298, which introduce the algebraic local
algebra and use the lattice translation operator. -/
lemma algebraicLocalTranslation_supportedIn_iff (d : ℕ) (a : ℤ)
    (A : AlgebraicLocalAlgebra d) (Λ : Finset ℤ) :
    SupportedIn A Λ ↔
      SupportedIn (algebraicLocalTranslation d a A) (translateRegion a Λ) := by
  constructor
  · exact algebraicLocalTranslation_supportedIn d a
  · intro hA
    have h := algebraicLocalTranslation_supportedIn d (-a) hA
    change SupportedIn
      (algebraicLocalTranslationHom d (-a) (algebraicLocalTranslationHom d a A))
      (translateRegion (-a) (translateRegion a Λ)) at h
    rw [← StarAlgHom.comp_apply, algebraicLocalTranslationHom_add,
      add_neg_cancel, algebraicLocalTranslationHom_zero] at h
    rw [translateRegion_add a (-a), add_neg_cancel, translateRegion_zero] at h
    exact h

/-- Algebraic-local translation preserves the operator norm.

Context: arXiv:1703.09188, Appendix, lines 2292--2306, which use the norm topology and lattice
translations in the definition and construction of one-dimensional QCA. -/
lemma norm_algebraicLocalTranslation (d : ℕ) [NeZero d] (a : ℤ)
    (A : AlgebraicLocalAlgebra d) :
    ‖algebraicLocalTranslation d a A‖ = ‖A‖ := by
  induction A using DirectLimit.induction with
  | _ Λ A =>
      exact localTranslation_norm d a Λ A

/-- Algebraic-local translation is an operator-norm isometry.

Context: arXiv:1703.09188, Appendix, lines 2292--2306, which use the norm topology and lattice
translations in the definition and construction of one-dimensional QCA. -/
lemma algebraicLocalTranslation_isometry (d : ℕ) [NeZero d] (a : ℤ) :
    Isometry (algebraicLocalTranslation d a) := by
  rw [isometry_iff_dist_eq]
  intro A B
  rw [dist_eq_norm, dist_eq_norm]
  rw [← map_sub]
  exact norm_algebraicLocalTranslation d a (A - B)

end SpinChain
