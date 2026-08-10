/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.LocalAlgebra
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# The algebraic local algebra of a one-dimensional spin chain

The finite-region local observable algebras form a directed system under the canonical
identity-tensor inclusions.  This file defines their concrete algebraic direct limit and the
finite-support API for local observables.  It does not take the norm completion, so the
quasi-local C⋆-algebra is not defined here.

## Main definitions

* `SpinChain.AlgebraicLocalAlgebra` — the algebraic local algebra.
* `SpinChain.localObservable` — the canonical inclusion of a finite-region local algebra.
* `SpinChain.SupportedIn` — a local observable represented on a specified finite region.
* `SpinChain.algebraicLocalAlgebraLift` — the star-preserving universal map from the limit.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2285--2300.
* Schumacher--Werner, quant-ph/0405174, Definition 1.
-/

namespace SpinChain

/-- The transition map in the directed system of finite-region local algebras. -/
noncomputable abbrev localAlgebraMap (d : ℕ) (Λ Γ : Finset ℤ) (h : Λ ⊆ Γ) :
    LocalAlgebra d Λ →⋆ₐ[ℂ] LocalAlgebra d Γ :=
  localInclusion h

/-- The finite-region local algebras and their canonical inclusions form a directed system.

Source: arXiv:1703.09188, Appendix, lines 2292--2295. -/
instance instDirectedSystemLocalAlgebra (d : ℕ) :
    DirectedSystem (LocalAlgebra d) (localAlgebraMap d · · ·) where
  map_self {Λ} A := by
    change localInclusion (show Λ ⊆ Λ from le_rfl) A = A
    rw [localInclusion_refl]
    rfl
  map_map {k} {j} {i} hΛΓ hΓΔ A := by
    change localInclusion hΓΔ (localInclusion hΛΓ A) =
      localInclusion (hΛΓ.trans hΓΔ) A
    exact DFunLike.congr_fun (localInclusion_trans hΛΓ hΓΔ) A

/-- The algebraic local algebra of a spin chain is the direct limit of the local observable
algebras over finite regions.

This is \(\mathcal A_{\mathrm{loc}}=\bigcup_\Lambda^\infty \mathcal A_\Lambda\) in the
paper.  No norm completion is taken.
Source: arXiv:1703.09188, Appendix, lines 2292--2296. -/
abbrev AlgebraicLocalAlgebra (d : ℕ) :=
  DirectLimit (LocalAlgebra d) (localAlgebraMap d)

/-- The canonical inclusion of the local algebra on the finite region \(\Lambda\) into the
algebraic local algebra.

Source: arXiv:1703.09188, Appendix, lines 2292--2295. -/
noncomputable def localObservable (d : ℕ) (Λ : Finset ℤ) :
    LocalAlgebra d Λ →⋆ₐ[ℂ] AlgebraicLocalAlgebra d where
  __ := DirectLimit.Algebra.of (LocalAlgebra d) (localAlgebraMap d) Λ
  map_star' A := (DirectLimit.star_def Λ A).symm

/-- Canonical inclusions agree after enlarging the finite region. -/
@[simp]
lemma localObservable_localInclusion (d : ℕ) {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ)
    (A : LocalAlgebra d Λ) :
    localObservable d Γ (localInclusion h A) = localObservable d Λ A :=
  DirectLimit.Algebra.of_f h A

/-- For positive on-site dimension, every canonical finite-region inclusion into the
algebraic local algebra is injective. -/
lemma localObservable_injective (d : ℕ) [NeZero d] (Λ : Finset ℤ) :
    Function.Injective (localObservable d Λ) := by
  apply DirectLimit.mk_injective (f := localAlgebraMap d)
  intro i j h
  exact localInclusion_injective (d := d) h

section UniversalProperty

variable {d : ℕ} {B : Type*} [Semiring B] [Star B] [Algebra ℂ B]

/-- A compatible family of star-algebra homomorphisms from all finite-region local algebras
induces a star-algebra homomorphism from the algebraic local algebra. -/
noncomputable def algebraicLocalAlgebraLift
    (g : (Λ : Finset ℤ) → LocalAlgebra d Λ →⋆ₐ[ℂ] B)
    (hg : ∀ (Λ Γ : Finset ℤ) (h : Λ ⊆ Γ) (A : LocalAlgebra d Λ),
      g Γ (localInclusion h A) = g Λ A) :
    AlgebraicLocalAlgebra d →⋆ₐ[ℂ] B where
  __ := DirectLimit.Algebra.lift (LocalAlgebra d) (localAlgebraMap d) B
    (fun Λ ↦ (g Λ).toAlgHom) hg
  map_star' x := by
    induction x using DirectLimit.induction with
    | _ Λ A => exact map_star (g Λ) A

/-- The universal map agrees with the supplied map on every finite-region local algebra. -/
@[simp]
lemma algebraicLocalAlgebraLift_localObservable
    (g : (Λ : Finset ℤ) → LocalAlgebra d Λ →⋆ₐ[ℂ] B)
    (hg : ∀ (Λ Γ : Finset ℤ) (h : Λ ⊆ Γ) (A : LocalAlgebra d Λ),
      g Γ (localInclusion h A) = g Λ A)
    (Λ : Finset ℤ) (A : LocalAlgebra d Λ) :
    algebraicLocalAlgebraLift g hg (localObservable d Λ A) = g Λ A :=
  rfl

/-- Star-algebra homomorphisms from the algebraic local algebra are equal when they agree on
all finite-region local observables. -/
@[ext]
lemma algebraicLocalAlgebra_starAlgHom_ext {f g : AlgebraicLocalAlgebra d →⋆ₐ[ℂ] B}
    (h : ∀ Λ, f.comp (localObservable d Λ) = g.comp (localObservable d Λ)) : f = g := by
  ext x
  induction x using DirectLimit.induction with
  | _ Λ A => exact DFunLike.congr_fun (h Λ) A

/-- The star-preserving lift is the unique homomorphism extending a compatible family of
finite-region maps. -/
lemma algebraicLocalAlgebraLift_unique
    (g : (Λ : Finset ℤ) → LocalAlgebra d Λ →⋆ₐ[ℂ] B)
    (hg : ∀ (Λ Γ : Finset ℤ) (h : Λ ⊆ Γ) (A : LocalAlgebra d Λ),
      g Γ (localInclusion h A) = g Λ A)
    (f : AlgebraicLocalAlgebra d →⋆ₐ[ℂ] B)
    (hf : ∀ Λ, f.comp (localObservable d Λ) = g Λ) :
    f = algebraicLocalAlgebraLift g hg := by
  apply algebraicLocalAlgebra_starAlgHom_ext
  intro Λ
  rw [hf]
  ext A
  exact (algebraicLocalAlgebraLift_localObservable g hg Λ A).symm

end UniversalProperty

/-- A local observable is supported in the finite region \(\Lambda\) when it has a
representative in \(\mathcal A_\Lambda\).

Source: arXiv:1703.09188, Appendix, lines 2292--2296. -/
def SupportedIn {d : ℕ} (A : AlgebraicLocalAlgebra d) (Λ : Finset ℤ) : Prop :=
  ∃ a : LocalAlgebra d Λ, localObservable d Λ a = A

namespace SupportedIn

variable {d : ℕ} {A B : AlgebraicLocalAlgebra d} {Λ Γ : Finset ℤ}

/-- Support is monotone under enlargement of the finite region. -/
lemma mono (hA : SupportedIn A Λ) (hΛΓ : Λ ⊆ Γ) : SupportedIn A Γ := by
  obtain ⟨a, rfl⟩ := hA
  exact ⟨localInclusion hΛΓ a, localObservable_localInclusion d hΛΓ a⟩

/-- A support remains a support after adjoining another finite region. -/
lemma union_left (hA : SupportedIn A Λ) : SupportedIn A (Λ ∪ Γ) :=
  hA.mono Finset.subset_union_left

/-- A support remains a support when it is the right member of a finite union. -/
lemma union_right (hA : SupportedIn A Γ) : SupportedIn A (Λ ∪ Γ) :=
  hA.mono Finset.subset_union_right

/-- The sum of local observables is supported in the union of their finite regions. -/
lemma add (hA : SupportedIn A Λ) (hB : SupportedIn B Γ) :
    SupportedIn (A + B) (Λ ∪ Γ) := by
  obtain ⟨a, ha⟩ := hA.union_left (Γ := Γ)
  obtain ⟨b, hb⟩ := hB.union_right (Λ := Λ)
  exact ⟨a + b, by rw [map_add, ha, hb]⟩

/-- The product of local observables is supported in the union of their finite regions. -/
lemma mul (hA : SupportedIn A Λ) (hB : SupportedIn B Γ) :
    SupportedIn (A * B) (Λ ∪ Γ) := by
  obtain ⟨a, ha⟩ := hA.union_left (Γ := Γ)
  obtain ⟨b, hb⟩ := hB.union_right (Λ := Λ)
  exact ⟨a * b, by rw [map_mul, ha, hb]⟩

/-- Taking the adjoint does not enlarge the support of a local observable. -/
lemma star (hA : SupportedIn A Λ) : SupportedIn (star A) Λ := by
  obtain ⟨a, rfl⟩ := hA
  exact ⟨star a, map_star (localObservable d Λ) a⟩

/-- The zero local observable is supported in every finite region. -/
lemma zero (d : ℕ) (Λ : Finset ℤ) : SupportedIn (0 : AlgebraicLocalAlgebra d) Λ :=
  ⟨0, map_zero (localObservable d Λ)⟩

/-- The unit local observable is supported in every finite region. -/
lemma one (d : ℕ) (Λ : Finset ℤ) : SupportedIn (1 : AlgebraicLocalAlgebra d) Λ :=
  ⟨1, map_one (localObservable d Λ)⟩

end SupportedIn

/-- Every element of the algebraic local algebra is a local observable with some finite
support. -/
lemma exists_supportedIn (A : AlgebraicLocalAlgebra d) :
    ∃ Λ : Finset ℤ, SupportedIn A Λ := by
  obtain ⟨Λ, a, rfl⟩ := DirectLimit.exists_eq_mk (localAlgebraMap d) A
  exact ⟨Λ, a, rfl⟩

end SpinChain
