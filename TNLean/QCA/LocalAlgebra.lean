/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.CStarMatrixKronecker
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Finite-region observable algebras for one-dimensional spin chains

For a finite region \(\Lambda \subset \mathbb Z\) and on-site dimension \(d\), this file
defines the local observable C⋆-algebra on \(\Lambda\) and its canonical inclusion into the
algebra on a larger finite region.  The inclusion tensors an observable with the identity on
complementary sites and then reindexes product configurations as configurations on the larger
region.

This is only the finite directed system.  No quasi-local completion or quantum cellular
automaton is defined here.

## Main definitions

* `SpinChain.Config` — spin configurations on a finite region.
* `SpinChain.LocalAlgebra` — the operator-norm C⋆-matrix algebra of local observables.
* `SpinChain.localInclusion` — the identity-tensor inclusion for nested finite regions.

## Main results

* `SpinChain.localInclusion_injective` — faithfulness of the inclusion.
* `SpinChain.localInclusion_norm` — preservation of the operator norm.
* `SpinChain.localInclusion_isometry` — operator-norm isometry.
* `SpinChain.localInclusion_refl` — the identity inclusion.
* `SpinChain.localInclusion_trans` — composition of inclusions.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2285--2300.
* Schumacher--Werner, quant-ph/0405174, Definition 1.
-/

open scoped ComplexOrder

namespace SpinChain

/-- Configurations of \(d\)-level spins on the finite region \(\Lambda\).

Source: arXiv:1703.09188, Appendix, lines 2285--2292. -/
def Config (d : ℕ) (Λ : Finset ℤ) := Λ → Fin d

/-- The local observable C⋆-algebra on a finite region \(\Lambda\).

Its norm is the `CStarMatrix` operator norm, rather than a norm inherited from plain matrices.
Source: arXiv:1703.09188, Appendix, lines 2285--2292. -/
abbrev LocalAlgebra (d : ℕ) (Λ : Finset ℤ) :=
  CStarMatrix (Config d Λ) (Config d Λ) ℂ

/-- Configurations on a finite region form a finite type. -/
instance instFintypeConfig (d : ℕ) (Λ : Finset ℤ) : Fintype (Config d Λ) := by
  change Fintype (Λ → Fin d)
  infer_instance

/-- Equality of finite-region configurations is decidable. -/
instance instDecidableEqConfig (d : ℕ) (Λ : Finset ℤ) :
    DecidableEq (Config d Λ) := by
  change DecidableEq (Λ → Fin d)
  infer_instance

/-- A positive on-site dimension supplies configurations on every finite region. -/
instance instNonemptyConfig (d : ℕ) [NeZero d] (Λ : Finset ℤ) : Nonempty (Config d Λ) := by
  change Nonempty (Λ → Fin d)
  exact ⟨fun _ ↦ ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩

namespace Config

/-- Restrict a configuration to a smaller region. -/
def restrict {d : ℕ} {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ) (x : Config d Γ) : Config d Λ :=
  fun i ↦ x ⟨i, h i.2⟩

@[simp]
lemma restrict_apply {d : ℕ} {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ) (x : Config d Γ) (i : Λ) :
    restrict h x i = x ⟨i, h i.2⟩ := rfl

@[simp]
lemma restrict_refl {d : ℕ} {Λ : Finset ℤ} (x : Config d Λ) : restrict (by rfl) x = x := by
  rfl

lemma restrict_trans {d : ℕ} {Λ Γ Δ : Finset ℤ} (hΛΓ : Λ ⊆ Γ) (hΓΔ : Γ ⊆ Δ)
    (x : Config d Δ) : restrict hΛΓ (restrict hΓΔ x) = restrict (hΛΓ.trans hΓΔ) x := by
  rfl

/-- Split a configuration on \(\Gamma\) into its restrictions to \(\Lambda\) and
\(\Gamma \setminus \Lambda\).

This is the canonical reindexing used after tensoring with the identity on the complement.
Source: arXiv:1703.09188, Appendix, lines 2285--2292. -/
def splitEquiv {d : ℕ} {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ) :
    Config d Γ ≃ Config d Λ × Config d (Γ \ Λ) where
  toFun x :=
    (restrict h x, fun i ↦ x ⟨i, (Finset.mem_sdiff.mp i.2).1⟩)
  invFun x i :=
    if hi : (i : ℤ) ∈ Λ then x.1 ⟨i, hi⟩
    else x.2 ⟨i, Finset.mem_sdiff.mpr ⟨i.2, hi⟩⟩
  left_inv x := by
    funext i
    simp only [restrict]
    split <;> rfl
  right_inv x := by
    apply Prod.ext
    · funext i
      simp [restrict]
    · funext i
      simp [Finset.mem_sdiff.mp i.2]

@[simp]
lemma splitEquiv_apply_fst {d : ℕ} {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ) (x : Config d Γ) :
    (splitEquiv h x).1 = restrict h x := rfl

end Config

section Inclusion

variable {d : ℕ}

/-- The canonical inclusion of local observables for \(\Lambda \subseteq \Gamma\).

It sends \(A\) to \(A \otimes 1\) on configurations of
\(\Lambda \times (\Gamma \setminus \Lambda)\), then reindexes those configurations as
configurations of \(\Gamma\).  Thus it is a unital star-algebra homomorphism by
construction.

Source: arXiv:1703.09188, Appendix, lines 2285--2292. -/
noncomputable def localInclusion {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ) :
    LocalAlgebra d Λ →⋆ₐ[ℂ] LocalAlgebra d Γ :=
  (CStarMatrix.reindexₐ ℂ ℂ (Config.splitEquiv h).symm).toStarAlgHom.comp
    (CStarMatrix.leftKroneckerEmbed (n := Config d (Γ \ Λ)))

@[simp]
lemma localInclusion_apply {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ) (A : LocalAlgebra d Λ)
    (x y : Config d Γ) :
    localInclusion h A x y =
      A (Config.restrict h x) (Config.restrict h y) *
        if (Config.splitEquiv h x).2 = (Config.splitEquiv h y).2 then 1 else 0 := by
  change CStarMatrix.leftKroneckerEmbed A
    (Config.splitEquiv h x) (Config.splitEquiv h y) = _
  rw [CStarMatrix.leftKroneckerEmbed_apply_apply]
  rfl

/-- The local identity-tensor inclusion is injective.

Source: arXiv:1703.09188, Appendix, lines 2285--2292. -/
lemma localInclusion_injective [NeZero d] {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ) :
    Function.Injective (localInclusion (d := d) h) := by
  apply Function.Injective.comp
    (CStarMatrix.reindexₐ ℂ ℂ (Config.splitEquiv h).symm).injective
  exact CStarMatrix.leftKroneckerEmbed_injective

/-- The local identity-tensor inclusion preserves the C⋆ operator norm.

Source: arXiv:1703.09188, Appendix, lines 2285--2300. -/
lemma localInclusion_norm [NeZero d] {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ)
    (A : LocalAlgebra d Λ) :
    ‖localInclusion h A‖ = ‖A‖ := by
  exact NonUnitalStarAlgHom.norm_map (localInclusion h) (localInclusion_injective h) A

/-- The local identity-tensor inclusion is an operator-norm isometry.

Source: arXiv:1703.09188, Appendix, lines 2285--2300. -/
lemma localInclusion_isometry [NeZero d] {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ) :
    Isometry (localInclusion (d := d) h) := by
  exact NonUnitalStarAlgHom.isometry (localInclusion h) (localInclusion_injective h)

/-- Inclusion of a finite region into itself is the identity map.

Source: arXiv:1703.09188, Appendix, lines 2285--2292. -/
@[simp]
lemma localInclusion_refl (Λ : Finset ℤ) :
    localInclusion (d := d) (show Λ ⊆ Λ from by rfl) =
      StarAlgHom.id ℂ (LocalAlgebra d Λ) := by
  ext A x y
  change localInclusion _ A x y = A x y
  rw [localInclusion_apply]
  have hcomp : (Config.splitEquiv (show Λ ⊆ Λ from by rfl) x).2 =
      (Config.splitEquiv (show Λ ⊆ Λ from by rfl) y).2 := by
    funext i
    exact False.elim ((Finset.mem_sdiff.mp i.2).2 (Finset.mem_sdiff.mp i.2).1)
  simp [hcomp]

/-- Canonical local inclusions compose for nested finite regions.

Source: arXiv:1703.09188, Appendix, lines 2285--2292. -/
lemma localInclusion_trans {Λ Γ Δ : Finset ℤ} (hΛΓ : Λ ⊆ Γ) (hΓΔ : Γ ⊆ Δ) :
    (localInclusion (d := d) hΓΔ).comp (localInclusion hΛΓ) =
      localInclusion (hΛΓ.trans hΓΔ) := by
  ext A x y
  simp only [StarAlgHom.comp_apply, localInclusion_apply]
  rw [Config.restrict_trans, Config.restrict_trans]
  by_cases hxy : (Config.splitEquiv (hΛΓ.trans hΓΔ) x).2 =
      (Config.splitEquiv (hΛΓ.trans hΓΔ) y).2
  · have hxyΓ : (Config.splitEquiv hΓΔ x).2 = (Config.splitEquiv hΓΔ y).2 := by
      funext i
      exact congrFun hxy ⟨i, Finset.mem_sdiff.mpr
        ⟨(Finset.mem_sdiff.mp i.2).1,
          fun hiΛ ↦ (Finset.mem_sdiff.mp i.2).2 (hΛΓ hiΛ)⟩⟩
    have hxyΛ :
        (Config.splitEquiv hΛΓ (Config.restrict hΓΔ x)).2 =
          (Config.splitEquiv hΛΓ (Config.restrict hΓΔ y)).2 := by
      funext i
      exact congrFun hxy ⟨i, Finset.mem_sdiff.mpr
        ⟨hΓΔ (Finset.mem_sdiff.mp i.2).1,
          (Finset.mem_sdiff.mp i.2).2⟩⟩
    simp [hxy, hxyΓ, hxyΛ]
  · have hor :
        (Config.splitEquiv hΓΔ x).2 ≠ (Config.splitEquiv hΓΔ y).2 ∨
          (Config.splitEquiv hΛΓ (Config.restrict hΓΔ x)).2 ≠
            (Config.splitEquiv hΛΓ (Config.restrict hΓΔ y)).2 := by
      by_contra hn
      push Not at hn
      apply hxy
      funext i
      by_cases hiΓ : (i : ℤ) ∈ Γ
      · exact congrFun hn.2 ⟨i, Finset.mem_sdiff.mpr
        ⟨hiΓ, (Finset.mem_sdiff.mp i.2).2⟩⟩
      · exact congrFun hn.1 ⟨i, Finset.mem_sdiff.mpr
        ⟨(Finset.mem_sdiff.mp i.2).1, hiΓ⟩⟩
    rcases hor with hne | hne <;> simp [hxy, hne]

end Inclusion

end SpinChain
