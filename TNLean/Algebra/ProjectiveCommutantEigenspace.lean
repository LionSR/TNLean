/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import TNLean.Algebra.CocycleCohomology

/-!
# Eigenspaces of an operator commuting with a non-trivial projective representation

A matrix `Λ` that commutes with every matrix `ρ(g)` of a projective representation
leaves each of its eigenspaces invariant under all `ρ(g)`.  A one-dimensional
invariant subspace spanned by `v` gives scalars `c_g` with `ρ(g) v = c_g v`, and the
projective multiplication law then writes the factor system as the coboundary of
`c`.  So if the factor system has a non-trivial class, no eigenspace of `Λ` is
one-dimensional: every eigenvalue of `Λ` is degenerate.

This is the step "projective representations … cannot be reduced to 1-dimensional
representations" of arXiv:2011.12127, §III.A, paragraph "Entanglement spectrum and
edge modes" (`Papers/2011.12127/TN-Review-main.tex` line 1171).

## Main results

* `TNLean.Algebra.ProjectiveRepresentation.finrank_eigenspace_ne_one_of_commute`
-/

open Module

namespace TNLean.Algebra

variable {G : Type} [Group G] {D : ℕ}

/-- **No one-dimensional eigenspace for a commutant of a non-trivial projective
representation.**  Source: arXiv:2011.12127, §III.A
(`Papers/2011.12127/TN-Review-main.tex` line 1171). -/
theorem ProjectiveRepresentation.finrank_eigenspace_ne_one_of_commute
    {ω : ScalarCocycle G} (ρ : ProjectiveRepresentation (D := D) ω)
    (hω : ScalarCocycle.IsNontrivialClass ω) {Λ : Matrix (Fin D) (Fin D) ℂ}
    (hΛ : ∀ g, Commute Λ (ρ.X g : Matrix (Fin D) (Fin D) ℂ)) (μ : ℂ) :
    finrank ℂ (Module.End.eigenspace (Matrix.toLin' Λ) μ) ≠ 1 := by
  intro h1
  set E := Module.End.eigenspace (Matrix.toLin' Λ) μ
  obtain ⟨v, hv0, hspan⟩ := finrank_eq_one_iff'.mp h1
  -- Each `ρ(g)` maps the eigenspace into itself.
  have hmaps : ∀ g, Matrix.toLin' (ρ.X g : Matrix (Fin D) (Fin D) ℂ) (v : Fin D → ℂ) ∈ E := by
    intro g
    have hc : Commute (Matrix.toLin' Λ) (Matrix.toLin' (ρ.X g : Matrix (Fin D) (Fin D) ℂ)) :=
      (hΛ g).map (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin D))
    exact Module.End.mapsTo_genEigenspace_of_comm hc μ 1 v.2
  choose c hc using fun g => hspan ⟨_, hmaps g⟩
  have hv0' : (v : Fin D → ℂ) ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hcv : ∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ).mulVec (v : Fin D → ℂ) =
      c g • (v : Fin D → ℂ) := by
    intro g
    have := congrArg Subtype.val (hc g)
    simpa [Matrix.toLin'_apply] using this.symm
  have hc0 : ∀ g, c g ≠ 0 := by
    intro g hg
    apply hv0'
    have h := congrArg (((ρ.X g)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ).mulVec (hcv g)
    simpa [Matrix.mulVec_mulVec, hg] using h
  apply hω
  refine ⟨fun g => Units.mk0 (c g) (hc0 g), fun g h => ?_⟩
  apply Units.ext
  simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, mul_one]
  have hmul := congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => M.mulVec (v : Fin D → ℂ))
    (ρ.map_mul g h)
  simp only [← Matrix.mulVec_mulVec, hcv, Matrix.mulVec_smul, Matrix.smul_mulVec,
    smul_smul] at hmul
  have hωc : (ω g h : ℂ) * c (g * h) = c h * c g := by
    by_contra hne
    apply hv0'
    have := sub_eq_zero.mpr hmul
    rw [← sub_smul] at this
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hne))
  field_simp [hc0 (g * h)]
  linear_combination hωc

end TNLean.Algebra
