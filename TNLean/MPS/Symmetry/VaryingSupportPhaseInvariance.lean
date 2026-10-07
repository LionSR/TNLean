/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ProjectiveRepresentation
import QICLean.Algebra.MatrixUnitaryBetween
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Projective symmetry on an invariant bond subspace

Compressing a unitary projective action to an invariant single-bond
subspace preserves its factor system. This is the algebraic restriction
used at the end of Schuch–Pérez-García–Cirac, arXiv:1010.3732,
Appendix C, lines 2712–2717.

The results are auxiliary: the isometric inclusion and invariance of its
range are explicit hypotheses. They do not construct a continuous canonical
support from an exact MPS ground-state path. That analytic step, including
changes of the minimal bond dimension, remains open and is recorded in
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

open scoped Matrix

namespace Matrix

/-- Isometric compression is multiplicative when the first matrix
preserves the compressed subspace. Source context: arXiv:1010.3732,
Appendix C, lines 2712–2717. -/
theorem isometry_compression_mul_of_commute {D r : ℕ}
    (J : Matrix (Fin D) (Fin r) ℂ) (hJ : J.IsIsometry)
    (X Y : Matrix (Fin D) (Fin D) ℂ) (hX : Commute X (J * Jᴴ)) :
    (Jᴴ * X * J) * (Jᴴ * Y * J) = Jᴴ * (X * Y) * J := by
  calc
    (Jᴴ * X * J) * (Jᴴ * Y * J) = Jᴴ * (X * (J * Jᴴ)) * Y * J := by
      simp only [Matrix.mul_assoc]
    _ = Jᴴ * ((J * Jᴴ) * X) * Y * J := by rw [hX.eq]
    _ = (Jᴴ * J) * Jᴴ * (X * Y) * J := by simp only [Matrix.mul_assoc]
    _ = Jᴴ * (X * Y) * J := by rw [show Jᴴ * J = 1 from hJ, Matrix.one_mul]

/-- A unitary matrix remains unitary on an invariant isometrically
included subspace. Source context: arXiv:1010.3732, Appendix C,
lines 2712–2717. -/
theorem isometry_compression_mem_unitaryGroup {D r : ℕ}
    (J : Matrix (Fin D) (Fin r) ℂ) (hJ : J.IsIsometry)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X ∈ Matrix.unitaryGroup _ ℂ)
    (hComm : Commute X (J * Jᴴ)) :
    Jᴴ * X * J ∈ Matrix.unitaryGroup _ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  have hXX : X * Xᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hX
  have heq : Jᴴ * (X * Xᴴ) * J = 1 := by
    simpa only [hXX, Matrix.mul_one] using (show Jᴴ * J = 1 from hJ)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc] using (isometry_compression_mul_of_commute J hJ X Xᴴ hComm).trans heq

end Matrix

namespace TNLean.Algebra

/-- Restriction of a unitary projective representation to a nonzero
invariant single-bond subspace retains its factor system and unitarity.
The isometric inclusion is supplied here, not derived from a physical
path. Source: arXiv:1010.3732, Appendix C, lines 2712–2717. -/
theorem ProjectiveRepresentation.exists_unitary_compression
    {G : Type} [Group G] {D r : ℕ} [NeZero r] {ω : ScalarCocycle G}
    (ρ : ProjectiveRepresentation (D := D) ω)
    (J : Matrix (Fin D) (Fin r) ℂ) (hJ : J.IsIsometry)
    (hUnitary : ∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (hComm : ∀ g, Commute (ρ.X g : Matrix (Fin D) (Fin D) ℂ) (J * Jᴴ)) :
    ∃ σ : ProjectiveRepresentation (D := r) ω,
      (∀ g, (σ.X g : Matrix (Fin r) (Fin r) ℂ) =
        Jᴴ * (ρ.X g : Matrix (Fin D) (Fin D) ℂ) * J) ∧
      ∀ g, (σ.X g : Matrix (Fin r) (Fin r) ℂ) ∈ Matrix.unitaryGroup _ ℂ := by
  have hW (g : G) : Jᴴ * (ρ.X g : Matrix (Fin D) (Fin D) ℂ) * J ∈
      Matrix.unitaryGroup _ ℂ :=
    Matrix.isometry_compression_mem_unitaryGroup J hJ _ (hUnitary g) (hComm g)
  let X (g : G) : GL (Fin r) ℂ := {
    val := Jᴴ * (ρ.X g : Matrix (Fin D) (Fin D) ℂ) * J
    inv := star (Jᴴ * (ρ.X g : Matrix (Fin D) (Fin D) ℂ) * J)
    val_inv := (hW g).2
    inv_val := (hW g).1
  }
  let σ : ProjectiveRepresentation (D := r) ω := {
    X := X
    map_mul' := by
      intro g h
      change (Jᴴ * (ρ.X g : Matrix (Fin D) (Fin D) ℂ) * J) *
        (Jᴴ * (ρ.X h : Matrix (Fin D) (Fin D) ℂ) * J) =
        (ω g h : ℂ) • (Jᴴ * (ρ.X (g * h) : Matrix (Fin D) (Fin D) ℂ) * J)
      rw [Matrix.isometry_compression_mul_of_commute J hJ _ _ (hComm g), ρ.map_mul]
      simp only [Matrix.mul_smul, Matrix.smul_mul]
  }
  exact ⟨σ, fun _ => rfl, hW⟩

end TNLean.Algebra
