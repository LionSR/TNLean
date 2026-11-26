/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Cohomology.ProjectiveRepresentation
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import Mathlib.LinearAlgebra.UnitaryGroup
import TNLean.MPS.Symmetry.ContinuousFamily.ContinuousProjectionFrame

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

It also contains the following results.

* `ProjectiveRepresentation.exists_local_continuous_unitary_compression`,
  `ProjectiveRepresentation.continuous_factor_family`: continuous projective compression on
  invariant projection ranges.
-/

open scoped Matrix

section VaryingSupportPhaseInvariance

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
        (ω (g, h) : ℂ) • (Jᴴ * (ρ.X (g * h) : Matrix (Fin D) (Fin D) ℂ) * J)
      rw [Matrix.isometry_compression_mul_of_commute J hJ _ _ (hComm g), ρ.map_mul]
      simp only [Matrix.mul_smul, Matrix.smul_mul]
  }
  exact ⟨σ, fun _ => rfl, hW⟩

end VaryingSupportPhaseInvariance

section ContinuousInvariantCompression

/-!
## Continuous projective compression on invariant projection ranges

The local polar frame of a continuous fixed-rank orthogonal projection
compresses a continuous unitary projective action to a continuous unitary
projective action with exactly the same factor system.

This is an auxiliary support-restriction result in the context of
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Appendix C, lines 2653–2717.
The ambient virtual action and projection continuity are explicit hypotheses.
They are not derived here from a physical gap; that canonical-support
construction remains open, as recorded in
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

/-- Continuous local compression to a nonzero invariant projection range
preserves the factor system exactly. Source context: arXiv:1010.3732,
Appendix C, lines 2653–2717. -/
theorem ProjectiveRepresentation.exists_local_continuous_unitary_compression
    {T : Type*} {G : Type} [TopologicalSpace T] [Group G] {D r : ℕ} [NeZero r]
    (ω : T → ScalarCocycle G) (ρ : ∀ t, ProjectiveRepresentation (D := D) (ω t))
    (hρ : ∀ g, Continuous fun t => ((ρ t).X g : Matrix (Fin D) (Fin D) ℂ))
    (hUnitary : ∀ t g, ((ρ t).X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (P : T → Matrix (Fin D) (Fin D) ℂ) (hP : Continuous P)
    (hHerm : ∀ t, (P t).IsHermitian) (hid : ∀ t, P t * P t = P t)
    (hrank : ∀ t, (P t).rank = r)
    (hComm : ∀ t g, Commute ((ρ t).X g : Matrix (Fin D) (Fin D) ℂ) (P t))
    (t₀ : T) (J₀ : Matrix (Fin D) (Fin r) ℂ) (hJ₀ : J₀.IsIsometry)
    (hbase : P t₀ = J₀ * J₀ᴴ) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧
      ∃ σ : ∀ t : S, ProjectiveRepresentation (D := r) (ω t),
        (∀ g, Continuous fun t : S => ((σ t).X g : Matrix (Fin r) (Fin r) ℂ)) ∧
        (∀ t g, ((σ t).X g : Matrix (Fin r) (Fin r) ℂ) ∈ Matrix.unitaryGroup _ ℂ) ∧
        ∀ t g, ((σ t).X g : Matrix (Fin r) (Fin r) ℂ) =
          (Matrix.polarIso (P t * J₀))ᴴ *
            ((ρ t).X g : Matrix (Fin D) (Fin D) ℂ) * Matrix.polarIso (P t * J₀) := by
  classical
  obtain ⟨S, hS, ht₀, hcont, hFrame⟩ :=
    Matrix.exists_local_continuous_projection_frame P hP hHerm hid
      (fun t => by simpa using hrank t) t₀ J₀ hJ₀ hbase
  have hcomp (t : S) : ∃ σ : ProjectiveRepresentation (D := r) (ω t),
      (∀ g, (σ.X g : Matrix (Fin r) (Fin r) ℂ) =
        (Matrix.polarIso (P t * J₀))ᴴ *
          ((ρ t).X g : Matrix (Fin D) (Fin D) ℂ) * Matrix.polarIso (P t * J₀)) ∧
      ∀ g, (σ.X g : Matrix (Fin r) (Fin r) ℂ) ∈ Matrix.unitaryGroup _ ℂ := by
    apply (ρ t).exists_unitary_compression _ (hFrame t t.property).1 (hUnitary t)
    intro g
    rw [(hFrame t t.property).2]
    exact hComm t g
  choose σ hσ hσUnitary using hcomp
  refine ⟨S, hS, ht₀, σ, ?_, hσUnitary, hσ⟩
  intro g
  have hJ : Continuous fun t : S => Matrix.polarIso (P t * J₀) :=
    continuousOn_iff_continuous_domRestrict.mp hcont
  have h := (hJ.matrix_conjTranspose.matrix_mul
    ((hρ g).comp continuous_subtype_val)).matrix_mul hJ
  exact h.congr (fun t => (hσ t g).symm)

/-- A continuous projective matrix family of positive fixed dimension has
continuous factors. Hence the unchanged factors of an invariant local
compression are continuous as well. Source context: arXiv:1010.3732,
Section II.F.2, lines 1000–1029, and Appendix C, lines 2653–2717. -/
theorem ProjectiveRepresentation.continuous_factor_family
    {T : Type*} {G : Type} [TopologicalSpace T] [Group G] {D : ℕ} (hD : 0 < D)
    (ω : T → ScalarCocycle G) (ρ : ∀ t, ProjectiveRepresentation (D := D) (ω t))
    (hρ : ∀ g, Continuous fun t => ((ρ t).X g : Matrix (Fin D) (Fin D) ℂ))
    (g h : G) : Continuous fun t => (ω t (g, h) : ℂ) := by
  let i : Fin D := ⟨0, hD⟩
  have hformula (t : T) : (ω t (g, h) : ℂ) =
      ((((ρ t).X g : Matrix (Fin D) (Fin D) ℂ) * (ρ t).X h *
        ((ρ t).X (g * h) : Matrix (Fin D) (Fin D) ℂ).adjugate) i i) /
          ((ρ t).X (g * h) : Matrix (Fin D) (Fin D) ℂ).det := by
    rw [(ρ t).map_mul, Matrix.smul_mul, Matrix.mul_adjugate]
    simp [Matrix.smul_apply, ((ρ t).X (g * h)).det_ne_zero]
  have hc := ((((hρ g).matrix_mul (hρ h)).matrix_mul
    (hρ (g * h)).matrix_adjugate).matrix_elem i i).div
      (hρ (g * h)).matrix_det (fun t => ((ρ t).X (g * h)).det_ne_zero)
  exact hc.congr (fun t => (hformula t).symm)

end ContinuousInvariantCompression
