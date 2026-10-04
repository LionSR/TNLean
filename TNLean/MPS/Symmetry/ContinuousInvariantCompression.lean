/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ContinuousProjectionFrame
import TNLean.MPS.Symmetry.VaryingSupportPhaseInvariance

/-!
# Continuous projective compression on invariant projection ranges

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

open scoped Matrix

namespace TNLean.Algebra

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
    (g h : G) : Continuous fun t => (ω t g h : ℂ) := by
  let i : Fin D := ⟨0, hD⟩
  have hformula (t : T) : (ω t g h : ℂ) =
      ((((ρ t).X g : Matrix (Fin D) (Fin D) ℂ) * (ρ t).X h *
        ((ρ t).X (g * h) : Matrix (Fin D) (Fin D) ℂ).adjugate) i i) /
          ((ρ t).X (g * h) : Matrix (Fin D) (Fin D) ℂ).det := by
    rw [(ρ t).map_mul, Matrix.smul_mul, Matrix.mul_adjugate]
    simp [Matrix.smul_apply, ((ρ t).X (g * h)).det_ne_zero]
  have hc := ((((hρ g).matrix_mul (hρ h)).matrix_mul
    (hρ (g * h)).matrix_adjugate).matrix_elem i i).div
      (hρ (g * h)).matrix_det (fun t => ((ρ t).X (g * h)).det_ne_zero)
  exact hc.congr (fun t => (hformula t).symm)

end TNLean.Algebra
