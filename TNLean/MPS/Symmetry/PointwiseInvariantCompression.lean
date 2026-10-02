/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryGeneralLinearInverse
import TNLean.MPS.Symmetry.GlobalVirtualGauge
import TNLean.MPS.Symmetry.VaryingSupportPhaseInvariance

/-!
# Pointwise invariant bond compression

A continuous one-site injective tensor family on a fixed positive bond space
has constant virtual cohomology class. This module applies that result to
pointwise invariant compressions of tensors whose ambient bond dimensions
may vary. The ambient tensors, isometric frames, virtual matrices and factor
systems need no continuity. Only the compressed tensor family is continuous.

These are auxiliary results for Schuch–Pérez-García–Cirac,
arXiv:1010.3732, Appendix C, lines 2712–2717. They do not construct the
continuous compressed family from a gapped physical ground-state path.
That remaining question is recorded in
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix

namespace Matrix

/-- Conjugation descends through an invariant isometric corner without
requiring the tensor letters themselves to preserve that corner.
Source context: arXiv:1010.3732, Appendix C, lines 2712–2717. -/
theorem isometry_compression_conj_of_commute {D r : ℕ}
    (J : Matrix (Fin D) (Fin r) ℂ) (hJ : J.IsIsometry)
    (X M : Matrix (Fin D) (Fin D) ℂ) (hX : Commute X (J * Jᴴ)) :
    Jᴴ * (X * M * Xᴴ) * J =
      (Jᴴ * X * J) * (Jᴴ * M * J) * (Jᴴ * X * J)ᴴ := by
  have hleft := congrArg (fun Y => Jᴴ * Y) hX.eq
  have hL : Jᴴ * X = (Jᴴ * X * J) * Jᴴ := by
    simpa only [← Matrix.mul_assoc, show Jᴴ * J = 1 from hJ, Matrix.one_mul]
      using hleft.symm
  have hR : Xᴴ * J = J * (Jᴴ * X * J)ᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      using congrArg Matrix.conjTranspose hL
  calc
    Jᴴ * (X * M * Xᴴ) * J = (Jᴴ * X) * M * (Xᴴ * J) := by
      simp only [Matrix.mul_assoc]
    _ = (Jᴴ * X * J) * (Jᴴ * M * J) * (Jᴴ * X * J)ᴴ := by
      rw [hL, hR]
      simp only [Matrix.mul_assoc, show Jᴴ * J = 1 from hJ, Matrix.mul_one]

end Matrix

namespace MPSTensor

open TNLean.Algebra

/-- A continuous injective tensor family obtained by pointwise invariant
single-bond compression has constant virtual class. Neither the original
bond dimensions nor their tensors, frames, projective matrices, or factor
systems are assumed continuous. This is an auxiliary restriction theorem
in the context of arXiv:1010.3732, Appendix C, lines 2712–2717; it does not
derive the required compressed family from a physical gap. -/
theorem cohomologousTo_of_continuous_injective_pointwise_compression
    {G : Type} [Group G] {d r : ℕ} (hr : 0 < r)
    (D : unitInterval → ℕ) (ω : unitInterval → ScalarCocycle G)
    (ρ : ∀ t, ProjectiveRepresentation (D := D t) (ω t))
    (A : ∀ t, MPSTensor d (D t))
    (J : ∀ t, Matrix (Fin (D t)) (Fin r) ℂ)
    (hJ : ∀ t, (J t).IsIsometry)
    (hUnitary : ∀ t g, ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (hComm : ∀ t g, Commute ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ)
      (J t * (J t)ᴴ))
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hCov : ∀ t g i, twistedTensor (A t) U g i =
      ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
        ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ)ᴴ)
    (C : unitInterval → MPSTensor d r) (hC : Continuous C)
    (hInj : ∀ t, Kraus.IsInjective (C t))
    (hCompress : ∀ t i, C t i = (J t)ᴴ * A t i * J t) :
    (ω 1).CohomologousTo (ω 0) := by
  let : NeZero r := ⟨Nat.ne_of_gt hr⟩
  choose σ hσ hσUnitary using fun t =>
    (ρ t).exists_unitary_compression (J t) (hJ t) (hUnitary t) (hComm t)
  have hCovC : ∀ t g i, twistedTensor (C t) U g i =
      ((σ t).X (g⁻¹) : Matrix (Fin r) (Fin r) ℂ) * C t i *
        ((((σ t).X (g⁻¹))⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
    intro t g i
    have hrot : twistedTensor (C t) U g i =
        (J t)ᴴ * twistedTensor (A t) U g i * J t := by
      simp only [twistedTensor, hCompress, Matrix.mul_sum, Matrix.sum_mul,
        Matrix.mul_smul, Matrix.smul_mul]
    rw [hrot, hCov,
      Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup _ (hσUnitary t g⁻¹),
      hσ, hCompress]
    exact Matrix.isometry_compression_conj_of_commute
      (J t) (hJ t) ((ρ t).X g⁻¹) (A t i) (hComm t g⁻¹)
  have hSym : ∀ t, IsOnSiteSymmetric (C t) U := fun t g =>
    GaugeEquiv.sameMPV ⟨(σ t).X g⁻¹, hCovC t g⟩
  exact cohomologousTo_of_continuous_isOnSiteSymmetric_tensorPath
    hr C hC hInj U hSym (σ 0) (σ 1) (hCovC 0) (hCovC 1)

end MPSTensor
