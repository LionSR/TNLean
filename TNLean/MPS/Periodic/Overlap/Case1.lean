/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Overlap.SelfOverlap
import TNLean.MPS.Periodic.Overlap.GaugePhase

/-!
# Periodic overlap dichotomy: Case 1

This module contains the different-period case of Appendix A of
arXiv:1708.00029: if two periodic tensors have different periods, then their
overlap tends to $0$.

## Main declarations

* `periodicOverlap_tendsto_zero_of_ne_period`

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Appendix A.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace
open Filter Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ## Case 1: Different periods → orthogonal (Appendix A, first case) -/

/-- The conjugation `Y ↦ X Y Xᴴ` as a linear equivalence on matrices. -/
private noncomputable def glConjEquiv (X : GL (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  (X.mulLeftLinearEquiv ℂ (Matrix (Fin D) (Fin D) ℂ)).trans
    ((star X).mulRightLinearEquiv ℂ)

@[simp] private lemma glConjEquiv_apply (X : GL (Fin D) ℂ)
    (Y : Matrix (Fin D) (Fin D) ℂ) :
    glConjEquiv X Y = X.val * Y * X.valᴴ := rfl

@[simp] private lemma glConjEquiv_symm_apply (X : GL (Fin D) ℂ)
    (Y : Matrix (Fin D) (Fin D) ℂ) :
    (glConjEquiv X).symm Y = X⁻¹.val * Y * X⁻¹.valᴴ := by
  simp only [glConjEquiv]
  rw [LinearEquiv.symm_trans_apply]
  rw [Units.symm_mulRightLinearEquiv_apply, Units.symm_mulLeftLinearEquiv_apply]
  rw [Units.coe_star_inv]
  simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]

/-- **GaugePhaseEquiv preserves periods.**

If two periodic tensors (same bond dimension) are gauge-phase equivalent,
they must have the same period.

arXiv:0909.5347, via eigenvalue uniqueness (Wolf Theorem 6.3). -/
private theorem period_eq_of_gaugePhaseEquiv_of_isPeriodic
    [NeZero D] {A B : MPSTensor d D}
    {m_a m_b : ℕ} (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B)
    (hGPE : GaugePhaseEquiv A B) : m_a = m_b := by
  obtain ⟨X, ζ, hζ_ne, hBi⟩ := hGPE
  -- Transfer map scaling: B = ζ • (X A X⁻¹) implies E_B = |ζ|² E_{XAX⁻¹}
  have hEB_eq : ∀ Y, transferMap (d := d) (D := D) B Y =
      (ζ * starRingEnd ℂ ζ) •
        (X.val * transferMap (d := d) (D := D) A
          (X⁻¹.val * Y * X⁻¹.valᴴ) * X.valᴴ) := by
    intro Y
    simp only [transferMap_apply]
    simp_rw [hBi]
    simp only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm,
      smul_smul, ← Finset.smul_sum, Matrix.conjTranspose_mul,
      Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]
    congr 1; exact mul_comm _ _
  have hζ_norm : ‖ζ‖ = 1 :=
    gaugePhase_scalar_norm_eq_one_of_leftCanonical_irreducible
      hA.leftCanonical hB.leftCanonical hB.irreducible hζ_ne hBi
  have hζζ_real : ζ * starRingEnd ℂ ζ = (↑(‖ζ‖ ^ 2) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h_eig_eq : ‖ζ‖ ^ 2 = 1 := by
    rw [hζ_norm]
    norm_num
  have hRepeated : RepeatedBlocks A B :=
    repeatedBlocks_of_gaugePhaseData_norm_one X hζ_norm hBi
  -- Peripheral eigenvalue equality via conjugation
  have hSpec : peripheralEigenvalues (transferMap (d := d) (D := D) A) =
      peripheralEigenvalues (transferMap (d := d) (D := D) B) := by
    have hEB_is_conj : transferMap (d := d) (D := D) B =
        (glConjEquiv X).conj (transferMap (d := d) (D := D) A) := by
      apply LinearMap.ext; intro Y
      rw [hEB_eq, hζζ_real, show (↑(‖ζ‖ ^ 2) : ℂ) = (1 : ℂ) from by simp [h_eig_eq],
        one_smul]
      simp [LinearEquiv.conj_apply, transferMap_apply, Finset.mul_sum, Finset.sum_mul,
        Matrix.mul_assoc]
    rw [hEB_is_conj]
    exact (peripheralEigenvalues_conj (glConjEquiv X)
      (transferMap (d := d) (D := D) A)).symm
  exact IsPeriodic.period_eq_of_repeatedBlocks hA hB hRepeated hSpec

/-- If two periodic tensors have different periods `m_a ≠ m_b`, their overlap
decays to zero.

Source: arXiv:1708.00029, Appendix A, lines 917--950. There the different-period
decay is obtained by blocking at p = lcm(m_a, m_b) and using that, by
Lemma bdcf, the blocks P_u A^{(p)} and Q_v B^{(p)} are non-repeated normal
tensors, so that applying the one-site translation operator to Q_v B^{(p)}
versus Q_{v+1} B^{(p)} yields a contradiction unless the overlap vanishes.

**Different-period decay via the peripheral spectrum:** the Lean
proof realizes the *same* obstruction through the peripheral-spectrum form rather
than the paper's lcm-blocking + translation argument. If D₁ = D₂ and
B i = ζ X (A i) X⁻¹, then
𝓔_B(Y) = ζ · (conj ζ) · X 𝓔_A(X⁻¹ Y X⁻ᴴ) Xᴴ. Eigenvalue uniqueness for an irreducible CP
map (Wolf, *Quantum Channels & Operations*, Thm 6.3) forces |ζ| = 1, so the
peripheral spectra of 𝓔_A and 𝓔_B agree. An `m`-periodic tensor has peripheral
spectrum {e^{2πi r/m} : 0 ≤ r < m}, so agreement forces m_a = m_b; hence
different periods exclude gauge-phase equivalence, and equal-or-orthogonal (the
irreducible trace-preserving overlap dichotomy) gives the decay. This is a
mathematically equivalent substitute for the paper's step, documented in
docs/paper-gaps/1708_periodic_overlap_route_alignment.tex. -/
theorem periodicOverlap_tendsto_zero_of_ne_period
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    {m_a m_b : ℕ}
    (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B)
    (hne : m_a ≠ m_b) :
    Tendsto (fun N => mpvOverlap A B N) atTop (nhds 0) := by
  by_cases hD : D₁ = D₂
  · subst hD
    exact mpvOverlap_tendsto_zero_of_irreducible_TP A B
      hA.irreducible hB.irreducible hA.leftCanonical hB.leftCanonical
      (fun hGPE => hne (period_eq_of_gaugePhaseEquiv_of_isPeriodic hA hB hGPE))
  · exact mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP A B
      hA.irreducible hB.irreducible hA.leftCanonical hB.leftCanonical hD


end MPSTensor
