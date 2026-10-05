/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Spectral.PhysicalCorrelationJordan
import TNLean.Spectral.PhysicalCorrelationGauge

/-!
# Jordan-aware physical correlation expansion for normal tensors

Normality with leading transfer eigenvalue one supplies subleading eigenvalues
of modulus strictly below one.
The physical correlator is expanded at every separation as polynomial-weighted
nonzero exponentials plus a finite zero-eigenvalue transient. The arbitrary
bond-basis theorem constructs the positive left/right fixed pair and uses the
existing exact gauge invariance of physical insertions.

**Scope restriction (normal tensors):** The source also discusses a unique
algebraically simple dominant eigenvalue with possibly singular fixed
matrices. The physical normalization here uses the normal-tensor Perron gauge;
see `docs/paper-gaps/cpgsv21_correlator_diagonalizable_expansion.tex`.

## References

- arXiv:2011.12127, Section II.B.3, lines 433–441.
-/

open scoped Matrix BigOperators ComplexOrder Polynomial

namespace MPSTensor

private theorem transfer_eigenvalue_of_complement_ne_zero {d D : ℕ}
    (A : MPSTensor d D) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (htr : Matrix.trace ρ ≠ 0)
    {μ : ℂ} (hμ : μ ≠ 0)
    (hEig : Module.End.HasEigenvalue (Kraus.transferMap A - fixedPointProj ρ htr) μ) :
    Module.End.HasEigenvalue (Kraus.transferMap A) μ := by
  obtain ⟨v, hv⟩ := hEig.exists_hasEigenvector
  have hEv := Module.End.mem_eigenspace_iff.mp hv.1
  have hPtr : Matrix.trace (fixedPointProj ρ htr v) = Matrix.trace v := by
    change Matrix.trace ((Matrix.trace v / Matrix.trace ρ) • ρ) = Matrix.trace v
    rw [Matrix.trace_smul, smul_eq_mul, div_mul_cancel₀ _ htr]
  have ht := congrArg Matrix.trace hEv
  rw [LinearMap.sub_apply, Matrix.trace_sub,
    Kraus.isTracePreservingMap_mapLM_of_isTP A hTP v, hPtr, sub_self,
    Matrix.trace_smul, smul_eq_mul] at ht
  have hvtr : Matrix.trace v = 0 := (mul_eq_zero.mp ht.symm).resolve_left hμ
  have hAev : Kraus.transferMap A v = μ • v := by
    change Kraus.transferMap A v - (Matrix.trace v / Matrix.trace ρ) • ρ = μ • v at hEv
    simpa only [hvtr, zero_div, zero_smul, sub_zero] using hEv
  exact hasEigenvalue_of_eigenvector_eq _ μ v hAev hv.2

/-- In trace-preserving gauge, a normal tensor has an all-separation physical
Jordan expansion whose nonzero frequencies are genuine subleading transfer
eigenvalues. The zero-eigenvalue transient vanishes by the squared bond
dimension, and each polynomial has degree below its maximal Jordan-block size.

Source: arXiv:2011.12127, Section II.B.3, source lines 433–441.
The Jordan correction is documented in
`docs/paper-gaps/cpgsv21_correlator_diagonalizable_expansion.tex`. -/
theorem physicalConnectedCorrelator_exists_normal_jordan_expansion {d D : ℕ}
    {A : MPSTensor d D} (hNormal : IsNormalTensor A)
    (hTP : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hTr : Matrix.trace ρ = 1) (hFix : Kraus.transferMap A ρ = ρ)
    (L₁ L₂ : ℕ) (X : Matrix (Cfg d L₁) (Cfg d L₁) ℂ)
    (Y : Matrix (Cfg d L₂) (Cfg d L₂) ℂ) :
    let htr : Matrix.trace ρ ≠ 0 := by simp [hTr]
    let T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) := Kraus.transferMap A - fixedPointProj ρ htr
    ∃ s : Finset ℂ, ∃ p : ℂ → Polynomial ℂ, ∃ t : ℕ → ℂ,
      0 ∉ s ∧ (∀ μ ∈ s, Module.End.HasEigenvalue (Kraus.transferMap A) μ ∧ ‖μ‖ < 1) ∧
      (∀ μ ∈ s, (p μ).degree < (T.maxGenEigenspaceIndex μ : WithBot ℕ)) ∧
      (∀ n, D ^ 2 ≤ n → t n = 0) ∧
      ∀ n, physicalConnectedCorrelator A ρ htr L₁ L₂ X Y n =
        t n + ∑ μ ∈ s, (p μ).eval (n : ℂ) * μ ^ n := by
  classical
  let : NeZero D := ⟨hNormal.bondDim_ne_zero⟩
  dsimp only
  let htr : Matrix.trace ρ ≠ 0 := by simp [hTr]
  let T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) := Kraus.transferMap A - fixedPointProj ρ htr
  obtain ⟨s, p, t, hs0, hs, hp, ht, hsum⟩ :=
    physicalConnectedCorrelator_exists_jordan_expansion A ρ htr L₁ L₂ X Y
  refine ⟨s, p, t, hs0, ?_, hp, ?_, hsum⟩
  · intro μ hμ
    have hμ0 : μ ≠ 0 := fun h => hs0 (h ▸ hμ)
    have hρ0 : ρ ≠ 0 := by intro h; simp [h] at hTr
    exact ⟨transfer_eigenvalue_of_complement_ne_zero A hTP ρ htr hμ0 (hs μ hμ),
      compl_eigenvalue_norm_lt_one_of_primitive_of_irreducible_channel _
        (Kraus.isChannel_mapLM A hTP)
        (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hNormal.no_invariant_proj)
        ρ hFix hρ0 htr hNormal.primitive_transfer μ (hs μ hμ)⟩
  · intro n hn
    apply ht n
    have hk : T.maxGenEigenspaceIndex 0 ≤ D ^ 2 := by
      simpa [Module.finrank_matrix, pow_two] using T.maxUnifEigenspaceIndex_le_finrank 0
    exact hk.trans hn

/-- Every normal tensor with leading transfer eigenvalue one admits positive
normalized left/right fixed matrices
for which every finite-support physical connected correlator has an exact
Jordan expansion, without a trace-preserving hypothesis on the original
representation. A single canonical representative supplies the sharp Jordan
indices for all supports and observables.

Source: arXiv:2011.12127, Section II.B.3, source lines 433–441.
The Jordan correction is documented in
`docs/paper-gaps/cpgsv21_correlator_diagonalizable_expansion.tex`. -/
theorem IsNormalTensor.exists_physicalLeftRightCorrelation_jordan_expansion
    {d D : ℕ} {A : MPSTensor d D} (hNormal : IsNormalTensor A) :
    ∃ ℓ ρ : Matrix (Fin D) (Fin D) ℂ,
      ℓ.PosDef ∧ ρ.PosDef ∧ Kraus.transferMap (fun i => (A i)ᴴ) ℓ = ℓ ∧
      Kraus.transferMap A ρ = ρ ∧ Matrix.trace (ℓ * ρ) = 1 ∧
      ∃ B : MPSTensor d D, ∃ ρB : Matrix (Fin D) (Fin D) ℂ,
        ∃ htrB : Matrix.trace ρB ≠ 0, GaugeEquiv A B ∧ IsNormalTensor B ∧ (∑ i, (B i)ᴴ * B i = 1) ∧
        ρB.PosDef ∧ Kraus.transferMap B ρB = ρB ∧ Matrix.trace ρB = 1 ∧
        ∀ (L₁ L₂ : ℕ) (X : Matrix (Cfg d L₁) (Cfg d L₁) ℂ)
          (Y : Matrix (Cfg d L₂) (Cfg d L₂) ℂ),
          let T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) :=
            Kraus.transferMap B - fixedPointProj ρB htrB
          ∃ s : Finset ℂ, ∃ p : ℂ → Polynomial ℂ, ∃ t : ℕ → ℂ,
            0 ∉ s ∧
            (∀ μ ∈ s, Module.End.HasEigenvalue (Kraus.transferMap A) μ ∧ ‖μ‖ < 1) ∧
            (∀ μ ∈ s, (p μ).degree < (T.maxGenEigenspaceIndex μ : WithBot ℕ)) ∧
            (∀ n, D ^ 2 ≤ n → t n = 0) ∧
            ∀ n, physicalLeftRightConnectedCorrelator A ℓ ρ L₁ L₂ X Y n =
              t n + ∑ μ ∈ s, (p μ).eval (n : ℂ) * μ ^ n := by
  obtain ⟨B, ρB, ℓ, ρ, hG, hNormalB, hTP, hρB, hFix, hTr,
    hℓ, hρ, hLeft, hRight, hPair, hCorr⟩ := hNormal.exists_physicalCorrelation_normalGauge
  refine ⟨ℓ, ρ, hℓ, hρ, hLeft, hRight, hPair,
    B, ρB, (by simp [hTr]), hG, hNormalB, hTP, hρB, hFix, hTr, ?_⟩
  intro L₁ L₂ X Y
  obtain ⟨s, p, t, hs0, hs, hp, ht, hsum⟩ :=
    physicalConnectedCorrelator_exists_normal_jordan_expansion
      hNormalB hTP hTr hFix L₁ L₂ X Y
  refine ⟨s, p, t, hs0, ?_, hp, ht, ?_⟩
  · intro μ hμ
    exact ⟨(hasEigenvalue_transferMap_iff_of_gaugeEquiv hG μ).mpr (hs μ hμ).1,
      (hs μ hμ).2⟩
  · intro n
    rw [hCorr, physicalLeftRightConnectedCorrelator_one B ρB hTr hTP hFix]
    exact hsum n

end MPSTensor
