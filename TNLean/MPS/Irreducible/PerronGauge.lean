/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.PerronFrobenius.Existence
import QICLean.Kraus.TransferChannel
import TNLean.MPS.Core.TPGauge
import TNLean.MPS.Irreducible.Adjoint
import TNLean.MPS.Irreducible.FormII

/-!
# Perron–Frobenius gauges for irreducible MPS tensors

The Perron–Frobenius eigenvector of the adjoint transfer map of an irreducible
MPS tensor gives the standard trace-preserving and unital gauge normalizations.
The channel-level eigenvector existence lives in
`TNLean.Channel.PerronFrobenius.Existence`; this file states the transfer-map
specializations and combines them with the explicit gauge constructions from
`TNLean.MPS.Core.TPGauge`.

## Main results

* `MPSTensor.exists_posDef_adjoint_eigenvector`:
    PosDef eigenvector for the adjoint transfer map
* `MPSTensor.exists_tp_data_of_irreducible`:
    TP-normalized tensor from an irreducible one
* `MPSTensor.exists_unital_data_of_irreducible`:
    unital PGVWC07-orientation tensor from an irreducible one

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.2
  Theorems 6.3/6.5][Wolf2012QChannels]
* [Cirac et al., arXiv:1606.00608, Appendix A][Cirac2017Annals]
* [Pérez-García et al., quant-ph/0608197, Theorem `Th:TIcanonical`][PerezGarcia2007]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators

variable {d D : ℕ}

namespace MPSTensor

/-- **PosDef eigenvector of the adjoint transfer map**
(combines Wolf Theorem 6.5 for existence with Wolf Theorem 6.3(2) for positive
definiteness).

For an irreducible MPS tensor `A` with `D > 0` and some `A i ≠ 0`, there exist a
positive definite matrix `σ` and a positive real `r` with
`∑ (A i)ᴴ * σ * A i = r • σ` (the adjoint eigenvector equation).

This is the transfer-map form of `Kraus.exists_posDef_adjoint_eigenvector`. -/
theorem exists_posDef_adjoint_eigenvector
    [NeZero D]
    (A : MPSTensor d D)
    (hIrr : Kraus.IsIrreducibleFamily (d := d) (D := D) A)
    (hA : ∃ i, A i ≠ 0) :
    ∃ (σ : Matrix (Fin D) (Fin D) ℂ) (r : ℝ),
      σ.PosDef ∧ 0 < r ∧
      Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) σ = (r : ℂ) • σ := by
  obtain ⟨σ, r, hσ_pd, hr_pos, hσ_eig⟩ :=
    Kraus.exists_posDef_adjoint_eigenvector (K := A)
      (Kraus.isIrreducibleMap_mapLM_of_transferMap _
        (isIrreducibleCP_transferMap_of_isIrreducibleTensor A hIrr)) hA
  refine ⟨σ, r, hσ_pd, hr_pos, ?_⟩
  rwa [Kraus.mapLM_eq_transferMap] at hσ_eig

/-- **TP / left-canonical gauge data for an irreducible MPS tensor.**

For an irreducible MPS tensor `A` with `D > 0` and some `A i ≠ 0`, there exist:
* a positive real `r` (the spectral radius of the adjoint transfer map),
* a positive definite matrix `σ`,
* such that the rescaled-and-gauged tensor `B i = σ^{1/2} ((1/√r) • A i) σ^{-1/2}`
  satisfies the TP / left-canonical condition `∑ (B i)ᴴ * B i = 1`.

The tensor `B` is gauge-equivalent to the rescaled tensor `(1/√r) • A`, hence has
the same MPV as `A` up to a system-size-dependent factor `(1/√r)^N`.

This theorem combines `exists_posDef_adjoint_eigenvector` with the explicit `tpGauge`
construction. -/
theorem exists_tp_data_of_irreducible
    [NeZero D]
    (A : MPSTensor d D)
    (hIrr : Kraus.IsIrreducibleFamily (d := d) (D := D) A)
    (hA : ∃ i, A i ≠ 0) :
    ∃ (B : MPSTensor d D) (r : ℝ) (σ : Matrix (Fin D) (Fin D) ℂ),
      σ.PosDef ∧ 0 < r ∧
      -- B is the tpGauge of the rescaled tensor
      (∀ i : Fin d,
        B i = CFC.sqrt σ *
          ((↑((Real.sqrt r)⁻¹) : ℂ) • A i) * (CFC.sqrt σ)⁻¹) ∧
      -- B is TP
      (∑ i : Fin d, (B i)ᴴ * B i = 1) ∧
      -- B is gauge-equivalent to the rescaled tensor
      GaugeEquiv (d := d) (D := D)
        (fun i => (↑((Real.sqrt r)⁻¹) : ℂ) • A i) B := by
  obtain ⟨σ, r, hσ_pd, hr_pos, hσ_eig⟩ :=
    exists_posDef_adjoint_eigenvector A hIrr hA
  let A' : MPSTensor d D := fun i => (↑((Real.sqrt r)⁻¹) : ℂ) • A i
  let B := tpGauge (d := d) (D := D) A' σ
  refine ⟨B, r, σ, hσ_pd, hr_pos, fun i => rfl, ?_, gaugeEquiv_tpGauge A' σ hσ_pd⟩
  exact tpGauge_isTP_of_transferMap_conjTranspose_eigenvector A σ r hσ_pd hr_pos hσ_eig

/-- **Unital gauge data for an irreducible MPS tensor.**

Pérez-García, Verstraete, Wolf, and Cirac, Theorem `Th:TIcanonical`, proof
lines 765--770.  For an irreducible nonzero tensor, the Perron--Frobenius
eigenvector of the transfer map gives a positive scalar `r` and a positive
definite matrix `ρ`; the spectral gauge
`B i = r^{-1/2} ρ^{-1/2} A i ρ^{1/2}` is unital and gauge-equivalent to the
rescaled tensor `r^{-1/2} A`. -/
theorem exists_unital_data_of_irreducible
    [NeZero D]
    (A : MPSTensor d D)
    (hIrr : Kraus.IsIrreducibleFamily (d := d) (D := D) A)
    (hA : ∃ i, A i ≠ 0) :
    ∃ (B : MPSTensor d D) (r : ℝ) (ρ : Matrix (Fin D) (Fin D) ℂ),
      ρ.PosDef ∧ 0 < r ∧
      (∀ i : Fin d,
        B i =
          (↑((Real.sqrt r)⁻¹) : ℂ) •
            ((CFC.sqrt ρ)⁻¹ * A i * CFC.sqrt ρ)) ∧
      (∑ i : Fin d, B i * (B i)ᴴ = 1) ∧
      GaugeEquiv (d := d) (D := D)
        (fun i => (↑((Real.sqrt r)⁻¹) : ℂ) • A i) B := by
  classical
  let Aadj : MPSTensor d D := fun i => (A i)ᴴ
  have hIrrAdjMap :
      IsIrreducibleMap (Kraus.transferMap (d := d) (D := D) Aadj) := by
    simpa [Aadj] using
      isIrreducibleCP_transferMap_conjTranspose_of_isIrreducibleTensor
        (d := d) (D := D) A hIrr
  have hIrrAdj : Kraus.IsIrreducibleFamily (d := d) (D := D) Aadj :=
    isIrreducibleTensor_of_isIrreducibleMap Aadj hIrrAdjMap
  have hAadj : ∃ i, Aadj i ≠ 0 := by
    rcases hA with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    intro h
    exact hi (Matrix.conjTranspose_eq_zero.mp (by simpa [Aadj] using h))
  obtain ⟨ρ, r, hρ, hr, hρ_eig_adj⟩ :=
    exists_posDef_adjoint_eigenvector (d := d) (D := D) Aadj hIrrAdj hAadj
  have hρ_eig : Kraus.transferMap (d := d) (D := D) A ρ = (r : ℂ) • ρ := by
    simpa [Aadj, Matrix.conjTranspose_conjTranspose] using hρ_eig_adj
  let B : MPSTensor d D := spectralUnitalGauge (d := d) (D := D) A r ρ
  have hB_unital : ∑ i : Fin d, B i * (B i)ᴴ = 1 := by
    simpa [B] using
      spectralUnitalGauge_isUnital_of_transferMap_eigenvector
        (d := d) (D := D) A ρ r hρ hr hρ_eig
  have hGauge : GaugeEquiv (d := d) (D := D)
      (fun i => (↑((Real.sqrt r)⁻¹) : ℂ) • A i) B := by
    convert
      gaugeEquiv_unitalGauge (d := d) (D := D)
        (fun i => (↑((Real.sqrt r)⁻¹) : ℂ) • A i) ρ hρ using 1
    ext i
    simp [B, spectralUnitalGauge, unitalGauge]
  refine ⟨B, r, ρ, hρ, hr, ?_, hB_unital, hGauge⟩
  intro i
  rfl

end MPSTensor
