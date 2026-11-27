/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausMap.KrausGauge
import QICLean.Channel.Irreducible.KrausSetup
import QICLean.Channel.Irreducible.InvariantProjection
import QICLean.Kraus.Transfer
import TNLean.MPS.Tensor.Gauge.TPGauge
import TNLean.MPS.Transfer.Irreducible.DiagonalFixedPoint
import QICLean.Channel.Peripheral.Irreducible.PeripheralUnitary

/-!
# Perron–Frobenius gauges for irreducible MPS tensors

The Perron–Frobenius eigenvector of the adjoint transfer map of an irreducible
MPS tensor gives the standard trace-preserving and unital gauge normalizations.
The channel-level eigenvector existence and generic gauge constructions live in
QICLean. This file states their transfer-map specializations and combines them
with the MPS gauge-equivalence bridges from `TNLean.MPS.Core.TPGauge`.

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

## Scalar fixed points for irreducible unital MPS transfer maps

This file records the MPS formulation of the fixed-point endpoint used in the
translation-invariant canonical-form proof.

### Main result

* `MPSTensor.fixed_eq_scalar_of_isIrreducibleFamily_unital`: if an MPS tensor is
  irreducible and its transfer map is unital, then every fixed point of the
  transfer map is a scalar multiple of the identity.

### References

* Pérez-García, Verstraete, Wolf, and Cirac, Theorem `Th:TIcanonical`,
  proof lines 816--826.
* Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.6.
-/

open MPTensor

section

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
    (hIrr : Kraus.IsIrreducibleFamily (ι := Fin d) (n := Fin D) A)
    (hA : ∃ i, A i ≠ 0) :
    ∃ (σ : Matrix (Fin D) (Fin D) ℂ) (r : ℝ),
      σ.PosDef ∧ 0 < r ∧
      Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ) σ = (r : ℂ) • σ := by
  obtain ⟨σ, r, hσ_pd, hr_pos, hσ_eig⟩ :=
    Kraus.exists_posDef_adjoint_eigenvector (K := A)
      (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hIrr) hA
  refine ⟨σ, r, hσ_pd, hr_pos, ?_⟩
  exact hσ_eig

/-- **TP / left-canonical gauge data for an irreducible MPS tensor.**

For an irreducible MPS tensor `A` with `D > 0` and some `A i ≠ 0`, there exist:
* a positive real `r` (the spectral radius of the adjoint transfer map),
* a positive definite matrix `σ`,
* such that the rescaled-and-gauged tensor `B i = σ^{1/2} ((1/√r) • A i) σ^{-1/2}`
  satisfies the TP / left-canonical condition `∑ (B i)ᴴ * B i = 1`.

The tensor `B` is gauge-equivalent to the rescaled tensor `(1/√r) • A`, hence has
the same MPV as `A` up to a system-size-dependent factor `(1/√r)^N`.

This theorem combines `exists_posDef_adjoint_eigenvector` with the explicit
`Kraus.tpGauge` construction. -/
theorem exists_tp_data_of_irreducible
    [NeZero D]
    (A : MPSTensor d D)
    (hIrr : Kraus.IsIrreducibleFamily (ι := Fin d) (n := Fin D) A)
    (hA : ∃ i, A i ≠ 0) :
    ∃ (B : MPSTensor d D) (r : ℝ) (σ : Matrix (Fin D) (Fin D) ℂ),
      σ.PosDef ∧ 0 < r ∧
      -- B is the Kraus.tpGauge of the rescaled tensor
      (∀ i : Fin d,
        B i = CFC.sqrt σ *
          ((↑((Real.sqrt r)⁻¹) : ℂ) • A i) * (CFC.sqrt σ)⁻¹) ∧
      -- B is TP
      (∑ i : Fin d, (B i)ᴴ * B i = 1) ∧
      -- B is gauge-equivalent to the rescaled tensor
      GaugeEquiv (α := Fin d) (β := Fin D)
        (fun i => (↑((Real.sqrt r)⁻¹) : ℂ) • A i) B := by
  obtain ⟨σ, r, hσ_pd, hr_pos, hσ_eig⟩ :=
    exists_posDef_adjoint_eigenvector A hIrr hA
  let A' : MPSTensor d D := fun i => (↑((Real.sqrt r)⁻¹) : ℂ) • A i
  let B := Kraus.tpGauge (d := d) (D := D) A' σ
  refine ⟨B, r, σ, hσ_pd, hr_pos, fun i => rfl, ?_, gaugeEquiv_tpGauge A' σ hσ_pd⟩
  exact Kraus.tpGauge_isTP_of_map_conjTranspose_eigenvector A σ r hσ_pd hr_pos hσ_eig

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
    (hIrr : Kraus.IsIrreducibleFamily (ι := Fin d) (n := Fin D) A)
    (hA : ∃ i, A i ≠ 0) :
    ∃ (B : MPSTensor d D) (r : ℝ) (ρ : Matrix (Fin D) (Fin D) ℂ),
      ρ.PosDef ∧ 0 < r ∧
      (∀ i : Fin d,
        B i =
          (↑((Real.sqrt r)⁻¹) : ℂ) •
            ((CFC.sqrt ρ)⁻¹ * A i * CFC.sqrt ρ)) ∧
      (∑ i : Fin d, B i * (B i)ᴴ = 1) ∧
      GaugeEquiv (α := Fin d) (β := Fin D)
        (fun i => (↑((Real.sqrt r)⁻¹) : ℂ) • A i) B := by
  classical
  let Aadj : MPSTensor d D := fun i => (A i)ᴴ
  have hIrrAdjMap :
      IsIrreducibleMap (Kraus.transferMap (ι := Fin d) (n := Fin D) Aadj) := by
    simpa [Aadj] using
      Kraus.isIrreducibleMap_mapLM_conjTranspose A
        (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hIrr)
  have hIrrAdj : Kraus.IsIrreducibleFamily (ι := Fin d) (n := Fin D) Aadj :=
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM Aadj hIrrAdjMap
  have hAadj : ∃ i, Aadj i ≠ 0 := by
    rcases hA with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    intro h
    exact hi (Matrix.conjTranspose_eq_zero.mp (by simpa [Aadj] using h))
  obtain ⟨ρ, r, hρ, hr, hρ_eig_adj⟩ :=
    exists_posDef_adjoint_eigenvector (d := d) (D := D) Aadj hIrrAdj hAadj
  have hρ_eig : Kraus.transferMap (ι := Fin d) (n := Fin D) A ρ = (r : ℂ) • ρ := by
    simpa [Aadj, Matrix.conjTranspose_conjTranspose] using hρ_eig_adj
  let B : MPSTensor d D := Kraus.spectralUnitalGauge (d := d) (D := D) A r ρ
  have hB_unital : ∑ i : Fin d, B i * (B i)ᴴ = 1 := by
    simpa [B, Kraus.IsUnital] using
      Kraus.spectralUnitalGauge_isUnital_of_map_eigenvector
        (d := d) (D := D) A ρ r hρ hr hρ_eig
  have hGauge : GaugeEquiv (α := Fin d) (β := Fin D)
      (fun i => (↑((Real.sqrt r)⁻¹) : ℂ) • A i) B := by
    convert
      gaugeEquiv_unitalGauge (d := d) (D := D)
        (fun i => (↑((Real.sqrt r)⁻¹) : ℂ) • A i) ρ hρ using 1
    ext i
    simp [B, Kraus.spectralUnitalGauge, Kraus.unitalGauge]
  refine ⟨B, r, ρ, hρ, hr, ?_, hB_unital, hGauge⟩
  intro i
  rfl

end MPSTensor

end

section

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

/-- For an irreducible unital MPS tensor, every transfer-map fixed point is a
scalar multiple of the identity.

This is the MPS formulation of the endpoint in the proof of
PGVWC07 Theorem `Th:TIcanonical`, lines 816--826: after all invariant
subspace splittings have been exhausted, a further non-scalar fixed point
would give another split, so the fixed-point space of the unital block is the
scalar line.  The channel-theoretic input is Wolf Theorem 6.6, formalized as
`Kraus.fixed_eq_scalar_of_irreducible_unital`. -/
theorem fixed_eq_scalar_of_isIrreducibleFamily_unital
    {d D : ℕ}
    (A : MPSTensor d D)
    (hIrr : Kraus.IsIrreducibleFamily (ι := Fin d) (n := Fin D) A)
    (hUnital : Kraus.transferMap (ι := Fin d) (n := Fin D) A 1 = 1)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hfix : Kraus.transferMap (ι := Fin d) (n := Fin D) A X = X) :
    ∃ c : ℂ, X = c • (1 : Matrix (Fin D) (Fin D) ℂ) := by
  classical
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact ⟨0, Subsingleton.elim _ _⟩
  have : NeZero D := ⟨hD.ne'⟩
  have hUnitalKraus : KadisonSchwarz.IsUnitalKraus (d := d) (D := D) A := by
    simpa [Kraus.transferMap_apply, Matrix.mul_one, KadisonSchwarz.IsUnitalKraus]
      using hUnital
  have hIrrMap : IsIrreducibleMap (Kraus.mapLM A) :=
    Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hIrr
  have hfix_map : Kraus.mapLM A X = X := hfix
  exact Kraus.fixed_eq_scalar_of_irreducible_unital A hUnitalKraus hIrrMap X hfix_map

end MPSTensor

end
