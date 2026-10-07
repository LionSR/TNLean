/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixUnitConjugator
import TNLean.MPS.Symmetry.Defs
import TNLean.MPS.Preparation.BlockedPolar
import Mathlib.Topology.Instances.Matrix
import QICLean.Algebra.MatrixUnitConjugator

/-!
# Local continuous virtual gauges

A continuous action on a fixed matrix algebra admits locally continuous
conjugating matrices. A column obtained by applying the action to matrix
units gives an explicit choice near any prescribed invertible conjugator.

This is an auxiliary construction for the fixed-bond-dimension continuity
step in Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2,
lines 1000–1018.

**Scope restriction (fixed bond dimension and exact tensor symmetry):**
The on-site symmetry theorem assumes a continuous family of one-site
injective tensors of one fixed positive bond dimension, and symmetry
preserves their periodic vectors exactly. It constructs virtual matrices
that are invertible locally. It does not extract a continuous tensor family
from an arbitrary Hamiltonian path, extend the local virtual matrices over
the whole interval, or handle a change of minimal bond dimension. These
remaining parts of the separation argument are recorded in
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

open scoped Matrix ComplexOrder

namespace Matrix

variable {D : ℕ}

/-- A continuous family of inner matrix actions has continuous conjugators
near a prescribed invertible conjugator. Their matrix entries are defined
on the whole parameter space, while invertibility holds in a neighborhood
of the base point. Source context: arXiv:1010.3732, Section II.F.2,
lines 1000–1018. -/
theorem exists_continuous_local_matrixConjugator
    {T : Type*} [TopologicalSpace T] (hD : 0 < D)
    (α : T → Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ)
    (hα : ∀ M, Continuous fun t => α t M)
    (hinner : ∀ t, ∃ Y : GL (Fin D) ℂ, ∀ M, α t M = Y * M * Y⁻¹)
    (t₀ : T) (X₀ : GL (Fin D) ℂ)
    (hbase : ∀ M, α t₀ M = X₀ * M * X₀⁻¹) :
    ∃ X : T → Matrix (Fin D) (Fin D) ℂ,
      Continuous X ∧ X t₀ = X₀ ∧
      (∀ᶠ t in nhds t₀, (X t).det ≠ 0) ∧
      ∀ t M, α t M * X t = X t * M := by
  let a : Fin D := ⟨0, hD⟩
  let X : T → Matrix (Fin D) (Fin D) ℂ :=
    fun t => matrixUnitConjugator (α t) X₀ a
  have hX : Continuous X := by
    exact continuous_matrix fun i j =>
      ((hα (single j a 1)).matrix_mul continuous_const).matrix_elem i a
  have hXbase : X t₀ = X₀ := by
    simpa using matrixUnitConjugator_eq_smul (α t₀) X₀ a X₀ hbase
  have hdet : (X t₀).det ≠ 0 := hXbase ▸ X₀.det_ne_zero
  refine ⟨X, hX, hXbase, hX.matrix_det.continuousAt.eventually_ne hdet, ?_⟩
  intro t M
  obtain ⟨Y, hY⟩ := hinner t
  exact matrixUnitConjugator_intertwines (α t) X₀ a Y hY M

end Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- The inverse Gram matrix gives a right inverse to the coefficient map
of an injective tensor. Source context: arXiv:1010.3732, Section II.F.2,
lines 1000–1018, inversion of the injective tensor map. -/
noncomputable def coefficientInverseMatrix (A : MPSTensor d D) :
    Matrix (Fin d) (Fin D × Fin D) ℂ :=
  (((physicalMatrix A)ᴴ * physicalMatrix A)⁻¹ * (physicalMatrix A)ᴴ)ᵀ

/-- The inverse Gram coefficient matrix reconstructs every virtual matrix.
Source context: arXiv:1010.3732, Section II.F.2, lines 1000–1018. -/
theorem physicalMatrix_transpose_mul_coefficientInverseMatrix
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) :
    (physicalMatrix A)ᵀ * coefficientInverseMatrix A = 1 := by
  have hGram : IsUnit ((physicalMatrix A)ᴴ * physicalMatrix A).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.PosDef.conjTranspose_mul_self (physicalMatrix A)
        (injective_physicalMatrix_mulVec_of_isInjective hA)).isUnit
  rw [coefficientInverseMatrix, ← Matrix.transpose_mul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hGram, Matrix.transpose_one]

/-- The inverse Gram coefficient matrices vary continuously along a
continuous family of one-site injective tensors. Source context:
arXiv:1010.3732, Section II.F.2, lines 1000–1018. -/
theorem continuous_coefficientInverseMatrix_family
    {T : Type*} [TopologicalSpace T] (A : T → MPSTensor d D)
    (hA : Continuous A) (hInj : ∀ t, Kraus.IsInjective (A t)) :
    Continuous fun t => coefficientInverseMatrix (A t) := by
  have hP : Continuous fun t => physicalMatrix (A t) :=
    continuous_pi fun i => continuous_pi fun p =>
      (((continuous_apply i).comp hA).matrix_elem p.1 p.2)
  have hGram : Continuous fun t => (physicalMatrix (A t))ᴴ * physicalMatrix (A t) :=
    hP.matrix_conjTranspose.matrix_mul hP
  have hInv : Continuous fun t =>
      ((physicalMatrix (A t))ᴴ * physicalMatrix (A t))⁻¹ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hdet : ((physicalMatrix (A t))ᴴ * physicalMatrix (A t)).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp
        (Matrix.PosDef.conjTranspose_mul_self (physicalMatrix (A t))
          (injective_physicalMatrix_mulVec_of_isInjective (hInj t))).isUnit).ne_zero
    exact (continuousAt_matrix_inv _
      (by simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet)).comp
        hGram.continuousAt
  exact (hInv.matrix_mul hP.matrix_conjTranspose).matrix_transpose

/-- The inverse Gram coefficients expand any virtual matrix in the tensor
letters. Source context: arXiv:1010.3732, Section II.F.2, lines 1000–1018. -/
theorem coefficientInverseMatrix_reconstruct
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (M : Matrix (Fin D) (Fin D) ℂ) :
    ∑ i, ((coefficientInverseMatrix A).mulVec (fun p => M p.1 p.2)) i • A i = M := by
  have hvec : (physicalMatrix A)ᵀ *ᵥ
      ((coefficientInverseMatrix A) *ᵥ (fun p => M p.1 p.2)) =
        (fun p => M p.1 p.2) := by
    rw [Matrix.mulVec_mulVec, physicalMatrix_transpose_mul_coefficientInverseMatrix A hA,
      Matrix.one_mulVec]
  ext a b
  simpa [Matrix.mulVec, dotProduct, physicalMatrix, Matrix.sum_apply,
    Matrix.smul_apply, mul_comm] using congrFun hvec (a, b)

/-- The virtual matrix action obtained by applying the physical twist to
inverse Gram coefficients. Source context: arXiv:1010.3732, Section II.F.2,
lines 1000–1018. -/
noncomputable def virtualActionOfTensors (A B : MPSTensor d D)
    (M : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  ∑ i, ((coefficientInverseMatrix A).mulVec (fun p => M p.1 p.2)) i • B i

/-- When the tensor letters are related by a bond gauge, the reconstructed
virtual action is conjugation by that gauge. Source context:
arXiv:1010.3732, Section II.F.2, lines 1000–1018. -/
theorem virtualActionOfTensors_eq_conj
    (A B : MPSTensor d D) (hA : Kraus.IsInjective A) (Y : GL (Fin D) ℂ)
    (hY : ∀ i, B i = Y * A i * Y⁻¹) (M : Matrix (Fin D) (Fin D) ℂ) :
    virtualActionOfTensors A B M = Y * M * Y⁻¹ := by
  have heq : virtualActionOfTensors A B M =
      Y * (∑ i, ((coefficientInverseMatrix A).mulVec (fun p => M p.1 p.2)) i • A i) *
        Y⁻¹ := by
    simp only [virtualActionOfTensors, hY, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  simpa only [coefficientInverseMatrix_reconstruct A hA M] using heq

/-- A continuously varying pair of tensors induces continuous virtual
matrix actions when the first tensor remains one-site injective. Source
context: arXiv:1010.3732, Section II.F.2, lines 1000–1018. -/
theorem continuous_virtualActionOfTensors_family
    {T : Type*} [TopologicalSpace T] (A B : T → MPSTensor d D)
    (hA : Continuous A) (hB : Continuous B)
    (hInj : ∀ t, Kraus.IsInjective (A t)) (M : Matrix (Fin D) (Fin D) ℂ) :
    Continuous fun t => virtualActionOfTensors (A t) (B t) M := by
  have hC := continuous_coefficientInverseMatrix_family A hA hInj
  unfold virtualActionOfTensors Matrix.mulVec dotProduct
  exact continuous_finsetSum _ fun i _ =>
    (continuous_finsetSum _ fun p _ => (hC.matrix_elem i p).mul continuous_const).smul
      ((continuous_apply i).comp hB)

/-- Pointwise gauge-equivalent continuous injective tensor families admit
locally continuous invertible bond gauges near any prescribed initial
gauge. No continuous choice of the pointwise gauges is assumed.
Source: arXiv:1010.3732, Section II.F.2, lines 1000–1018. -/
theorem exists_continuous_local_gauge_of_gaugeEquiv
    {T : Type*} [TopologicalSpace T] (hD : 0 < D)
    (A B : T → MPSTensor d D) (hA : Continuous A) (hB : Continuous B)
    (hInj : ∀ t, Kraus.IsInjective (A t))
    (hGauge : ∀ t, GaugeEquiv (A t) (B t))
    (t₀ : T) (X₀ : GL (Fin D) ℂ)
    (hbase : ∀ i, B t₀ i = X₀ * A t₀ i * X₀⁻¹) :
    ∃ X : T → Matrix (Fin D) (Fin D) ℂ,
      Continuous X ∧ X t₀ = X₀ ∧
      (∀ᶠ t in nhds t₀, (X t).det ≠ 0) ∧
      ∀ t i, B t i * X t = X t * A t i := by
  have hinner : ∀ t, ∃ Y : GL (Fin D) ℂ,
      ∀ M, virtualActionOfTensors (A t) (B t) M = Y * M * Y⁻¹ := by
    intro t
    obtain ⟨Y, hY⟩ := hGauge t
    exact ⟨Y, virtualActionOfTensors_eq_conj (A t) (B t) (hInj t) Y hY⟩
  obtain ⟨X, hX, hXbase, hdet, hInt⟩ := Matrix.exists_continuous_local_matrixConjugator
    hD (fun t => virtualActionOfTensors (A t) (B t))
    (continuous_virtualActionOfTensors_family A B hA hB hInj) hinner t₀ X₀
    (virtualActionOfTensors_eq_conj (A t₀) (B t₀) (hInj t₀) X₀ hbase)
  refine ⟨X, hX, hXbase, hdet, ?_⟩
  intro t i
  obtain ⟨Y, hY⟩ := hGauge t
  simpa only [virtualActionOfTensors_eq_conj (A t) (B t) (hInj t) Y hY,
    ← hY i] using hInt t (A t i)

/-- A continuous family of one-site injective tensors with exact on-site
symmetry admits continuous virtual symmetry matrices near every parameter.
The matrices are invertible in that neighborhood. No continuous virtual
representation is assumed. Source: arXiv:1010.3732, Section II.F.2,
lines 1000–1018, at a fixed positive bond dimension. -/
theorem exists_continuous_local_virtualGauge_of_isOnSiteSymmetric
    {T G : Type*} [TopologicalSpace T] [Group G] (hD : 0 < D)
    (A : T → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ t, Kraus.IsInjective (A t))
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hSym : ∀ t, IsOnSiteSymmetric (A t) U) (t₀ : T) (g : G) :
    ∃ X : T → Matrix (Fin D) (Fin D) ℂ,
      Continuous X ∧ (∀ᶠ t in nhds t₀, (X t).det ≠ 0) ∧
      ∀ t i, twistedTensor (A t) U g i * X t = X t * A t i := by
  have hGauge (t : T) : GaugeEquiv (A t) (twistedTensor (A t) U g) :=
    gaugeEquiv_twistedTensor_of_injective (A t) (hInj t) U (hSym t) g
  have hB : Continuous fun t => twistedTensor (A t) U g := by
    unfold twistedTensor
    exact continuous_pi fun i => continuous_finsetSum _ fun j _ =>
      (continuous_const : Continuous fun _ : T => U g i j).smul
        ((continuous_apply j).comp hA)
  obtain ⟨X₀, hbase⟩ := hGauge t₀
  obtain ⟨X, hX, _, hdet, hInt⟩ := exists_continuous_local_gauge_of_gaugeEquiv
    hD A (fun t => twistedTensor (A t) U g) hA hB hInj hGauge t₀ X₀ hbase
  exact ⟨X, hX, hdet, hInt⟩

end MPSTensor
