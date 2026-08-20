/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge

/-!
# MPS canonical-form conjugation

Entrywise complex conjugation preserves injectivity, normality, left-canonical normalization,
and the transfer-map fixed-point equations used in canonical forms.

## Main definitions

* `MPSTensor.mapStar`: entrywise complex conjugation of an MPS tensor.

## Main results

* `MPSTensor.IsInjective.mapStar`: conjugation preserves injectivity.
* `MPSTensor.IsNormal.mapStar`: conjugation preserves normality.
* `MPSTensor.IsLeftCanonical.mapStar`: conjugation preserves left-canonical normalization.
* `MPSTensor.GaugeEquiv.mapStar`: conjugation preserves gauge equivalence.
* `MPSTensor.IsNormalTensor.mapStar`: conjugation preserves normalized normal tensors.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- Entrywise complex conjugation of every letter of an MPS tensor. -/
def mapStar (A : MPSTensor d D) : MPSTensor d D :=
  fun i ↦ (A i).map (starRingEnd ℂ)

/-- Entrywise conjugation evaluated at one physical letter. -/
@[simp] theorem mapStar_apply (A : MPSTensor d D) (i : Fin d) :
    mapStar A i = (A i).map (starRingEnd ℂ) := rfl

/-- Entrywise conjugation is an involution on MPS tensors. -/
@[simp] theorem mapStar_mapStar (A : MPSTensor d D) :
    mapStar (mapStar A) = A := by
  ext i β α
  simp [mapStar, Matrix.map_apply]

/-- Entrywise conjugation preserves algebraic injectivity. -/
theorem IsInjective.mapStar {A : MPSTensor d D} (hA : IsInjective A) :
    IsInjective (mapStar A) := by
  classical
  rw [IsInjective]
  apply top_unique
  intro X _
  have hmem : X.map (starRingEnd ℂ) ∈ Submodule.span ℂ (Set.range A) := by
    rw [hA]
    trivial
  have hconj : ∀ Y ∈ Submodule.span ℂ (Set.range A),
      Y.map (starRingEnd ℂ) ∈ Submodule.span ℂ (Set.range (MPSTensor.mapStar A)) := by
    intro Y hY
    induction hY using Submodule.span_induction with
    | mem Z hZ =>
        obtain ⟨i, rfl⟩ := hZ
        exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add Y Z _ _ hY hZ =>
        rw [show (Y + Z).map (starRingEnd ℂ) =
          Y.map (starRingEnd ℂ) + Z.map (starRingEnd ℂ) by
            exact Matrix.map_add _ (map_add (starRingEnd ℂ)) Y Z]
        exact Submodule.add_mem _ hY hZ
    | smul c Y _ hY =>
        rw [show (c • Y).map (starRingEnd ℂ) =
          star c • Y.map (starRingEnd ℂ) by
            ext i j
            simp [Matrix.map_apply]]
        exact Submodule.smul_mem _ (star c) hY
  have := hconj _ hmem
  convert this using 1
  ext i j
  simp [Matrix.map_apply]

private theorem evalWord_mapStar (A : MPSTensor d D) (w : List (Fin d)) :
    evalWord (mapStar A) w = (evalWord A w).map (starRingEnd ℂ) := by
  induction w with
  | nil => simp
  | cons i w ih =>
      simp only [Kraus.evalWord, mapStar_apply, ih]
      exact ((starRingEnd ℂ).mapMatrix.map_mul (A i) (evalWord A w)).symm

/-- Entrywise conjugation preserves positive-length block injectivity, hence normality. -/
theorem IsNormal.mapStar {A : MPSTensor d D} (hA : IsNormal A) :
    IsNormal (mapStar A) := by
  obtain ⟨N, hN, hInj⟩ := hA
  refine ⟨N, hN, ?_⟩
  change Kraus.IsNBlkInjective A N at hInj
  change Kraus.IsNBlkInjective (mapStar A) N
  rw [isNBlkInjective_iff_blockTensor_isInjective] at hInj ⊢
  change IsInjective (blockTensor A N) at hInj
  change IsInjective (blockTensor (mapStar A) N)
  have hConj := hInj.mapStar
  convert hConj using 1
  ext σ β α
  simp [blockTensor, evalWord_mapStar]

/-- Left-canonical normalization is preserved by entrywise complex conjugation. -/
theorem IsLeftCanonical.mapStar {A : MPSTensor d D} (hA : IsLeftCanonical A) :
    IsLeftCanonical (mapStar A) := by
  classical
  rw [IsLeftCanonical] at hA ⊢
  calc
    ∑ i, (MPSTensor.mapStar A i)ᴴ * MPSTensor.mapStar A i =
        (∑ i, (A i)ᴴ * A i).map (starRingEnd ℂ) := by
      rw [show (∑ i, (A i)ᴴ * A i).map (starRingEnd ℂ) =
        ∑ i, ((A i)ᴴ * A i).map (starRingEnd ℂ) by
      exact map_sum ((starRingEnd ℂ).mapMatrix) _ Finset.univ]
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.map_mul, Matrix.conjTranspose_map (starRingEnd ℂ) (by simp [Function.Semiconj])]
      rfl
    _ = 1 := by rw [hA]; simp

/-- Gauge equivalence is preserved by entrywise complex conjugation.

This conjugates the invertible gauge in the relation of arXiv:1606.00608,
lines 264--268. -/
theorem GaugeEquiv.mapStar {A B : MPSTensor d D} (h : GaugeEquiv A B) :
    GaugeEquiv (mapStar A) (mapStar B) := by
  obtain ⟨X, hX⟩ := h
  let f : Matrix (Fin D) (Fin D) ℂ →+* Matrix (Fin D) (Fin D) ℂ :=
    (starRingEnd ℂ).mapMatrix
  let Xbar : GL (Fin D) ℂ := (Units.map f.toMonoidHom) X
  refine ⟨Xbar, fun i ↦ ?_⟩
  rw [mapStar_apply, mapStar_apply, hX i, Matrix.map_mul, Matrix.map_mul]
  rfl

/-- Entrywise complex conjugation preserves CPSV normal tensors.

The proof uses the pure trace-preserving Perron gauge associated with the
normal tensor, conjugates that gauge, and transports normality back. Entrywise
conjugation transports the spectral-radius-one normalization of
arXiv:1606.00608, lines 224--235, together with the gauge relation at lines
264--268. -/
theorem IsNormalTensor.mapStar {A : MPSTensor d D} (hA : IsNormalTensor A) :
    IsNormalTensor (mapStar A) := by
  let : NeZero D := ⟨hA.bondDim_ne_zero⟩
  obtain ⟨σ, _hσ, _hσfix, hLeft, hGauge, _hPrim, _hIrr⟩ := hA.exists_tpGauge
  have hGaugeNormal : IsNormalTensor (tpGauge (d := d) (D := D) A σ) :=
    hA.of_gaugeEquiv hGauge.symm
  have hGaugeStarNormal :
      IsNormalTensor (MPSTensor.mapStar (tpGauge (d := d) (D := D) A σ)) :=
    isNormalTensor_of_isNormal_leftCanonical _ hGaugeNormal.isNormal.mapStar hLeft.mapStar
  exact hGaugeStarNormal.of_gaugeEquiv hGauge.mapStar

/-- A diagonal positive-definite complex matrix is fixed by entrywise conjugation. -/
theorem map_star_eq_self_of_posDef_isDiag
    {n : ℕ} {Λ : Matrix (Fin n) (Fin n) ℂ} (hΛpos : Λ.PosDef) (hΛdiag : Λ.IsDiag) :
    Λ.map (starRingEnd ℂ) = Λ := by
  ext i j
  by_cases hij : i = j
  · subst j
    simpa [Matrix.map_apply] using hΛpos.1.apply i i
  · simp [Matrix.map_apply, hΛdiag hij]

/-- The transfer map of an entrywise-conjugated tensor is the conjugate of the original
transfer map on conjugated inputs. -/
theorem transferMap_mapStar (A : MPSTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    transferMap (mapStar A) (X.map (starRingEnd ℂ)) =
      (transferMap A X).map (starRingEnd ℂ) := by
  classical
  simp only [transferMap_apply]
  rw [show (∑ i, A i * X * (A i)ᴴ).map (starRingEnd ℂ) =
      ∑ i, (A i * X * (A i)ᴴ).map (starRingEnd ℂ) by
    exact map_sum ((starRingEnd ℂ).mapMatrix) _ Finset.univ]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.map_mul, Matrix.map_mul,
    Matrix.conjTranspose_map (starRingEnd ℂ) (by simp [Function.Semiconj])]
  rfl

end MPSTensor
