/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import TNLean.MPS.Symmetry.Defs
import TNLean.MPS.Symmetry.TimeReversalIndex
import TNLean.Wielandt.SpanGrowth.CumulativeSpan

/-!
# No normal spin-`1/2` MPS is invariant under on-site `SU(2)`

**Source.** Cirac, Pérez-García, Schuch, Verstraete (arXiv:2011.12127), §III.A,
`Papers/2011.12127/TN-Review-main.tex` line 1100, and §III.C, paragraph
"Kramers theorem and Lieb-Schultz-Mattis" (line 1230): for a spin-`1/2` chain with
`SU(2)` symmetry, no uniform normal MPS exhibits the symmetry, the tensor-network
form of the Lieb–Schultz–Mattis theorem.

**Formalized here.**
* `MPSTensor.not_anticommuting_gauges_of_isNormal`: if two physical operators
  anticommute, `P Q = -Q P`, no normal tensor of positive bond dimension has
  virtual gauges for both, `∑ⱼ Pᵢⱼ Aʲ = ζ X Aⁱ X⁻¹` and
  `∑ⱼ Qᵢⱼ Aʲ = η Y Aⁱ Y⁻¹` with `ζ, η ≠ 0`: composing the two twists in both orders
  gives `(Y X) Aⁱ (Y X)⁻¹ = -(X Y) Aⁱ (X Y)⁻¹`, which eq. `eq:XAX=B` rules out.
* `MPSTensor.not_isOnSiteSymmetric_specialUnitaryGroup_of_isNormal`: no normal
  tensor on a spin-`1/2` site of positive bond dimension is on-site symmetric under
  the defining representation of `SU(2)`.  Blocking to an odd injective length, the
  two elements `iσ_x` and `iσ_z` act by anticommuting Kronecker powers.

The source argues through the Clebsch–Gordan structure of the virtual
representations (integer and half-integer spins alternate).  The proof here uses
only the anticommuting pair `iσ_x`, `iσ_z` inside `SU(2)`.  On-site symmetry is the
project's predicate: each group element preserves the matrix product vectors
exactly.

## Main results

* `MPSTensor.not_anticommuting_gauges_of_isNormal`
* `MPSTensor.blockKron_smul`
* `MPSTensor.not_isOnSiteSymmetric_specialUnitaryGroup_of_isNormal`

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García,
  Schuch, Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Twisting a gauge-transformed family:
if `Bʲ = c Y Cʲ Y⁻¹`, then `∑ⱼ Pᵢⱼ Bʲ = c Y (∑ⱼ Pᵢⱼ Cʲ) Y⁻¹`. -/
private lemma sum_smul_gauge {B C : MPSTensor d D} (P : Matrix (Fin d) (Fin d) ℂ)
    (Y : GL (Fin D) ℂ) (c : ℂ)
    (h : ∀ j, B j = c • ((Y : Matrix (Fin D) (Fin D) ℂ) * C j *
      ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) (i : Fin d) :
    ∑ j : Fin d, P i j • B j = c • ((Y : Matrix (Fin D) (Fin D) ℂ) *
      (∑ j : Fin d, P i j • C j) * ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
  simp only [h, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, Matrix.mul_smul,
    Matrix.smul_mul, smul_comm c]

/-- The twist by a product is the composite of the twists. -/
private lemma sum_mul_smul (A : MPSTensor d D) (P Q : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) :
    ∑ k : Fin d, (P * Q) i k • A k = ∑ j : Fin d, P i j • ∑ k : Fin d, Q j k • A k := by
  simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

/-- The composite of two gauged twists is gauged by the product of the gauges. -/
private lemma sum_mul_smul_gauge {A : MPSTensor d D} {P Q : Matrix (Fin d) (Fin d) ℂ}
    {X Y : GL (Fin D) ℂ} {ζ η : ℂ}
    (hX : ∀ i, ∑ j : Fin d, P i j • A j =
      ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i * ((X⁻¹ : GL (Fin D) ℂ) : Matrix _ _ ℂ)))
    (hY : ∀ i, ∑ j : Fin d, Q i j • A j =
      η • ((Y : Matrix (Fin D) (Fin D) ℂ) * A i * ((Y⁻¹ : GL (Fin D) ℂ) : Matrix _ _ ℂ)))
    (i : Fin d) :
    ∑ k : Fin d, (P * Q) i k • A k = (η * ζ) •
      (((Y * X : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((Y * X)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
  rw [sum_mul_smul, sum_smul_gauge P Y η hY i, hX i]
  simp only [mul_inv_rev, Units.val_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    Matrix.mul_assoc]

/-- **Anticommuting physical symmetries have no common gauge description.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
lines 1085–1086 and 1117): a physical symmetry acting projectively on the site is
obstructed by eq. `eq:XAX=B`.  If `P Q = -Q P`, no normal tensor of positive bond
dimension satisfies both `∑ⱼ Pᵢⱼ Aʲ = ζ X Aⁱ X⁻¹` and
`∑ⱼ Qᵢⱼ Aʲ = η Y Aⁱ Y⁻¹` with `ζ, η ≠ 0`. -/
theorem not_anticommuting_gauges_of_isNormal [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) {P Q : Matrix (Fin d) (Fin d) ℂ} (hPQ : P * Q = -(Q * P))
    (X Y : GL (Fin D) ℂ) {ζ η : ℂ} (hζ : ζ ≠ 0) (hη : η ≠ 0)
    (hX : ∀ i, ∑ j : Fin d, P i j • A j =
      ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i * ((X⁻¹ : GL (Fin D) ℂ) : Matrix _ _ ℂ)))
    (hY : ∀ i, ∑ j : Fin d, Q i j • A j =
      η • ((Y : Matrix (Fin D) (Fin D) ℂ) * A i * ((Y⁻¹ : GL (Fin D) ℂ) : Matrix _ _ ℂ))) :
    False := by
  have hPQA := sum_mul_smul_gauge hX hY
  have hQPA := sum_mul_smul_gauge hY hX
  -- `(Y X) Aⁱ (Y X)⁻¹ = -(X Y) Aⁱ (X Y)⁻¹`.
  have hrel : ∀ i, (((Y * X : GL (Fin D) ℂ)) : Matrix (Fin D) (Fin D) ℂ) * A i *
      (((Y * X)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) = (-1 : ℂ) •
        ((((X * Y : GL (Fin D) ℂ)) : Matrix (Fin D) (Fin D) ℂ) * A i *
          (((X * Y)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
    intro i
    have h1 : ∑ k : Fin d, (P * Q) i k • A k = -∑ k : Fin d, (Q * P) i k • A k := by
      rw [hPQ, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [Matrix.neg_apply, neg_smul]
    rw [hPQA i, hQPA i, mul_comm ζ η, ← smul_neg] at h1
    rw [smul_right_injective _ (mul_ne_zero hη hζ) h1, neg_one_smul]
  obtain ⟨hc, -⟩ := gauge_phase_unique_of_isNormal hA (X := (Y * X)⁻¹) (Y := (X * Y)⁻¹)
    (c := -1) (fun i => by rw [inv_inv, inv_inv]; exact hrel i)
  norm_num at hc

/-- The Kronecker power of a scalar multiple: `blockKron L (c • P) = c ^ L • blockKron L P`. -/
theorem blockKron_smul {m n : ℕ} (L : ℕ) (c : ℂ) (P : Matrix (Fin m) (Fin n) ℂ) :
    blockKron L (c • P) = c ^ L • blockKron L P := by
  ext I J
  simp [blockKron, Finset.prod_mul_distrib, Finset.prod_const]

/-- The matrix `iσ_x` lies in `SU(2)`. -/
private lemma iPauliX_mem : (!![0, Complex.I; Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ) ∈
    Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, by simp [Matrix.det_fin_two]⟩
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]

/-- The matrix `iσ_z` lies in `SU(2)`. -/
private lemma iPauliZ_mem : (!![Complex.I, 0; 0, -Complex.I] : Matrix (Fin 2) (Fin 2) ℂ) ∈
    Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, by simp [Matrix.det_fin_two]⟩
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]

/-- **No normal spin-`1/2` MPS is invariant under on-site `SU(2)`.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
line 1100): "no uniform normal/injective MPS can exhibit such a symmetry", the
tensor-network form of the Lieb–Schultz–Mattis theorem (line 1230).

Here the symmetry is on-site symmetry under the defining representation of
`SU(2)` on `ℂ²`. -/
theorem not_isOnSiteSymmetric_specialUnitaryGroup_of_isNormal [NeZero D]
    {A : MPSTensor 2 D} (hA : Kraus.IsNormal A) :
    ¬ IsOnSiteSymmetric A (Matrix.specialUnitaryGroup (Fin 2) ℂ).subtype := by
  intro hsymm
  obtain ⟨N, hNpos, hN⟩ := hA
  -- Block to the odd length `L = 2N + 1`, where the blocked tensor is injective.
  set L := 2 * N + 1 with hL
  have hinj : Kraus.IsInjective (blockTensor A L) :=
    (isNBlkInjective_iff_blockTensor_isInjective A L).1
      (isNBlkInjective_of_le hNpos hN (by omega))
  have hBsymm := isOnSiteSymmetric_blockTensor A _ L hsymm
  let gx : Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨_, iPauliX_mem⟩
  let gz : Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨_, iPauliZ_mem⟩
  obtain ⟨X, hX⟩ := gaugeEquiv_twistedTensor_of_injective _ hinj _ hBsymm gx
  obtain ⟨Y, hY⟩ := gaugeEquiv_twistedTensor_of_injective _ hinj _ hBsymm gz
  have hanti : (gx : Matrix (Fin 2) (Fin 2) ℂ) * (gz : Matrix (Fin 2) (Fin 2) ℂ) =
      (-1 : ℂ) • ((gz : Matrix (Fin 2) (Fin 2) ℂ) * (gx : Matrix (Fin 2) (Fin 2) ℂ)) := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gx, gz, Matrix.mul_apply, Fin.sum_univ_two]
  have hPQ : blockKron L (gx : Matrix (Fin 2) (Fin 2) ℂ) * blockKron L gz =
      -(blockKron L (gz : Matrix (Fin 2) (Fin 2) ℂ) * blockKron L gx) := by
    rw [← blockKron_mul, ← blockKron_mul, hanti, blockKron_smul, hL, pow_succ, pow_mul]
    simp
  exact not_anticommuting_gauges_of_isNormal hinj.isNormal hPQ X Y one_ne_zero one_ne_zero
    (fun i => by simpa [twistedTensor] using hX i)
    (fun i => by simpa [twistedTensor] using hY i)

end MPSTensor
