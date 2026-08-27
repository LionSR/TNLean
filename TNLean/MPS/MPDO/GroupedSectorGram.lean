/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.NormalCommutant
import TNLean.MPS.MPDO.FigureEightPairwise
import TNLean.MPS.MPDO.GroupedReferenceCorner

/-!
# Gram kernels for grouped vertical sectors

This file isolates the canonical-form-independent part of the grouped Figure 8
argument. A grouped-corner Gram-dressing hypothesis compares any two positive
corners of one representative. The distinguished reference corner then makes
each grouped Gram conjugation trivial, and normality forces the Gram matrix to
be a positive scalar multiple of the identity.

## Main definitions

* `MPOTensor.HasGroupedCornerGramDressing`: the pairwise Figure 8 input used by
  the grouped-sector argument.

## Main results

* `MPOTensor.grouped_sector_gram_conj_eq_of_dressing`: the distinguished
  identity-gauge corner makes a grouped Gram conjugation fix its representative.
* `MPOTensor.grouped_sector_gram_eq_pos_smul_one_of_dressing`: normality makes
  the grouped Gram matrix a positive scalar multiple of the identity.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, Figures 7--8 and lines 1903--1921.
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- Pairwise equality of Gram dressings for two positive vertical corners of a
common representative.

This is the exact canonical-form-specific input used by the grouped Figure 8
argument. Both literal CPSV canonical form and normalized BNT-refined
horizontal form provide this statement independently.

Source: arXiv:1606.00608, proof of Proposition 4.13, Figures 7--8 and lines
1909--1919. -/
def HasGroupedCornerGramDressing (M : MPOTensor d D) : Prop :=
  ∀ {n : ℕ} (A : MPSTensor (D * D) n)
    (VX VY : Matrix (Fin d) (Fin n) ℂ) (X Y : GL (Fin n) ℂ)
    (cX cY : ℂ), (0 : ℂ) < cX → (0 : ℂ) < cY →
    (∀ v, VXᴴ * verticalTensor M v * VX =
      cX • ((X : Matrix (Fin n) (Fin n) ℂ) * A v *
        (↑(X⁻¹) : Matrix (Fin n) (Fin n) ℂ))) →
    (∀ v, VYᴴ * verticalTensor M v * VY =
      cY • ((Y : Matrix (Fin n) (Fin n) ℂ) * A v *
        (↑(Y⁻¹) : Matrix (Fin n) (Fin n) ℂ))) →
    gramDressing X A = gramDressing Y A

section GroupedSectors

variable {r : ℕ} {dim : Fin r → ℕ}
variable (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))

local notation "C" => MPSTensor.mpvPhaseClassData blocks

/-- The pairwise Gram-dressing hypothesis and the distinguished identity-gauge
corner imply that each grouped Gram conjugation fixes its representative.

The hypotheses after `hDressing` are clauses of
`HasVerticalBNTGroupingWithIsometry`.

Source: arXiv:1606.00608, proof of Proposition 4.13, Figures 7--8 and lines
1903--1919. -/
theorem grouped_sector_gram_conj_eq_of_dressing
    {M : MPOTensor d D} (hDressing : HasGroupedCornerGramDressing M)
    (μ : Fin r → ℂ) (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (hdim : ∀ j q, dim ((C).repr j) = dim ((C).enum j q))
    (X : (j : Fin (C).g) → (q : Fin ((C).copies j)) →
      GL (Fin (dim ((C).enum j q))) ℂ)
    (ζ : (j : Fin (C).g) → Fin ((C).copies j) → ℂ)
    (hXDist : ∀ j, X j ⟨0, (C).copies_pos j⟩ = 1)
    (hCoeffPos : ∀ j q, (0 : ℂ) < μ ((C).enum j q) * ζ j q)
    (hCorner : ∀ j q v,
      (μ ((C).enum j q) * ζ j q) •
          ((X j q : Matrix (Fin (dim ((C).enum j q)))
              (Fin (dim ((C).enum j q))) ℂ) *
            (cast (congrArg (MPSTensor (D * D)) (hdim j q))
              (blocks ((C).repr j))) v *
            (↑((X j q)⁻¹) : Matrix (Fin (dim ((C).enum j q)))
              (Fin (dim ((C).enum j q))) ℂ)) =
        (V ((C).enum j q))ᴴ * verticalTensor M v * V ((C).enum j q))
    (j : Fin (C).g) (q : Fin ((C).copies j))
    (v : Fin (D * D)) :
    let A := cast (congrArg (MPSTensor (D * D)) (hdim j q))
      (blocks ((C).repr j))
    let G := (X j q : Matrix (Fin (dim ((C).enum j q)))
      (Fin (dim ((C).enum j q))) ℂ)ᴴ * X j q
    G * A v * G⁻¹ = A v := by
  classical
  let A := cast (congrArg (MPSTensor (D * D)) (hdim j q))
    (blocks ((C).repr j))
  let cq := μ ((C).enum j q) * ζ j q
  obtain ⟨W, c0, hc0, hCorner0⟩ :=
    exists_distinguished_grouped_reference_corner blocks μ V hdim X ζ
      hXDist hCoeffPos hCorner j q
  have hCornerq : ∀ w,
      (V ((C).enum j q))ᴴ * verticalTensor M w * V ((C).enum j q) =
        cq • ((X j q : Matrix (Fin (dim ((C).enum j q)))
            (Fin (dim ((C).enum j q))) ℂ) * A w *
          (↑((X j q)⁻¹) : Matrix (Fin (dim ((C).enum j q)))
            (Fin (dim ((C).enum j q))) ℂ)) := by
    intro w
    simpa [cq, A] using (hCorner j q w).symm
  have hGram := hDressing A (V ((C).enum j q)) W (X j q) 1 cq c0
    (hCoeffPos j q) hc0 hCornerq (by intro w; simpa [A] using hCorner0 w)
  simpa [gramDressing, A] using congrFun hGram v

/-- Normality and the grouped Figure 8 comparison force a grouped gauge Gram
matrix to be a positive scalar multiple of the identity.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem grouped_sector_gram_eq_pos_smul_one_of_dressing
    {M : MPOTensor d D} (hDressing : HasGroupedCornerGramDressing M)
    (μ : Fin r → ℂ) (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (_hDimPos : ∀ k, 0 < dim k)
    (hdim : ∀ j q, dim ((C).repr j) = dim ((C).enum j q))
    (hNormal : ∀ j q, Kraus.IsNormal
      (cast (congrArg (MPSTensor (D * D)) (hdim j q))
        (blocks ((C).repr j))))
    (X : (j : Fin (C).g) → (q : Fin ((C).copies j)) →
      GL (Fin (dim ((C).enum j q))) ℂ)
    (ζ : (j : Fin (C).g) → Fin ((C).copies j) → ℂ)
    (hXDist : ∀ j, X j ⟨0, (C).copies_pos j⟩ = 1)
    (hCoeffPos : ∀ j q, (0 : ℂ) < μ ((C).enum j q) * ζ j q)
    (hCorner : ∀ j q v,
      (μ ((C).enum j q) * ζ j q) •
          ((X j q : Matrix (Fin (dim ((C).enum j q)))
              (Fin (dim ((C).enum j q))) ℂ) *
            (cast (congrArg (MPSTensor (D * D)) (hdim j q))
              (blocks ((C).repr j))) v *
            (↑((X j q)⁻¹) : Matrix (Fin (dim ((C).enum j q)))
              (Fin (dim ((C).enum j q))) ℂ)) =
        (V ((C).enum j q))ᴴ * verticalTensor M v * V ((C).enum j q))
    (j : Fin (C).g) (q : Fin ((C).copies j)) :
    ∃ ω : ℝ, 0 < ω ∧
      (X j q : Matrix (Fin (dim ((C).enum j q)))
        (Fin (dim ((C).enum j q))) ℂ)ᴴ * X j q = (ω : ℂ) • 1 := by
  let : NeZero (dim ((C).enum j q)) :=
    ⟨(_hDimPos ((C).enum j q)).ne'⟩
  let A := cast (congrArg (MPSTensor (D * D)) (hdim j q))
    (blocks ((C).repr j))
  have hNormalA : Kraus.IsNormal A := hNormal j q
  have hGramConj : ∀ v,
      (X j q : Matrix (Fin (dim ((C).enum j q)))
          (Fin (dim ((C).enum j q))) ℂ)ᴴ * X j q * A v *
          (((X j q : Matrix (Fin (dim ((C).enum j q)))
            (Fin (dim ((C).enum j q))) ℂ)ᴴ * X j q)⁻¹) = A v := by
    intro v
    simpa [A] using grouped_sector_gram_conj_eq_of_dressing blocks hDressing
      μ V hdim X ζ hXDist hCoeffPos hCorner j q v
  exact hNormalA.gram_eq_pos_smul_one_of_gram_conj_eq
    (Matrix.isUnits_det_units (X j q)) hGramConj

end GroupedSectors

end MPOTensor
