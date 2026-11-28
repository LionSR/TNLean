/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNT.PhaseCover
import TNLean.MPS.CanonicalForm.VerticalForm.VerticalCF
import QICLean.Kraus.NormalCommutant
import TNLean.MPS.MPDO.Vertical.FigureEightPairwise
import QICLean.Algebra.Unitary.MatrixGramUnitary

/-!
# Distinguished reference corners for grouped vertical sectors

This file transports the distinguished physical corner of a vertical phase
class to the bond dimension of any chosen copy.  The construction depends only
on the grouped corner equations and is shared by the literal CPSV and
BNT-refined Figure 8 arguments.

## Main result

* `MPOTensor.exists_distinguished_grouped_reference_corner`: the transported
  identity-gauge corner at the bond dimension of a chosen grouped copy.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1903--1919.

## Gram kernels for grouped vertical sectors

This file isolates the canonical-form-independent part of the grouped Figure 8
argument. A grouped-corner Gram-dressing hypothesis compares any two positive
corners of one representative. The distinguished reference corner then makes
each grouped Gram conjugation trivial, and normality forces the Gram matrix to
be a positive scalar multiple of the identity.

### Main definitions

* `MPOTensor.HasGroupedCornerGramDressing`: the pairwise Figure 8 input used by
  the grouped-sector argument.

### Main results

* `MPOTensor.grouped_sector_gram_conj_eq_of_dressing`: the distinguished
  identity-gauge corner makes a grouped Gram conjugation fix its representative.
* `MPOTensor.grouped_sector_gram_eq_pos_smul_one_of_dressing`: normality makes
  the grouped Gram matrix a positive scalar multiple of the identity.

### References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, Figures 7--8 and lines 1903--1921.

## Unitary normalization of grouped vertical sectors

The grouped-corner Gram-dressing hypothesis makes the Gram matrix of every
grouped gauge a positive multiple of the identity. Dividing the gauge by the
square root of that scalar makes it unitary. The argument uses no
canonical-form hypothesis: literal CPSV canonical form and
BNT-refined horizontal form each supply the Gram dressing independently.

### Main result

* `MPOTensor.grouped_sector_exists_unitary_normalization_of_dressing`:
  rescaling a grouped gauge by the inverse square root of its Gram scalar
  makes it unitary.

### References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1903--1921.
-/

section

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D m n : ℕ}

/-- Transporting a vertical corner along an equality of its bond dimensions
preserves its corner identity. -/
private theorem vertical_corner_cast (M : MPOTensor d D)
    (A : MPOTensor D m) (V : Matrix (Fin d) (Fin m) ℂ)
    (c : ℂ) (hcorner : ∀ v, Vᴴ * verticalTensor M v * V = c • A v)
    (h : m = n) (v : Fin D × Fin D) :
    let A' := cast (congrArg (MPOTensor D) h) A
    let V' := cast (congrArg (fun k ↦ Matrix (Fin d) (Fin k) ℂ) h) V
    V'ᴴ * verticalTensor M v * V' = c • A' v := by
  cases h
  simpa using hcorner v

section GroupedSectors

variable {r : ℕ} {dim : Fin r → ℕ}
variable (blocks : (k : Fin r) → MPOTensor D (dim k))

local notation "C" => MPSTensor.mpvPhaseClassData blocks

/-- Transport the distinguished physical corner of a grouped phase class to the
bond dimension of a chosen copy.

The construction uses only the grouped corner equations, positivity of their
effective coefficients, and the identity gauge at the distinguished copy.  It
is independent of the canonical-form hypothesis used later to compare the two
corners by Figure 8.

Source context: arXiv:1606.00608, proof of Proposition 4.13, lines
1903--1919. -/
theorem exists_distinguished_grouped_reference_corner
    {M : MPOTensor d D}
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
            (cast (congrArg (MPOTensor D) (hdim j q))
              (blocks ((C).repr j))) v *
            (↑((X j q)⁻¹) : Matrix (Fin (dim ((C).enum j q)))
              (Fin (dim ((C).enum j q))) ℂ)) =
        (V ((C).enum j q))ᴴ * verticalTensor M v * V ((C).enum j q))
    (j : Fin (C).g) (q : Fin ((C).copies j)) :
    let A := cast (congrArg (MPOTensor D) (hdim j q))
      (blocks ((C).repr j))
    ∃ (W : Matrix (Fin d) (Fin (dim ((C).enum j q))) ℂ) (c0 : ℂ),
      (0 : ℂ) < c0 ∧ ∀ w, Wᴴ * verticalTensor M w * W = c0 • A w := by
  classical
  let q0 : Fin ((C).copies j) := ⟨0, (C).copies_pos j⟩
  let A := cast (congrArg (MPOTensor D) (hdim j q))
    (blocks ((C).repr j))
  let A0 := cast (congrArg (MPOTensor D) (hdim j q0))
    (blocks ((C).repr j))
  let h0q := (hdim j q0).symm.trans (hdim j q)
  let W := cast
    (congrArg (fun k ↦ Matrix (Fin d) (Fin k) ℂ) h0q)
    (V ((C).enum j q0))
  let c0 := μ ((C).repr j) * ζ j q0
  have hEnum0 : (C).enum j q0 = (C).repr j :=
    MPSTensor.mpvPhaseClassData_enum_zero_eq_repr blocks j
  have hc0 : (0 : ℂ) < c0 := by
    simpa [c0, q0, hEnum0] using hCoeffPos j q0
  have hcoeff0 : μ ((C).enum j q0) * ζ j q0 = c0 := by
    change μ ((C).enum j q0) * ζ j q0 = μ ((C).repr j) * ζ j q0
    rw [hEnum0]
  have hCorner0 : ∀ w,
      (V ((C).enum j q0))ᴴ * verticalTensor M w * V ((C).enum j q0) =
        c0 • A0 w := by
    intro w
    have h := (hCorner j q0 w).symm
    rw [hXDist j] at h
    rw [inv_one, Matrix.GeneralLinearGroup.coe_one,
      Matrix.one_mul, Matrix.mul_one] at h
    rw [hcoeff0] at h
    simpa [A0, q0] using h
  have hAtransport :
      cast (congrArg (MPOTensor D) h0q) A0 = A :=
    cast_cast _ _ _
  refine ⟨W, c0, hc0, ?_⟩
  intro w
  have h := vertical_corner_cast M A0 (V ((C).enum j q0))
    c0 hCorner0 h0q w
  simpa [W, hAtransport] using h

end GroupedSectors

end MPOTensor

end

section

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- Pairwise equality of Gram dressings for two positive vertical corners of a
common representative.

This is the exact canonical-form-specific input used by the grouped Figure 8
argument. Both literal CPSV canonical form and BNT-refined
horizontal form provide this statement independently.

Source: arXiv:1606.00608, proof of Proposition 4.13, Figures 7--8 and lines
1909--1919. -/
def HasGroupedCornerGramDressing (M : MPOTensor d D) : Prop :=
  ∀ {n : ℕ} (A : MPOTensor D n)
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
variable (blocks : (k : Fin r) → MPOTensor D (dim k))

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
            (cast (congrArg (MPOTensor D) (hdim j q))
              (blocks ((C).repr j))) v *
            (↑((X j q)⁻¹) : Matrix (Fin (dim ((C).enum j q)))
              (Fin (dim ((C).enum j q))) ℂ)) =
        (V ((C).enum j q))ᴴ * verticalTensor M v * V ((C).enum j q))
    (j : Fin (C).g) (q : Fin ((C).copies j))
    (v : Fin D × Fin D) :
    let A := cast (congrArg (MPOTensor D) (hdim j q))
      (blocks ((C).repr j))
    let G := (X j q : Matrix (Fin (dim ((C).enum j q)))
      (Fin (dim ((C).enum j q))) ℂ)ᴴ * X j q
    G * A v * G⁻¹ = A v := by
  classical
  let A := cast (congrArg (MPOTensor D) (hdim j q))
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
      (cast (congrArg (MPOTensor D) (hdim j q))
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
            (cast (congrArg (MPOTensor D) (hdim j q))
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
  let A := cast (congrArg (MPOTensor D) (hdim j q))
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

end

section

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

section GroupedSectors

variable {r : ℕ} {dim : Fin r → ℕ}
variable (blocks : (k : Fin r) → MPOTensor D (dim k))

local notation "C" => MPSTensor.mpvPhaseClassData blocks

/-- Every grouped vertical-sector gauge becomes unitary after division by the
square root of its positive Gram scalar.

The hypotheses are those of
`grouped_sector_gram_eq_pos_smul_one_of_dressing`: the grouped-corner Gram
dressing together with the clauses of `HasVerticalBNTGroupingWithIsometry`.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem grouped_sector_exists_unitary_normalization_of_dressing
    {M : MPOTensor d D} (hDressing : HasGroupedCornerGramDressing M)
    (μ : Fin r → ℂ) (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (hDimPos : ∀ k, 0 < dim k)
    (hdim : ∀ j q, dim ((C).repr j) = dim ((C).enum j q))
    (hNormal : ∀ j q, Kraus.IsNormal
      (cast (congrArg (MPOTensor D) (hdim j q))
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
            (cast (congrArg (MPOTensor D) (hdim j q))
              (blocks ((C).repr j))) v *
            (↑((X j q)⁻¹) : Matrix (Fin (dim ((C).enum j q)))
              (Fin (dim ((C).enum j q))) ℂ)) =
        (V ((C).enum j q))ᴴ * verticalTensor M v * V ((C).enum j q))
    (j : Fin (C).g) (q : Fin ((C).copies j)) :
    ∃ ω : ℝ, 0 < ω ∧
      (Real.sqrt ω : ℂ)⁻¹ •
          (X j q : Matrix (Fin (dim ((C).enum j q)))
            (Fin (dim ((C).enum j q))) ℂ) ∈
        Matrix.unitaryGroup (Fin (dim ((C).enum j q))) ℂ := by
  obtain ⟨ω, hω, hGram⟩ :=
    grouped_sector_gram_eq_pos_smul_one_of_dressing blocks hDressing μ V
      hDimPos hdim hNormal X ζ hXDist hCoeffPos hCorner j q
  exact ⟨ω, hω,
    Matrix.smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one
      hω hGram⟩

end GroupedSectors

end MPOTensor

end
