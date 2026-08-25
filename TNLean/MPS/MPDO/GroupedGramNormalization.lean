/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVGroupedFigureEight
import TNLean.MPS.MPDO.GroupedFigure8

/-!
# Gram and unitary normalization of grouped vertical sectors

This file packages the grouped vertical-sector data shared by normalized
BNT-refined horizontal form and literal CPSV canonical form.  The two
canonical-form hypotheses supply the same grouped-corner Gram-dressing clause;
the subsequent Gram rigidity and unitary normalization are proved once.

## Main definitions

* `VerticalBNTGrouping`: the grouped-sector data needed for Gram normalization.
* `VerticalBNTGrouping.ofHorizontalCF`: the witness under normalized
  BNT-refined horizontal form.
* `VerticalBNTGrouping.ofCPSVCanonicalForm`: the witness under literal CPSV
  canonical form.

## Main results

* `VerticalBNTGrouping.gram_eq_pos_smul_one`
* `VerticalBNTGrouping.exists_unitary_normalization`
* `IsMPDO.grouped_sector_gram_eq_pos_smul_one`
* `MPSTensor.IsCPSVCanonicalForm.grouped_sector_gram_eq_pos_smul_one`

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1903--1921.
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- A concrete grouped vertical-sector family together with the
canonical-form-independent Gram-dressing property.

The fields are precisely the data used in the Gram-normalization step: the
normal block family, its phase-class gauges and coefficients, the physical
corner realizations, and the distinguished identity gauges.  The two smart
constructors below supply the final Gram-dressing field from the normalized
BNT-refined or literal CPSV canonical-form hypotheses, without relating those
two hypotheses.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
structure VerticalBNTGrouping (M : MPOTensor d D) where
  r : ℕ
  dim : Fin r → ℕ
  μ : Fin r → ℂ
  blocks : (k : Fin r) → MPSTensor (D * D) (dim k)
  V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ
  hDimPos : ∀ k, 0 < dim k
  hNormal : ∀ k, MPSTensor.IsNormalTensor (blocks k)
  hdim : ∀ j q,
    dim ((MPSTensor.mpvPhaseClassData blocks).repr j) =
      dim ((MPSTensor.mpvPhaseClassData blocks).enum j q)
  X : (j : Fin (MPSTensor.mpvPhaseClassData blocks).g) →
    (q : Fin ((MPSTensor.mpvPhaseClassData blocks).copies j)) →
      GL (Fin (dim ((MPSTensor.mpvPhaseClassData blocks).enum j q))) ℂ
  ζ : (j : Fin (MPSTensor.mpvPhaseClassData blocks).g) →
    Fin ((MPSTensor.mpvPhaseClassData blocks).copies j) → ℂ
  hXDist : ∀ j,
    X j ⟨0, (MPSTensor.mpvPhaseClassData blocks).copies_pos j⟩ = 1
  hCoeffPos : ∀ j q, (0 : ℂ) <
    μ ((MPSTensor.mpvPhaseClassData blocks).enum j q) * ζ j q
  hCorner : ∀ j q v,
    (μ ((MPSTensor.mpvPhaseClassData blocks).enum j q) * ζ j q) •
        ((X j q : Matrix
            (Fin (dim ((MPSTensor.mpvPhaseClassData blocks).enum j q)))
            (Fin (dim ((MPSTensor.mpvPhaseClassData blocks).enum j q))) ℂ) *
          (cast (congrArg (MPSTensor (D * D)) (hdim j q))
            (blocks ((MPSTensor.mpvPhaseClassData blocks).repr j))) v *
          (↑((X j q)⁻¹) : Matrix
            (Fin (dim ((MPSTensor.mpvPhaseClassData blocks).enum j q)))
            (Fin (dim ((MPSTensor.mpvPhaseClassData blocks).enum j q))) ℂ)) =
      (V ((MPSTensor.mpvPhaseClassData blocks).enum j q))ᴴ *
        verticalTensor M v *
          V ((MPSTensor.mpvPhaseClassData blocks).enum j q)
  hDressing : HasGroupedCornerGramDressing M

/-- The phase-class data of a bundled vertical grouping. -/
noncomputable abbrev VerticalBNTGrouping.classes
    {M : MPOTensor d D} (grouping : VerticalBNTGrouping M) :=
  MPSTensor.mpvPhaseClassData grouping.blocks

private theorem nonempty_verticalBNTGrouping_of_data
    (M : MPOTensor d D) (hGrouping : HasVerticalBNTGroupingWithIsometry M)
    (hDressing : HasGroupedCornerGramDressing M) :
    Nonempty (VerticalBNTGrouping M) := by
  classical
  obtain ⟨r, dim, μ, blocks, V, hDimPos, _, hNormal, _, _, _, _, _, _,
    hdim, X, ζ, _, _, hXDist, _, _, _, _, _, _, _, hCoeffPos, _, _, _, _,
    hCorner, _⟩ := hGrouping
  exact ⟨
    { r := r, dim := dim, μ := μ
      blocks := blocks, V := V
      hDimPos := hDimPos, hNormal := hNormal
      hdim := hdim, X := X, ζ := ζ
      hXDist := hXDist, hCoeffPos := hCoeffPos
      hCorner := hCorner, hDressing := hDressing }⟩

/-- Package grouped sectors under normalized BNT-refined horizontal form.

This constructor chooses the data furnished by
`IsHorizontalCF.exists_verticalBNTGrouping_with_isometry` and uses the
normalized-horizontal Figure 8 theorem to supply the Gram-dressing field.

**Scope restriction (BNT-refined horizontal form):** `IsHorizontalCF` is
stronger than the literal CPSV canonical form; see
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
noncomputable def VerticalBNTGrouping.ofHorizontalCF
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    VerticalBNTGrouping M :=
  Classical.choice <| nonempty_verticalBNTGrouping_of_data M
    (hHorizontal.exists_verticalBNTGrouping_with_isometry M hM) <| by
      intro n A VX VY X' Y cX cY hcX hcY hcornerX hcornerY
      exact hHorizontal.gramDressing_eq_of_two_grouped_corners M hM
        A VX VY X' Y cX cY hcX hcY hcornerX hcornerY

/-- Package grouped sectors under literal CPSV canonical form.

This constructor chooses the data furnished by
`MPSTensor.IsCPSVCanonicalForm.exists_verticalBNTGrouping_with_isometry` and
uses the literal Figure 8 theorem to supply the Gram-dressing field.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
noncomputable def VerticalBNTGrouping.ofCPSVCanonicalForm
    (M : MPOTensor d D)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor) (hM : IsMPDO M) :
    VerticalBNTGrouping M :=
  Classical.choice <| nonempty_verticalBNTGrouping_of_data M
    (hCanonical.exists_verticalBNTGrouping_with_isometry M hM) <| by
      intro n A VX VY X' Y cX cY hcX hcY hcornerX hcornerY
      exact hCanonical.gramDressing_eq_of_two_grouped_corners M hM
        A VX VY X' Y cX cY hcX hcY hcornerX hcornerY

/-- The Gram matrix of every gauge in a bundled vertical grouping is a
positive real multiple of the identity.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem VerticalBNTGrouping.gram_eq_pos_smul_one
    {M : MPOTensor d D} (grouping : VerticalBNTGrouping M)
    (j : Fin grouping.classes.g) (q : Fin (grouping.classes.copies j)) :
    ∃ ω : ℝ, 0 < ω ∧
      (grouping.X j q : Matrix
          (Fin (grouping.dim (grouping.classes.enum j q)))
          (Fin (grouping.dim (grouping.classes.enum j q))) ℂ)ᴴ *
        grouping.X j q = (ω : ℂ) • 1 := by
  apply grouped_sector_gram_eq_pos_smul_one_of_dressing grouping.blocks
    (M := M) (μ := grouping.μ) (V := grouping.V)
      (_hDimPos := grouping.hDimPos) (hdim := grouping.hdim)
      (X := grouping.X) (ζ := grouping.ζ) (hXDist := grouping.hXDist)
      (hCoeffPos := grouping.hCoeffPos) (hCorner := grouping.hCorner)
  · exact grouping.hDressing
  · intro l p
    exact ((MPSTensor.isNormalTensor_cast_iff (grouping.hdim l p)
      (grouping.blocks (grouping.classes.repr l))).2
        (grouping.hNormal (grouping.classes.repr l))).isNormal

/-- Every gauge in a bundled vertical grouping becomes unitary after division
by the square root of its positive Gram scalar.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem VerticalBNTGrouping.exists_unitary_normalization
    {M : MPOTensor d D} (grouping : VerticalBNTGrouping M)
    (j : Fin grouping.classes.g) (q : Fin (grouping.classes.copies j)) :
    ∃ ω : ℝ, 0 < ω ∧
      ((Real.sqrt ω : ℂ))⁻¹ •
          (grouping.X j q : Matrix
            (Fin (grouping.dim (grouping.classes.enum j q)))
            (Fin (grouping.dim (grouping.classes.enum j q))) ℂ) ∈
        Matrix.unitaryGroup
          (Fin (grouping.dim (grouping.classes.enum j q))) ℂ := by
  obtain ⟨ω, hω, hGram⟩ := grouping.gram_eq_pos_smul_one j q
  exact ⟨ω, hω,
    Matrix.smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one
      hω hGram⟩

section SourceFacingHorizontal

variable {r : ℕ} {dim : Fin r → ℕ}
variable (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))

local notation "C" => MPSTensor.mpvPhaseClassData blocks

/-- The Gram matrix of an actual grouped vertical-sector gauge is a positive
real multiple of the identity.

All hypotheses are clauses furnished by
`IsHorizontalCF.exists_verticalBNTGrouping_with_isometry`.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem IsMPDO.grouped_sector_gram_eq_pos_smul_one
    {M : MPOTensor d D} (hM : IsMPDO M)
    (hHorizontal : IsHorizontalCF M)
    (μ : Fin r → ℂ) (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (_hDimPos : ∀ k, 0 < dim k)
    (hNormal : ∀ k, MPSTensor.IsNormalTensor (blocks k))
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
    (j : Fin (C).g) (q : Fin ((C).copies j)) :
    ∃ ω : ℝ, 0 < ω ∧
      (X j q : Matrix (Fin (dim ((C).enum j q)))
        (Fin (dim ((C).enum j q))) ℂ)ᴴ * X j q = (ω : ℂ) • 1 := by
  let grouping : VerticalBNTGrouping M :=
    { r := r, dim := dim, μ := μ
      blocks := blocks, V := V
      hDimPos := _hDimPos, hNormal := hNormal
      hdim := hdim, X := X, ζ := ζ
      hXDist := hXDist, hCoeffPos := hCoeffPos
      hCorner := hCorner
      hDressing := by
        intro n A VX VY X' Y cX cY hcX hcY hcornerX hcornerY
        exact hHorizontal.gramDressing_eq_of_two_grouped_corners M hM
          A VX VY X' Y cX cY hcX hcY hcornerX hcornerY }
  exact grouping.gram_eq_pos_smul_one j q

/-- Every actual grouped vertical-sector gauge becomes unitary after division
by the square root of its positive Gram scalar.

All hypotheses are clauses furnished by
`IsHorizontalCF.exists_verticalBNTGrouping_with_isometry`.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem IsMPDO.grouped_sector_exists_unitary_normalization
    {M : MPOTensor d D} (hM : IsMPDO M)
    (hHorizontal : IsHorizontalCF M)
    (μ : Fin r → ℂ) (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (hDimPos : ∀ k, 0 < dim k)
    (hNormal : ∀ k, MPSTensor.IsNormalTensor (blocks k))
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
    (j : Fin (C).g) (q : Fin ((C).copies j)) :
    ∃ ω : ℝ, 0 < ω ∧
      ((Real.sqrt ω : ℂ))⁻¹ •
          (X j q : Matrix (Fin (dim ((C).enum j q)))
            (Fin (dim ((C).enum j q))) ℂ) ∈
        Matrix.unitaryGroup (Fin (dim ((C).enum j q))) ℂ := by
  obtain ⟨ω, hω, hGram⟩ :=
    hM.grouped_sector_gram_eq_pos_smul_one blocks hHorizontal μ V
      hDimPos hNormal hdim X ζ hXDist hCoeffPos hCorner j q
  exact ⟨ω, hω,
    Matrix.smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one
      hω hGram⟩

end SourceFacingHorizontal

end MPOTensor

open MPOTensor

namespace MPSTensor.IsCPSVCanonicalForm

variable {d D : ℕ}
variable {r : ℕ} {dim : Fin r → ℕ}
variable (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))

local notation "C" => MPSTensor.mpvPhaseClassData blocks

/-- The Gram matrix of an actual grouped vertical-sector gauge is a positive
real multiple of the identity.

All hypotheses after `hM` are clauses furnished by
`IsCPSVCanonicalForm.exists_verticalBNTGrouping_with_isometry`.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem grouped_sector_gram_eq_pos_smul_one
    {M : MPOTensor d D} (hCanonical : IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M)
    (μ : Fin r → ℂ) (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (_hDimPos : ∀ k, 0 < dim k)
    (hNormal : ∀ k, MPSTensor.IsNormalTensor (blocks k))
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
    (j : Fin (C).g) (q : Fin ((C).copies j)) :
    ∃ ω : ℝ, 0 < ω ∧
      (X j q : Matrix (Fin (dim ((C).enum j q)))
        (Fin (dim ((C).enum j q))) ℂ)ᴴ * X j q = (ω : ℂ) • 1 := by
  let grouping : VerticalBNTGrouping M :=
    { r := r, dim := dim, μ := μ
      blocks := blocks, V := V
      hDimPos := _hDimPos, hNormal := hNormal
      hdim := hdim, X := X, ζ := ζ
      hXDist := hXDist, hCoeffPos := hCoeffPos
      hCorner := hCorner
      hDressing := by
        intro n A VX VY X' Y cX cY hcX hcY hcornerX hcornerY
        exact hCanonical.gramDressing_eq_of_two_grouped_corners M hM
          A VX VY X' Y cX cY hcX hcY hcornerX hcornerY }
  exact grouping.gram_eq_pos_smul_one j q

/-- Every actual grouped vertical-sector gauge becomes unitary after division
by the square root of its positive Gram scalar.

All hypotheses after `hM` are clauses furnished by
`IsCPSVCanonicalForm.exists_verticalBNTGrouping_with_isometry`.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem grouped_sector_exists_unitary_normalization
    {M : MPOTensor d D} (hCanonical : IsCPSVCanonicalForm M.toMPSTensor)
    (hM : IsMPDO M)
    (μ : Fin r → ℂ) (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (hDimPos : ∀ k, 0 < dim k)
    (hNormal : ∀ k, MPSTensor.IsNormalTensor (blocks k))
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
    (j : Fin (C).g) (q : Fin ((C).copies j)) :
    ∃ ω : ℝ, 0 < ω ∧
      ((Real.sqrt ω : ℂ))⁻¹ •
          (X j q : Matrix (Fin (dim ((C).enum j q)))
            (Fin (dim ((C).enum j q))) ℂ) ∈
        Matrix.unitaryGroup (Fin (dim ((C).enum j q))) ℂ := by
  obtain ⟨ω, hω, hGram⟩ :=
    hCanonical.grouped_sector_gram_eq_pos_smul_one blocks hM μ V
      hDimPos hNormal hdim X ζ hXDist hCoeffPos hCorner j q
  exact ⟨ω, hω,
    Matrix.smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one
      hω hGram⟩

end MPSTensor.IsCPSVCanonicalForm
