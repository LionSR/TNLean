/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.KitaevNativeBoundaryCNOT
import TNLean.Algebra.ComplexSqrt
import Mathlib.Tactic.Abel

/-!
# Physical support reduction of the actual checkerboard block

Source: SCP10, arXiv:1001.3807, lines 2760–2827, including the footnote on
physical implementation on the support. All normalizations are derived from
the actual color-difference coefficients.

**Scope restriction (one locally oriented block):** The tensor-map identities
apply to one actual translated four-site block. They do not yet assert a globally
tiled renormalization. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

/-- The retained three physical bits after extracting even parity. Source: SCP10,
lines 2809–2827; explicit support coordinates for the physical RG footnote. -/
abbrev KitaevReducedSpins := Fin 3 → KitaevBit

private def physicalParity (σ : KitaevBlockSpins) : KitaevBlockSpins :=
  ![σ 0, σ 1, σ 2, σ 0 + σ 1 + σ 2 + σ 3]

private theorem physicalParity_involutive : Function.Involutive physicalParity := by
  intro σ
  funext i
  fin_cases i <;> simp [physicalParity]
  abel_nf
  simp [show (2 : KitaevBit) = 0 by decide]

/-- A full four-spin physical unitary extracts the parity into the last spin.
Source: SCP10, physical RG footnote in lines 2780–2794. -/
def kitaevPhysicalParity : Equiv.Perm KitaevBlockSpins :=
  { toFun := physicalParity
    invFun := physicalParity
    left_inv := physicalParity_involutive
    right_inv := physicalParity_involutive }

/-- The physical parity transformation is unitary on the entire four-spin space.
Source: SCP10, physical RG footnote in lines 2780–2794. -/
theorem kitaevPhysicalParity_permMatrix_mem_unitaryGroup :
    kitaevPhysicalParity.permMatrix ℂ ∈ Matrix.unitaryGroup KitaevBlockSpins ℂ :=
  kitaevPhysicalParity.permMatrix_mem_unitaryGroup

/-- The isometric inclusion fixes the extracted physical parity spin at zero.
Source: SCP10, lines 2780–2827, physical support of the color-difference tensor. -/
def kitaevPhysicalZeroEmbedding : KitaevReducedSpins ↪ KitaevBlockSpins where
  toFun σ := ![σ 0, σ 1, σ 2, 0]
  inj' := by
    intro σ τ h
    funext i
    fin_cases i
    · simpa using congrFun h 0
    · simpa using congrFun h 1
    · simpa using congrFun h 2

/-- Fixing the last physical spin at zero is an isometry. Source: SCP10,
lines 2780–2827, physical support of the color-difference tensor. -/
theorem kitaevPhysicalZeroEmbedding_isIsometry :
    Matrix.IsIsometry (endpointEmbeddingMatrix kitaevPhysicalZeroEmbedding) :=
  endpointEmbeddingMatrix_isIsometry kitaevPhysicalZeroEmbedding

/-- The three independent adjacent color differences. Source: SCP10,
`eq:ex:kitaev-colordiff-rep`, lines 2809–2827. -/
def kitaevReducedColorSpins (p : Fin 4 → KitaevBit) : KitaevReducedSpins :=
  ![p 0 + p 1, p 1 + p 2, p 2 + p 3]

private theorem parity_color (p : Fin 4 → KitaevBit) :
    kitaevPhysicalParity (kitaevBlockColorSpins p) =
      kitaevPhysicalZeroEmbedding (kitaevReducedColorSpins p) := by
  change physicalParity (kitaevBlockColorSpins p) =
    ![(kitaevReducedColorSpins p) 0, (kitaevReducedColorSpins p) 1,
      (kitaevReducedColorSpins p) 2, 0]
  funext i
  fin_cases i <;> simp [physicalParity, kitaevBlockColorSpins, kitaevReducedColorSpins]
  abel_nf
  simp [show (2 : KitaevBit) = 0 by decide]

/-- The retained tensor after the physical parity spin is removed. Source: SCP10,
lines 2780–2827; the tensor is defined by its actual color differences. -/
def kitaevReducedColorMatrix : Matrix KitaevReducedSpins (Fin 4 → KitaevBit) ℂ :=
  fun σ p => if σ = kitaevReducedColorSpins p then 1 else 0

/-- The original four physical spins are reduced by an explicit physical unitary,
with an isometric zero-spin inclusion and no assumed tensor equality. Source:
SCP10, physical RG footnote and color-difference tensor, lines 2780–2827. -/
theorem kitaevPhysicalParity_mul_colorMatrix :
    kitaevPhysicalParity.permMatrix ℂ * kitaevBlockColorMatrix =
      endpointEmbeddingMatrix kitaevPhysicalZeroEmbedding * kitaevReducedColorMatrix := by
  ext σ p
  change (kitaevPhysicalParity.permMatrix ℂ *ᵥ
    (fun τ => kitaevBlockColorMatrix τ p)) σ = _
  rw [Matrix.permMatrix_mulVec]
  have he : kitaevPhysicalParity σ = kitaevBlockColorSpins p ↔
      σ = kitaevPhysicalZeroEmbedding (kitaevReducedColorSpins p) := by
    rw [← parity_color p]
    change physicalParity σ = kitaevBlockColorSpins p ↔
      σ = physicalParity (kitaevBlockColorSpins p)
    constructor
    · intro h
      have hh := congrArg physicalParity h
      exact (physicalParity_involutive σ).symm.trans hh
    · intro h
      rw [h, physicalParity_involutive]
  simp [kitaevBlockColorMatrix, he, Matrix.mul_apply, endpointEmbeddingMatrix,
    kitaevReducedColorMatrix]

private def reconstructColors (s : KitaevReducedSpins) (t : KitaevBit) :
    Fin 4 → KitaevBit := ![t, t + s 0, t + s 0 + s 1, t + s 0 + s 1 + s 2]

private theorem differences_reconstruct (s : KitaevReducedSpins) (t : KitaevBit) :
    kitaevReducedColorSpins (reconstructColors s t) = s := by
  funext i
  fin_cases i <;> simp [kitaevReducedColorSpins, reconstructColors] <;>
    abel_nf <;> simp [show (2 : KitaevBit) = 0 by decide]

private theorem reconstruct_differences (p : Fin 4 → KitaevBit) :
    reconstructColors (kitaevReducedColorSpins p) (p 0) = p := by
  funext i
  fin_cases i <;> simp [kitaevReducedColorSpins, reconstructColors] <;>
    abel_nf <;> simp [show (2 : KitaevBit) = 0 by decide]

/-- Four colors are equivalent to their three adjacent differences and one common
color. Source: SCP10, `eq:ex:kitaev-colordiff-rep`, lines 2809–2827. -/
def kitaevColorSupportEquiv : (Fin 4 → KitaevBit) ≃ KitaevReducedSpins × KitaevBit where
  toFun p := (kitaevReducedColorSpins p, p 0)
  invFun st := reconstructColors st.1 st.2
  left_inv := reconstruct_differences
  right_inv := by
    intro st
    exact Prod.ext (differences_reconstruct st.1 st.2) rfl

/-- Every retained physical word has precisely two color preimages. Thus the raw
color tensor has squared singular value two. Source: SCP10, lines 2780–2827,
physical support and global binary color symmetry. -/
theorem kitaevReducedColorMatrix_mul_conjTranspose :
    kitaevReducedColorMatrix * kitaevReducedColorMatrixᴴ = (2 : ℂ) • 1 := by
  ext s t
  rw [Matrix.mul_apply]
  rw [← kitaevColorSupportEquiv.symm.sum_comp]
  simp [kitaevReducedColorMatrix, kitaevColorSupportEquiv, differences_reconstruct,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.one_apply]
  by_cases h : s = t <;> simp [h, KitaevBit]

/-- The uniform common-color embedding, with the derived normalization 1/√2.
Source: SCP10, physical RG footnote and color symmetry, lines 2780–2827. -/
def kitaevColorSupportIsometry : Matrix (Fin 4 → KitaevBit) KitaevReducedSpins ℂ :=
  Complex.invSqrtTwo • kitaevReducedColorMatrixᴴ

/-- The uniform color-orbit embedding is isometric, as follows from the actual
coefficient count. Source: SCP10, physical RG footnote, lines 2780–2794. -/
theorem kitaevColorSupportIsometry_isIsometry :
    Matrix.IsIsometry kitaevColorSupportIsometry := by
  change kitaevColorSupportIsometryᴴ * kitaevColorSupportIsometry = 1
  simp only [kitaevColorSupportIsometry, Matrix.conjTranspose_smul,
    Complex.star_invSqrtTwo, Matrix.conjTranspose_conjTranspose,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    kitaevReducedColorMatrix_mul_conjTranspose]
  rw [← mul_assoc, Complex.invSqrtTwo_mul_self]
  norm_num

section Native
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance kitaevSupportWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance kitaevSupportHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "TV" => TorusVertex width height
private abbrev Physical (v : TV) :=
  {w : TV // w ∈ torusPlaquetteRegion v} → KitaevBit
private abbrev Boundary (v : TV) :=
  {e : Edge (torusGraph width height) //
    IsRegionBoundaryEdge (torusPlaquetteRegion v) e} → KitaevBit

/-- The original four spins of the actual translated block, in clockwise order.
Source: SCP10, lines 2755–2827, original physical spins of the blocking diagram. -/
def kitaevNativePhysicalEquiv (v : TV) : Physical v ≃ KitaevBlockSpins :=
  (kitaevNativeBlockVertexEquiv v).symm.arrowCongr (Equiv.refl KitaevBit)

/-- The physical parity unitary on the original spins of the actual torus block.
Source: SCP10, physical RG footnote in lines 2780–2794. -/
def kitaevNativePhysicalParity (v : TV) : Equiv.Perm (Physical v) :=
  ((kitaevNativePhysicalEquiv v).trans kitaevPhysicalParity).trans
    (kitaevNativePhysicalEquiv v).symm

/-- The native parity operation is unitary on the full original four-spin space.
Source: SCP10, physical RG footnote in lines 2780–2794. -/
theorem kitaevNativePhysicalParity_permMatrix_mem_unitaryGroup (v : TV) :
    (kitaevNativePhysicalParity v).permMatrix ℂ ∈ Matrix.unitaryGroup (Physical v) ℂ :=
  (kitaevNativePhysicalParity v).permMatrix_mem_unitaryGroup

/-- The actual physical support inclusion fixes the extracted parity spin at zero.
Source: SCP10, physical support of the RG step, lines 2780–2827. -/
def kitaevNativePhysicalZeroEmbedding (v : TV) : KitaevReducedSpins ↪ Physical v :=
  { toFun := fun s => (kitaevNativePhysicalEquiv v).symm (kitaevPhysicalZeroEmbedding s)
    inj' := (kitaevNativePhysicalEquiv v).symm.injective.comp
      kitaevPhysicalZeroEmbedding.injective }

/-- The physical support inclusion is an isometry into the original spins.
Source: SCP10, physical RG footnote in lines 2780–2794. -/
theorem kitaevNativePhysicalZeroEmbedding_isIsometry (v : TV) :
    Matrix.IsIsometry (endpointEmbeddingMatrix (kitaevNativePhysicalZeroEmbedding v)) :=
  endpointEmbeddingMatrix_isIsometry (kitaevNativePhysicalZeroEmbedding v)

private theorem native_physical_color (v : TV) :
    (kitaevNativePhysicalParity v).permMatrix ℂ * kitaevNativeColorMatrix v =
      endpointEmbeddingMatrix (kitaevNativePhysicalZeroEmbedding v) *
        kitaevReducedColorMatrix := by
  let r := kitaevNativePhysicalEquiv v
  have hP : (kitaevNativePhysicalParity v).permMatrix ℂ =
      (kitaevPhysicalParity.permMatrix ℂ).submatrix r r := by
    ext σ τ
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      kitaevNativePhysicalParity, Equiv.symm_apply_eq, r]
  have hE : endpointEmbeddingMatrix (kitaevNativePhysicalZeroEmbedding v) =
      (endpointEmbeddingMatrix kitaevPhysicalZeroEmbedding).submatrix r id := by
    ext σ s
    simp [endpointEmbeddingMatrix, kitaevNativePhysicalZeroEmbedding,
      Equiv.eq_symm_apply, r]
  have hK : kitaevNativeColorMatrix v = kitaevBlockColorMatrix.submatrix r id := rfl
  rw [hP, hK, Matrix.submatrix_mul_equiv, kitaevPhysicalParity_mul_colorMatrix, hE]
  exact Matrix.submatrix_mul_equiv
    (endpointEmbeddingMatrix kitaevPhysicalZeroEmbedding) kitaevReducedColorMatrix
      r (Equiv.refl KitaevReducedSpins) (Equiv.refl (Fin 4 → KitaevBit))

/-- An explicit full physical unitary and the actual boundary CNOT reduce the
native four-site tensor to three physical bits with a zero parity spin and four
retained boundary colors with four zero registers. Source: SCP10, physical RG
footnote and color-difference tensor, lines 2780–2827. No coefficient or Gram
identity is a hypothesis. -/
theorem kitaevNativePhysicalParity_mul_checkerboard_boundaryCNOT (v : TV) :
    (kitaevNativePhysicalParity v).permMatrix ℂ *
        kitaevNativeCheckerboardMatrix v * (kitaevNativeBoundaryCNOT v).permMatrix ℂ =
      endpointEmbeddingMatrix (kitaevNativePhysicalZeroEmbedding v) *
        kitaevReducedColorMatrix *
          (endpointEmbeddingMatrix (kitaevNativeBoundaryZeroEmbedding v))ᴴ := by
  rw [Matrix.mul_assoc, kitaevNativeCheckerboardMatrix_mul_boundaryCNOT,
    ← Matrix.mul_assoc, native_physical_color]

/-- The normalized support of the transformed boundary tensor, including both
its common-color orbit and its four zero registers. Source: SCP10, physical RG
footnote, lines 2780–2794. -/
def kitaevNativeTransformedSupport (v : TV) :
    Matrix (Boundary v) KitaevReducedSpins ℂ :=
  endpointEmbeddingMatrix (kitaevNativeBoundaryZeroEmbedding v) * kitaevColorSupportIsometry

/-- The derived transformed virtual support is isometric. Source: SCP10,
physical RG footnote, lines 2780–2794. -/
theorem kitaevNativeTransformedSupport_isIsometry (v : TV) :
    Matrix.IsIsometry (kitaevNativeTransformedSupport v) := by
  change (endpointEmbeddingMatrix (kitaevNativeBoundaryZeroEmbedding v) *
    kitaevColorSupportIsometry)ᴴ *
      (endpointEmbeddingMatrix (kitaevNativeBoundaryZeroEmbedding v) *
        kitaevColorSupportIsometry) = 1
  have hE : (endpointEmbeddingMatrix (kitaevNativeBoundaryZeroEmbedding v))ᴴ *
      endpointEmbeddingMatrix (kitaevNativeBoundaryZeroEmbedding v) = 1 :=
    kitaevNativeBoundaryZeroEmbedding_isIsometry v
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (endpointEmbeddingMatrix (kitaevNativeBoundaryZeroEmbedding v))ᴴ,
    hE, Matrix.one_mul]
  exact kitaevColorSupportIsometry_isIsometry

/-- The raw native tensor has a single scalar normalization √2 on its support;
after division by √2 it identifies the derived virtual support with the original
physical support by an isometry. Source: SCP10, physical RG footnote,
lines 2780–2794. -/
theorem kitaevNativePhysicalParity_mul_checkerboard_support (v : TV) :
    (Complex.invSqrtTwo • ((kitaevNativePhysicalParity v).permMatrix ℂ *
      kitaevNativeCheckerboardMatrix v * (kitaevNativeBoundaryCNOT v).permMatrix ℂ)) *
        kitaevNativeTransformedSupport v =
      endpointEmbeddingMatrix (kitaevNativePhysicalZeroEmbedding v) := by
  rw [kitaevNativePhysicalParity_mul_checkerboard_boundaryCNOT]
  have hE : (endpointEmbeddingMatrix (kitaevNativeBoundaryZeroEmbedding v))ᴴ *
      endpointEmbeddingMatrix (kitaevNativeBoundaryZeroEmbedding v) = 1 :=
    kitaevNativeBoundaryZeroEmbedding_isIsometry v
  simp only [kitaevNativeTransformedSupport, Matrix.smul_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (endpointEmbeddingMatrix (kitaevNativeBoundaryZeroEmbedding v))ᴴ, hE]
  simp only [Matrix.one_mul, kitaevColorSupportIsometry, Matrix.mul_smul,
    kitaevReducedColorMatrix_mul_conjTranspose, Matrix.mul_one, smul_smul]
  rw [← mul_assoc, Complex.invSqrtTwo_mul_self]
  norm_num
/-- The normalized actual blocked tensor factors between two derived isometric
support inclusions. Source: SCP10, physical RG footnote, lines 2780–2794.
In particular the normalization is derived, rather than assumed. -/
theorem kitaevNativePhysicalParity_mul_checkerboard_supportFactorization (v : TV) :
    Complex.invSqrtTwo • ((kitaevNativePhysicalParity v).permMatrix ℂ *
      kitaevNativeCheckerboardMatrix v * (kitaevNativeBoundaryCNOT v).permMatrix ℂ) =
      endpointEmbeddingMatrix (kitaevNativePhysicalZeroEmbedding v) *
        (kitaevNativeTransformedSupport v)ᴴ := by
  rw [kitaevNativePhysicalParity_mul_checkerboard_boundaryCNOT]
  simp only [kitaevNativeTransformedSupport, kitaevColorSupportIsometry,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
    Complex.star_invSqrtTwo, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_smul, Matrix.mul_assoc]

/-- The Gram matrix of the normalized actual tensor is exactly its derived
virtual support projection. Source: SCP10, physical RG footnote, lines 2780–2794. -/
theorem kitaevNativeCheckerboard_transformed_initialProjection (v : TV) :
    let T := Complex.invSqrtTwo • ((kitaevNativePhysicalParity v).permMatrix ℂ *
      kitaevNativeCheckerboardMatrix v * (kitaevNativeBoundaryCNOT v).permMatrix ℂ)
    Tᴴ * T = kitaevNativeTransformedSupport v * (kitaevNativeTransformedSupport v)ᴴ := by
  dsimp only
  rw [kitaevNativePhysicalParity_mul_checkerboard_supportFactorization]
  have hE : (endpointEmbeddingMatrix (kitaevNativePhysicalZeroEmbedding v))ᴴ *
      endpointEmbeddingMatrix (kitaevNativePhysicalZeroEmbedding v) = 1 :=
    kitaevNativePhysicalZeroEmbedding_isIsometry v
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, ← Matrix.mul_assoc (endpointEmbeddingMatrix
      (kitaevNativePhysicalZeroEmbedding v))ᴴ, hE, Matrix.one_mul]

/-- The output support is the isometric image of the three retained physical
bits, with the fourth spin fixed at zero. Source: SCP10, physical RG footnote
and the even-parity constraint, lines 2780–2827. -/
theorem kitaevNativeCheckerboard_transformed_finalProjection (v : TV) :
    let T := Complex.invSqrtTwo • ((kitaevNativePhysicalParity v).permMatrix ℂ *
      kitaevNativeCheckerboardMatrix v * (kitaevNativeBoundaryCNOT v).permMatrix ℂ)
    T * Tᴴ = endpointEmbeddingMatrix (kitaevNativePhysicalZeroEmbedding v) *
      (endpointEmbeddingMatrix (kitaevNativePhysicalZeroEmbedding v))ᴴ := by
  dsimp only
  rw [kitaevNativePhysicalParity_mul_checkerboard_supportFactorization]
  have hJ : (kitaevNativeTransformedSupport v)ᴴ *
      kitaevNativeTransformedSupport v = 1 := kitaevNativeTransformedSupport_isIsometry v
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, ← Matrix.mul_assoc (kitaevNativeTransformedSupport v)ᴴ,
    hJ, Matrix.one_mul]

end Native

end TNLean.PEPS
