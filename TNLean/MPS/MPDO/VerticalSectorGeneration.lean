/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.SourceBNTBlocking
import TNLean.MPS.MPDO.VerticalSectorCoordinates

/-!
# Generation of vertical BNT sector algebras

The proof of the general MPDO renormalization fixed-point theorem uses the
fact that finite products of the weighted vertical bond contractions span the
full direct product of the BNT matrix algebras.  This file derives that claim
from simultaneous word-tuple span of the vertical BNT representatives.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 1980--1990.
-/

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace MPSTensor

/-- A matrix unit in the horizontal bond algebra selects the corresponding
letter of a vertically viewed tensor under bond contraction.

Source: arXiv:1606.00608, Appendix C.4, lines 1975--1984. -/
@[simp]
theorem contractBondMatrix_single_transpose
    {D n : ℕ} (A : MPSTensor (D * D) n) (a b : Fin D) :
    contractBondMatrix A (Matrix.single b a 1) =
      A (finProdFinEquiv (a, b)) := by
  rw [contractBondMatrix_apply, ← finProdFinEquiv.sum_comp]
  classical
  rw [Fintype.sum_eq_single (a, b)]
  · simp
  · intro x hx
    simp only [Matrix.single_apply, ite_smul, one_smul, zero_smul]
    rw [if_neg]
    intro h
    apply hx
    calc
      x = ((finProdFinEquiv x).divNat, (finProdFinEquiv x).modNat) := by
        apply finProdFinEquiv.injective
        exact (finProdFinEquiv.apply_symm_apply (finProdFinEquiv x)).symm
      _ = (a, b) := Prod.ext h.2.symm h.1.symm

/-- The preceding matrix-unit identity expressed directly in the encoded
product coordinate. -/
@[simp]
theorem contractBondMatrix_single_mod_div
    {D n : ℕ} (A : MPSTensor (D * D) n) (ab : Fin (D * D)) :
    contractBondMatrix A (Matrix.single ab.modNat ab.divNat 1) = A ab := by
  rw [contractBondMatrix_single_transpose]
  congr 1
  exact finProdFinEquiv.apply_symm_apply ab

end MPSTensor

namespace MPOTensor

/-- The direct-product sector operator whose `α`-th sector is the scalar
multiple $m_α M_α(X)$ obtained by contracting the common horizontal bond
matrix `X` into every vertical BNT representative.

Source: arXiv:1606.00608, Appendix C.4, lines 1975--1984. -/
def weightedVerticalBondContraction
    {g D : ℕ} {dim : Fin g → ℕ}
    (m : Fin g → ℂ)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (X : Matrix (Fin D) (Fin D) ℂ) : VerticalSectorAlgebra dim :=
  fun α => m α • MPSTensor.contractBondMatrix (A α) X

/-- A length-`L` product of weighted vertical bond contractions, with the
matrix product taken independently in every BNT sector.

Source: arXiv:1606.00608, Appendix C.4, lines 1980--1990. -/
def weightedVerticalBondContractionProduct
    {g D L : ℕ} {dim : Fin g → ℕ}
    (m : Fin g → ℂ)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (X : Fin L → Matrix (Fin D) (Fin D) ℂ) : VerticalSectorAlgebra dim :=
  fun α => (List.ofFn fun t => weightedVerticalBondContraction m A (X t) α).prod

/-- Length-`L` products of the weighted vertical bond contractions span the
full direct product of the BNT matrix algebras.

This is the equation `C_L(V) = 𝒜₁` in the proof of the general MPDO
renormalization fixed-point theorem.

Source: arXiv:1606.00608, Appendix C.4, lines 1980--1990. -/
def WeightedVerticalBondContractionProductSpanTop
    {g D : ℕ} {dim : Fin g → ℕ}
    (m : Fin g → ℂ)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (L : ℕ) : Prop :=
  Submodule.span ℂ
    (Set.range (weightedVerticalBondContractionProduct (L := L) m A)) = ⊤

/-- Sectorwise multiplication by nonzero scalars is a linear equivalence of
the direct product of the BNT matrix algebras. -/
def verticalSectorScaleEquiv
    {g : ℕ} {dim : Fin g → ℕ}
    (c : Fin g → ℂ) (hc : ∀ α, c α ≠ 0) :
    VerticalSectorAlgebra dim ≃ₗ[ℂ] VerticalSectorAlgebra dim where
  toFun X := fun α => c α • X α
  invFun X := fun α => (c α)⁻¹ • X α
  left_inv X := by
    funext α
    simp [smul_smul, hc α]
  right_inv X := by
    funext α
    simp [smul_smul, hc α]
  map_add' X Y := by
    funext α
    exact smul_add (c α) (X α) (Y α)
  map_smul' a X := by
    funext α
    change c α • (a • X α) = a • (c α • X α)
    rw [smul_smul, smul_smul, mul_comm]

/-- Products of weighted contractions against matrix units are the
corresponding simultaneous word tuples, scaled in sector $α$ by $m_α^L$.

Source: arXiv:1606.00608, Appendix C.4, lines 1980--1990. -/
theorem weightedVerticalBondContractionProduct_single
    {g D L : ℕ} {dim : Fin g → ℕ}
    (m : Fin g → ℂ)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (w : Fin L → Fin (D * D)) :
    weightedVerticalBondContractionProduct m A
        (fun t => Matrix.single (w t).modNat (w t).divNat 1) =
      fun α => (m α) ^ L • MPSTensor.wordTuple A L w α := by
  induction L with
  | zero =>
    funext α
    simp [weightedVerticalBondContractionProduct, MPSTensor.wordTuple]
  | succ L ih =>
    funext α
    have hih := congrFun (ih (w ∘ Fin.succ)) α
    simp only [weightedVerticalBondContractionProduct, Function.comp_apply] at hih
    simp only [weightedVerticalBondContractionProduct, List.ofFn_succ,
      List.prod_cons]
    rw [hih]
    simp only [weightedVerticalBondContraction,
      MPSTensor.contractBondMatrix_single_mod_div, MPSTensor.wordTuple]
    rw [List.ofFn_succ, MPSTensor.evalWord_cons]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp only [pow_succ]
    rw [mul_comm]
    simp only [Function.comp_def]

/-- A full simultaneous word-tuple span implies that length-`L` products of
the weighted vertical bond contractions span the full sector algebra, provided
that every sector weight is nonzero.

Source: arXiv:1606.00608, Appendix C.4, lines 1980--1990. -/
theorem weightedVerticalBondContractionProductSpanTop_of_wordTupleSpanTop
    {g D L : ℕ} {dim : Fin g → ℕ}
    (m : Fin g → ℂ)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (hm : ∀ α, m α ≠ 0)
    (hSpan : MPSTensor.WordTupleSpanTop A L) :
    WeightedVerticalBondContractionProductSpanTop m A L := by
  classical
  let e := verticalSectorScaleEquiv (dim := dim) (fun α => (m α) ^ L)
    (fun α => pow_ne_zero L (hm α))
  have hScaledSpan :
      Submodule.span ℂ
          (Set.range (fun w α => (m α) ^ L • MPSTensor.wordTuple A L w α)) =
        ⊤ := by
    change Submodule.span ℂ (Set.range (e ∘ MPSTensor.wordTuple A L)) = ⊤
    calc
      _ = (Submodule.span ℂ (Set.range (MPSTensor.wordTuple A L))).map
          e.toLinearMap := by
        simpa only [Set.range_comp, LinearEquiv.coe_coe] using
          (Submodule.map_span e.toLinearMap
            (Set.range (MPSTensor.wordTuple A L))).symm
      _ = ⊤ := by
        rw [hSpan, Submodule.map_top, LinearEquiv.range]
  unfold WeightedVerticalBondContractionProductSpanTop
  apply top_unique
  rw [← hScaledSpan]
  apply Submodule.span_mono
  rintro _ ⟨w, rfl⟩
  refine ⟨fun t => Matrix.single (w t).modNat (w t).divNat 1, ?_⟩
  exact weightedVerticalBondContractionProduct_single m A w

/-- If the length-`L` products of weighted vertical bond contractions span the
sector algebra, then a linear endomorphism fixing every such product is the
identity.

This isolates the final linear-spanning implication in the inverse-map argument.
It does not prove that fixed weighted contractions have fixed products.

**Scope restriction (fixed products):** Appendix C.4 does not assume that the
products are fixed.  It obtains the stronger identity conclusion from Wolf's
density-weighted fixed-point theorem.  Here fixedness of the products is an
explicit hypothesis.  The missing fixed-point argument is recorded in
`docs/paper-gaps/cpsv16_vertical_sector_invertibility.tex`.

Source: arXiv:1606.00608, Appendix C.4, lines 1980--1993. -/
theorem eq_id_of_weightedVerticalBondContractionProducts_fixed
    {g D L : ℕ} {dim : Fin g → ℕ}
    (m : Fin g → ℂ)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (F : VerticalSectorAlgebra dim →ₗ[ℂ] VerticalSectorAlgebra dim)
    (hSpan : WeightedVerticalBondContractionProductSpanTop m A L)
    (hFixed : ∀ X : Fin L → Matrix (Fin D) (Fin D) ℂ,
      F (weightedVerticalBondContractionProduct m A X) =
        weightedVerticalBondContractionProduct m A X) :
    F = LinearMap.id := by
  apply LinearMap.ext_on_range hSpan
  intro X
  simpa using hFixed X

/-- A CPSV basis of normal tensors, with nonzero sector weights, admits one
positive length at which the weighted vertical bond contractions generate the
full direct product of its matrix algebras.

Source: arXiv:1606.00608, BNT definition at lines 271--274 and Appendix C.4,
lines 1980--1990. -/
theorem exists_positive_weightedVerticalBondContractionProductSpanTop_of_bnt
    {g D E : ℕ} {dim : Fin g → ℕ}
    {A₀ : MPSTensor (D * D) E}
    {A : (α : Fin g) → MPSTensor (D * D) (dim α)}
    (hBNT : MPSTensor.IsCPSVBasisOfNormalTensors A₀
      (fun α => ⟨dim α, A α⟩))
    (m : Fin g → ℂ) (hm : ∀ α, m α ≠ 0) :
    ∃ L : ℕ, 0 < L ∧
      WeightedVerticalBondContractionProductSpanTop m A L := by
  obtain ⟨L, hL, hSpan⟩ := hBNT.exists_positive_wordTupleSpanTop
  exact ⟨L, hL,
    weightedVerticalBondContractionProductSpanTop_of_wordTupleSpanTop
      m A hm hSpan⟩

/-- For positive multiplicity weights, a vertical CPSV basis of normal
tensors admits one positive length at which its bond contractions generate the
full sector algebra.  The sector scalar is the trace of the corresponding
multiplicity matrix.

This is the claim `C_L(V) = 𝒜₁` used in the inverse-map argument for the
general MPDO renormalization fixed-point theorem.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1971 and 1980--1990. -/
theorem exists_positive_verticalMultiplicityTraceBondContractionProductSpanTop_of_bnt
    {g D E : ℕ} {dim mult : Fin g → ℕ}
    {A₀ : MPSTensor (D * D) E}
    {A : (α : Fin g) → MPSTensor (D * D) (dim α)}
    (hBNT : MPSTensor.IsCPSVBasisOfNormalTensors A₀
      (fun α => ⟨dim α, A α⟩))
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (hMult : ∀ α, 0 < mult α)
    (hWeight : ∀ α q, (0 : ℂ) < weight α q) :
    ∃ L : ℕ, 0 < L ∧
      WeightedVerticalBondContractionProductSpanTop
        (verticalMultiplicityTrace weight) A L := by
  apply exists_positive_weightedVerticalBondContractionProductSpanTop_of_bnt
    hBNT (verticalMultiplicityTrace weight)
  intro α
  exact verticalMultiplicityTrace_ne_zero α (hMult α) (hWeight α)

end MPOTensor
