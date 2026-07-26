/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.SourceBNTBlocking
import TNLean.MPS.MPDO.VerticalSectorCoordinates
import TNLean.MPS.MPDO.VerticalSectorFixedPointProductSpan

/-!
# Generation of vertical BNT sector algebras

The proof of the general MPDO renormalization fixed-point theorem uses the
fact that finite products of the weighted vertical bond contractions span the
full direct product of the BNT matrix algebras.  This file derives that claim
from simultaneous word-tuple span of the vertical BNT representatives.  It also
packages the shared algebraic and analytic hypotheses for the subsequent
positivity, identity, and trace-preservation results.

## Main declarations

* `MPOTensor.VerticalSectorHypotheses`: the common vertical-sector assumptions.
* `MPOTensor.exists_vertical_weightedProduct_span_eq_top`: generation of the
  full product algebra.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 1980--1993.
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

/-- The full vertical-sector hypotheses used in the analytic argument of
Appendix C.4.

They extend the algebraic fixed-generator context by the normal-tensor,
coisometry, and channel assumptions needed for positivity, trace
preservation, and the trace-adjoint Schwarz inequalities.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1995. -/
structure VerticalSectorHypotheses {g₁ g₂ d D : ℕ} : Type
    extends VerticalSectorFixedGeneratorHypotheses (g₁ := g₁) (g₂ := g₂) (d := d) (D := D) where
  /-- The one-site vertical tensors form a basis of normal tensors.

  Source: arXiv:1606.00608, Appendix C.4, lines 1980--1995. -/
  hBNT₁ : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor M)
    (fun α ↦ ⟨dim₁ α, A₁ α⟩)
  /-- The two-site vertical tensors form a basis of normal tensors.

  Source: arXiv:1606.00608, Appendix C.4, lines 1980--1995. -/
  hBNT₂ : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor (blockTwo M))
    (fun β ↦ ⟨dim₂ β, A₂ β⟩)
  /-- The one-site retained coordinate map is a coisometry.

  Source: arXiv:1606.00608, Appendix C.4, lines 1955--1971. -/
  hU₁ : U₁ * U₁ᴴ = 1
  /-- The two-site retained coordinate map is a coisometry.

  Source: arXiv:1606.00608, Appendix C.4, lines 1955--1971. -/
  hU₂ : U₂ * U₂ᴴ = 1
  /-- The physical refinement map is completely positive and trace preserving.

  Source: arXiv:1606.00608, Definition 4.1 and Appendix C.4, lines 1972--1979. -/
  hTCPTP : IsKrausCPTP T
  /-- The physical coarse-graining map is completely positive and trace preserving.

  Source: arXiv:1606.00608, Definition 4.1 and Appendix C.4, lines 1972--1979. -/
  hSCPTP : IsKrausCPTP S

namespace VerticalSectorHypotheses

/-- The transported vertical-sector refinement map determined by the strong
Appendix C.4 hypotheses.

Source: arXiv:1606.00608, Appendix C.4, lines 1972--1979. -/
abbrev Tbar {g₁ g₂ d D : ℕ} (h : VerticalSectorHypotheses
    (g₁ := g₁) (g₂ := g₂) (d := d) (D := D)) :=
  h.toVerticalSectorFixedGeneratorHypotheses.Tbar

/-- The transported vertical-sector coarse-graining map determined by the
strong Appendix C.4 hypotheses.

Source: arXiv:1606.00608, Appendix C.4, lines 1972--1979. -/
abbrev Sbar {g₁ g₂ d D : ℕ} (h : VerticalSectorHypotheses
    (g₁ := g₁) (g₂ := g₂) (d := d) (D := D)) :=
  h.toVerticalSectorFixedGeneratorHypotheses.Sbar

/-- The coarse-graining--refinement composite determined by the strong
Appendix C.4 hypotheses.

Source: arXiv:1606.00608, Appendix C.4, lines 1974--1980. -/
abbrev SbarTbar {g₁ g₂ d D : ℕ} (h : VerticalSectorHypotheses
    (g₁ := g₁) (g₂ := g₂) (d := d) (D := D)) :=
  h.toVerticalSectorFixedGeneratorHypotheses.SbarTbar

/-- The refinement--coarse-graining composite determined by the strong
Appendix C.4 hypotheses.

Source: arXiv:1606.00608, Appendix C.4, lines 1974--1980. -/
abbrev TbarSbar {g₁ g₂ d D : ℕ} (h : VerticalSectorHypotheses
    (g₁ := g₁) (g₂ := g₂) (d := d) (D := D)) :=
  h.toVerticalSectorFixedGeneratorHypotheses.TbarSbar

end VerticalSectorHypotheses


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

/-- If the weighted vertical bond contractions span by products of length
`L`, then the identity belongs to the corresponding pointwise product span.

Local pointwise-product reformulation of arXiv:1606.00608, Appendix C.4,
lines 1980--1990. -/
theorem one_mem_product_span_of_weightedVerticalBondContractions
    {g D L : ℕ} {dim : Fin g → ℕ}
    (m : Fin g → ℂ)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (hSpan : WeightedVerticalBondContractionProductSpanTop m A L) :
    (1 : VerticalSectorAlgebra dim) ∈
      Submodule.span ℂ (Set.range fun x : Fin L → Matrix (Fin D) (Fin D) ℂ ↦
        (List.ofFn fun t ↦ weightedVerticalBondContraction m A (x t)).prod) := by
  have hOneRaw : (1 : VerticalSectorAlgebra dim) ∈
      Submodule.span ℂ (Set.range
        (weightedVerticalBondContractionProduct (L := L) m A)) := by
    rw [hSpan]
    exact Submodule.mem_top
  have hRange : Set.range (weightedVerticalBondContractionProduct
      (L := L) m A) =
      Set.range (fun x : Fin L → Matrix (Fin D) (Fin D) ℂ ↦
        (List.ofFn fun t ↦ weightedVerticalBondContraction m A (x t)).prod) := by
    ext Y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      funext α
      change ((List.ofFn fun t ↦
          weightedVerticalBondContraction m A (x t)).prod) α =
        (List.ofFn fun t ↦ weightedVerticalBondContraction m A (x t) α).prod
      rw [Pi.list_prod_apply, List.map_ofFn]
      rfl
    · rintro ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      funext α
      change (List.ofFn fun t ↦
          weightedVerticalBondContraction m A (x t) α).prod =
        ((List.ofFn fun t ↦ weightedVerticalBondContraction m A (x t)).prod) α
      rw [Pi.list_prod_apply, List.map_ofFn]
      rfl
  rw [← hRange]
  exact hOneRaw

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

/-- Fixed weighted contractions determine an endomorphism once the products
of arbitrary fixed points have no larger dimension than the fixed-point
space.

This is the finite-dimensional step in the inverse-map argument of Appendix
C.4.  Unlike `eq_id_of_weightedVerticalBondContractionProducts_fixed`, it
does not assume that products of the distinguished contractions are fixed.
The contractions themselves lie in the fixed-point space, so their spanning
products force $C_L(\mathcal F)$ to be the whole sector algebra.
The dimension bound then forces the fixed-point space itself to be the whole
sector algebra.

**Scope restriction (fixed-point dimension):** The source obtains the
dimension bound from Wolf's density-weighted description of the fixed-point
space.  Its derivation from positivity and trace preservation remains recorded
in `docs/paper-gaps/cpsv16_vertical_sector_invertibility.tex`; the bound is
therefore an explicit hypothesis here.

Source: arXiv:1606.00608, Appendix C.4, lines 1980--1993. -/
theorem eq_id_of_weightedVerticalBondContractions_fixed_of_productSpan_finrank_le
    {g D L : ℕ} {dim : Fin g → ℕ}
    (m : Fin g → ℂ)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (F : VerticalSectorAlgebra dim →ₗ[ℂ] VerticalSectorAlgebra dim)
    (hSpan : WeightedVerticalBondContractionProductSpanTop m A L)
    (hFixed : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      F (weightedVerticalBondContraction m A X) =
        weightedVerticalBondContraction m A X)
    (hFinrank : Module.finrank ℂ (fixedPointProductSpan L F) ≤
      Module.finrank ℂ F.fixedSubmodule) :
    F = LinearMap.id := by
  have hProductMem (X : Fin L → Matrix (Fin D) (Fin D) ℂ) :
      weightedVerticalBondContractionProduct m A X ∈
        fixedPointProductSpan L F := by
    apply Submodule.subset_span
    refine ⟨fun t => ⟨weightedVerticalBondContraction m A (X t), ?_⟩, rfl⟩
    exact LinearMap.mem_fixedSubmodule_iff.mpr (hFixed (X t))
  have hProductSpanTop : fixedPointProductSpan L F = ⊤ := by
    apply top_unique
    rw [← hSpan]
    apply Submodule.span_le.mpr
    rintro _ ⟨X, rfl⟩
    exact hProductMem X
  have hAmbientFinrankLe :
      Module.finrank ℂ (VerticalSectorAlgebra dim) ≤
        Module.finrank ℂ F.fixedSubmodule := by
    rw [hProductSpanTop] at hFinrank
    simpa using hFinrank
  have hFixedTop : F.fixedSubmodule = ⊤ :=
    Submodule.eq_top_of_finrank_eq
      ((Submodule.finrank_le F.fixedSubmodule).antisymm hAmbientFinrankLe)
  exact LinearMap.fixedSubmodule_eq_top_iff.mp hFixedTop

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
