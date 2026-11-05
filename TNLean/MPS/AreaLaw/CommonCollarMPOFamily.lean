/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntervalMPOTransfer
import QICLean.Analysis.MatrixTensorCoordinates

/-!
# One common family under enlargement by interval collars

The prescribed regional change of coordinates extends the same middle
family by product matrix units. Numbering that one family retains its
member bond bound and the exact collar count before any exterior
coefficients, whole operator or estimated energy center are supplied.
This is supporting algebra for ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1332–1333. It asserts no runtime or printed sharp
bond estimate.
-/

open Matrix
open scoped BigOperators Kronecker TensorProduct

noncomputable section
namespace TNLean.MPS.AreaLaw

/-- Enlarge a fixed interval family once, before every whole operator and
its exterior coefficients. The same operator has both its literal matrix
and canonical middle-first tensor decomposition on the larger interval.
The input member bond bound is retained as its maximum with one.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
theorem exists_common_collar_mpo_tensor_family
    {L q c d p r n B : ℕ} (hq : 0 < q)
    (hpc : p ≤ c) (hcd : c ≤ d) (hdr : d ≤ r) (hrL : r ≤ L)
    (W0 : Fin n → Matrix (interval L c d → Fin q) (interval L c d → Fin q) ℂ)
    (hW0 : ∀ j, let e0 := intervalShiftOrderIso hcd (hdr.trans hrL)
      IsOpenMPS (d - c) (q * q) B (fun x ↦ W0 j
        (fun z ↦ (finProdFinEquiv.symm (x (e0.symm z))).1)
        (fun z ↦ (finProdFinEquiv.symm (x (e0.symm z))).2))) :
    let E := interval L c d
    let J := interval L p r
    let ep := intervalShiftOrderIso (hpc.trans (hcd.trans hdr)) hrL
    let tau := (FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) J).trans (Equiv.prodComm _ _)
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
    let Phi := ((EuclideanSpace.basisFun (↥(Jᶜ) → Fin q) ℂ).tensorProduct
      (EuclideanSpace.basisFun (J → Fin q) ℂ)).repr
    let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
      (EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) (EuclideanSpace ℂ (J → Fin q)))
    ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ),
      N = n * q ^ (2 * (J \ E).card) ∧
      (∀ j, IsOpenMPS (r - p) (q * q) (max 1 B) (fun x ↦ W j
        (fun z ↦ (finProdFinEquiv.symm (x (ep.symm z))).1)
        (fun z ↦ (finProdFinEquiv.symm (x (ep.symm z))).2))) ∧
      ∀ Z : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
        (∃ M0 : Fin n → Matrix (↥(Eᶜ) → Fin q) (↥(Eᶜ) → Fin q) ℂ,
          Z = (∑ j, M0 j ⊗ₖ W0 j).submatrix
            ((FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) E).trans (Equiv.prodComm _ _))
            ((FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) E).trans (Equiv.prodComm _ _))) →
        ∃ M : Fin N → Matrix (↥(Jᶜ) → Fin q) (↥(Jᶜ) → Fin q) ℂ,
          Z = (∑ j, M j ⊗ₖ W j).submatrix tau tau ∧
          Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
              Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) Z ∘L
              Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
            ∑ j, TensorProduct.mapL
              (Matrix.toEuclideanCLM (n := J → Fin q) (𝕜 := ℂ) (W j))
              (Matrix.toEuclideanCLM (n := ↥(Jᶜ) → Fin q) (𝕜 := ℂ) (M j)) := by
  classical
  intro E J ep tau U Phi Tm
  let beta := fun _ : Fin L ↦ Fin q
  let I := Fin n × (FiniteProduct.Configuration beta (E \ J) ×
    FiniteProduct.Configuration beta (E \ J)) ×
    (FiniteProduct.Configuration beta (J \ E) × FiniteProduct.Configuration beta (J \ E))
  let Wall := FiniteProduct.changingRegionalMiddleFamily beta E J W0
  let number := Fintype.equivFin I
  have hsub : E ⊆ J := interval_mono hpc hdr
  have hEmpty : E \ J = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hsub
  have hover : max c p ≤ min d r := by omega
  obtain ⟨hcard, hbond, htransfer⟩ :=
    changingRegionalMiddleFamily_mpo_and_global_decomposition hq hcd (hdr.trans hrL)
      (hpc.trans (hcd.trans hdr)) hrL hover W0 (fun _ ↦ B) hW0
  refine ⟨Fintype.card I, fun j ↦ Wall (number.symm j), ?_, ?_, ?_⟩
  · change Fintype.card I = Fintype.card (Fin n) *
      q ^ (2 * (E \ J).card + 2 * (J \ E).card) at hcard
    simpa only [Fintype.card_fin, hEmpty, Finset.card_empty, Nat.mul_zero, Nat.zero_add]
      using hcard
  · intro j
    exact hbond (number.symm j)
  · intro Z hZ
    obtain ⟨M0, hM0⟩ := hZ
    obtain ⟨Mall, hMall⟩ := htransfer M0
    let M := fun j : Fin (Fintype.card I) ↦ Mall (number.symm j)
    have hmatrix : Z = (∑ j, M j ⊗ₖ Wall (number.symm j)).submatrix tau tau := by
      exact hM0.trans (hMall.trans (congrArg (fun P ↦ P.submatrix tau tau)
        (number.symm.sum_comp (fun j ↦ Mall j ⊗ₖ Wall j)).symm))
    exact ⟨M, hmatrix,
      Matrix.toEuclideanCLM_middleFirst_conjugation_of_kronecker_sum
        tau M (fun j ↦ Wall (number.symm j)) Z hmatrix⟩

end TNLean.MPS.AreaLaw
