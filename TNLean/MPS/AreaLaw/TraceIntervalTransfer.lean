/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntervalMPOTransfer
import TNLean.MPS.AreaLaw.RetainedCoreFamilies
import TNLean.MPS.MPDO.TraceChainOperator
import TNLean.Algebra.MatrixFactorExchange

/-!
# Trace presentations under a change of interval

The actual regional matrix factor is a fixed-configuration slice on the common
interval, extended by a matrix unit on the newly retained sites. A supplied
site-dependent trace presentation therefore transfers with exactly the same
virtual dimension. Its new cap may differ from the original cap.

The prescribed regional middle family, its cardinality and its exterior
coefficient identity remain unchanged. These are explicit trace-algebra
consequences supporting ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1332–1333. No open-boundary representation or cap-rank assumption is used.
-/

open Matrix
open scoped BigOperators Kronecker Matrix

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- The actual change of regional middle factor preserves a supplied trace
presentation with its virtual dimension. The new cap and site tensors are
chosen before the variable natural row and column configurations. The removed
and inserted configurations and the common overlap are the actual canonical
regional coordinates. Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1332–1333. No open-boundary or cap-rank hypothesis is used. -/
theorem exists_traceChainOperator_changingRegionalMiddleFactor
    {T q c d u v D : ℕ} (hq : 0 < q)
    (hcd : c ≤ d) (hd : d ≤ T) (huv : u ≤ v) (hv : v ≤ T)
    (hover : max c u ≤ min d v)
    (Vphys : Matrix (FiniteProduct.Configuration (fun _ : Fin T ↦ Fin q) (interval T c d))
      (FiniteProduct.Configuration (fun _ : Fin T ↦ Fin q) (interval T c d)) ℂ)
    (hV : let eE := intervalShiftOrderIso hcd hd
      ∃ C : Matrix (Fin D) (Fin D) ℂ, ∃ A : Fin (d - c) → MPOTensor q D,
        Vphys.submatrix (fun σ z ↦ σ (eE.symm z))
          (fun σ z ↦ σ (eE.symm z)) = MPOTensor.traceChainOperator A C)
    (αr αc : FiniteProduct.Configuration (fun _ : Fin T ↦ Fin q)
      (interval T c d \ interval T u v))
    (ηr ηc : FiniteProduct.Configuration (fun _ : Fin T ↦ Fin q)
      (interval T u v \ interval T c d)) :
    let old := FiniteProduct.changingOldMiddleConfigEquiv
      (fun _ : Fin T ↦ Fin q) (interval T c d) (interval T u v)
    let new := FiniteProduct.changingNewMiddleConfigEquiv
      (fun _ : Fin T ↦ Fin q) (interval T c d) (interval T u v)
    let Wphys := ((Matrix.single ηr ηc (1 : ℂ)) ⊗ₖ
      Matrix.operatorBlock (Vphys.reindex old old) αr αc).reindex new.symm new.symm
    let eJ := intervalShiftOrderIso huv hv
    ∃ Cnew : Matrix (Fin D) (Fin D) ℂ, ∃ Anew : Fin (v - u) → MPOTensor q D,
      Wphys.submatrix (fun σ z ↦ σ (eJ.symm z))
        (fun σ z ↦ σ (eJ.symm z)) = MPOTensor.traceChainOperator Anew Cnew := by
  obtain ⟨C, A, hA⟩ := hV
  obtain ⟨a, b, len, ha, hb, fixedRow, fixedCol, outsideRow, outsideCol, hentry⟩ :=
    exists_intervalSlice_changingRegionalMiddleFactor
      hq hcd hd huv hv hover Vphys αr αc ηr ηc
  obtain ⟨Cnew, Anew, htrace⟩ :=
    MPOTensor.exists_traceChainOperator_intervalSlice_extend_by_configuration
      A C a ha fixedRow fixedCol b hb outsideRow outsideCol
  rw [hA] at hentry
  exact ⟨Cnew, Anew, hentry.trans htrace⟩

/-- The same prescribed changing-region family has trace presentations at
exactly the original virtual dimensions. Its cardinality and decomposition
for every later exterior family are the canonical regional ones. The middle
family is not chosen again. Supporting ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1332–1333, as an explicit trace-algebra consequence. -/
theorem changingRegionalMiddleFamily_trace_and_global_decomposition
    {T q c d u v : ℕ} {ι : Type*} [Fintype ι]
    (hq : 0 < q) (hcd : c ≤ d) (hd : d ≤ T) (huv : u ≤ v) (hv : v ≤ T)
    (hover : max c u ≤ min d v)
    (V : ι → Matrix (FiniteProduct.Configuration (fun _ : Fin T ↦ Fin q) (interval T c d))
      (FiniteProduct.Configuration (fun _ : Fin T ↦ Fin q) (interval T c d)) ℂ)
    (D : ι → ℕ)
    (hV : ∀ t, let eE := intervalShiftOrderIso hcd hd
      ∃ C : Matrix (Fin (D t)) (Fin (D t)) ℂ,
      ∃ A : Fin (d - c) → MPOTensor q (D t),
        (V t).submatrix (fun σ z ↦ σ (eE.symm z))
          (fun σ z ↦ σ (eE.symm z)) = MPOTensor.traceChainOperator A C) :
    let β := fun _ : Fin T ↦ Fin q
    let E := interval T c d
    let J := interval T u v
    let A := E \ J
    let B := J \ E
    let I := ι × (FiniteProduct.Configuration β A × FiniteProduct.Configuration β A) ×
      (FiniteProduct.Configuration β B × FiniteProduct.Configuration β B)
    let W := FiniteProduct.changingRegionalMiddleFamily β E J V
    let eJ := intervalShiftOrderIso huv hv
    Fintype.card I = Fintype.card ι * q ^ (2 * A.card + 2 * B.card) ∧
      (∀ r : I, ∃ Cnew : Matrix (Fin (D r.1)) (Fin (D r.1)) ℂ,
        ∃ Anew : Fin (v - u) → MPOTensor q (D r.1),
          (W r).submatrix (fun σ z ↦ σ (eJ.symm z))
            (fun σ z ↦ σ (eJ.symm z)) = MPOTensor.traceChainOperator Anew Cnew) ∧
      ∀ M : ι → Matrix (FiniteProduct.Configuration β Eᶜ)
          (FiniteProduct.Configuration β Eᶜ) ℂ,
        ∃ Mnew : I → Matrix (FiniteProduct.Configuration β Jᶜ)
            (FiniteProduct.Configuration β Jᶜ) ℂ,
          (∑ t, M t ⊗ₖ V t).submatrix
            ((FiniteProduct.splitEquiv β E).trans (Equiv.prodComm _ _))
            ((FiniteProduct.splitEquiv β E).trans (Equiv.prodComm _ _)) =
          (∑ r, Mnew r ⊗ₖ W r).submatrix
            ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _))
            ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _)) := by
  let β := fun _ : Fin T ↦ Fin q
  let E := interval T c d
  let J := interval T u v
  let A := E \ J
  let B := J \ E
  let I := ι × (FiniteProduct.Configuration β A × FiniteProduct.Configuration β A) ×
    (FiniteProduct.Configuration β B × FiniteProduct.Configuration β B)
  let W := FiniteProduct.changingRegionalMiddleFamily β E J V
  let eJ := intervalShiftOrderIso huv hv
  have hcard : Fintype.card I = Fintype.card ι * q ^ (2 * A.card + 2 * B.card) := by
    calc
      Fintype.card I = Fintype.card ι *
          Fintype.card (FiniteProduct.Configuration β A) ^ 2 *
          Fintype.card (FiniteProduct.Configuration β B) ^ 2 :=
        Matrix.card_exchangedMiddleFamily_index
      _ = Fintype.card ι * q ^ (2 * A.card + 2 * B.card) := by
        simp only [FiniteProduct.Configuration, β, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_coe, ← pow_mul]
        rw [Nat.mul_assoc, ← pow_add]
        rw [show A.card * 2 + B.card * 2 = 2 * A.card + 2 * B.card by omega]
  have hW : ∀ r : I, ∃ Cnew : Matrix (Fin (D r.1)) (Fin (D r.1)) ℂ,
      ∃ Anew : Fin (v - u) → MPOTensor q (D r.1),
        (W r).submatrix (fun σ z ↦ σ (eJ.symm z))
          (fun σ z ↦ σ (eJ.symm z)) = MPOTensor.traceChainOperator Anew Cnew := by
    intro r
    obtain ⟨Cnew, Anew, hfactor⟩ :=
      exists_traceChainOperator_changingRegionalMiddleFactor hq hcd hd huv hv hover
        (V r.1) (hV r.1) r.2.1.1 r.2.1.2 r.2.2.1 r.2.2.2
    refine ⟨Cnew, Anew, ?_⟩
    convert hfactor using 1;
      (ext σ τ;
        simp only [W, FiniteProduct.changingRegionalMiddleFamily, β, E, J, eJ,
          Matrix.exchangedMiddleFamily, Matrix.exchangedMiddleFactor, Matrix.reindex_apply,
          Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.single_apply,
          Equiv.symm_symm];
        split_ifs <;> rfl)
  refine ⟨hcard, hW, ?_⟩
  intro M
  exact FiniteProduct.exists_changingRegional_exterior_family β E J V M

end TNLean.MPS.AreaLaw

end
