/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.CPPrimitive
import TNLean.MPS.Irreducible.FormII
import TNLean.MPS.RFP.Defs
import TNLean.PiAlgebra.CanonicalFormSepAux
import TNLean.Spectral.QuantitativeGap

/-!
# Structural form of RFP tensors

This file states the structural characterisation theorems for MPS tensors
that are renormalization fixed points, following arXiv:1606.00608 Section 3.4
(Cirac–Pérez-García–Schuch–Verstraete) and Appendix B.

## Main results

* `rfp_nt_structural`: a normal RFP tensor is already injective
* `rfp_nt_structural_of_leftCanonical`: left-canonical normal RFP tensors are injective
* `rfp_nt_cfii_diagonal_fixedPoint`: Appendix B / CFII reduction step — after unitary
  conjugation, a left-canonical normal RFP tensor has a diagonal positive-definite fixed point
* `rfp_cf_structural`: each canonical-form block is injective

## Proof strategy

The full Appendix B decomposition `A i = X * Λ * U i * X⁻¹` is now formalized in
`TNLean.MPS.RFP.StructuralFull`. What *is* formalized here is the span-collapse step:
`E² = E` implies every nonempty blocked word lies in the one-site Kraus span, so a normal RFP
tensor is automatically injective.
-/

open scoped Matrix ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- For an RFP tensor, every nonempty word evaluates into the one-site Kraus span.

This is the algebraic consequence of `E² = E`: the product family `{AᵢAⱼ}` is already a linear
combination of `{Aₖ}`, and a strong induction on the word length propagates this to all nonempty
words. -/
private theorem evalWord_mem_span_of_isTransferIdempotent
    (A : MPSTensor d D) (hRFP : IsTransferIdempotent A) :
    ∀ w : List (Fin d), w ≠ [] →
      evalWord A w ∈ Submodule.span ℂ (Set.range A) := by
  obtain ⟨V, _, hprod⟩ := (isTransferIdempotent_iff_kraus_isometry A).1 hRFP
  have hmain :
      ∀ n : ℕ, ∀ w : List (Fin d), w.length = n → w ≠ [] →
        evalWord A w ∈ Submodule.span ℂ (Set.range A) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih w hlen hne
    cases w with
    | nil =>
        contradiction
    | cons i w =>
        cases w with
        | nil =>
            exact Submodule.subset_span ⟨i, by simp [evalWord]⟩
        | cons j w =>
            have hword :
                evalWord A (i :: j :: w) = ∑ k : Fin d, V (i, j) k • evalWord A (k :: w) := by
              calc
                evalWord A (i :: j :: w) = (A i * A j) * evalWord A w := by
                  simp [evalWord, Matrix.mul_assoc]
                _ = (∑ k : Fin d, V (i, j) k • A k) * evalWord A w := by
                  rw [hprod]
                _ = ∑ k : Fin d, V (i, j) k • evalWord A (k :: w) := by
                  simp [evalWord, Finset.sum_mul]
            rw [hword]
            simpa using
              (Submodule.sum_mem (Submodule.span ℂ (Set.range A))
                (t := Finset.univ)
                (f := fun k : Fin d => V (i, j) k • evalWord A (k :: w))
                (by
                  intro k hk
                  refine Submodule.smul_mem _ _ ?_
                  have hk_lt : (k :: w).length < n := by
                    have hlen' : w.length + 2 = n := by
                      simpa using hlen
                    simpa [hlen'] using Nat.lt_succ_self (w.length + 1)
                  exact ih (k :: w).length hk_lt (k :: w) rfl (by simp)))
  intro w hne
  exact hmain w.length w rfl hne

/-- Formalized structural precursor to Appendix B: a normal RFP tensor is
already injective.

The proof uses the RFP span-collapse lemma above: once every nonempty blocked word lies in the
one-site Kraus span, any positive-length block-injectivity witness immediately upgrades to
single-site injectivity.

Source context: CPSV16, Appendix B, lines 1274--1300, proves a stronger structural
decomposition for the paper's normal-tensor notion. The present implication is the
project's span-collapse precursor and is not a formalization of that lemma. -/
theorem rfp_nt_structural (A : MPSTensor d D)
    (hNT : IsNormal A) (hRFP : IsTransferIdempotent A) :
    IsInjective A := by
  obtain ⟨N, hNpos, hNinj⟩ := hNT
  rw [IsInjective]
  have htop_le : (⊤ : Submodule ℂ Mat) ≤ Submodule.span ℂ (Set.range A) := by
    unfold IsNBlkInjective at hNinj
    refine hNinj.ge.trans (Submodule.span_le.2 ?_)
    rintro _ ⟨σ, rfl⟩
    apply evalWord_mem_span_of_isTransferIdempotent A hRFP
    exact List.ne_nil_of_length_pos (by simpa using hNpos)
  exact le_antisymm le_top htop_le

/-- Appendix B precursor without a separate nonzero side condition:
for a left-canonical normal RFP tensor, the one-site Kraus span is already all of `M_D(ℂ)`.

The left-canonical hypothesis is retained because this is the specialization stated in
arXiv:1606.00608, Appendix B. The stronger theorem `rfp_nt_structural` shows that the
normalization is not needed for this implication. -/
theorem rfp_nt_structural_of_leftCanonical
    (A : MPSTensor d D)
    (hNT : IsNormal A) (hRFP : IsTransferIdempotent A)
    (_hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    IsInjective A :=
  rfp_nt_structural A hNT hRFP

/-- Appendix B / CFII reduction step:
after unitary conjugation, a left-canonical normal RFP tensor has a diagonal
positive-definite fixed point for its transfer map. -/
theorem rfp_nt_cfii_diagonal_fixedPoint [NeZero D]
    (A : MPSTensor d D)
    (hNT : IsNormal A) (hRFP : IsTransferIdempotent A)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    ∃ (U : Matrix.unitaryGroup (Fin D) ℂ)
      (Λ : Matrix (Fin D) (Fin D) ℂ),
        Λ.PosDef ∧ Λ.IsDiag ∧
        (∑ i : Fin d, ((↑U : Matrix _ _ ℂ)ᴴ * A i * (↑U : Matrix _ _ ℂ))ᴴ
                      * ((↑U : Matrix _ _ ℂ)ᴴ * A i * (↑U : Matrix _ _ ℂ)) = 1) ∧
        transferMap (d := d) (D := D)
          (fun i => (↑U : Matrix _ _ ℂ)ᴴ * A i * (↑U : Matrix _ _ ℂ)) Λ = Λ := by
  have hInj : IsInjective A := rfp_nt_structural_of_leftCanonical A hNT hRFP hLeft
  have hIrrMap : IsIrreducibleMap (transferMap (d := d) (D := D) A) :=
    injective_implies_irreducibleCP A hInj
  have hIrrTensor : IsIrreducibleTensor (d := d) (D := D) A :=
    isIrreducibleTensor_of_isIrreducibleMap A hIrrMap
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  exact exists_unitary_diag_posDef_fixedPoint_of_TP_of_isIrreducibleTensor
    (d := d) (D := D) A hLeft hIrrTensor hD

/-- **Rank-one classification** (arXiv:1606.00608, Appendix B): for an injective
left-canonical RFP tensor, the transfer map equals the rank-one fixed-point projection
`X ↦ (tr X / tr ρ) • ρ`.

The proof combines exponential convergence (`E^n → P`) with idempotence (`E^n = E`
for `n ≥ 1`). Since `E` is both the limit and is equal to every iterate, `E = P`. -/
theorem transferMap_eq_fixedPointProj_of_isTransferIdempotent_injective [NeZero D]
    (A : MPSTensor d D)
    (hInj : IsInjective A) (hRFP : IsTransferIdempotent A)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ_pd : ρ.PosDef)
    (hρ_fix : transferMap A ρ = ρ) :
    transferMap A = fixedPointProj ρ (ne_of_gt hρ_pd.trace_pos) := by
  obtain ⟨C, δ, hC, hδ, hδ1, hbound⟩ :=
    exponential_convergence_of_primitive A hLeft hInj ρ hρ_pd hρ_fix
  have hIdem : IsIdempotentElem (transferMap (d := d) (D := D) A) := hRFP
  set E := transferMap (d := d) (D := D) A
  set P := fixedPointProj ρ (ne_of_gt hρ_pd.trace_pos)
  apply LinearMap.ext; intro X
  -- For all n: E^[n+1] X = E X (idempotence), so ‖E X - P X‖ ≤ C(1-δ)^{n+1} ‖X‖
  have h_bound_const : ∀ n : ℕ, ‖E X - P X‖ ≤
      C * (1 - δ) ^ (n + 1) * ‖X‖ := by
    intro n
    have h_iter : E^[n + 1] X = E X := by
      rw [← Module.End.pow_apply]; congr 1; exact hIdem.pow_succ_eq n
    rw [← h_iter]; exact hbound (n + 1) X
  -- C(1-δ)^{n+1} ‖X‖ → 0
  have h_rate : Filter.Tendsto (fun n => C * (1 - δ) ^ (n + 1) * ‖X‖)
      Filter.atTop (nhds 0) := by
    have h_base := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ 1 - δ by linarith) (show 1 - δ < 1 by linarith)
    -- (1-δ)^(n+1) = (1-δ) * (1-δ)^n → (1-δ) * 0 = 0
    have h_shift : Filter.Tendsto (fun n => (1 - δ) ^ (n + 1)) Filter.atTop (nhds 0) := by
      have := h_base.const_mul (1 - δ)
      simp only [mul_zero] at this
      exact this.congr fun n => by ring
    have h_mul := h_shift.const_mul (C * ‖X‖)
    simp only [mul_zero] at h_mul
    exact h_mul.congr fun n => by ring
  -- Constant sequence E X - P X → 0 by squeeze, so E X - P X = 0
  have h_tend : Filter.Tendsto (fun _ : ℕ => E X - P X) Filter.atTop (nhds 0) :=
    squeeze_zero_norm h_bound_const h_rate
  exact eq_of_sub_eq_zero (tendsto_nhds_unique tendsto_const_nhds h_tend)

/-- Canonical-form blocks are already injective, so the structural precursor above is automatic. -/
theorem rfp_cf_structural {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalForm μ A) :
    ∀ k, IsInjective (A k) :=
  hCF.block_injective

end MPSTensor
