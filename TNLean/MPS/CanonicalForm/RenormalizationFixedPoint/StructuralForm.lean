/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.PrimitiveFixedPoint.FromPeripheral
import TNLean.MPS.Transfer.RenormalizationFixedPoint.Defs
import TNLean.MPS.CanonicalForm.BlockFamily

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

## Proof strategy

The full Appendix B decomposition `A i = X * Λ * U i * X⁻¹` is now formalized in
`TNLean.MPS.RFP.StructuralFull`. What *is* formalized here is the span-collapse step:
`E² = E` implies every nonempty blocked word lies in the one-site Kraus span, so a normal RFP
tensor is automatically injective.
-/

open scoped Matrix ComplexOrder Kraus

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
      Kraus.evalWord A w ∈ Submodule.span ℂ (Set.range A) := by
  obtain ⟨V, _, hprod⟩ := (isTransferIdempotent_iff_kraus_isometry A).1 hRFP
  have hmain :
      ∀ n : ℕ, ∀ w : List (Fin d), w.length = n → w ≠ [] →
        Kraus.evalWord A w ∈ Submodule.span ℂ (Set.range A) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih w hlen hne
    cases w with
    | nil =>
        contradiction
    | cons i w =>
        cases w with
        | nil =>
            exact Submodule.subset_span ⟨i, by simp [Kraus.evalWord]⟩
        | cons j w =>
            have hword :
                Kraus.evalWord A (i :: j :: w) =
                  ∑ k : Fin d, V (i, j) k • Kraus.evalWord A (k :: w) := by
              calc
                Kraus.evalWord A (i :: j :: w) = (A i * A j) * Kraus.evalWord A w := by
                  simp [Kraus.evalWord, Matrix.mul_assoc]
                _ = (∑ k : Fin d, V (i, j) k • A k) * Kraus.evalWord A w := by
                  rw [hprod]
                _ = ∑ k : Fin d, V (i, j) k • Kraus.evalWord A (k :: w) := by
                  simp [Kraus.evalWord, Finset.sum_mul]
            rw [hword]
            simpa using
              (Submodule.sum_mem (Submodule.span ℂ (Set.range A))
                (t := Finset.univ)
                (f := fun k : Fin d => V (i, j) k • Kraus.evalWord A (k :: w))
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
    (hNT : Kraus.IsNormal A) (hRFP : IsTransferIdempotent A) :
    Kraus.IsInjective A := by
  obtain ⟨N, hNpos, hNinj⟩ := hNT
  rw [Kraus.IsInjective]
  have htop_le : (⊤ : Submodule ℂ Mat) ≤ Submodule.span ℂ (Set.range A) := by
    unfold Kraus.IsNBlkInjective at hNinj
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
    (hNT : Kraus.IsNormal A) (hRFP : IsTransferIdempotent A)
    (_hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    Kraus.IsInjective A :=
  rfp_nt_structural A hNT hRFP

/-- Appendix B / CFII reduction step:
after unitary conjugation, a left-canonical normal RFP tensor has a diagonal
positive-definite fixed point for its transfer map. -/
theorem rfp_nt_cfii_diagonal_fixedPoint [NeZero D]
    (A : MPSTensor d D)
    (hNT : Kraus.IsNormal A) (hRFP : IsTransferIdempotent A)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    ∃ (U : Matrix.unitaryGroup (Fin D) ℂ)
      (Λ : Matrix (Fin D) (Fin D) ℂ),
        Λ.PosDef ∧ Λ.IsDiag ∧
        (∑ i : Fin d, ((↑U : Matrix _ _ ℂ)ᴴ * A i * (↑U : Matrix _ _ ℂ))ᴴ
                      * ((↑U : Matrix _ _ ℂ)ᴴ * A i * (↑U : Matrix _ _ ℂ)) = 1) ∧
        Kraus.transferMap (ι := Fin d) (n := Fin D)
          (fun i => (↑U : Matrix _ _ ℂ)ᴴ * A i * (↑U : Matrix _ _ ℂ)) Λ = Λ := by
  have hInj : Kraus.IsInjective A := rfp_nt_structural_of_leftCanonical A hNT hRFP hLeft
  have hIrrMap : IsIrreducibleMap (Kraus.transferMap (ι := Fin d) (n := Fin D) A) :=
    Kraus.injective_implies_irreducibleCP A hInj
  have hIrrTensor : Kraus.IsIrreducibleFamily (d := d) (D := D) A :=
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A hIrrMap
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  exact exists_unitary_diag_posDef_fixedPoint_of_TP_of_isIrreducibleFamily
    (d := d) (D := D) A hLeft hIrrTensor hD

/-- **Rank-one classification** (arXiv:1606.00608, Appendix B): for an injective
left-canonical RFP tensor, the transfer map equals the rank-one fixed-point projection
`X ↦ (tr X / tr ρ) • ρ`.

For \(E\) the transfer map, \(Y=E(X)-(\operatorname{tr}X/\operatorname{tr}\rho)\rho\) satisfies
\(E(Y)=Y\) and \(\operatorname{tr}Y=0\). Injectivity gives \(Y=0\), hence \(E(X)=P_\rho(X)\). -/
theorem transferMap_eq_fixedPointProj_of_isTransferIdempotent_injective [NeZero D]
    (A : MPSTensor d D)
    (hInj : Kraus.IsInjective A) (hRFP : IsTransferIdempotent A)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ_pd : ρ.PosDef)
    (hρ_fix : Kraus.transferMap A ρ = ρ) :
    Kraus.transferMap A = fixedPointProj ρ (ne_of_gt hρ_pd.trace_pos) := by
  apply LinearMap.ext; intro X
  apply sub_eq_zero.mp
  apply Kraus.mapLM_fixedPoint_eq_zero_of_trace_eq_zero A hInj hLeft
  · change Kraus.transferMap A
      (Kraus.transferMap A X - (Matrix.trace X / Matrix.trace ρ) • ρ) =
        Kraus.transferMap A X - (Matrix.trace X / Matrix.trace ρ) • ρ
    rw [map_sub, map_smul, hρ_fix]
    congr 1
    exact congrArg (fun f : Mat →ₗ[ℂ] Mat => f X) hRFP
  · change Matrix.trace (Kraus.transferMap A X - (Matrix.trace X / Matrix.trace ρ) • ρ) = 0
    rw [Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
      Kraus.isTracePreservingMap_mapLM_of_isTP A hLeft X,
      div_mul_cancel₀ _ (ne_of_gt hρ_pd.trace_pos), sub_self]

end MPSTensor
