/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Chain.BlockTensor
import TNLean.Algebra.FinKronecker
import TNLean.Algebra.FinSumPermutation

/-!
# Weighted overlaps of two site-dependent matrix product chains

The ordered product of the local mixed transfer matrices expands into the
weighted product of the two chains' ordered amplitudes. Local physical
weights give the matrix elements of a tensor product of one-site operators.
The identity applies to arbitrary boundary entries and to empty chains.
-/

open Matrix
open scoped BigOperators Kronecker

namespace MPSChainTensor

variable {q Da Db n : ℕ}

/-- A mixed transfer matrix with an arbitrary physical weight at one site. -/
def weightedTransferMatrix (A : MPSTensor q Da) (B : MPSTensor q Db)
    (W : Matrix (Fin q) (Fin q) ℂ) :
    Matrix (Fin Da × Fin Db) (Fin Da × Fin Db) ℂ :=
  ∑ s : Fin q × Fin q, W s.1 s.2 • ((A s.1).map (starRingEnd ℂ) ⊗ₖ B s.2)

/-- Ordered products preserve the paired virtual coordinates of a mixed
Kronecker factor, with entrywise conjugation on the first chain. -/
theorem prod_ofFn_conj_kronecker
    (A : Fin n → Matrix (Fin Da) (Fin Da) ℂ)
    (B : Fin n → Matrix (Fin Db) (Fin Db) ℂ) :
    (List.ofFn fun p ↦ (A p).map (starRingEnd ℂ) ⊗ₖ B p).prod =
      ((List.ofFn A).prod).map (starRingEnd ℂ) ⊗ₖ (List.ofFn B).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons, ih, Matrix.map_mul,
      Matrix.mul_kronecker_mul]

/-- The mixed transfer product equals the configuration expansion of the
weighted overlap of the two ordered matrix products. -/
theorem prod_weightedTransferMatrix
    (A : MPSChainTensor q Da n) (B : MPSChainTensor q Db n)
    (W : Fin n → Matrix (Fin q) (Fin q) ℂ) :
    (List.ofFn fun p ↦ weightedTransferMatrix (A p) (B p) (W p)).prod =
      ∑ σ : Fin n → Fin q, ∑ τ : Fin n → Fin q,
        (∏ p, W p (σ p) (τ p)) •
          ((eval A σ).map (starRingEnd ℂ) ⊗ₖ eval B τ) := by
  classical
  rw [show (fun p ↦ weightedTransferMatrix (A p) (B p) (W p)) =
      (fun p ↦ ∑ s : Fin q × Fin q,
        W p s.1 s.2 • ((A p s.1).map (starRingEnd ℂ) ⊗ₖ B p s.2)) from rfl,
    List.prod_ofFn_sum]
  have hprod (s : Fin n → Fin q × Fin q) :
      (List.ofFn fun p ↦ W p (s p).1 (s p).2 •
        ((A p (s p).1).map (starRingEnd ℂ) ⊗ₖ B p (s p).2)).prod =
      (∏ p, W p (s p).1 (s p).2) •
        ((eval A (fun p ↦ (s p).1)).map (starRingEnd ℂ) ⊗ₖ
          eval B (fun p ↦ (s p).2)) := by
    rw [List.prod_ofFn_smul, prod_ofFn_conj_kronecker,
      ← eval_eq_prod_ofFn, ← eval_eq_prod_ofFn]
  simp_rw [hprod]
  simpa only [Fintype.sum_prod_type, Equiv.arrowProdEquivProdArrow,
    Equiv.coe_fn_mk] using
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ ↦ Fin q) (fun _ ↦ Fin q)).sum_comp
      (fun z ↦ (∏ p, W p (z.1 p) (z.2 p)) •
        ((eval A z.1).map (starRingEnd ℂ) ⊗ₖ eval B z.2))

/-- A boundary entry of the transfer product gives the corresponding weighted
matrix element of the two chains. -/
theorem prod_weightedTransferMatrix_apply
    (A : MPSChainTensor q Da n) (B : MPSChainTensor q Db n)
    (W : Fin n → Matrix (Fin q) (Fin q) ℂ)
    (a c : Fin Da) (b d : Fin Db) :
    (List.ofFn fun p ↦ weightedTransferMatrix (A p) (B p) (W p)).prod (a, b) (c, d) =
      ∑ σ : Fin n → Fin q, ∑ τ : Fin n → Fin q,
        (∏ p, W p (σ p) (τ p)) * star (eval A σ a c) * eval B τ b d := by
  rw [prod_weightedTransferMatrix]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply,
    Matrix.map_apply, starRingEnd_apply]
  apply Finset.sum_congr₂
  intro σ _ τ _
  ring

end MPSChainTensor
