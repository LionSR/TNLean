/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.OpenMPSRank
import TNLean.MPS.MPDO.TraceChainOperator
import TNLean.MPS.MPDO.Purity
import QICLean.Algebra.OperatorSchmidtRealignment

/-!
# An actual site-dependent operator chain from the operator cut ranks

Pairing the two physical indices at each site identifies operator Schmidt rank with the cut rank
of a vector. The existing open-chain construction then gives actual operator tensors.
Supporting ALVV, arXiv:1602.08828v2, `thm:cluster`, source lines 1298–1303 and 2014–2115.
-/

open Finset Matrix
open TNLean.MPS.AreaLaw

namespace MPOTensor

private theorem pairCfgEquiv_symm_glue {L q : ℕ} (B : Finset (Fin L))
    (ij : ({v : Fin L // v ∈ B} → Fin q) × ({v : Fin L // v ∈ B} → Fin q))
    (kl : ({v : Fin L // v ∉ B} → Fin q) × ({v : Fin L // v ∉ B} → Fin q)) :
    (pairCfgEquiv q L).symm ((Entropy.cutEquiv (fun _ : Fin L ↦ q * q) B).symm
      ((fun v ↦ finProdFinEquiv (ij.1 v, ij.2 v)),
       (fun v ↦ finProdFinEquiv (kl.1 v, kl.2 v)))) =
    ((Entropy.cutEquiv (fun _ : Fin L ↦ q) B).symm (ij.1, kl.1),
     (Entropy.cutEquiv (fun _ : Fin L ↦ q) B).symm (ij.2, kl.2)) := by
  classical
  apply (pairCfgEquiv q L).injective
  funext v
  by_cases hv : v ∈ B <;>
    simp [pairCfgEquiv, Entropy.cutEquiv, Equiv.piEquivPiSubtypeProd, hv]

/-- Pairing the ket and bra indices at each site identifies the coefficient cut rank with the
actual operator Schmidt rank. Supporting ALVV, arXiv:1602.08828v2, `thm:cluster`,
source lines 1298–1303 and 2014–2115. -/
theorem rank_pairedOperator_cutMatrix_eq {L q : ℕ}
    (M : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (k : ℕ) :
    let ψ : EuclideanSpace ℂ (Fin L → Fin (q * q)) := WithLp.toLp 2
      (fun z ↦ M ((pairCfgEquiv q L).symm z).1 ((pairCfgEquiv q L).symm z).2)
    (cutMatrix ψ k).rank = operatorSchmidtRank
      (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) M) := by
  classical
  let ψ : EuclideanSpace ℂ (Fin L → Fin (q * q)) := WithLp.toLp 2
    (fun z ↦ M ((pairCfgEquiv q L).symm z).1 ((pairCfgEquiv q L).symm z).2)
  let A := leftBlock L k
  let e (V : Type) : (V → Fin (q * q)) ≃ ((V → Fin q) × (V → Fin q)) :=
    (Equiv.piCongrRight fun _ : V ↦ (finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)).symm).trans
      (Equiv.arrowProdEquivProdArrow V (fun _ ↦ Fin q) (fun _ ↦ Fin q))
  have hmat : (cutMatrix ψ k).reindex (e {v : Fin L // v ∈ A}) (e {v : Fin L // v ∉ A}) =
      fun ij kl ↦ (Entropy.cutOperator (n := fun _ : Fin L ↦ q) A M)
        (ij.1, kl.1) (ij.2, kl.2) := by
    ext ij kl
    change M ((pairCfgEquiv q L).symm
      ((Entropy.cutEquiv (fun _ : Fin L ↦ q * q) A).symm
        ((fun v ↦ finProdFinEquiv (ij.1 v, ij.2 v)),
         (fun v ↦ finProdFinEquiv (kl.1 v, kl.2 v))))).1
      ((pairCfgEquiv q L).symm
      ((Entropy.cutEquiv (fun _ : Fin L ↦ q * q) A).symm
        ((fun v ↦ finProdFinEquiv (ij.1 v, ij.2 v)),
         (fun v ↦ finProdFinEquiv (kl.1 v, kl.2 v))))).2 = _
    rw [pairCfgEquiv_symm_glue]
    rfl
  change (cutMatrix ψ k).rank = operatorSchmidtRank (Entropy.cutOperator A M)
  rw [← Matrix.rank_reindex (e {v : Fin L // v ∈ A})
    (e {v : Fin L // v ∉ A}) (cutMatrix ψ k), hmat,
    Matrix.operatorSchmidtRank_eq_rank_realignment]

/-- Every nonempty operator chain with cut ranks at most a positive integer has actual
site-dependent operator tensors of that virtual dimension. Supporting the representation
step in ALVV, arXiv:1602.08828v2, `thm:cluster`, lines 1298–1303 and 2014–2115. -/
theorem exists_traceChainOperator_of_operatorSchmidtRank_le {L q D : ℕ}
    (hL : 1 ≤ L) (hD : 1 ≤ D)
    (M : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hrank : ∀ k : ℕ, operatorSchmidtRank
      (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) M) ≤ D) :
    ∃ A : Fin L → MPOTensor q D, M = traceChainOperator A 1 := by
  classical
  let ψ : EuclideanSpace ℂ (Fin L → Fin (q * q)) := WithLp.toLp 2
    (fun z ↦ M ((pairCfgEquiv q L).symm z).1 ((pairCfgEquiv q L).symm z).2)
  have hmps := isOpenMPS_of_cutMatrix_rank_le ψ (fun k ↦
    (rank_pairedOperator_cutMatrix_eq M k).trans_le (hrank k))
  unfold IsOpenMPS at hmps
  rw [max_eq_right hD] at hmps
  obtain ⟨B, c, _, hψ⟩ := hmps
  let : NeZero L := ⟨by omega⟩
  let A : Fin L → MPOTensor q D :=
    fun v s t ↦ B.zeroPad v (finProdFinEquiv (s, t))
  have hM : M = traceChainOperator A (c • 1) := by
    ext σ τ
    have he := hψ (pairCfgEquiv q L (σ, τ))
    simp only [ψ, Equiv.symm_apply_apply] at he
    rw [← B.coeff_zeroPad] at he
    change M σ τ = Matrix.trace ((c • (1 : Matrix (Fin D) (Fin D) ℂ)) *
      (List.ofFn (fun v ↦ A v (σ v) (τ v))).prod)
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul]
    simpa only [MPSChainTensor.coeff, MPSChainTensor.eval, pairCfgEquiv_apply,
      Fin.prod_eq_prod_map_finRange, ← List.ofFn_eq_map, smul_eq_mul] using he
  obtain ⟨A', hA'⟩ := exists_traceChainOperator_one hL A (c • 1)
  exact ⟨A', hM.trans hA'⟩

end MPOTensor
