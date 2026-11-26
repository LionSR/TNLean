/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.VaryingBond.OpenMPSRank
import TNLean.MPS.Operator.Periodic.TraceChainOperator
import TNLean.MPS.CanonicalForm.VerticalForm.Purity
import QICLean.Algebra.OperatorSchmidt.Basic
import QICLean.Analysis.ClusterExpansion.Path
import QICLean.ManyBody.Sites.OperatorSchmidtRank
import QICLean.ManyBody.Entropy.Filter.Stationarity
import QICLean.Algebra.OperatorSchmidt.Bounds
import QICLean.Analysis.Exponential.TraceExponentialPerturbation
import TNLean.MPS.Operator.Periodic.TraceChainLinearCombination
import QICLean.Spectral.Filter.SoftTruncationHeatExpansion
import QICLean.Algebra.Hermitian.HermitianPartSum
import QICLean.ManyBody.Hamiltonian.ClusterExpansion.NearestNeighbor
import TNLean.MPS.Tensor.VaryingBond.OpenMPS

/-!
# An actual site-dependent operator chain from the operator cut ranks

Pairing the two physical indices at each site identifies operator Schmidt rank with the cut rank
of a vector. The existing open-chain construction then gives actual operator tensors.
Supporting ALVV, arXiv:1602.08828v2, `thm:cluster`, source lines 1298–1303 and 2014–2115.

## A matrix product operator for the corrected label truncation

The tensors are constructed from the actual nearest-neighbour interactions through their
finite cluster sum. The same operator satisfies the proved energy-normalized approximation
bound. Supporting ALVV, arXiv:1602.08828v2, `thm:cluster`, lines 1298–1303 and 2014–2115.

**Local fix (cutoff and normalization):** this theorem uses connected interaction-label
components, and a supplied lower energy normalizes the error. It does not assert the false
printed physical-support approximation; see `docs/paper-gaps/alvv16_cluster_approximation.tex`.

## Actual operator tensors for a local sum and a scalar

The support-square bound and the constructed all-cut representation give a polynomial exact
representation of the untruncated part of a soft Hamiltonian. Supporting ALVV,
arXiv:1602.08828v2, `def:soft-trunc` and `lem:exp-approx-eff`, lines 1178–1185 and 1262–1268.

## Constructed heat operators after a regional energy shift

The scalar shift is applied outside the local interactions. The proved energy-normalized
cluster estimate controls its effect exactly. Supporting the corrected interaction-label route
to ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268.

**Local fix (cluster cutoff and normalization):** this uses the corrected label selector and
normalized error, not the false printed physical-support estimate; see
`docs/paper-gaps/alvv16_cluster_approximation.tex`.

## Actual soft-truncation tensors from separate heat approximants

Each required heat operator is approximated directly by the constructed cluster MPO. The finite
weighted block sum has virtual dimension multiplied by the number of heat terms. Supporting a
corrected ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268.

**Local fix (cluster estimate):** the interaction-label selector and energy-normalized estimate
replace the false printed physical-support estimate; see
`docs/paper-gaps/alvv16_cluster_approximation.tex`. No computational running time is asserted.

It also contains the following results.

* `TNLean.MPS.AreaLaw.operatorSchmidtRank_cluster_truncation_all_cuts_le`: all chain cuts of the
  actual label truncation.
-/

section ClusterTruncationCutRank

/-!
## All chain cuts of the actual label truncation

The actual crossing-interval bound is combined with direct endpoint and one-dimensional local
space bounds. Supporting the interaction-label version of ALVV, arXiv:1602.08828v2,
`thm:cluster`, lines 1298–1303 and 1971–2013.

**Local fix (interaction-label cutoff):** the selected operator uses the existing label-path
selector, not the minimal physical support of a word product; see
`docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Finset Matrix SimpleGraph

namespace TNLean.MPS.AreaLaw

open ClusterExpansion

open Classical in
/-- The actual label-truncated nearest-neighbour operator has rank at most `r² q^r` at every
chain cut, including endpoints, `r = 1`, and local dimension one. No cut rank is supplied.
Supporting ALVV, arXiv:1602.08828v2, `thm:cluster`, lines 1298–1303 and 1971–2013. -/
theorem operatorSchmidtRank_cluster_truncation_all_cuts_le {N q r : ℕ}
    (hq : 1 ≤ q) (hr : 0 < r)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      (h i) {i.castSucc, i.succ}) (β : ℝ) (k : ℕ) :
    operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q)
      (leftBlock (N + 1) k) (truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) h β)) ≤
        r ^ 2 * q ^ r := by
  classical
  have hD : 1 ≤ r ^ 2 * q ^ r := Nat.mul_le_mul (one_le_pow₀ hr) (one_le_pow₀ hq)
  by_cases hq1 : q = 1
  · subst q
    apply le_trans ?_ hD
    rw [Matrix.operatorSchmidtRank_eq_rank_realignment]
    exact (Matrix.rank_le_card_height _).trans_eq (by simp)
  · by_cases hk0 : k = 0
    · subst k
      have hempty : leftBlock (N + 1) 0 = ∅ := by ext v; simp [leftBlock]
      apply le_trans ?_ hD
      rw [hempty, Matrix.operatorSchmidtRank_eq_rank_realignment]
      exact (Matrix.rank_le_card_height _).trans_eq (by simp)
    · by_cases hkL : N + 1 ≤ k
      · have huniv : leftBlock (N + 1) k = univ := by
          ext v
          simp only [mem_leftBlock, mem_univ, iff_true]
          exact v.isLt.trans_le hkL
        apply le_trans ?_ hD
        rw [huniv, Matrix.operatorSchmidtRank_eq_rank_realignment]
        exact (Matrix.rank_le_card_width _).trans_eq (by simp)
      · let p : Fin N := ⟨k - 1, by omega⟩
        have hA : leftBlock (N + 1) k =
            {v ∈ (univ : Finset (Fin (N + 1))) | v.val ≤ p.val} := by
          ext v
          simp only [mem_leftBlock, mem_filter, mem_univ, true_and]
          change v.val < k ↔ v.val ≤ k - 1
          omega
        rw [hA]
        by_cases hr1 : r = 1
        · subst r
          have hb :=
            ManyBody.ClusterExpansion.operatorSchmidtRank_truncatedExp_nearestNeighbor_le_count
              (r := 1) hq (⟨h, hs⟩ : ManyBody.Interaction (fun _ ↦ Fin q) (ManyBody.chainBond N))
              p β
          have hb' : operatorSchmidtRank (ManyBody.cutOperator
              {v ∈ (univ : Finset (Fin (N + 1))) | v.val ≤ p.val}
                (truncatedExp (pathGraph N) (fun C ↦ 1 ≤ C.card) h β)) ≤ 1 := by
            simpa using hb
          simpa using hb'.trans hq
        · exact ManyBody.ClusterExpansion.operatorSchmidtRank_truncatedExp_nearestNeighbor_le hq hr
            (⟨h, hs⟩ : ManyBody.Interaction (fun _ ↦ Fin q) (ManyBody.chainBond N)) p β

end TNLean.MPS.AreaLaw

end ClusterTruncationCutRank

section OperatorMPOFromCutRank

section

open Finset Matrix
open TNLean.MPS.AreaLaw
open ManyBody (cutMatrix)

namespace MPOTensor

private theorem pairCfgEquiv_symm_glue {L q : ℕ} (B : Finset (Fin L))
    (ij : ({v : Fin L // v ∈ B} → Fin q) × ({v : Fin L // v ∈ B} → Fin q))
    (kl : ({v : Fin L // v ∉ B} → Fin q) × ({v : Fin L // v ∉ B} → Fin q)) :
    (pairCfgEquiv q L).symm ((ManyBody.cutEquiv (fun _ ↦ Fin (q * q)) B).symm
      ((fun v ↦ finProdFinEquiv (ij.1 v, ij.2 v)),
       (fun v ↦ finProdFinEquiv (kl.1 v, kl.2 v)))) =
    ((ManyBody.cutEquiv (fun _ ↦ Fin q) B).symm (ij.1, kl.1),
     (ManyBody.cutEquiv (fun _ ↦ Fin q) B).symm (ij.2, kl.2)) := by
  classical
  apply (pairCfgEquiv q L).injective
  funext v
  by_cases hv : v ∈ B <;>
    simp [pairCfgEquiv, ManyBody.cutEquiv, Equiv.piEquivPiSubtypeProd, hv]

/-- Pairing the ket and bra indices at each site identifies the coefficient cut rank with the
actual operator Schmidt rank. Supporting ALVV, arXiv:1602.08828v2, `thm:cluster`,
source lines 1298–1303 and 2014–2115. -/
theorem rank_pairedOperator_cutMatrix_eq {L q : ℕ}
    (M : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (k : ℕ) :
    let ψ : EuclideanSpace ℂ (Fin L → Fin (q * q)) := WithLp.toLp 2
      (fun z ↦ M ((pairCfgEquiv q L).symm z).1 ((pairCfgEquiv q L).symm z).2)
    (cutMatrix (leftBlock L k) ψ).rank = operatorSchmidtRank
      (ManyBody.cutOperator (X := fun _ ↦ Fin q) (leftBlock L k) M) := by
  classical
  let ψ : EuclideanSpace ℂ (Fin L → Fin (q * q)) := WithLp.toLp 2
    (fun z ↦ M ((pairCfgEquiv q L).symm z).1 ((pairCfgEquiv q L).symm z).2)
  let A := leftBlock L k
  let e (V : Type) : (V → Fin (q * q)) ≃ ((V → Fin q) × (V → Fin q)) :=
    (Equiv.piCongrRight fun _ : V ↦ (finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)).symm).trans
      (Equiv.arrowProdEquivProdArrow V (fun _ ↦ Fin q) (fun _ ↦ Fin q))
  have hmat : (cutMatrix (leftBlock L k) ψ).reindex (e {v : Fin L // v ∈ A})
      (e {v : Fin L // v ∉ A}) =
      fun ij kl ↦ (ManyBody.cutOperator (X := fun _ ↦ Fin q) A M)
        (ij.1, kl.1) (ij.2, kl.2) := by
    ext ij kl
    change M ((pairCfgEquiv q L).symm
      ((ManyBody.cutEquiv (fun _ ↦ Fin (q * q)) A).symm
        ((fun v ↦ finProdFinEquiv (ij.1 v, ij.2 v)),
         (fun v ↦ finProdFinEquiv (kl.1 v, kl.2 v))))).1
      ((pairCfgEquiv q L).symm
      ((ManyBody.cutEquiv (fun _ ↦ Fin (q * q)) A).symm
        ((fun v ↦ finProdFinEquiv (ij.1 v, ij.2 v)),
         (fun v ↦ finProdFinEquiv (kl.1 v, kl.2 v))))).2 = _
    rw [pairCfgEquiv_symm_glue]
    rfl
  change (cutMatrix (leftBlock L k) ψ).rank = operatorSchmidtRank (ManyBody.cutOperator A M)
  rw [← Matrix.rank_reindex (e {v : Fin L // v ∈ A})
    (e {v : Fin L // v ∉ A}) (cutMatrix (leftBlock L k) ψ), hmat,
    Matrix.operatorSchmidtRank_eq_rank_realignment]

/-- Every nonempty operator chain with cut ranks at most a positive integer has actual
site-dependent operator tensors of that virtual dimension. Supporting the representation
step in ALVV, arXiv:1602.08828v2, `thm:cluster`, lines 1298–1303 and 2014–2115. -/
theorem exists_traceChainOperator_of_operatorSchmidtRank_le {L q D : ℕ}
    (hL : 1 ≤ L) (hD : 1 ≤ D)
    (M : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hrank : ∀ k : ℕ, operatorSchmidtRank
      (ManyBody.cutOperator (X := fun _ ↦ Fin q) (leftBlock L k) M) ≤ D) :
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
    fun v (s, t) ↦ B.zeroPad v (finProdFinEquiv (s, t))
  have hM : M = traceChainOperator A (c • 1) := by
    ext σ τ
    have he := hψ (pairCfgEquiv q L (σ, τ))
    simp only [ψ, Equiv.symm_apply_apply] at he
    rw [← B.coeff_zeroPad] at he
    change M σ τ = Matrix.trace ((c • (1 : Matrix (Fin D) (Fin D) ℂ)) *
      (List.ofFn (fun v ↦ A v (σ v, τ v))).prod)
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul]
    simpa only [MPSChainTensor.coeff, MPSChainTensor.eval, pairCfgEquiv_apply,
      Fin.prod_eq_prod_map_finRange, ← List.ofFn_eq_map, smul_eq_mul] using he
  obtain ⟨A', hA'⟩ := exists_traceChainOperator_one hL A (c • 1)
  exact ⟨A', hM.trans hA'⟩

end MPOTensor

end

section

namespace TNLean.MPS.AreaLaw

open Matrix SimpleGraph
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open ClusterExpansion

open Classical in
/-- The actual interaction-label truncation is represented by site-dependent operator tensors
of virtual dimension `r² q^r`. All ranks and tensors are constructed from the supported
interactions. Supporting the corrected label version of ALVV, arXiv:1602.08828v2,
`thm:cluster`, lines 1298–1303 and 2014–2115. -/
theorem exists_mpo_cluster_truncation {N q r : ℕ} (hq : 1 ≤ q) (hr : 0 < r)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      (h i) {i.castSucc, i.succ}) (β : ℝ) :
    ∃ A : Fin (N + 1) → MPOTensor q (r ^ 2 * q ^ r),
      ClusterExpansion.truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) h β =
        MPOTensor.traceChainOperator A 1 := by
  exact MPOTensor.exists_traceChainOperator_of_operatorSchmidtRank_le (by omega)
    (Nat.mul_le_mul (one_le_pow₀ hr) (one_le_pow₀ hq)) _
    (operatorSchmidtRank_cluster_truncation_all_cuts_le hq hr h hs β)

open Classical in
/-- The constructed matrix product operator obeys the corrected energy-normalized tail bound.
This uses the actual nearest-neighbour Hamiltonian, with arbitrary Hermitian interactions of
norm at most one and an explicit lower energy. Supporting a corrected version of ALVV,
arXiv:1602.08828v2, `thm:cluster-approx` and `thm:cluster`, lines 1270–1303. -/
theorem exists_mpo_cluster_approximation {N q r : ℕ} (hq : 1 ≤ q) (hr : 0 < r)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      (h i) {i.castSucc, i.succ})
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (lambda β : ℝ) (hlo : (lambda : ℂ) • 1 ≤ ∑ i, h i) (hβ : 0 ≤ β)
    (hsmall : 2 * (Real.exp β - 1) ≤ 1) :
    ∃ A : Fin (N + 1) → MPOTensor q (r ^ 2 * q ^ r),
      ClusterExpansion.truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) h β =
          MPOTensor.traceChainOperator A 1 ∧
      Real.exp (β * lambda) *
        ‖NormedSpace.exp (-(β • ∑ i, h i)) - MPOTensor.traceChainOperator A 1‖ ≤
          Real.exp ((N : ℝ) ^ 2 * (2 * (Real.exp β - 1)) ^ r) - 1 := by
  obtain ⟨A, hA⟩ := exists_mpo_cluster_truncation hq hr h hs β
  refine ⟨A, hA, ?_⟩
  rw [← hA]
  exact ClusterExpansion.norm_exp_sub_truncatedExp_pathGraph_le hr h hh hnorm lambda β hlo hβ hsmall

end TNLean.MPS.AreaLaw

end

section

open Matrix

namespace TNLean.MPS.AreaLaw

/-- An actual sum of supported nearest-neighbour terms and a scalar identity has actual
site-dependent operator tensors of dimension at most one plus the number of terms times the
square of the local dimension. No Hermiticity or positivity is required. Supporting ALVV,
arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem exists_local_sum_add_scalar_mpo {N q : ℕ} (hq : 1 ≤ q)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      (h i) {i.castSucc, i.succ}) (c : ℂ) :
    ∃ A : Fin (N + 1) → MPOTensor q (1 + N * q ^ 2),
      (∑ i, h i) + c • 1 = MPOTensor.traceChainOperator A 1 := by
  classical
  apply MPOTensor.exists_traceChainOperator_of_operatorSchmidtRank_le (by omega) (by omega)
  intro k
  let X := leftBlock (N + 1) k
  let φ := Matrix.reindexAlgEquiv ℂ ℂ (ManyBody.cutEquiv (fun _ ↦ Fin q) X)
  have hterm (i : Fin N) : operatorSchmidtRank (φ (h i)) ≤ q ^ 2 := by
    change operatorSchmidtRank (ManyBody.cutOperator X (h i)) ≤ _
    exact ((hs i).operatorSchmidtRank_cutOperator_le_pow_card hq).trans
      (Nat.pow_le_pow_right hq Finset.card_le_two)
  have hsum : operatorSchmidtRank (∑ i, φ (h i)) ≤ N * q ^ 2 := by
    exact (operatorSchmidtRank_sum_le Finset.univ _).trans
      ((Finset.sum_le_sum fun i _ ↦ hterm i).trans_eq (by simp))
  have hId : operatorSchmidtRank (φ (1 : Matrix _ _ ℂ)) ≤ 1 := by
    change operatorSchmidtRank (ManyBody.cutOperator X (1 : Matrix _ _ ℂ)) ≤ 1
    exact ManyBody.IsSupportedOn.operatorSchmidtRank_cutOperator_le_one
      (show ManyBody.IsSupportedOn (X := fun _ : Fin (N + 1) ↦ Fin q) 1 ∅ from
        one_mem (ManyBody.supportedOperators (fun _ : Fin (N + 1) ↦ Fin q) ∅))
      (Or.inl (Finset.empty_subset _))
  change operatorSchmidtRank (φ ((∑ i, h i) + c • 1)) ≤ _
  rw [map_add, map_sum, map_smul]
  exact (operatorSchmidtRank_add_le _ _).trans
    ((Nat.add_le_add hsum ((operatorSchmidtRank_smul_le _ _).trans hId)).trans_eq (by omega))

end TNLean.MPS.AreaLaw

end

section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- Actual supported interactions and a lower energy produce actual tensors approximating the
heat operator of the shifted sum, without distributing the scalar shift among the local terms.
Supporting a corrected ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem exists_shifted_heat_mpo {N q r : ℕ} (hq : 1 ≤ q) (hr : 0 < r)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      (h i) {i.castSucc, i.succ})
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (eps β : ℝ) (hlo : (eps : ℂ) • 1 ≤ ∑ i, h i) (hβ : 0 ≤ β)
    (hsmall : 2 * (Real.exp β - 1) ≤ 1) :
    ∃ A : Fin (N + 1) → MPOTensor q (r ^ 2 * q ^ r),
      ‖NormedSpace.exp (-(β • ((∑ i, h i) - (eps : ℂ) • 1))) -
          MPOTensor.traceChainOperator A 1‖ ≤
        Real.exp ((N : ℝ) ^ 2 * (2 * (Real.exp β - 1)) ^ r) - 1 := by
  classical
  obtain ⟨A, _hA, herr⟩ := exists_mpo_cluster_approximation hq hr h hs hh hnorm
    eps β hlo hβ hsmall
  let c : ℂ := (Real.exp (β * eps) : ℝ)
  obtain ⟨B, hB⟩ := MPOTensor.exists_traceChainOperator_one (by omega) A (c • 1)
  have hscaled : MPOTensor.traceChainOperator A (c • 1) =
      c • MPOTensor.traceChainOperator A 1 := by
    ext σ τ
    simp only [MPOTensor.traceChainOperator, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_smul, Matrix.smul_apply]
  have hexp : NormedSpace.exp (-(β • ((∑ i, h i) - (eps : ℂ) • 1))) =
      c • NormedSpace.exp (-(β • ∑ i, h i)) := by
    have he : -(β • ((∑ i, h i) - (eps : ℂ) • 1)) =
        -(β • ∑ i, h i) + (β * eps) • (1 : Matrix _ _ ℂ) := by
      simp only [smul_sub, neg_sub]
      module
    rw [he, Matrix.exp_add_smul_one]
    rfl
  refine ⟨B, ?_⟩
  rw [hexp, ← hB, hscaled, ← smul_sub, norm_smul]
  simpa only [c, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using herr

end TNLean.MPS.AreaLaw

end

section

open Matrix Finset
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- Actual local interactions give actual soft-truncation tensors with an explicit coefficient
and cluster error budget. No heat approximation family or cut rank is supplied. Supporting the
corrected label route to ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem exists_softTruncation_mpo_of_cluster_order {N q r m : ℕ}
    (hq : 1 ≤ q) (hr : 0 < r)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      (h i) {i.castSucc, i.succ})
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (eps t : ℝ) (hlo : (eps : ℂ) • 1 ≤ ∑ i, h i) (ht : 0 < t)
    (hsmall : 2 * (Real.exp ((m : ℝ) / t) - 1) ≤ 1) :
    ∃ A : Fin (N + 1) → MPOTensor q ((r ^ 2 * q ^ r) * (m + 1)),
      ‖cfc (Real.softTruncation t m) ((∑ i, h i) - (eps : ℂ) • 1) -
          MPOTensor.traceChainOperator A 1‖ ≤
        (t * (2 : ℝ) ^ (m + 1)) *
          (Real.exp ((N : ℝ) ^ 2 * (2 * (Real.exp ((m : ℝ) / t) - 1)) ^ r) - 1) := by
  classical
  let U := (∑ i, h i) - (eps : ℂ) • (1 : Matrix (Fin (N + 1) → Fin q) _ ℂ)
  have hU : U.IsHermitian := (isHermitian_sum _ (fun i _ ↦ hh i)).sub
    (isHermitian_one.smul (by simp [isSelfAdjoint_iff]))
  have ha (a : Fin (m + 1)) : 0 ≤ (a.val : ℝ) / t ∧ (a.val : ℝ) / t ≤ (m : ℝ) / t := by
    constructor
    · positivity
    · exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_of_lt_succ a.isLt) ht.le
  have heach (a : Fin (m + 1)) := exists_shifted_heat_mpo hq hr h hs hh hnorm eps
    ((a.val : ℝ) / t) hlo (ha a).1
    ((mul_le_mul_of_nonneg_left
      (sub_le_sub_right (Real.exp_le_exp.mpr (ha a).2) 1) (by norm_num)).trans hsmall)
  choose A hA using heach
  obtain ⟨B, hB⟩ := MPOTensor.exists_traceChainOperator_linearCombination (by omega) A
    (fun a ↦ (Real.softTruncationHeatCoefficient t m a.val : ℂ))
  refine ⟨B, ?_⟩
  let δ := Real.exp ((N : ℝ) ^ 2 * (2 * (Real.exp ((m : ℝ) / t) - 1)) ^ r) - 1
  have hb0 : 0 ≤ 2 * (Real.exp ((m : ℝ) / t) - 1) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.one_le_exp (by positivity)))
  have hδ : 0 ≤ δ := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hA' (a : Fin (m + 1)) :
      ‖NormedSpace.exp (-(((a.val : ℝ) / t) • U)) -
        MPOTensor.traceChainOperator (A a) 1‖ ≤ δ := by
    apply (hA a).trans
    have hba : 0 ≤ 2 * (Real.exp ((a.val : ℝ) / t) - 1) :=
      mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.one_le_exp (ha a).1))
    dsimp only [δ]
    gcongr
    exact Nat.le_of_lt_succ a.isLt
  have hsoft := hU.cfc_softTruncation_eq_sum_heat t m
  rw [← Fin.sum_univ_eq_sum_range] at hsoft
  have hc := Real.sum_abs_softTruncationHeatCoefficient_le t m ht.le
  rw [← Fin.sum_univ_eq_sum_range] at hc
  rw [← hB]
  change ‖cfc (Real.softTruncation t m) U - _‖ ≤ _
  rw [hsoft]
  simp only [← Complex.coe_smul]
  rw [← Finset.sum_sub_distrib]
  simp only [← smul_sub]
  calc
    _ ≤ ∑ a : Fin (m + 1), ‖(Real.softTruncationHeatCoefficient t m a.val : ℂ) •
        (NormedSpace.exp (-(((a.val : ℝ) / t) • U)) -
          MPOTensor.traceChainOperator (A a) 1)‖ := norm_sum_le _ _
    _ = ∑ a : Fin (m + 1), |Real.softTruncationHeatCoefficient t m a.val| *
        ‖NormedSpace.exp (-(((a.val : ℝ) / t) • U)) -
          MPOTensor.traceChainOperator (A a) 1‖ := by
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ a : Fin (m + 1), |Real.softTruncationHeatCoefficient t m a.val| * δ :=
      Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left (hA' a) (abs_nonneg _)
    _ = (∑ a : Fin (m + 1), |Real.softTruncationHeatCoefficient t m a.val|) * δ :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (t * (2 : ℝ) ^ (m + 1)) * δ := mul_le_mul_of_nonneg_right hc hδ

end TNLean.MPS.AreaLaw

end

end OperatorMPOFromCutRank
