/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.InhomogeneousMixingPreparation
import TNLean.MPS.Preparation.InhomogeneousPositivePartRate

/-!
# Physical preparation from actual-site Choi domination

Trace-preserving site maps with one common faithful fixed state and a uniform normalized
Choi lower bound satisfy the ordered mixing condition used for physical logarithmic-depth
preparation. The transfer-matrix estimate is obtained by the inverse Gram reshuffling from
the existing actual-block Doeblin bound. No contraction proof is repeated here.

**Scope restriction (Choi domination):** this is an explicit quantitative sufficient
condition, not a consequence of individual sitewise spectral gaps or the qualitative
finite-correlation definition in arXiv:2307.01696. See
`docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

## References

* Wolf, *Quantum Channels & Operations*, Theorem 8.17 (quantum Doeblin).
* arXiv:2307.01696, eq. (8) and paragraph "Inhomogeneous short-range correlated MPS".
-/

open Matrix MPSTensor QuantumCircuit
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Kronecker
  Matrix.Norms.L2Operator

namespace MPSPreparation

private theorem transferMap_chainBlockTensor_one {d D N : ℕ} (A : MPSChainTensor d D N)
    (hN : ∑ _ : Fin N, 1 = N) (j : Fin N) :
    Kraus.transferMap (chainBlockTensor A hN j) = Kraus.transferMap (A j) := by
  have hi : blockSite hN j (0 : Fin 1) = j := by
    apply Fin.ext
    simp [blockSite_val, blockOffset_const 1 j.isLt.le]
  rw [chainBlockTensor, MPSChainTensor.transferMap_blockTensor]
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, hi]

/-- Actual-site Choi domination gives an exponential bound in the `L²` norm of the transfer
matrix of the actual ordered product. The constant is uniform before the chain, physical
dimension, length, and domination parameter are chosen. Both endpoints `η = 0,1` are kept.

This is the inverse Gram reshuffling of the actual-block Doeblin estimate, based on
Wolf, *Quantum Channels & Operations*, Theorem 8.17. -/
theorem exists_norm_transferMatrix_blockTensor_sub_le_of_choi_domination
    {D : ℕ} {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ {d N : ℕ} (A : MPSChainTensor d D N) {η : ℝ},
      0 ≤ η → η ≤ 1 →
      (∀ j, IsTracePreservingMap (Kraus.transferMap (A j))) →
      (∀ j, Kraus.transferMap (A j) σ = σ) →
      (∀ j, ChoiRectangular.choiMatrix (Kraus.transferMap (A j)) ≥
        ((η : ℂ) / D) • (σ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))) →
      ‖transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor A)) -
        transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤ K * (1 - η) ^ N := by
  have := Matrix.neZero_of_trace_eq_one htr
  obtain ⟨Kr, hKr, hr⟩ := exists_norm_gram_transferMatrix_sub_le D
  obtain ⟨_, _, hg⟩ := exists_norm_polarPos_chainBlockTensor_sub_le_of_choi_domination hσ htr
  have hD : (0 : ℝ) < D := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne D))
  refine ⟨Kr * (2 * D), mul_pos hKr (mul_pos two_pos hD),
    fun {d N} A η hη hη1 htp hfix hchoi => ?_⟩
  have hsum : ∑ _ : Fin N, 1 = N := by simp
  have hmaps := transferMap_chainBlockTensor_one A hsum
  have hb := (hg A (fun _ : Fin N => 1) hsum 1 zero_lt_one (fun _ => le_rfl) hη hη1
    (fun j => by rw [hmaps j]; exact htp j)
    (fun j => by rw [hmaps j]; exact hfix j)
    (fun j => by rw [hmaps j]; exact hchoi j)).1
  simp only [Nat.div_one] at hb
  exact (hr _ σ hσ.posSemidef).2.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hKr.le)

/-- Strict actual-site Choi domination bounds the squared norm of every positive-length
periodic target below by the domination parameter. Split off the first site as
`E₀ = η Rσ + Q` with `Q` completely positive. The remaining ordered product `S` preserves
trace, so `E₀ S = η Rσ + Q S`; the supertrace of a completely positive map is nonnegative.
No nonzero-target hypothesis or stationary-state hypothesis is needed for this bound. -/
theorem le_norm_chainState_sq_of_choi_domination
    {d D N : ℕ} [NeZero N] {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) (A : MPSChainTensor d D N) {η : ℝ}
    (htp : ∀ j, IsTracePreservingMap (Kraus.transferMap (A j)))
    (hchoi : ∀ j, ChoiRectangular.choiMatrix (Kraus.transferMap (A j)) ≥
      ((η : ℂ) / D) • (σ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))) :
    η ≤ ‖chainState A‖ ^ 2 := by
  classical
  have := Matrix.neZero_of_trace_eq_one htr
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 :=
    ⟨N - 1, (Nat.succ_pred_eq_of_ne_zero (NeZero.ne N)).symm⟩
  let B : MPSChainTensor d D n := fun j => A j.succ
  let S := Kraus.transferMap (MPSChainTensor.blockTensor B)
  let P := Matrix.tracePrepareMap (α := Fin D) σ
  let R := Kraus.transferMap (A 0) - (η : ℂ) • P
  have hRcp : IsCPMap R := by
    apply (ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef _).2
    have heq : ChoiRectangular.choiMatrix R =
        ChoiRectangular.choiMatrix (Kraus.transferMap (A 0)) -
          ((η : ℂ) / D) • (σ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
      have hsub := (ChoiRectangular.choiMatrixLinearMap (d := D) (d' := D)).map_sub
        (Kraus.transferMap (A 0)) ((η : ℂ) • P)
      change ChoiRectangular.choiMatrix R =
        ChoiRectangular.choiMatrix (Kraus.transferMap (A 0)) -
          ChoiRectangular.choiMatrix ((η : ℂ) • P) at hsub
      rw [hsub, ChoiRectangular.choiMatrix_smul]
      dsimp only [P]
      rw [Matrix.choiMatrix_tracePrepareMap, smul_smul]
      congr 2
      ring
    rw [heq]
    exact Matrix.le_iff.mp (hchoi 0)
  have hScp : IsCPMap S := isCPMap_of_krausMapLM (MPSChainTensor.blockTensor B)
  have hStr : ∀ X, (S X).trace = X.trace :=
    MPSChainTensor.trace_transferMap_blockTensor B (fun j => htp j.succ)
  have hwhole : Kraus.transferMap (MPSChainTensor.blockTensor A) =
      R * S + (η : ℂ) • P := by
    rw [MPSChainTensor.transferMap_blockTensor, List.ofFn_succ, List.prod_cons]
    have htail : (List.ofFn fun j => Kraus.transferMap (A j.succ)).prod = S :=
      (MPSChainTensor.transferMap_blockTensor B).symm
    rw [htail]
    ext X : 1
    change Kraus.transferMap (A 0) (S X) = R (S X) + (η : ℂ) • P X
    simp only [R, LinearMap.sub_apply, LinearMap.smul_apply, P,
      Matrix.tracePrepareMap_apply, hStr, sub_add_cancel]
  have hsuper : ∀ E : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ),
      IsCPMap E → 0 ≤ (transferMatrix E).trace := by
    intro E hE
    obtain ⟨k, K, hK⟩ := hE
    have heq : E = Kraus.transferMap K := by ext X : 1; exact hK X
    rw [heq, ← pow_one (transferMatrix _),
      trace_transferMatrix_transferMap_pow_eq_mpvOverlap, ← ofReal_norm_mpvState_sq]
    exact Complex.zero_le_real.mpr (sq_nonneg _)
  have hPtr : (transferMatrix P).trace = 1 := by
    have heq : P = Kraus.transferMap (fixedPointTensor σ) := by
      ext X : 1
      simpa only [P, Matrix.tracePrepareMap_apply] using
        (transferMap_fixedPointTensor_apply hσ X).symm
    rw [heq, ← pow_one (transferMatrix _),
      trace_transferMatrix_transferMap_pow_eq_mpvOverlap, mpvOverlap_fixedPointTensor_self hσ htr]
  have hnorm : ((‖chainState A‖ ^ 2 : ℝ) : ℂ) =
      (transferMatrix (R * S)).trace + (η : ℂ) := by
    rw [ofReal_norm_chainState_sq, hwhole]
    change (transferMatrixLM (R * S + (η : ℂ) • P)).trace = _
    rw [map_add, map_smul, Matrix.trace_add, Matrix.trace_smul]
    change (transferMatrix (R * S)).trace + (η : ℂ) * (transferMatrix P).trace = _
    rw [hPtr, mul_one]
  apply Complex.real_le_real.mp
  rw [hnorm]
  exact le_add_of_nonneg_left (hsuper _ (hRcp.comp hScp))

/-- Uniform actual-site Choi domination with `0 < η ≤ 1` and a common faithful fixed state
implies physical depth `O(log(N/ε))`. Strict domination proves that every periodic target
is nonzero, including the short rings. The domination parameter,
bond bound, and fixed state are independent of the ring. The theorem reuses the proved
ordered-mixing and normalized pair-approximation estimates.

At the endpoint `η = 1`, weaken the domination to `η/2` so that the logarithmic decay
parameter remains finite and positive. Qualitative finite correlation alone is not asserted
to imply the hypotheses; see `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`. -/
theorem exists_isPreparedInDepth_inhomogeneous_le_log_of_choi_domination
    (d D : ℕ) (hd : 0 < d) (A : ∀ N, MPSChainTensor d D N)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (htp : ∀ (N : ℕ) [NeZero N] (j : Fin N),
      IsTracePreservingMap (Kraus.transferMap (A N j)))
    (hfix : ∀ (N : ℕ) [NeZero N] (j : Fin N), Kraus.transferMap (A N j) σ = σ)
    (hchoi : ∀ (N : ℕ) [NeZero N] (j : Fin N),
      ChoiRectangular.choiMatrix (Kraus.transferMap (A N j)) ≥
        ((η : ℂ) / D) • (σ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N],
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ C * Real.log (N / ε) ∧
        IsPreparedInDepth T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖chainState (A N)‖ : ℂ)⁻¹ • chainState (A N)⟫_ℂ‖ ≤ ε := by
  have := Matrix.neZero_of_trace_eq_one htr
  have hne (N : ℕ) [NeZero N] : chainState (A N) ≠ 0 := by
    intro hz
    have hb := le_norm_chainState_sq_of_choi_domination hσ.posSemidef htr (A N)
      (htp N) (hchoi N)
    have hη0 : η ≤ 0 := by simpa only [hz, norm_zero, zero_pow two_ne_zero] using hb
    exact (not_le_of_gt hη) hη0
  obtain ⟨K, hK, hmix⟩ :=
    exists_norm_transferMatrix_blockTensor_sub_le_of_choi_domination hσ htr
  have hh0 : 0 ≤ η / 2 := by positivity
  have hh1 : η / 2 ≤ 1 := by linarith
  have hρ0 : 0 < 1 - η / 2 := by linarith
  have hρ1 : 1 - η / 2 < 1 := by linarith
  have hdom : (((η / 2 : ℝ) : ℂ) / D) • (σ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) ≤
      ((η : ℂ) / D) • (σ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
    apply Matrix.le_iff.mpr
    rw [← sub_smul]
    apply (hσ.posSemidef.kronecker Matrix.PosSemidef.one).smul
    have heq : (η : ℂ) / D - ((η / 2 : ℝ) : ℂ) / D = ((η / (2 * D) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [heq]
    exact Complex.zero_le_real.mpr (by positivity)
  apply exists_isPreparedInDepth_inhomogeneous_le_log_of_ordered_mixing d D hd A hσ htr
    K (-Real.log (1 - η / 2)) hK (neg_pos.mpr (Real.log_neg hρ0 hρ1)) hne
  intro N _ M ℓ hN j _
  have h := hmix (fun i : Fin (ℓ j) => A N (blockSite hN j i)) hh0 hh1
    (fun i => htp N _) (fun i => hfix N _) (fun i => hdom.trans (hchoi N _))
  rw [MPSChainTensor.transferMap_blockTensor] at h
  have hexp : Real.exp (-(-Real.log (1 - η / 2) * (ℓ j : ℝ))) = (1 - η / 2) ^ ℓ j := by
    rw [neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hρ0]
  rwa [hexp]

end MPSPreparation
