/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.InhomogeneousDoeblin
import TNLean.MPS.Preparation.BlockIsometryState
import QICLean.Channel.Semigroup.CPClosure

/-!
# Uniform positive-part rates from Choi domination

The normalized Choi matrix of the transfer map is the transpose of the blocked physical
Gram matrix divided by the bond dimension. A uniform Choi lower bound on the actual
inhomogeneous site maps, together with a common faithful fixed state, yields a Gram error
at most `2D (1 - ε)^(N/s)` on a chain partitioned into actual contiguous blocks of at most
`s` sites. The square-root Lipschitz estimate at the faithful limiting Gram matrix gives
the same exponential rate for the positive polar factor. The quotient `N/s` is rounded down.

The sites may be fixed-length contiguous blocks, but the domination hypothesis must then
hold for the transfer maps of those actual blocks. Individual microscopic spectral gaps
are not a replacement for this hypothesis.

## Main results

* `gram_eq_smul_choi_transpose`: the exact bond-dimension normalization and index order.
* `exists_norm_polarPos_chainBlockTensor_sub_le_of_choi_domination`: uniform Gram and polar
  bounds from actual contiguous-block domination and a common faithful fixed state.

## References

* arXiv:2307.01696, eq. (8) and paragraph "Inhomogeneous short-range correlated MPS".
* Wolf, *Quantum Channels & Operations*, Theorem 8.17 (quantum Doeblin).
* arXiv:2103.13367, Supplemental Material, equations (19), (21), and (26).
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace MPSPreparation

/-- The physical Gram matrix is the bond dimension times the transpose of the normalized
Choi matrix of the transfer map, with both indexed by the ordered pair of bond indices. -/
theorem gram_eq_smul_choi_transpose {d D : ℕ} [NeZero D] (A : MPSTensor d D) :
    (physicalMatrix A)ᴴ * physicalMatrix A =
      (D : ℂ) • (ChoiRectangular.choiMatrix (Kraus.transferMap A)).transpose := by
  ext a b
  rw [conjTranspose_physicalMatrix_mul_apply, Matrix.smul_apply, Matrix.transpose_apply,
    ChoiRectangular.choiMatrix_apply, MaximallyEntangled.omegaSlice_eq_single,
    MaximallyEntangled.omegaCoeff_eq_inv (Nat.pos_of_ne_zero (NeZero.ne D))]
  rw [show Matrix.single b.2 a.2 (1 / (D : ℂ)) =
      (1 / (D : ℂ)) • Matrix.single b.2 a.2 1 by simp,
    map_smul, Matrix.smul_apply]
  simp only [smul_eq_mul]
  field_simp

/-- **Uniform Gram and positive-part rates for an inhomogeneous chain.** Fix a faithful
state `σ` of trace one. There is `K`, depending only on `D` and `σ`, such that for any chain
partitioned into contiguous blocks of lengths at most `s > 0`, if those actual block maps
preserve trace, fix `σ`, and have normalized Choi matrices at least `(ε/D) (σ ⊗ I)`, the Gram
error is at most `2D (1 - ε)^(N/s)` and the positive-part error is at most
`K (1 - ε)^(N/s)`, for `0 ≤ ε ≤ 1`. Here `N/s` is integer division.

The hypotheses concern actual ordered block maps; they are quantitative assumptions,
not consequences of separate spectral gaps of the individual microscopic tensors. -/
theorem exists_norm_polarPos_chainBlockTensor_sub_le_of_choi_domination
    {D : ℕ} {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {d N M : ℕ} (A : MPSChainTensor d D N)
      (ℓ : Fin M → ℕ) (hN : ∑ k, ℓ k = N) (s : ℕ), 0 < s →
      (∀ k, ℓ k ≤ s) → ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ 1 →
      (∀ k, IsTracePreservingMap (Kraus.transferMap (chainBlockTensor A hN k))) →
      (∀ k, Kraus.transferMap (chainBlockTensor A hN k) σ = σ) →
      (∀ k, ChoiRectangular.choiMatrix (Kraus.transferMap (chainBlockTensor A hN k)) ≥
        ((ε : ℂ) / D) • (σ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))) →
      ‖(physicalMatrix (MPSChainTensor.blockTensor A))ᴴ *
          physicalMatrix (MPSChainTensor.blockTensor A) - σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤
        2 * D * (1 - ε) ^ (N / s) ∧
      ‖Matrix.polarPos (physicalMatrix (MPSChainTensor.blockTensor A)) -
          (CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤ K * (1 - ε) ^ (N / s) := by
  classical
  haveI := Matrix.neZero_of_trace_eq_one htr
  have hpd : (σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)).PosDef :=
    (Matrix.PosDef.transpose_iff.2 hσ).kronecker Matrix.PosDef.one
  obtain ⟨L, hL, hlip⟩ := hpd.isStrictlyPositive.exists_norm_sqrt_sub_sqrt_le
  refine ⟨L * (2 * D), by positivity,
    fun {d N M} A ℓ hN s hs hℓ ε hε hε1 hA hfix hchoi => ?_⟩
  let E : Fin M → Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    fun k => Kraus.transferMap (chainBlockTensor A hN k)
  have hwhole : Kraus.transferMap (MPSChainTensor.blockTensor A) = (List.ofFn E).prod := by
    rw [MPSChainTensor.transferMap_blockTensor]
    change (List.ofFn fun i => Kraus.transferMap (A i)).prod =
      (List.ofFn fun k => Kraus.transferMap (chainBlockTensor A hN k)).prod
    simp only [chainBlockTensor, MPSChainTensor.transferMap_blockTensor]
    exact prod_ofFn_blockSite ℓ hN (fun i => Kraus.transferMap (A i))
  let P := Matrix.tracePrepareMap (α := Fin D) σ
  let r : ℝ := 1 - ε
  let R (B : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) := B - (ε : ℂ) • P
  have hPtr : ∀ X, (P X).trace = X.trace := by
    intro X
    simp [P, Matrix.tracePrepareMap_trace, htr]
  have hRtr (B : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) (hB : IsTracePreservingMap B)
      (X : Matrix (Fin D) (Fin D) ℂ) : (R B X).trace = (r : ℂ) * X.trace := by
    simp only [R, LinearMap.sub_apply, LinearMap.smul_apply, Matrix.trace_sub,
      Matrix.trace_smul, smul_eq_mul, hB, hPtr]
    simp only [r, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hRprodtr : ∀ m (B : Fin m → Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)),
      (∀ i, IsTracePreservingMap (B i)) →
      ∀ X, (((List.ofFn fun i => R (B i)).prod) X).trace = (r : ℂ) ^ m * X.trace := by
    intro m
    induction m with
    | zero => intro B hB X; simp
    | succ m ih =>
      intro B hB X
      rw [List.ofFn_succ, List.prod_cons]
      change (R (B 0) (((List.ofFn fun i => R (B i.succ)).prod) X)).trace = _
      rw [hRtr _ (hB 0), ih _ (fun i => hB i.succ), pow_succ]
      ring
  have hdec : ∀ m (B : Fin m → Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)),
      (∀ i, IsTracePreservingMap (B i)) →
      (∀ i, B i σ = σ) → ∀ X,
      ((List.ofFn fun i => B i).prod) X =
        ((1 - r ^ m : ℝ) : ℂ) • (X.trace • σ) +
          ((List.ofFn fun i => R (B i)).prod) X := by
    intro m
    induction m with
    | zero => intro B hB hBfix X; simp
    | succ m ih =>
      intro B hB hBfix X
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
      change B 0
        (((List.ofFn fun i => B i.succ).prod) X) =
          _ + R (B 0) (((List.ofFn fun i => R (B i.succ)).prod) X)
      rw [ih _ (fun i => hB i.succ) (fun i => hBfix i.succ)]
      simp only [map_add, map_smul, hBfix]
      simp only [R, LinearMap.sub_apply, LinearMap.smul_apply, P, Matrix.tracePrepareMap_apply]
      rw [hRprodtr _ _ (fun i => hB i.succ)]
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast
      simp only [pow_succ, r, Complex.ofReal_sub, Complex.ofReal_one]
      ring
  have hRcp : ∀ i, IsCPMap (R (E i)) := by
    intro i
    apply (ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef _).2
    have hC : ChoiRectangular.choiMatrix (R (E i)) =
        ChoiRectangular.choiMatrix (E i) -
          ((ε : ℂ) / D) • (σ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
      rw [show R (E i) = E i - (ε : ℂ) • P from rfl,
        (ChoiRectangular.choiMatrixLinearMap (d := D) (d' := D)).map_sub,
        ChoiRectangular.choiMatrix_smul, P, Matrix.choiMatrix_tracePrepareMap, smul_smul]
      congr 2
      ring
    rw [hC]
    exact Matrix.le_iff.mp (hchoi i)
  have hprodcp : ∀ Ts : List (Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)),
      (∀ T ∈ Ts, IsCPMap T) → IsCPMap Ts.prod := by
    intro Ts
    induction Ts with
    | nil => intro h; exact isCPMap_id
    | cons T Ts ih =>
      intro h
      exact (h T (by simp)).comp (ih fun S hS => h S (by simp [hS]))
  let Q := (List.ofFn fun i => R (E i)).prod
  have hQcp : IsCPMap Q := hprodcp _ fun T hT => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hT
    exact hRcp i
  have htc : ∀ (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) (c : ℂ),
      (∀ X, (T X).trace = c * X.trace) → (ChoiRectangular.choiMatrix T).trace = c := by
    intro T c hT
    rw [ChoiRectangular.trace_choiMatrix]
    have ht := Matrix.trace_traceAdjointMap_mul T 1 1
    simp only [Matrix.mul_one, Matrix.one_mul] at ht
    rw [ht, hT, Matrix.trace_one, Fintype.card_fin]
    field_simp
  have hQtr : (ChoiRectangular.choiMatrix Q).trace = (r : ℂ) ^ M :=
    htc Q _ (hRprodtr M E hA)
  have hPctr : (ChoiRectangular.choiMatrix P).trace = 1 :=
    htc P 1 (fun X => by simpa using hPtr X)
  have hPcpos : (ChoiRectangular.choiMatrix P).PosSemidef := by
    rw [P, Matrix.choiMatrix_tracePrepareMap]
    exact (hσ.posSemidef.kronecker Matrix.PosSemidef.one).smul (by positivity)
  have hQcpos : (ChoiRectangular.choiMatrix Q).PosSemidef :=
    (ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef Q).1 hQcp
  have hnorm : ∀ {X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ},
      X.PosSemidef → ‖X‖ ≤ X.trace.re := by
    intro X hX
    have ht : X.trace.re = ∑ i, hX.isHermitian.eigenvalues i := by
      rw [hX.isHermitian.trace_eq_sum_eigenvalues]
      simp
    conv_lhs => rw [hX.isHermitian.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal]
    rw [ht]
    refine (pi_norm_le_iff_of_nonneg
      (Finset.sum_nonneg fun i _ => hX.eigenvalues_nonneg i)).2 ?_
    intro i
    simp only [Function.comp_apply, RCLike.norm_ofReal, abs_of_nonneg (hX.eigenvalues_nonneg i)]
    exact Finset.single_le_sum (fun j _ => hX.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hQnorm : ‖(ChoiRectangular.choiMatrix Q).transpose‖ ≤ r ^ M := by
    simpa only [Matrix.trace_transpose, hQtr, ← Complex.ofReal_pow, Complex.ofReal_re]
      using hnorm hQcpos.transpose
  have hPnorm : ‖(ChoiRectangular.choiMatrix P).transpose‖ ≤ 1 := by
    simpa [Matrix.trace_transpose, hPctr] using hnorm hPcpos.transpose
  have hmaps : Kraus.transferMap (MPSChainTensor.blockTensor A) =
      ((1 - r ^ M : ℝ) : ℂ) • P + Q := by
    rw [hwhole]
    ext X : 1
    exact hdec M E hA hfix X
  have hlim : (D : ℂ) • (ChoiRectangular.choiMatrix P).transpose =
      σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) := by
    rw [P, Matrix.choiMatrix_tracePrepareMap, Matrix.transpose_smul,
      ← Matrix.kroneckerMap_transpose, Matrix.transpose_one, smul_smul]
    simp [NeZero.ne D]
  have hgram : (physicalMatrix (MPSChainTensor.blockTensor A))ᴴ *
      physicalMatrix (MPSChainTensor.blockTensor A) - σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) =
      (D : ℂ) • ((ChoiRectangular.choiMatrix Q).transpose -
        ((r ^ M : ℝ) : ℂ) • (ChoiRectangular.choiMatrix P).transpose) := by
    rw [gram_eq_smul_choi_transpose, hmaps, ChoiRectangular.choiMatrix_add,
      ChoiRectangular.choiMatrix_smul, Matrix.transpose_add, Matrix.transpose_smul, ← hlim]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hbound : ‖(physicalMatrix (MPSChainTensor.blockTensor A))ᴴ *
      physicalMatrix (MPSChainTensor.blockTensor A) - σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤
      2 * D * r ^ M := by
    rw [hgram, norm_smul, Complex.norm_natCast]
    have hp : ‖((r ^ M : ℝ) : ℂ) • (ChoiRectangular.choiMatrix P).transpose‖ ≤ r ^ M := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (sub_nonneg.mpr hε1) M)]
      exact (mul_le_mul_of_nonneg_left hPnorm (pow_nonneg (sub_nonneg.mpr hε1) M)).trans_eq
        (mul_one _)
    have hb := norm_sub_le (ChoiRectangular.choiMatrix Q).transpose
      (((r ^ M : ℝ) : ℂ) • (ChoiRectangular.choiMatrix P).transpose)
    nlinarith [Nat.cast_nonneg (α := ℝ) D]
  have hNs : N ≤ M * s := by
    rw [← hN]
    calc ∑ k, ℓ k ≤ ∑ _ : Fin M, s := Finset.sum_le_sum (fun k _ => hℓ k)
      _ = M * s := by simp
  have hcount : N / s ≤ M := by
    calc N / s ≤ (M * s) / s := Nat.div_le_div_right hNs
      _ = M := Nat.mul_div_left M hs
  have hpow : r ^ M ≤ r ^ (N / s) :=
    pow_le_pow_of_le_one (sub_nonneg.mpr hε1) (by dsimp [r]; linarith) hcount
  have hfinal := hbound.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  refine ⟨hfinal, ?_⟩
  have hsqrt := hlip _
    (Matrix.posSemidef_conjTranspose_mul_self
      (physicalMatrix (MPSChainTensor.blockTensor A))).nonneg
  rw [sqrt_transpose_kronecker_one hσ.posSemidef] at hsqrt
  exact hsqrt.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hfinal hL)

end MPSPreparation
