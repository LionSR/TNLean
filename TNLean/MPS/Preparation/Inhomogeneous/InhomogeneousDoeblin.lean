/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Chain.BlockTensor
import QICLean.Channel.Choi.Doeblin
import TNLean.MPS.CanonicalForm.FixedPointApproximation.PositivePartRate
import TNLean.MPS.Transfer.RenormalizationFixedPoint.BlockIsometryState
import TNLean.MPS.CanonicalForm.FixedPointApproximation.SecondOrderOverlap
import QICLean.Channel.Semigroup.CPClosure
import QICLean.Channel.KrausMap.ChoiResidual

/-!
# Uniform contraction along an inhomogeneous chain

A common lower bound on the Choi matrices of the actual site maps gives a uniform exponential
contraction for their ordered products. The sites may themselves be fixed-length contiguous
blocks. Separate spectral gaps of the individual maps are not used: they do not control
products of different maps.

The contraction step reuses the quantum Doeblin theorem from QICLean. Its tensor interpretation
uses the exact transfer map of the blocked chain, not a power of any one site map.

## Main result

* `MPSChainTensor.traceNorm_transferMap_blockTensor_sub_le_of_choi_domination`: a uniform
  `n`-step trace-distance contraction derived from actual Choi domination.

## References

* Wolf, *Quantum Channels & Operations*, Theorem 8.17 (quantum Doeblin).
* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS".

## Residual Choi bounds for actual inhomogeneous blocks

The minorizing density and its strength may vary between actual blocks. Removing the
trace-prepare part leaves a completely positive residual with a known trace scale. On
traceless inputs the ordered original and residual products coincide. Consequently the
whole blocked Gram matrix is close to the reset Gram matrix of any transported input
density, without a common fixed point or a lower eigenvalue bound.

This is a quantitative sufficient-condition argument for arXiv:2307.01696, paragraph
"Inhomogeneous short-range correlated MPS", using the normalized Choi convention in Wolf,
*Quantum Channels & Operations*, Theorem 8.17. The source's qualitative definition does
not imply these minorization hypotheses; see `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

### References

* Wolf, *Quantum Channels & Operations*, Proposition 2.1, Theorem 8.17, and Eq. (8.86).
* arXiv:2307.01696, eq. (8) and paragraph "Inhomogeneous short-range correlated MPS".

## Uniform positive-part rates from Choi domination

The normalized Choi matrix of the transfer map is the transpose of the blocked physical
Gram matrix divided by the bond dimension. A uniform Choi lower bound on the actual
inhomogeneous site maps, together with a common faithful fixed state, yields a Gram error
at most `2D (1 - ε)^(N/s)` on a chain partitioned into actual contiguous blocks of at most
`s` sites. The square-root Lipschitz estimate at the faithful limiting Gram matrix gives
the same exponential rate for the positive polar factor. The quotient `N/s` is rounded down.

The sites may be fixed-length contiguous blocks, but the domination hypothesis must then
hold for the transfer maps of those actual blocks. Individual microscopic spectral gaps
are not a replacement for this hypothesis.

### Main results

* `gram_eq_smul_choi_transpose`: the exact bond-dimension normalization and index order.
* `exists_norm_polarPos_chainBlockTensor_sub_le_of_choi_domination`: uniform Gram and polar
  bounds from actual contiguous-block domination and a common faithful fixed state.

### References

* arXiv:2307.01696, eq. (8) and paragraph "Inhomogeneous short-range correlated MPS".
* Wolf, *Quantum Channels & Operations*, Theorem 8.17 (quantum Doeblin).
* arXiv:2103.13367, Supplemental Material, equations (19), (21), and (26).
-/

section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace MPSChainTensor

variable {d D n : ℕ}

/-- The blocked chain has a trace-preserving transfer map when every site map does. -/
theorem trace_transferMap_blockTensor (A : MPSChainTensor d D n)
    (hA : ∀ i, IsTracePreservingMap (Kraus.transferMap (A i)))
    (X : Matrix (Fin D) (Fin D) ℂ) :
    (Kraus.transferMap (blockTensor A) X).trace = X.trace := by
  induction n with
  | zero => simp [transferMap_blockTensor]
  | succ n ih =>
    rw [transferMap_blockTensor, List.ofFn_succ, List.prod_cons]
    change (Kraus.transferMap (A 0)
      (((List.ofFn fun i => Kraus.transferMap (A i.succ)).prod) X)).trace = _
    rw [hA 0, ← transferMap_blockTensor]
    exact ih _ (fun i => hA i.succ)

/-- **Uniform Doeblin contraction on a chain.** If every site's normalized Choi matrix
uniformly dominates `ε/D` times `σ ⊗ I`, where `σ` is a density matrix and `0 ≤ ε ≤ 1`,
then the transfer map of the whole `n`-site block contracts the trace distance of density
matrices by at least the factor `(1 - ε)^n`. No translation invariance is assumed.

When each site is a fixed-length contiguous block, the condition is imposed on those actual
blocks, not on powers of the individual microscopic site maps. -/
theorem traceNorm_transferMap_blockTensor_sub_le_of_choi_domination
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    (A : MPSChainTensor d D n)
    (hA : ∀ i, IsTracePreservingMap (Kraus.transferMap (A i)))
    (hchoi : ∀ i, ChoiRectangular.choiMatrix (Kraus.transferMap (A i)) ≥
      ((ε : ℂ) / D) • (σ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)))
    {ρ₁ ρ₂ : Matrix (Fin D) (Fin D) ℂ} (h₁ : ρ₁.PosSemidef)
    (h₂ : ρ₂.PosSemidef) (h₁tr : ρ₁.trace = 1) (h₂tr : ρ₂.trace = 1) :
    traceNorm (Kraus.transferMap (blockTensor A) ρ₁ -
      Kraus.transferMap (blockTensor A) ρ₂) ≤
      (1 - ε) ^ n * traceNorm (ρ₁ - ρ₂) := by
  induction n with
  | zero => simp [transferMap_blockTensor]
  | succ n ih =>
    let B : MPSChainTensor d D n := fun i => A i.succ
    have hB : ∀ i, IsTracePreservingMap (Kraus.transferMap (B i)) := fun i => hA i.succ
    have hhead : Kraus.transferMap (blockTensor A) =
        Kraus.transferMap (A 0) * Kraus.transferMap (blockTensor B) := by
      rw [transferMap_blockTensor, transferMap_blockTensor, List.ofFn_succ, List.prod_cons]
    rw [hhead]
    change traceNorm (Kraus.transferMap (A 0) (Kraus.transferMap (blockTensor B) ρ₁) -
      Kraus.transferMap (A 0) (Kraus.transferMap (blockTensor B) ρ₂)) ≤ _
    have hstep := traceNorm_map_sub_map_le_of_choi_domination (hA 0)
      (fun X hX => isHermitian_map_of_positive
        (fun Y hY => Kraus.transferMap_pos (A 0) hY) hX)
      hσ.isHermitian htr hε (hchoi 0)
      (Kraus.transferMap_pos (blockTensor B) h₁)
      (Kraus.transferMap_pos (blockTensor B) h₂)
      ((trace_transferMap_blockTensor B hB ρ₁).trans h₁tr)
      ((trace_transferMap_blockTensor B hB ρ₂).trans h₂tr)
    have htail := ih B hB (fun i => hchoi i.succ)
    calc _ ≤ (1 - ε) * traceNorm (Kraus.transferMap (blockTensor B) ρ₁ -
        Kraus.transferMap (blockTensor B) ρ₂) := hstep
      _ ≤ (1 - ε) * ((1 - ε) ^ n * traceNorm (ρ₁ - ρ₂)) :=
        mul_le_mul_of_nonneg_left htail (sub_nonneg.mpr hε1)
      _ = _ := by rw [pow_succ]; ring

end MPSChainTensor

end

section

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
  field_simp [NeZero.ne D]

/-- Actual blockwise Choi minorization gives a Gram bound relative to the transported
input density. The factors `1-ε_j` multiply. Only trace one is required of the minorizing matrices
for this algebraic bound; in particular density references may be singular and need not be
stationary or equal to one another. All Choi matrices are normalized by `1/D`. -/
theorem norm_gram_blockTensor_sub_transport_le_of_choi_domination
    {d D N M : ℕ} (A : MPSChainTensor d D N)
    (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N)
    (ε : Fin M → ℝ)
    (τ : Fin M → Matrix (Fin D) (Fin D) ℂ)
    (hτtr : ∀ j, (τ j).trace = 1)
    (htp : ∀ j, IsTracePreservingMap (Kraus.transferMap (chainBlockTensor A hN j)))
    (hchoi : ∀ j, ChoiRectangular.choiMatrix (Kraus.transferMap (chainBlockTensor A hN j)) ≥
      ((ε j : ℂ) / D) • (τ j ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)))
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1) :
    ‖(physicalMatrix (MPSChainTensor.blockTensor A))ᴴ *
        physicalMatrix (MPSChainTensor.blockTensor A) -
      (Kraus.transferMap (MPSChainTensor.blockTensor A) ρ)ᵀ ⊗ₖ
        (1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤ 2 * D * ∏ j, (1 - ε j) := by
  classical
  have := Matrix.neZero_of_trace_eq_one hρtr
  let E : Fin M → Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    fun j => Kraus.transferMap (chainBlockTensor A hN j)
  have hwhole : Kraus.transferMap (MPSChainTensor.blockTensor A) = (List.ofFn E).prod := by
    rw [MPSChainTensor.transferMap_blockTensor]
    change (List.ofFn fun i => Kraus.transferMap (A i)).prod =
      (List.ofFn fun j => Kraus.transferMap (chainBlockTensor A hN j)).prod
    simp only [chainBlockTensor, MPSChainTensor.transferMap_blockTensor]
    exact prod_ofFn_blockSite ℓ hN (fun i => Kraus.transferMap (A i))
  let R (B : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) (e : ℝ)
      (ω : Matrix (Fin D) (Fin D) ℂ) := B - (e : ℂ) • Matrix.tracePrepareMap (α := Fin D) ω
  have hRtr (B : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
      (hB : IsTracePreservingMap B) (e : ℝ) (ω : Matrix (Fin D) (Fin D) ℂ)
      (hω : ω.trace = 1) (X : Matrix (Fin D) (Fin D) ℂ) :
      (R B e ω X).trace = ((1 - e : ℝ) : ℂ) * X.trace := by
    exact Matrix.trace_sub_smul_tracePrepareMap B hB ω hω e X
  have hprodtr : ∀ m (B : Fin m → Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)),
      (∀ i, IsTracePreservingMap (B i)) → ∀ X,
        (((List.ofFn B).prod) X).trace = X.trace := by
    intro m
    induction m with
    | zero => intro B hB X; simp
    | succ m ih =>
      intro B hB X
      rw [List.ofFn_succ, List.prod_cons]
      exact (hB 0 _).trans (ih _ (fun i => hB i.succ) X)
  have hRprodtr : ∀ m (B : Fin m → Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
      (e : Fin m → ℝ) (ω : Fin m → Matrix (Fin D) (Fin D) ℂ),
      (∀ i, IsTracePreservingMap (B i)) → (∀ i, (ω i).trace = 1) → ∀ X,
      (((List.ofFn fun i => R (B i) (e i) (ω i)).prod) X).trace =
        ((∏ i, (1 - e i) : ℝ) : ℂ) * X.trace := by
    intro m
    induction m with
    | zero => intro B e ω hB hω X; simp
    | succ m ih =>
      intro B e ω hB hω X
      rw [List.ofFn_succ, List.prod_cons]
      change (R (B 0) (e 0) (ω 0)
        (((List.ofFn fun i => R (B i.succ) (e i.succ) (ω i.succ)).prod) X)).trace = _
      rw [hRtr _ (hB 0) _ _ (hω 0), ih _ _ _ (fun i => hB i.succ) (fun i => hω i.succ),
        Fin.prod_univ_succ]
      push_cast
      ring
  have hzero : ∀ m (B : Fin m → Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
      (e : Fin m → ℝ) (ω : Fin m → Matrix (Fin D) (Fin D) ℂ),
      (∀ i, IsTracePreservingMap (B i)) → ∀ X, X.trace = 0 →
      ((List.ofFn fun i => R (B i) (e i) (ω i)).prod) X = ((List.ofFn B).prod) X := by
    intro m
    induction m with
    | zero => intro B e ω hB X hX; simp
    | succ m ih =>
      intro B e ω hB X hX
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
      change R (B 0) (e 0) (ω 0)
          (((List.ofFn fun i => R (B i.succ) (e i.succ) (ω i.succ)).prod) X) =
        B 0 (((List.ofFn fun i => B i.succ).prod) X)
      rw [ih _ _ _ (fun i => hB i.succ) X hX]
      simp [R, Matrix.tracePrepareMap_apply, hprodtr _ _ (fun i => hB i.succ), hX]
  let Q := (List.ofFn fun i => R (E i) (ε i) (τ i)).prod
  have hRcp : ∀ i, IsCPMap (R (E i) (ε i) (τ i)) := by
    intro i
    exact Matrix.isKrausCP_sub_smul_tracePrepareMap_of_choi_domination
      (E i) (τ i) (ε i) (hchoi i)
  have hprodcp : ∀ Ts : List (Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)),
      (∀ T ∈ Ts, IsCPMap T) → IsCPMap Ts.prod := by
    intro Ts
    induction Ts with
    | nil => intro h; exact isCPMap_id
    | cons T Ts ih =>
      intro h
      exact (h T (by simp)).comp (ih fun S hS => h S (by simp [hS]))
  have hQcp : IsCPMap Q := hprodcp _ fun T hT => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hT
    exact hRcp i
  let t : ℝ := ∏ j, (1 - ε j)
  have hQtr : ∀ X, (Q X).trace = (t : ℂ) * X.trace := hRprodtr M E ε τ htp hτtr
  let P := Matrix.tracePrepareMap (α := Fin D) (Q ρ)
  have hmaps : Kraus.transferMap (MPSChainTensor.blockTensor A) -
      Matrix.tracePrepareMap (α := Fin D) (Kraus.transferMap (MPSChainTensor.blockTensor A) ρ) =
        Q - P := by
    ext X : 1
    have hX : (X - X.trace • ρ).trace = 0 := by simp [hρtr]
    have h := hzero M E ε τ htp (X - X.trace • ρ) hX
    rw [← hwhole] at h
    simpa only [map_sub, map_smul, LinearMap.sub_apply, Matrix.tracePrepareMap_apply, P]
      using h.symm
  have htc : ∀ (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) (c : ℂ),
      (∀ X, (T X).trace = c * X.trace) → (ChoiRectangular.choiMatrix T).trace = c := by
    intro T c hT
    rw [ChoiRectangular.trace_choiMatrix]
    have ht := Matrix.trace_traceAdjointMap_mul T 1 1
    simp only [Matrix.mul_one, Matrix.one_mul] at ht
    rw [ht, hT, Matrix.trace_one, Fintype.card_fin]
    field_simp [NeZero.ne D]
  have hQctr : (ChoiRectangular.choiMatrix Q).trace = (t : ℂ) := htc Q _ hQtr
  have hPctr : (ChoiRectangular.choiMatrix P).trace = (t : ℂ) := by
    apply htc P
    intro X
    simp [P, hQtr, hρtr, mul_comm]
  have hPcpos : (ChoiRectangular.choiMatrix P).PosSemidef := by
    dsimp only [P]
    rw [Matrix.choiMatrix_tracePrepareMap]
    exact ((hQcp.isPositiveMap ρ hρ).kronecker Matrix.PosSemidef.one).smul (by positivity)
  have hQcpos : (ChoiRectangular.choiMatrix Q).PosSemidef :=
    (ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef Q).1 hQcp
  have hQnorm : ‖(ChoiRectangular.choiMatrix Q).transpose‖ ≤ t := by
    simpa only [Matrix.trace_transpose, hQctr, Complex.ofReal_re] using
      hQcpos.transpose.l2_opNorm_le_trace_re
  have hPnorm : ‖(ChoiRectangular.choiMatrix P).transpose‖ ≤ t := by
    simpa only [Matrix.trace_transpose, hPctr, Complex.ofReal_re] using
      hPcpos.transpose.l2_opNorm_le_trace_re
  have hlim (ω : Matrix (Fin D) (Fin D) ℂ) :
      (D : ℂ) • (ChoiRectangular.choiMatrix (Matrix.tracePrepareMap (α := Fin D) ω)).transpose =
        ωᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) := by
    rw [Matrix.choiMatrix_tracePrepareMap, Matrix.transpose_smul,
      ← Matrix.kroneckerMap_transpose, Matrix.transpose_one, smul_smul]
    simp [NeZero.ne D]
  have hgram : (physicalMatrix (MPSChainTensor.blockTensor A))ᴴ *
      physicalMatrix (MPSChainTensor.blockTensor A) -
      (Kraus.transferMap (MPSChainTensor.blockTensor A) ρ)ᵀ ⊗ₖ
        (1 : Matrix (Fin D) (Fin D) ℂ) =
      (D : ℂ) • ((ChoiRectangular.choiMatrix Q).transpose -
        (ChoiRectangular.choiMatrix P).transpose) := by
    rw [gram_eq_smul_choi_transpose, ← hlim, ← smul_sub, ← Matrix.transpose_sub]
    change (D : ℂ) • (ChoiRectangular.choiMatrixLinearMap _ -
      ChoiRectangular.choiMatrixLinearMap _).transpose = _
    rw [← map_sub, hmaps, map_sub, Matrix.transpose_sub]
    rfl
  rw [hgram, norm_smul, Complex.norm_natCast]
  have hb := norm_sub_le (ChoiRectangular.choiMatrix Q).transpose
    (ChoiRectangular.choiMatrix P).transpose
  dsimp only [t] at hQnorm hPnorm
  nlinarith [Nat.cast_nonneg (α := ℝ) D]

end MPSPreparation

end

section

open Matrix MPSTensor
open scoped BigOperators ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace MPSPreparation

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
  have := Matrix.neZero_of_trace_eq_one htr
  have hpd : (σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)).PosDef :=
    (Matrix.PosDef.transpose_iff.2 hσ).kronecker Matrix.PosDef.one
  obtain ⟨L, hL, hlip⟩ := hpd.isStrictlyPositive.exists_norm_sqrt_sub_sqrt_le
  refine ⟨L * (2 * D), by positivity,
    fun {d N M} A ℓ hN s hs hℓ ε hε hε1 hA hfix hchoi => ?_⟩
  let E : Fin M → Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    fun j => Kraus.transferMap (chainBlockTensor A hN j)
  have hwhole : Kraus.transferMap (MPSChainTensor.blockTensor A) = (List.ofFn E).prod := by
    rw [MPSChainTensor.transferMap_blockTensor]
    change (List.ofFn fun i => Kraus.transferMap (A i)).prod =
      (List.ofFn fun j => Kraus.transferMap (chainBlockTensor A hN j)).prod
    simp only [chainBlockTensor, MPSChainTensor.transferMap_blockTensor]
    exact prod_ofFn_blockSite ℓ hN (fun i => Kraus.transferMap (A i))
  have hfixed : Kraus.transferMap (MPSChainTensor.blockTensor A) σ = σ := by
    rw [hwhole]
    have hp : ∀ Ts : List (Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)),
        (∀ T ∈ Ts, T σ = σ) → Ts.prod σ = σ := by
      intro Ts
      induction Ts with
      | nil => intro h; rfl
      | cons T Ts ih =>
        intro h
        change T (Ts.prod σ) = σ
        rw [ih fun S hS => h S (by simp [hS])]
        exact h T (by simp)
    exact hp _ fun T hT => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hT
      exact hfix j
  let r : ℝ := 1 - ε
  have hbound := norm_gram_blockTensor_sub_transport_le_of_choi_domination A ℓ hN
    (fun _ => ε) (fun _ => σ) (fun _ => htr) hA hchoi σ hσ.posSemidef htr
  rw [hfixed, Fin.prod_const] at hbound
  have hNs : N ≤ M * s := by
    rw [← hN]
    calc ∑ k, ℓ k ≤ ∑ _ : Fin M, s := Finset.sum_le_sum (fun k _ => hℓ k)
      _ = M * s := by simp
  have hcount : N / s ≤ M := by
    calc N / s ≤ (M * s) / s := Nat.div_le_div_right hNs
      _ = M := Nat.mul_div_left M hs
  have hpow : r ^ M ≤ r ^ (N / s) :=
    pow_le_pow_of_le_one (sub_nonneg.mpr hε1) (sub_le_self 1 hε) hcount
  have hfinal := hbound.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  refine ⟨hfinal, ?_⟩
  have hsqrt := hlip _
    (Matrix.posSemidef_conjTranspose_mul_self
      (physicalMatrix (MPSChainTensor.blockTensor A))).nonneg
  rw [sqrt_transpose_kronecker_one hσ.posSemidef] at hsqrt
  exact hsqrt.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hfinal hL)

end MPSPreparation

end
