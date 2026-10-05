/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.InhomogeneousDoeblin
import TNLean.MPS.Preparation.BlockIsometryState
import TNLean.MPS.Preparation.SecondOrderOverlap
import QICLean.Channel.Semigroup.CPClosure

/-!
# Residual Choi bounds for actual inhomogeneous blocks

The minorizing density and its strength may vary between actual blocks. Removing the
trace-prepare part leaves a completely positive residual with a known trace scale. On
traceless inputs the ordered original and residual products coincide. Consequently the
whole blocked Gram matrix is close to the reset Gram matrix of any transported input
density, without a common fixed point or a lower eigenvalue bound.

This is a quantitative sufficient-condition argument for arXiv:2307.01696, paragraph
"Inhomogeneous short-range correlated MPS", using the normalized Choi convention in Wolf,
*Quantum Channels & Operations*, Theorem 8.17. The source's qualitative definition does
not imply these minorization hypotheses; see `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

## References

* Wolf, *Quantum Channels & Operations*, Proposition 2.1, Theorem 8.17, and Eq. (8.86).
* arXiv:2307.01696, eq. (8) and paragraph "Inhomogeneous short-range correlated MPS".
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
    simp only [R, LinearMap.sub_apply, LinearMap.smul_apply, Matrix.trace_sub,
      Matrix.trace_smul, smul_eq_mul, hB X, Matrix.tracePrepareMap_trace, hω, mul_one]
    push_cast
    ring
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
    apply (ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef _).2
    have hC : ChoiRectangular.choiMatrix (R (E i) (ε i) (τ i)) =
        ChoiRectangular.choiMatrix (E i) -
          ((ε i : ℂ) / D) • (τ i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
      change ChoiRectangular.choiMatrixLinearMap (E i - (ε i : ℂ) •
        Matrix.tracePrepareMap (α := Fin D) (τ i)) = _
      rw [map_sub, map_smul]
      change _ - (ε i : ℂ) • ChoiRectangular.choiMatrix
        (Matrix.tracePrepareMap (α := Fin D) (τ i)) = _
      rw [Matrix.choiMatrix_tracePrepareMap, smul_smul]
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
  have hQnorm : ‖(ChoiRectangular.choiMatrix Q).transpose‖ ≤ t := by
    simpa only [Matrix.trace_transpose, hQctr, Complex.ofReal_re] using hnorm hQcpos.transpose
  have hPnorm : ‖(ChoiRectangular.choiMatrix P).transpose‖ ≤ t := by
    simpa only [Matrix.trace_transpose, hPctr, Complex.ofReal_re] using hnorm hPcpos.transpose
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
