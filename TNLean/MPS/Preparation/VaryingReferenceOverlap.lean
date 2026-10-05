/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.InhomogeneousApproximationError

/-!
# Ordered overlap with varying density-matrix references

The reference density matrices may vary between blocks and may be singular. The global
square-root Hölder estimate gives constants uniform over all references of trace one.
The pair on the bond leaving block `j` uses the reference of the following block.

**Scope restriction (ordered mixing):** these are quantitative sufficient conditions for
arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS". They assume
ordered-product estimates on a fixed square bond space; they do not infer those estimates
from qualitative finite correlation. See `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

## References

* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS".
* arXiv:2103.13367, Supplemental Material, eq. (26) and proof of Theorem MPS_classification.
-/

open Matrix MPSTensor
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Kronecker
  Matrix.Norms.L2Operator

namespace MPSPreparation

/-- The positive-polar error has a uniform square-root bound over all positive semidefinite
references, including singular ones. The constant depends only on the bond dimension. -/
theorem exists_norm_polarPos_sub_le_sqrt_transferMatrix (D : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {d : ℕ} (A : MPSTensor d D)
      (σ : Matrix (Fin D) (Fin D) ℂ), σ.PosSemidef →
      ‖Matrix.polarPos (physicalMatrix A) -
          (CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤
        K * Real.sqrt ‖transferMatrix (Kraus.transferMap A) -
          transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ := by
  classical
  obtain ⟨K, hK, hgram⟩ := exists_norm_gram_transferMatrix_sub_le D
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, fun {d} A σ hσ => ?_⟩
  have hsqrt := CFC.norm_sqrt_sub_sqrt_le
    (Matrix.posSemidef_conjTranspose_mul_self (physicalMatrix A)).nonneg
    (hσ.transpose.kronecker Matrix.PosSemidef.one).nonneg
  rw [sqrt_transpose_kronecker_one hσ] at hsqrt
  refine hsqrt.trans ?_
  calc Real.sqrt ‖(physicalMatrix A)ᴴ * physicalMatrix A -
          σᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)‖
      ≤ Real.sqrt (K * ‖transferMatrix (Kraus.transferMap A) -
          transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖) :=
        Real.sqrt_le_sqrt (hgram A σ hσ).1
    _ = _ := Real.sqrt_mul hK.le _

/-- Site-dependent fixed-point tensors give the nearest-neighbor pair of the *following*
site on each outgoing bond. This cyclic shift is invisible in the constant-reference case. -/
theorem mpvFamily_fixedPointTensor {D M : ℕ} [NeZero M]
    (σ : Fin M → Matrix (Fin D) (Fin D) ℂ) (τ : Fin M → Fin (D * D)) :
    mpvFamily (fun j => fixedPointTensor (σ j)) τ =
      pairFamilyState (fun j => fixedPointPair (σ (finRotate M j)))
        (fun j => finProdFinEquiv.symm (τ j)) := by
  classical
  obtain ⟨L, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
  set S := fun j => CFC.sqrt (σ j)
  set l := fun j => (finProdFinEquiv.symm (τ j)).1
  set r := fun j => (finProdFinEquiv.symm (τ j)).2
  have hletter : ∀ j, fixedPointTensor (σ j) (τ j) =
      S j * Matrix.single (l j) (r j) (1 : ℂ) := fun _ => rfl
  have hentry (j : Fin (L + 1)) (a b : Fin D) :
      (S j * Matrix.single (l j) (r j) (1 : ℂ)) a b =
        if b = r j then S j a (l j) else 0 := by
    split_ifs with h
    · subst b; simp
    · exact Matrix.mul_single_apply_of_ne (hbj := h) ..
  rw [mpvFamily, Matrix.trace_ofFn_prod_eq_sum_cyclic]
  simp only [hletter, hentry]
  rw [Finset.sum_eq_single (fun j => r ((finRotate (L + 1)).symm j))]
  · simp only [Equiv.symm_apply_apply, ite_true]
    rw [pairFamilyState]
    exact (Fintype.prod_equiv (finRotate (L + 1)) _ _ (fun j => by
      simp only [Equiv.symm_apply_apply]; rfl)).symm
  · intro t _ ht
    have : ∃ j, t (finRotate (L + 1) j) ≠ r j := by
      by_contra h
      push Not at h
      exact ht (funext fun j => by simpa using h ((finRotate (L + 1)).symm j))
    obtain ⟨j, hj⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right_iff.2 fun h => absurd h hj)
  · simp

/-- The overlap of two inhomogeneous periodic tensor families is the trace of the ordered
mixed-transfer product. -/
theorem sum_mpvFamily_mul_star_mpvFamily {D M κ : ℕ} [NeZero M]
    (X Y : Fin M → MPSTensor κ D) :
    ∑ u : Fin M → Fin κ, mpvFamily X u * star (mpvFamily Y u) =
      Matrix.trace (List.ofFn fun j => transferMatrix (Kraus.mixedMapLM (X j) (Y j))).prod := by
  classical
  obtain ⟨L, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
  rw [Matrix.trace_ofFn_prod_eq_sum_cyclic]
  simp_rw [transferMatrix_mixedMapLM_apply, Fintype.prod_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [mpvFamily, Matrix.trace_ofFn_prod_eq_sum_cyclic, mpvFamily,
    Matrix.trace_ofFn_prod_eq_sum_cyclic, star_sum, Finset.sum_mul_sum,
    ← (Equiv.arrowProdEquivProdArrow (Fin (L + 1)) (fun _ => Fin D) (fun _ => Fin D)).symm.sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [star_prod, ← Finset.prod_mul_distrib]
  rfl

private theorem exists_uniform_reference_bounds (D : ℕ) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ σ : Matrix (Fin D) (Fin D) ℂ,
      σ.PosSemidef → σ.trace = 1 →
      ‖transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤ c ∧
      ‖LinearMap.toContinuousLinearMap
        (transferMatrixLM ∘ₗ mixedMapLMLeft (fixedPointTensor σ) ∘ₗ
          (ofPhysicalMatrixLM (D := D)))‖ ≤ c := by
  classical
  let F (S : Matrix (Fin D) (Fin D) ℂ) : MPSTensor (D * D) D := fun i =>
    Sᴴ * Matrix.single (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 (1 : ℂ)
  let L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      (Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ →L[ℂ]
        Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :=
    { toFun := fun S => LinearMap.toContinuousLinearMap
        (transferMatrixLM ∘ₗ mixedMapLMLeft (F S) ∘ₗ ofPhysicalMatrixLM)
      map_add' := by
        intro S T
        apply ContinuousLinearMap.ext
        intro G
        change transferMatrixLM (Kraus.mixedMapLM (ofPhysicalMatrixLM G) (F (S + T))) =
          transferMatrixLM (Kraus.mixedMapLM (ofPhysicalMatrixLM G) (F S)) +
            transferMatrixLM (Kraus.mixedMapLM (ofPhysicalMatrixLM G) (F T))
        rw [← map_add]
        congr 1
        ext X : 1
        simp [F, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.mul_add,
          Matrix.add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro z S
        apply ContinuousLinearMap.ext
        intro G
        change transferMatrixLM (Kraus.mixedMapLM (ofPhysicalMatrixLM G) (F (z • S))) =
          z • transferMatrixLM (Kraus.mixedMapLM (ofPhysicalMatrixLM G) (F S))
        rw [← map_smul]
        congr 1
        ext X : 1
        simp [F, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Finset.smul_sum] }
  let Lc := LinearMap.toContinuousLinearMap L
  let R : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
    { toFun := fun σ => transferMatrix ((Matrix.traceLinearMap (Fin D) ℂ ℂ).smulRight σ)
      map_add' := by intro S T; ext a b; simp [transferMatrix, mul_add]
      map_smul' := by intro z S; ext a b; simp [transferMatrix, mul_comm, mul_assoc] }
  let Rc := LinearMap.toContinuousLinearMap R
  obtain ⟨B, hB⟩ := (densityMatrices_isCompact (D := D)).isBounded.exists_norm_le
  let c := 1 + ‖Rc‖ * |B| + ‖Lc‖ * Real.sqrt |B|
  have hRpos : 0 ≤ ‖Rc‖ * |B| := by positivity
  have hLpos : 0 ≤ ‖Lc‖ * Real.sqrt |B| := by positivity
  refine ⟨c, by dsimp [c]; linarith, fun σ hσ htr => ?_⟩
  have hn : ‖σ‖ ≤ |B| := (hB σ ⟨hσ, htr⟩).trans (le_abs_self B)
  constructor
  · have heq : transferMatrix (Kraus.transferMap (fixedPointTensor σ)) = Rc σ := by
      change transferMatrix (Kraus.transferMap (fixedPointTensor σ)) =
        transferMatrix ((Matrix.traceLinearMap (Fin D) ℂ ℂ).smulRight σ)
      congr 1
      exact LinearMap.ext fun X => transferMap_fixedPointTensor_apply hσ X
    rw [heq]
    exact (Rc.le_opNorm σ).trans ((mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans
      (by dsimp [c]; linarith))
  · have hF : F (CFC.sqrt σ) = fixedPointTensor σ := by
      funext i
      dsimp [F, fixedPointTensor]
      rw [(Matrix.isHermitian_iff_isSelfAdjoint.mpr (CFC.sqrt_nonneg σ).isSelfAdjoint).eq]
    rw [← hF]
    change ‖Lc (CFC.sqrt σ)‖ ≤ c
    have hs : ‖CFC.sqrt σ‖ ≤ Real.sqrt |B| := by
      rw [CFC.norm_sqrt σ hσ.nonneg]
      exact Real.sqrt_le_sqrt hn
    exact (Lc.le_opNorm _).trans ((mul_le_mul_of_nonneg_left hs (norm_nonneg _)).trans
      (by dsimp [c]; linarith))

private theorem transferMatrix_fixedPointTensor_mul {D : ℕ}
    {σ τ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosSemidef)
    (hτ : τ.PosSemidef) (htr : τ.trace = 1) :
    transferMatrix (Kraus.transferMap (fixedPointTensor σ)) *
      transferMatrix (Kraus.transferMap (fixedPointTensor τ)) =
        transferMatrix (Kraus.transferMap (fixedPointTensor σ)) := by
  rw [← transferMatrix_comp]
  congr 1
  ext X : 1
  simp only [LinearMap.comp_apply, transferMap_fixedPointTensor_apply hσ,
    transferMap_fixedPointTensor_apply hτ, Matrix.trace_smul, htr, smul_eq_mul, mul_one]

private theorem prod_range_transferMatrix_fixedPointTensor {D : ℕ}
    (σ : ℕ → Matrix (Fin D) (Fin D) ℂ) (hσ : ∀ j, (σ j).PosSemidef)
    (htr : ∀ j, (σ j).trace = 1) (n : ℕ) :
    ((List.range (n + 1)).map (fun j =>
      transferMatrix (Kraus.transferMap (fixedPointTensor (σ j))))).prod =
        transferMatrix (Kraus.transferMap (fixedPointTensor (σ 0))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, ih]
    exact transferMatrix_fixedPointTensor_mul (hσ _) (hσ _) (htr _)

/-- Uniform overlap control for singular, site-dependent density references. The square-root
loss comes from the global Hölder estimate; no minimum eigenvalue is assumed. -/
theorem exists_norm_trace_prod_polarPos_sub_one_le_varying_reference (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : ℕ} [NeZero M] (d : Fin M → ℕ)
      (A : ∀ j, MPSTensor (d j) D) (σ : Fin M → Matrix (Fin D) (Fin D) ℂ),
      (∀ j, (σ j).PosSemidef) → (∀ j, (σ j).trace = 1) → ∀ {δ : ℝ}, 0 ≤ δ →
      (∀ j, ‖transferMatrix (Kraus.transferMap (A j)) -
        transferMatrix (Kraus.transferMap (fixedPointTensor (σ j)))‖ ≤ δ) →
      ‖Matrix.trace (List.ofFn fun j => transferMatrix
          (Kraus.mixedMapLM (polarPosTensor (A j)) (fixedPointTensor (σ j)))).prod - 1‖ ≤
        C * (M * Real.sqrt δ) * Real.exp (C * (M * Real.sqrt δ)) := by
  classical
  obtain ⟨Kp, hKp, hp⟩ := exists_norm_polarPos_sub_le_sqrt_transferMatrix D
  obtain ⟨c, hc, hb⟩ := exists_uniform_reference_bounds D
  let trL := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ)
  let K := c * (c * Kp)
  have hc0 : 0 ≤ c := by linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let C := ‖trL‖ * c * K + K + 1
  refine ⟨C, by dsimp [C]; positivity, fun {M} _ d A σ hσ htr δ hδ hA => ?_⟩
  have := Matrix.neZero_of_trace_eq_one (htr 0)
  let ρ : ℕ → Matrix (Fin D) (Fin D) ℂ := fun j =>
    if h : j < M then σ ⟨j, h⟩ else σ 0
  have hρ (j : ℕ) : (ρ j).PosSemidef := by dsimp [ρ]; split_ifs <;> apply hσ
  have hρtr (j : ℕ) : (ρ j).trace = 1 := by dsimp [ρ]; split_ifs <;> apply htr
  let Y : ℕ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun j =>
    transferMatrix (Kraus.transferMap (fixedPointTensor (ρ j)))
  let X : ℕ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun j =>
    if h : j < M then transferMatrix
      (Kraus.mixedMapLM (polarPosTensor (A ⟨j, h⟩)) (fixedPointTensor (σ ⟨j, h⟩))) else Y j
  have hY (a n : ℕ) : ‖((List.range n).map (fun j => Y (a + j))).prod‖ ≤ c := by
    cases n with
    | zero => simpa using hc
    | succ n =>
      change ‖((List.range (n + 1)).map (fun j => transferMatrix
        (Kraus.transferMap (fixedPointTensor (ρ (a + j)))))).prod‖ ≤ c
      rw [prod_range_transferMatrix_fixedPointTensor (fun j => ρ (a + j))
        (fun j => hρ _) (fun j => hρtr _)]
      exact (hb _ (hρ _) (hρtr _)).1
  have hXY : ∀ j, ‖X j - Y j‖ ≤ c * Kp * Real.sqrt δ := by
    intro j
    dsimp only [X]
    split_ifs with hj
    · let Ψ := LinearMap.toContinuousLinearMap
        (transferMatrixLM ∘ₗ mixedMapLMLeft (fixedPointTensor (σ ⟨j, hj⟩)) ∘ₗ
          (ofPhysicalMatrixLM (D := D)))
      have heq : transferMatrix
          (Kraus.mixedMapLM (polarPosTensor (A ⟨j, hj⟩)) (fixedPointTensor (σ ⟨j, hj⟩))) - Y j =
          Ψ (Matrix.polarPos (physicalMatrix (A ⟨j, hj⟩)) -
            (CFC.sqrt (σ ⟨j, hj⟩))ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
        rw [map_sub]
        congr 1
        change Y j = transferMatrix (Kraus.mixedMapLM (ofPhysicalMatrix
          (((CFC.sqrt (σ ⟨j, hj⟩))ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)).submatrix
            (virtualPairEquiv D) id)) (fixedPointTensor (σ ⟨j, hj⟩)))
        rw [ofPhysicalMatrix_sqrt_transpose_kronecker_one, Kraus.mixedMapLM_self]
        simp [Y, ρ, hj]
      rw [heq, mul_assoc]
      exact (Ψ.le_opNorm _).trans (mul_le_mul (hb _ (hσ _) (htr _)).2
        ((hp _ _ (hσ _)).trans (mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (hA _)) hKp)) (norm_nonneg _) hc0)
    · rw [sub_self, norm_zero]; positivity
  have ht := norm_prod_range_sub_prod_range_le_of_forall_norm_prod_le hY hXY M
  have hgeom := one_add_pow_sub_one_le_mul_exp
    (show 0 ≤ c * (c * Kp * Real.sqrt δ) by positivity) M
  have htrace : Matrix.trace ((List.range M).map Y).prod = 1 := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
    rw [hm]
    change Matrix.trace ((List.range (m + 1)).map (fun j =>
      transferMatrix (Kraus.transferMap (fixedPointTensor (ρ j))))).prod = 1
    rw [prod_range_transferMatrix_fixedPointTensor ρ hρ hρtr]
    simpa only [pow_one] using
      (trace_transferMatrix_transferMap_pow_eq_mpvOverlap (fixedPointTensor (ρ 0)) 1).trans
        (mpvOverlap_fixedPointTensor_self (hρ 0) (hρtr 0) 1)
  have hprod : (List.ofFn fun j => transferMatrix
      (Kraus.mixedMapLM (polarPosTensor (A j)) (fixedPointTensor (σ j)))) =
      (List.range M).map X := by
    refine List.ext_getElem (by simp) fun j hj _ => ?_
    have hjM : j < M := by simpa using hj
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    dsimp [X]
    rw [dite_eq_left hjM]
  rw [hprod, ← htrace, ← Matrix.trace_sub]
  change ‖trL _‖ ≤ _
  calc ‖trL _‖ ≤ ‖trL‖ * ‖((List.range M).map X).prod - ((List.range M).map Y).prod‖ :=
        trL.le_opNorm _
    _ ≤ ‖trL‖ * (c * ((1 + c * (c * Kp * Real.sqrt δ)) ^ M - 1)) := by gcongr
    _ ≤ ‖trL‖ * (c * (M * (c * (c * Kp * Real.sqrt δ)) *
        Real.exp (M * (c * (c * Kp * Real.sqrt δ))))) := by gcongr
    _ = ‖trL‖ * c * K * (M * Real.sqrt δ) * Real.exp (K * (M * Real.sqrt δ)) := by
        dsimp [K]; ring_nf
    _ ≤ C * (M * Real.sqrt δ) * Real.exp (C * (M * Real.sqrt δ)) := by
        have hKC : K ≤ C := by
          dsimp [C]
          nlinarith [mul_nonneg (mul_nonneg (norm_nonneg trL) hc0) hK]
        have hKC' : ‖trL‖ * c * K ≤ C := by dsimp [C]; linarith
        gcongr

end MPSPreparation
