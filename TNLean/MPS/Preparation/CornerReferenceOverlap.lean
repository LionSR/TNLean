/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.VaryingReferenceOverlap
import TNLean.Algebra.FinCyclicInduction

/-!
# Ordered overlap with corner-supported density references

For varying bonds padded to dimension `D`, the reset reference at a block sends `X` to
`Tr(P X) σ`, where `P` projects onto the outgoing bond. Its Gram reference is `σᵀ ⊗ P`.
The mixed transfer still uses the full fixed-point tensor, so the existing shifted pair
identity applies without change. Ordered reference products retain both endpoint bonds.

These quantitative sufficient hypotheses implement the varying-bond setting of
arXiv:2307.01696v2, paragraph "Inhomogeneous short-range correlated MPS" and Supplemental
Material, eq. (S39). No rate is inferred from qualitative finite correlation.
-/

open Matrix MPSTensor
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Kronecker
  Matrix.Norms.L2Operator

namespace MPSPreparation

/-- The coordinate projection onto a bond of dimension `b` in the ambient bond space. -/
def cornerProjection (D b : ℕ) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.diagonal fun i => if i.val < b then 1 else 0

/-- The density reset reference on a padded rectangular block. Its input trace is restricted
to the outgoing bond, as required in arXiv:2307.01696v2, Supplemental Material, eq. (S39). -/
noncomputable def cornerReferenceMap {D : ℕ} (σ : Matrix (Fin D) (Fin D) ℂ) (b : ℕ) :
    Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  ((Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
    (LinearMap.mulLeft ℂ (cornerProjection D b))).smulRight σ

@[simp] theorem cornerReferenceMap_apply {D : ℕ} (σ X : Matrix (Fin D) (Fin D) ℂ) (b : ℕ) :
    cornerReferenceMap σ b X = (cornerProjection D b * X).trace • σ := rfl

/-- Coordinate projections are positive semidefinite. -/
theorem posSemidef_cornerProjection (D b : ℕ) : (cornerProjection D b).PosSemidef := by
  rw [cornerProjection, Matrix.posSemidef_diagonal_iff]
  intro i
  split_ifs <;> simp

@[simp] theorem cornerProjection_mul_self (D b : ℕ) :
    cornerProjection D b * cornerProjection D b = cornerProjection D b := by
  rw [cornerProjection, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

@[simp] theorem cornerProjection_full (D : ℕ) : cornerProjection D D = 1 := by
  ext i j
  simp [cornerProjection, Matrix.diagonal_apply, Matrix.one_apply]

/-- A full outgoing corner gives the ordinary density reset. -/
theorem cornerReferenceMap_full {D : ℕ} {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) :
    cornerReferenceMap σ D = Kraus.transferMap (fixedPointTensor σ) := by
  ext X : 1
  simp [transferMap_fixedPointTensor_apply hσ]

/-- The reference Gram matrix has positive square root `√σᵀ ⊗ P`. -/
theorem sqrt_transpose_kronecker_corner {D : ℕ} {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (b : ℕ) :
    CFC.sqrt (σᵀ ⊗ₖ cornerProjection D b) =
      (CFC.sqrt σ)ᵀ ⊗ₖ cornerProjection D b := by
  rw [hσ.transpose.sqrt_kronecker (posSemidef_cornerProjection D b), hσ.sqrt_transpose,
    CFC.sqrt_unique (cornerProjection_mul_self D b) (posSemidef_cornerProjection D b).nonneg]

/-- The global square-root Hölder estimate for a corner reset reference. The constant depends
only on `D`, including for singular density matrices and smaller endpoint bonds. -/
theorem exists_norm_polarPos_sub_le_sqrt_cornerReferenceMap (D : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {d : ℕ} (A : MPSTensor d D)
      (σ : Matrix (Fin D) (Fin D) ℂ) (b : ℕ), σ.PosSemidef →
      ‖Matrix.polarPos (physicalMatrix A) -
          (CFC.sqrt σ)ᵀ ⊗ₖ cornerProjection D b‖ ≤
        K * Real.sqrt ‖transferMatrix (Kraus.transferMap A) -
          transferMatrix (cornerReferenceMap σ b)‖ := by
  obtain ⟨K, hK, h⟩ := exists_norm_polarPos_sub_le_sqrt_transferMatrix_of_square D
  refine ⟨K, hK, fun {d} A σ b hσ => h A _ _ ?_ ?_⟩
  · exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ)).transpose.kronecker
      (posSemidef_cornerProjection D b)
  · intro a c
    rw [← Matrix.mul_kronecker_mul, cornerProjection_mul_self, ← Matrix.transpose_mul,
      CFC.sqrt_mul_sqrt_self σ hσ.nonneg]
    simp [Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.trace_mul_single,
      mul_comm]

/-- The positive reference, reshaped as a tensor, is the usual fixed-point tensor followed
by the outgoing corner projection. -/
theorem ofPhysicalMatrix_sqrt_transpose_kronecker_corner {D : ℕ}
    (σ : Matrix (Fin D) (Fin D) ℂ) (b : ℕ) :
    ofPhysicalMatrixLM ((CFC.sqrt σ)ᵀ ⊗ₖ cornerProjection D b) =
      fun i => fixedPointTensor σ i * cornerProjection D b := by
  funext i α β
  simp [ofPhysicalMatrixLM, ofPhysicalMatrix, Matrix.kroneckerMap_apply,
    virtualPairEquiv, fixedPointTensor, Matrix.mul_apply,
    Matrix.single_apply, cornerProjection, Matrix.diagonal_apply, ite_and, Finset.sum_ite_eq]
  by_cases h : i.modNat = β
  · have hv : i.val % D = β.val := congrArg Fin.val h
    simp [h, hv]
  · simp [h]

/-- Mixing the corner positive reference against the full fixed-point tensor gives the
corner reset. Thus the unchanged full fixed-point pair identity can be used for overlap. -/
theorem mixedMapLM_sqrt_transpose_kronecker_corner {D : ℕ}
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosSemidef) (b : ℕ) :
    Kraus.mixedMapLM (ofPhysicalMatrixLM ((CFC.sqrt σ)ᵀ ⊗ₖ cornerProjection D b))
      (fixedPointTensor σ) = cornerReferenceMap σ b := by
  rw [ofPhysicalMatrix_sqrt_transpose_kronecker_corner]
  ext X : 1
  rw [Kraus.mixedMapLM_apply]
  have heq : (∑ i, (fixedPointTensor σ i * cornerProjection D b) * X *
      (fixedPointTensor σ i)ᴴ) =
      Kraus.transferMap (fixedPointTensor σ) (cornerProjection D b * X) := by
    simp only [Kraus.transferMap_apply, Matrix.mul_assoc]
  rw [heq, transferMap_fixedPointTensor_apply hσ, cornerReferenceMap_apply]

/-- Restricting the trace functional is right multiplication of the transfer matrix by a
coordinate contraction. -/
theorem transferMatrix_cornerReferenceMap_eq_mul_diagonal {D : ℕ}
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosSemidef) (b : ℕ) :
    transferMatrix (cornerReferenceMap σ b) =
      transferMatrix (Kraus.transferMap (fixedPointTensor σ)) *
        Matrix.diagonal (fun p : Fin D × Fin D => if p.1.val < b then 1 else 0) := by
  ext p ⟨k, l⟩
  by_cases h : k = l
  · subst l
    simp [transferMatrix, transferMap_fixedPointTensor_apply hσ,
      Matrix.mul_diagonal, Matrix.trace_mul_single, cornerProjection,
      mul_comm]
  · simp [transferMatrix, transferMap_fixedPointTensor_apply hσ,
      Matrix.mul_diagonal, Matrix.trace_mul_single, cornerProjection,
      h, Ne.symm h]

/-- A corner reset has no larger transfer norm than the full density reset. -/
theorem norm_transferMatrix_cornerReferenceMap_le {D : ℕ}
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosSemidef) (b : ℕ) :
    ‖transferMatrix (cornerReferenceMap σ b)‖ ≤
      ‖transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ := by
  rw [transferMatrix_cornerReferenceMap_eq_mul_diagonal hσ]
  have hn : ‖(Matrix.diagonal (fun p : Fin D × Fin D =>
      if p.1.val < b then (1 : ℂ) else 0))‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun p => ?_
    split_ifs <;> simp
  calc ‖transferMatrix (Kraus.transferMap (fixedPointTensor σ)) * _‖
      ≤ ‖transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ * ‖_‖ := norm_mul_le _ _
    _ ≤ ‖transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ * 1 :=
      mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = _ := mul_one _

/-- Composing two adjacent corner reset maps leaves the incoming density and outgoing trace
functional; the common middle bond disappears by normalization. -/
theorem transferMatrix_cornerReferenceMap_mul {D : ℕ}
    (σ τ : Matrix (Fin D) (Fin D) ℂ) (a b : ℕ)
    (hτ : cornerProjection D a * τ = τ) (htr : τ.trace = 1) :
    transferMatrix (cornerReferenceMap σ a) * transferMatrix (cornerReferenceMap τ b) =
      transferMatrix (cornerReferenceMap σ b) := by
  rw [← transferMatrix_comp]
  congr 1
  ext X : 1
  simp [LinearMap.comp_apply, cornerReferenceMap_apply, hτ, htr]

/-- A nonempty reference interval keeps precisely its two endpoints. -/
theorem prod_range_transferMatrix_cornerReferenceMap {D : ℕ}
    (σ : ℕ → Matrix (Fin D) (Fin D) ℂ) (b : ℕ → ℕ)
    (hsupp : ∀ j, cornerProjection D (b j) * σ j = σ j)
    (htr : ∀ j, (σ j).trace = 1) (a n : ℕ) :
    ((List.range (n + 1)).map (fun j =>
      transferMatrix (cornerReferenceMap (σ (a + j)) (b (a + j + 1))))).prod =
        transferMatrix (cornerReferenceMap (σ a) (b (a + n + 1))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, ih]
    simpa only [Nat.add_assoc] using transferMatrix_cornerReferenceMap_mul
      (σ a) (σ (a + (n + 1))) (b (a + n + 1)) (b (a + (n + 1) + 1))
      (by simpa only [Nat.add_assoc] using hsupp (a + (n + 1))) (htr _)

/-- The matrix trace of a corner reset is the corner trace of its density. -/
theorem trace_transferMatrix_cornerReferenceMap {D : ℕ} [NeZero D]
    (σ : Matrix (Fin D) (Fin D) ℂ) (b : ℕ) :
    Matrix.trace (transferMatrix (cornerReferenceMap σ b)) =
      (cornerProjection D b * σ).trace := by
  rw [trace_transferMatrix_eq_linearMap_trace, cornerReferenceMap, LinearMap.trace_smulRight]
  rfl

/-- Uniform overlap for positive, trace-one references supported on genuinely varying
endpoint bonds. The full fixed-point tensors remain in the mixed product, while transfer
errors are measured against the corner reset maps. -/
theorem exists_norm_trace_prod_polarPos_sub_one_le_corner_reference (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : ℕ} [NeZero M] (d : Fin M → ℕ)
      (A : ∀ j, MPSTensor (d j) D) (σ : Fin M → Matrix (Fin D) (Fin D) ℂ)
      (b : Fin M → ℕ),
      (∀ j, (σ j).PosSemidef) → (∀ j, (σ j).trace = 1) →
      (∀ j, cornerProjection D (b j) * σ j = σ j) → ∀ {δ : ℝ}, 0 ≤ δ →
      (∀ j, ‖transferMatrix (Kraus.transferMap (A j)) -
        transferMatrix (cornerReferenceMap (σ j) (b (finRotate M j)))‖ ≤ δ) →
      ‖Matrix.trace (List.ofFn fun j => transferMatrix
          (Kraus.mixedMapLM (polarPosTensor (A j)) (fixedPointTensor (σ j)))).prod - 1‖ ≤
        C * (M * Real.sqrt δ) * Real.exp (C * (M * Real.sqrt δ)) := by
  classical
  obtain ⟨Kp, hKp, hp⟩ := exists_norm_polarPos_sub_le_sqrt_cornerReferenceMap D
  obtain ⟨c, hc, hb⟩ := exists_uniform_reference_bounds D
  have hc0 : 0 ≤ c := by linarith
  obtain ⟨C, hC, hbound⟩ := exists_norm_trace_prod_sub_one_le_of_reference_bounds D c
    (c * Kp) hc (mul_nonneg hc0 hKp)
  refine ⟨C, hC, fun {M} _ d A σ b hσ htr hsupp δ hδ hA => ?_⟩
  have := Matrix.neZero_of_trace_eq_one (htr 0)
  let ι : ℕ → Fin M := fun j => ⟨j % M, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne M))⟩
  have hi (j : ℕ) (hj : j < M) : ι j = ⟨j, hj⟩ := by
    apply Fin.ext
    simp [ι, Nat.mod_eq_of_lt hj]
  have hsucc (j : ℕ) : ι (j + 1) = finRotate M (ι j) := by
    apply Fin.ext
    rw [coe_finRotate_mod]
    change (j + 1) % M = (j % M + 1) % M
    exact (Nat.mod_add_mod _ _ _).symm
  let ρ : ℕ → Matrix (Fin D) (Fin D) ℂ := fun j => σ (ι j)
  let β : ℕ → ℕ := fun j => b (ι j)
  let Y : ℕ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun j =>
    transferMatrix (cornerReferenceMap (ρ j) (β (j + 1)))
  let X : ℕ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun j =>
    if h : j < M then transferMatrix
      (Kraus.mixedMapLM (polarPosTensor (A ⟨j, h⟩)) (fixedPointTensor (σ ⟨j, h⟩))) else Y j
  have hY (a n : ℕ) : ‖((List.range n).map (fun j => Y (a + j))).prod‖ ≤ c := by
    cases n with
    | zero => simpa using hc
    | succ n =>
      change ‖((List.range (n + 1)).map (fun j =>
        transferMatrix (cornerReferenceMap (ρ (a + j)) (β (a + j + 1))))).prod‖ ≤ c
      rw [prod_range_transferMatrix_cornerReferenceMap ρ β
        (fun j => hsupp (ι j)) (fun j => htr (ι j))]
      exact (norm_transferMatrix_cornerReferenceMap_le (hσ _) _).trans (hb _ (hσ _) (htr _)).1
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
            (CFC.sqrt (σ ⟨j, hj⟩))ᵀ ⊗ₖ cornerProjection D (b (finRotate M ⟨j, hj⟩))) := by
        rw [map_sub]
        congr 1
        change Y j = transferMatrix (Kraus.mixedMapLM
          (ofPhysicalMatrixLM ((CFC.sqrt (σ ⟨j, hj⟩))ᵀ ⊗ₖ
            cornerProjection D (b (finRotate M ⟨j, hj⟩)))) (fixedPointTensor (σ ⟨j, hj⟩)))
        rw [mixedMapLM_sqrt_transpose_kronecker_corner (hσ _)]
        simp [Y, ρ, β, hsucc, hi j hj]
      rw [heq, mul_assoc]
      exact (Ψ.le_opNorm _).trans (mul_le_mul (hb _ (hσ _) (htr _)).2
        ((hp _ _ _ (hσ _)).trans (mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (hA _)) hKp)) (norm_nonneg _) hc0)
    · rw [sub_self, norm_zero]; positivity
  have htrace : Matrix.trace ((List.range M).map Y).prod = 1 := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
    have hYeq : Y = fun j =>
        transferMatrix (cornerReferenceMap (ρ (0 + j)) (β (0 + j + 1))) := by
      funext j
      simp only [Y, Nat.zero_add]
    rw [hYeq]
    rw [hm, prod_range_transferMatrix_cornerReferenceMap ρ β
      (fun j => hsupp (ι j)) (fun j => htr (ι j)), trace_transferMatrix_cornerReferenceMap]
    have hperiod : β (0 + m + 1) = b (ι 0) := by
      apply congrArg b
      apply Fin.ext
      change (0 + m + 1) % M = 0 % M
      rw [show 0 + m + 1 = M from by omega, Nat.mod_self, Nat.zero_mod]
    rw [hperiod]
    change (cornerProjection D (b (ι 0)) * σ (ι 0)).trace = 1
    rw [hsupp, htr]
  have hprod : (List.ofFn fun j => transferMatrix
      (Kraus.mixedMapLM (polarPosTensor (A j)) (fixedPointTensor (σ j)))) =
      (List.range M).map X := by
    refine List.ext_getElem (by simp) fun j hj _ => ?_
    have hjM : j < M := by simpa using hj
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    dsimp [X]
    rw [dite_eq_left hjM]
  rw [hprod]
  exact hbound X Y hδ hY hXY M htrace

end MPSPreparation
