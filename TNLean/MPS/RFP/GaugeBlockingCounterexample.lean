/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.FundamentalCoord
import TNLean.MPS.MPDO.PhysicalBlocking
import TNLean.MPS.MPDO.PureAreaLaw
import TNLean.MPS.RFP.PhaseOscillation
import TNLean.MPS.SharedInfra.BlockAssembly

/-!
# A counterexample to blocking up to virtual gauge implying an RFP

Appendix D, equation `RFP-gauge`, of arXiv:1606.00608 asserts that in the pure case,
blocking up to a virtual gauge is equivalent to the ordinary renormalization fixed-point
condition. The one-letter tensor `cubePhaseTensor`, whose matrix is
$\operatorname{diag}(1,\omega)$ for a primitive cube root $\omega$, refutes this assertion.
If `cubeSwapGauge` exchanges the two virtual coordinates, then
$$
  A=\omega S A^2S^{-1}.
$$
After doubling, the amplitude phase cancels and the blocked doubled-MPDO tensor is
virtually gauge equivalent to the original tensor with the orientation printed in
`APPE_Fig1.png`, while the pure transfer map is not idempotent.

**Scope restriction (one-letter MPS lift):** The counterexample realizes the exact
source diagram for one physical letter. It does not decide the mixed-state continuation.
See `docs/paper-gaps/cpsv16_rfp_gauge_pure_equivalence_false.tex`.
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor

/-- The literal one-letter specialization of the doubled-MPDO virtual-gauge condition in
Appendix D, equation `RFP-gauge`, of arXiv:1606.00608, lines 2091--2110.

For a one-dimensional physical space, every unitary-conjugation channel on the original
or blocked physical algebra is the identity. The virtual `GaugeEquiv` equation gives one
direction of the printed diagram, and its symmetry gives the other.

**Scope restriction (one-letter MPS lift):** This predicate specializes the physical
alphabet to one letter. See
`docs/paper-gaps/cpsv16_rfp_gauge_pure_equivalence_false.tex`. -/
def IsOneLetterRFPViaTSUpToVirtualGauge {D : ℕ} (M : MPOTensor 1 D) : Prop :=
  MPSTensor.GaugeEquiv (blockTwo M).toMPSTensor M.toMPSTensor

end MPOTensor

namespace MPSTensor

/-- The exact one-letter pure-state specialization of the doubled-MPDO condition
`RFP-gauge` in arXiv:1606.00608, Appendix D, lines 2091--2110.

**Scope restriction (one-letter MPS lift):** The physical alphabet has one letter. See
`docs/paper-gaps/cpsv16_rfp_gauge_pure_equivalence_false.tex`. -/
def IsPureOneLetterRFPViaTSUpToVirtualGauge {D : ℕ} (A : MPSTensor 1 D) : Prop :=
  MPOTensor.IsOneLetterRFPViaTSUpToVirtualGauge (doubledTensor A)

/-- The virtual gauge induced on the doubled bond space by $X$: after identifying
`Fin (D * D)` with `Fin D × Fin D`, its matrix is $X \otimes \overline X$.

Source: arXiv:1606.00608, Appendix D, equation `RFP-gauge`, lines 2091--2110. -/
noncomputable def doubledVirtualGauge {D : ℕ} (X : GL (Fin D) ℂ) : GL (Fin (D * D)) ℂ :=
  Units.mapEquiv
      (Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv).toRingEquiv.toMulEquiv
    (Matrix.GeneralLinearGroup.kronecker X
      (Matrix.GeneralLinearGroup.map (starRingEnd ℂ) X))

/-- The virtual-coordinate permutation exchanging the $1$ and $\omega$ blocks of
`cubePhaseTensor`. -/
private noncomputable def cubeCoordinateSwap :
    Equiv.Perm (Fin (∑ k : Fin 2, cubePhaseBondDim k)) :=
  finSigmaFinEquiv.symm.trans
    (blockIndexCoordinateEquiv cubePhaseBondDim (Equiv.swap 0 1))

/-- The invertible permutation gauge exchanging the $1$ and $\omega$ virtual
coordinates of `cubePhaseTensor`.

Source: arXiv:1606.00608, Appendix D, equation `RFP-gauge`, lines 2091--2110. -/
noncomputable def cubeSwapGauge :
    GL (Fin (∑ k : Fin 2, cubePhaseBondDim k)) ℂ :=
  permGL cubeCoordinateSwap

private lemma primitiveCubeRoot_pow_three : primitiveCubeRoot ^ 3 = 1 :=
  primitiveCubeRoot_isPrimitiveRoot.pow_eq_one

private lemma norm_primitiveCubeRoot : ‖primitiveCubeRoot‖ = 1 := by
  simp [primitiveCubeRoot, Complex.norm_exp, Complex.mul_re]

/-- The weight $\mu_p\overline{\mu_q}$ of a flattened doubled bond coordinate
$(p,q)$ in the four-block canonical decomposition.

Source: arXiv:1606.00608, equation `II_CF1` and canonical-form data and
normalization at lines 219--246. -/
private noncomputable def cubePhaseDoubledWeight (q : Fin 4) : ℂ :=
  let pair := (finProdFinEquiv :
    Fin (∑ k : Fin 2, cubePhaseBondDim k) ×
      Fin (∑ k : Fin 2, cubePhaseBondDim k) ≃ Fin 4).symm q
  cubePhaseWeight (finSigmaFinEquiv.symm pair.1).1 *
    star (cubePhaseWeight (finSigmaFinEquiv.symm pair.2).1)

/-- The doubled cube-phase tensor decomposes into four bond-one normal blocks.

Source: arXiv:1606.00608, equation `II_CF1` and canonical-form data at lines 219--246. -/
private theorem cubePhaseDoubledTensor_eq_toTensorFromBlocks :
    (doubledTensor cubePhaseTensor).toMPSTensor =
      toTensorFromBlocks cubePhaseDoubledWeight (fun _ : Fin 4 => scalarUnitTensor) := by
  have hflat_symm (q : Fin 4) :
      (finSigmaFinEquiv : (Σ _q : Fin 4, Fin 1) ≃ Fin 4).symm q = ⟨q, 0⟩ := by
    fin_cases q <;> rfl
  have hcoord (k₁ k₂ l₁ l₂ : Fin 2) :
      finProdFinEquiv
          (finSigmaFinEquiv ⟨k₁, (0 : Fin (cubePhaseBondDim k₁))⟩,
            finSigmaFinEquiv ⟨k₂, (0 : Fin (cubePhaseBondDim k₂))⟩) =
        finProdFinEquiv
          (finSigmaFinEquiv ⟨l₁, (0 : Fin (cubePhaseBondDim l₁))⟩,
            finSigmaFinEquiv ⟨l₂, (0 : Fin (cubePhaseBondDim l₂))⟩) ↔
          k₁ = l₁ ∧ k₂ = l₂ := by
    constructor
    · intro h
      have hp := finProdFinEquiv.injective h
      exact ⟨congrArg Sigma.fst (finSigmaFinEquiv.injective (congrArg Prod.fst hp)),
        congrArg Sigma.fst (finSigmaFinEquiv.injective (congrArg Prod.snd hp))⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  ext p a b
  obtain ⟨⟨a₁, a₂⟩, rfl⟩ := (finProdFinEquiv :
    Fin (∑ k : Fin 2, cubePhaseBondDim k) ×
      Fin (∑ k : Fin 2, cubePhaseBondDim k) ≃
        Fin ((∑ k : Fin 2, cubePhaseBondDim k) *
          ∑ k : Fin 2, cubePhaseBondDim k)).surjective a
  obtain ⟨⟨b₁, b₂⟩, rfl⟩ := (finProdFinEquiv :
    Fin (∑ k : Fin 2, cubePhaseBondDim k) ×
      Fin (∑ k : Fin 2, cubePhaseBondDim k) ≃
        Fin ((∑ k : Fin 2, cubePhaseBondDim k) *
          ∑ k : Fin 2, cubePhaseBondDim k)).surjective b
  obtain ⟨⟨ka₁, ua₁⟩, rfl⟩ := (finSigmaFinEquiv :
    (Σ k : Fin 2, Fin (cubePhaseBondDim k)) ≃
      Fin (∑ k : Fin 2, cubePhaseBondDim k)).surjective a₁
  obtain ⟨⟨ka₂, ua₂⟩, rfl⟩ := (finSigmaFinEquiv :
    (Σ k : Fin 2, Fin (cubePhaseBondDim k)) ≃
      Fin (∑ k : Fin 2, cubePhaseBondDim k)).surjective a₂
  obtain ⟨⟨kb₁, ub₁⟩, rfl⟩ := (finSigmaFinEquiv :
    (Σ k : Fin 2, Fin (cubePhaseBondDim k)) ≃
      Fin (∑ k : Fin 2, cubePhaseBondDim k)).surjective b₁
  obtain ⟨⟨kb₂, ub₂⟩, rfl⟩ := (finSigmaFinEquiv :
    (Σ k : Fin 2, Fin (cubePhaseBondDim k)) ≃
      Fin (∑ k : Fin 2, cubePhaseBondDim k)).surjective b₂
  fin_cases p
  fin_cases ka₁ <;> fin_cases ka₂ <;> fin_cases kb₁ <;> fin_cases kb₂ <;>
    simp only [cubePhaseBondDim] at ua₁ ua₂ ub₁ ub₂ <;>
    fin_cases ua₁ <;> fin_cases ua₂ <;> fin_cases ub₁ <;> fin_cases ub₂ <;>
    simp only [MPOTensor.toMPSTensor, doubledTensor, cubePhaseBondDim, cubePhaseTensor,
      toTensorFromBlocks, cubePhaseWeight, scalarUnitTensor, Matrix.reindex_apply,
      Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.submatrix_apply,
      finProdFinEquiv.symm_apply_apply, Matrix.kroneckerMap_apply,
      finSigmaFinEquiv.symm_apply_apply, Matrix.blockDiagonal'_apply, zero_ne_one,
      one_ne_zero, ↓reduceDIte, Matrix.map_apply, cast_eq, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, map_zero, map_one, mul_zero, zero_mul,
      mul_one, one_mul, cubePhaseDoubledWeight, finProdFinEquiv_symm_apply,
      RCLike.star_def, hflat_symm, finProdFinEquiv_divNat, finProdFinEquiv_modNat,
      dite_eq_ite, right_eq_ite_iff, imp_false] <;>
    (intro h; have := (hcoord _ _ _ _).mp h; omega)

/-- Every scalar-block weight in the doubled decomposition has modulus one.

Source: arXiv:1606.00608, canonical-form normalization at line 246. -/
private theorem norm_cubePhaseDoubledWeight (q : Fin 4) :
    ‖cubePhaseDoubledWeight q‖ = 1 := by
  obtain ⟨⟨q₁, q₂⟩, rfl⟩ := (finProdFinEquiv :
    Fin (∑ k : Fin 2, cubePhaseBondDim k) ×
      Fin (∑ k : Fin 2, cubePhaseBondDim k) ≃ Fin 4).surjective q
  obtain ⟨⟨k₁, u₁⟩, rfl⟩ := (finSigmaFinEquiv :
    (Σ k : Fin 2, Fin (cubePhaseBondDim k)) ≃
      Fin (∑ k : Fin 2, cubePhaseBondDim k)).surjective q₁
  obtain ⟨⟨k₂, u₂⟩, rfl⟩ := (finSigmaFinEquiv :
    (Σ k : Fin 2, Fin (cubePhaseBondDim k)) ≃
      Fin (∑ k : Fin 2, cubePhaseBondDim k)).surjective q₂
  fin_cases k₁ <;> fin_cases k₂ <;>
    simp only [cubePhaseBondDim] at u₁ u₂ <;>
    fin_cases u₁ <;> fin_cases u₂ <;>
    simp [cubePhaseDoubledWeight, cubePhaseWeight, norm_primitiveCubeRoot,
      finProdFinEquiv.symm_apply_apply, finSigmaFinEquiv.symm_apply_apply]

/-- The doubled cube-phase tensor generates positive semidefinite operators on every
nonempty chain and hence satisfies the MPDO standing hypothesis.

Source: arXiv:1606.00608, Definition `RFPMixedTS`, lines 657--660, and the pure-state
purification identity at equation `MPDO-Puri-1`, line 752. -/
theorem cubePhaseDoubledTensor_isMPDO :
    MPOTensor.IsMPDO (doubledTensor cubePhaseTensor) := by
  intro N _
  exact doubledTensor_posSemidef cubePhaseTensor N

/-- The doubled cube-phase MPO is in the literal CPSV canonical form used for MPDO tensors.

Source: arXiv:1606.00608, Definition `RFPMixedTS`, lines 657--660, and Appendix D,
lines 2091--2110. -/
theorem cubePhaseDoubledTensor_isCPSVCanonicalForm :
    IsCPSVCanonicalForm (doubledTensor cubePhaseTensor).toMPSTensor := by
  rw [cubePhaseDoubledTensor_eq_toTensorFromBlocks]
  exact (CPSVCanonicalFormData.ofBlocks (fun _ => by simp) cubePhaseDoubledWeight
    (fun _ : Fin 4 => scalarUnitTensor)
    (fun _ => scalarUnitTensor_isNormalTensor)).isCPSVCanonicalForm

/-- The doubled cube-phase MPO admits canonical data satisfying the normalization at
arXiv:1606.00608, line 246. -/
theorem cubePhaseDoubledTensor_exists_weightNormalized :
    ∃ data : CPSVCanonicalFormData (doubledTensor cubePhaseTensor).toMPSTensor,
      data.IsWeightNormalized := by
  rw [cubePhaseDoubledTensor_eq_toTensorFromBlocks]
  refine ⟨CPSVCanonicalFormData.ofBlocks (fun _ : Fin 4 => by simp)
    cubePhaseDoubledWeight (fun _ : Fin 4 => scalarUnitTensor)
    (fun _ => scalarUnitTensor_isNormalTensor), ?_⟩
  refine {
    weight_norm_le_one := ?_
    weight_unit_exists := ?_ }
  · change ∀ q : Fin 4, ‖cubePhaseDoubledWeight q‖ ≤ 1
    intro q
    rw [norm_cubePhaseDoubledWeight]
  · change toTensorFromBlocks cubePhaseDoubledWeight
      (fun _ : Fin 4 => scalarUnitTensor) ≠ 0 →
        ∃ q : Fin 4, ‖cubePhaseDoubledWeight q‖ = 1
    intro _
    exact ⟨0, norm_cubePhaseDoubledWeight 0⟩

private lemma blockTensor_cubePhaseTensor_two (i : Fin 1) :
    blockTensor cubePhaseTensor 2 i =
      Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
        (Matrix.blockDiagonal' fun k =>
          (cubePhaseWeight k • (1 : Matrix (Fin 1) (Fin 1) ℂ)) *
            (cubePhaseWeight k • (1 : Matrix (Fin 1) (Fin 1) ℂ))) := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change cubePhaseTensor 0 * (cubePhaseTensor 0 * 1) = _
  rw [Matrix.mul_one]
  change Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
      (Matrix.blockDiagonal' fun k =>
        cubePhaseWeight k • (1 : Matrix (Fin 1) (Fin 1) ℂ)) *
    Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
      (Matrix.blockDiagonal' fun k =>
        cubePhaseWeight k • (1 : Matrix (Fin 1) (Fin 1) ℂ)) = _
  let B := Matrix.blockDiagonal' fun k =>
    cubePhaseWeight k • (1 : Matrix (Fin 1) (Fin 1) ℂ)
  calc
    Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv B *
        Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv B =
      Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv (B * B) :=
        Matrix.reindexLinearEquiv_mul ℂ ℂ finSigmaFinEquiv finSigmaFinEquiv
          finSigmaFinEquiv B B
    _ = Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
        (Matrix.blockDiagonal' fun k =>
          (cubePhaseWeight k • (1 : Matrix (Fin 1) (Fin 1) ℂ)) *
            (cubePhaseWeight k • (1 : Matrix (Fin 1) (Fin 1) ℂ))) := by
      apply congrArg (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
      exact (Matrix.blockDiagonal'_mul _ _).symm

/-- The blocked gauge-phase identity with the orientation of equation `RFP-gauge` in
arXiv:1606.00608, lines 2100--2107:
$A=\omega S A^{[2]}S^{-1}$. -/
theorem cube_phase_blocked_gauge_identity (i : Fin 1) :
    cubePhaseTensor i = primitiveCubeRoot •
      ((cubeSwapGauge : Matrix _ _ ℂ) * blockTensor cubePhaseTensor 2 i *
        ((cubeSwapGauge⁻¹ : GL (Fin (∑ k : Fin 2, cubePhaseBondDim k)) ℂ) :
          Matrix _ _ ℂ)) := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rw [blockTensor_cubePhaseTensor_two]
  ext a b
  rw [cubeSwapGauge, permGL_val, permGL_inv_val]
  rw [permMatrix_conj_eq_submatrix]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply]
  rcases ha : finSigmaFinEquiv.symm a with ⟨ka, aa⟩
  rcases hb : finSigmaFinEquiv.symm b with ⟨kb, bb⟩
  have hcube : primitiveCubeRoot * (primitiveCubeRoot * primitiveCubeRoot) = 1 := by
    calc
      primitiveCubeRoot * (primitiveCubeRoot * primitiveCubeRoot) =
          primitiveCubeRoot ^ 3 := by ring
      _ = 1 := primitiveCubeRoot_pow_three
  fin_cases ka <;> fin_cases aa <;> fin_cases kb <;> fin_cases bb <;>
    simp [cubeCoordinateSwap, blockIndexCoordinateEquiv, Equiv.sigmaCongr,
      Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft, cubePhaseTensor,
      toTensorFromBlocks, Matrix.reindex_apply, Matrix.blockDiagonal'_apply,
      cubePhaseWeight, cubePhaseBondDim,
      scalarUnitTensor, ha, hb, hcube]


/-- A stronger one-letter MPS-level witness for the doubled-MPDO virtual-gauge
condition in Appendix D, equation `RFP-gauge`, of arXiv:1606.00608, lines 2091--2110.

The scalar is an MPS amplitude phase. It is not a physical channel in the source diagram:
after doubling it appears as $\zeta\overline{\zeta}=1$. The theorem below proves that
this witness implies the exact doubled-MPDO predicate.

**Scope restriction (one-letter MPS lift):** This stronger MPS-level definition is
sufficient but is not itself the source predicate. See
`docs/paper-gaps/cpsv16_rfp_gauge_pure_equivalence_false.tex`. -/
def IsBlockedGaugePhaseFixedPoint {D : ℕ} (A : MPSTensor 1 D) : Prop :=
  ∃ (X : GL (Fin D) ℂ) (ζ : ℂ), ‖ζ‖ = 1 ∧ ∀ i : Fin 1,
    A i = ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * blockTensor A 2 i *
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))

/-- A one-letter MPS blocking identity with a unit amplitude phase gives the literal
doubled-MPDO virtual-gauge condition from Appendix D, equation `RFP-gauge`, of
arXiv:1606.00608, lines 2091--2110. The doubled scalar is
$\zeta\overline{\zeta}=1$. -/
theorem isPureOneLetterRFPViaTSUpToVirtualGauge_of_isBlockedGaugePhaseFixedPoint
    {D : ℕ} (A : MPSTensor 1 D) (h : IsBlockedGaugePhaseFixedPoint A) :
    IsPureOneLetterRFPViaTSUpToVirtualGauge A := by
  obtain ⟨X, ζ, hζ, hA⟩ := h
  refine ⟨doubledVirtualGauge X, ?_⟩
  intro ij
  fin_cases ij
  simp only [MPOTensor.toMPSTensor, Fin.divNat, Fin.modNat]
  simp only [doubledTensor, Nat.div_one, Fin.zero_eta, Fin.isValue, Nat.mod_succ,
    Nat.reduceMul, mul_one, MPOTensor.blockTwo_apply, Matrix.coe_units_inv,
    Matrix.submatrix_mul_equiv]
  have h₁ : (finProdFinEquiv.symm (0 : Fin (1 * 1))).1 = (0 : Fin 1) :=
    Subsingleton.elim _ _
  have h₂ : (finProdFinEquiv.symm (0 : Fin (1 * 1))).2 = (0 : Fin 1) :=
    Subsingleton.elim _ _
  rw [h₁, h₂]
  apply (Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv).symm.injective
  suffices hbase :
      (A 0 ⊗ₖ (A 0).map (starRingEnd ℂ)) =
        (↑(Matrix.GeneralLinearGroup.kronecker X
            (Matrix.GeneralLinearGroup.map (starRingEnd ℂ) X)) :
          Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) *
          ((A 0 ⊗ₖ (A 0).map (starRingEnd ℂ)) *
            (A 0 ⊗ₖ (A 0).map (starRingEnd ℂ))) *
          (↑(Matrix.GeneralLinearGroup.kronecker X
            (Matrix.GeneralLinearGroup.map (starRingEnd ℂ) X)) :
              Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)⁻¹ by
    simpa [Matrix.coe_reindexAlgEquiv, doubledVirtualGauge] using hbase
  rw [show (↑(Matrix.GeneralLinearGroup.kronecker X
      (Matrix.GeneralLinearGroup.map (starRingEnd ℂ) X)) :
      Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) =
      (X : Matrix _ _ ℂ) ⊗ₖ (X : Matrix _ _ ℂ).map (starRingEnd ℂ) from rfl]
  rw [Matrix.inv_kronecker]
  rw [← Matrix.GeneralLinearGroup.coe_inv X]
  change (A 0 ⊗ₖ (A 0).map (starRingEnd ℂ)) =
    ((X : Matrix _ _ ℂ) ⊗ₖ (X : Matrix _ _ ℂ).map (starRingEnd ℂ)) *
      ((A 0 ⊗ₖ (A 0).map (starRingEnd ℂ)) *
        (A 0 ⊗ₖ (A 0).map (starRingEnd ℂ))) *
      (((X⁻¹ : GL (Fin D) ℂ) : Matrix _ _ ℂ) ⊗ₖ
        ((X : Matrix _ _ ℂ).map (starRingEnd ℂ))⁻¹)
  repeat' rw [← Matrix.mul_kronecker_mul]
  have hmapinv : ((X : Matrix _ _ ℂ).map (starRingEnd ℂ))⁻¹ =
      ((↑(X⁻¹) : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ)) := by
    calc
      ((X : Matrix _ _ ℂ).map (starRingEnd ℂ))⁻¹ =
          (↑((Matrix.GeneralLinearGroup.map (starRingEnd ℂ) X)⁻¹) :
            Matrix (Fin D) (Fin D) ℂ) :=
        (Matrix.GeneralLinearGroup.coe_inv
          (Matrix.GeneralLinearGroup.map (starRingEnd ℂ) X)).symm
      _ = ↑(Matrix.GeneralLinearGroup.map (starRingEnd ℂ) (X⁻¹)) := by
        rw [map_inv]
      _ = ((↑(X⁻¹) : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ)) := rfl
  rw [hmapinv]
  have hblock : blockTensor A 2 (0 : Fin 1) = A 0 * A 0 := by
    change evalWord A [0, 0] = A 0 * A 0
    simp [evalWord]
  have hA0 : A 0 = ζ • ((X : Matrix _ _ ℂ) * (A 0 * A 0) *
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix _ _ ℂ)) := by
    simpa only [hblock] using hA 0
  have hmapG :
      ((X : Matrix _ _ ℂ) * (A 0 * A 0) *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix _ _ ℂ)).map (starRingEnd ℂ) =
        (X : Matrix _ _ ℂ).map (starRingEnd ℂ) *
          ((A 0).map (starRingEnd ℂ) * (A 0).map (starRingEnd ℂ)) *
          ((↑(X⁻¹) : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ)) := by
    calc
      ((X : Matrix _ _ ℂ) * (A 0 * A 0) *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix _ _ ℂ)).map (starRingEnd ℂ) =
          ((X : Matrix _ _ ℂ) * (A 0 * A 0)).map (starRingEnd ℂ) *
            ((↑(X⁻¹) : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ)) :=
        (starRingEnd ℂ).mapMatrix.map_mul _ _
      _ = ((X : Matrix _ _ ℂ).map (starRingEnd ℂ) *
            (A 0 * A 0).map (starRingEnd ℂ)) *
            ((↑(X⁻¹) : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ)) := by
        congr 1
        exact (starRingEnd ℂ).mapMatrix.map_mul _ _
      _ = _ := by
        congr 2
        exact (starRingEnd ℂ).mapMatrix.map_mul _ _
  rw [← hmapG]
  conv_lhs => rw [hA0]
  have hphase : ζ * star ζ = 1 := by
    rw [RCLike.star_def, Complex.mul_conj, ← Complex.sq_norm, hζ]
    norm_num
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  let G : Matrix (Fin D) (Fin D) ℂ :=
    (X : Matrix _ _ ℂ) * (A 0 * A 0) *
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix _ _ ℂ)
  change ζ * G a c * star (ζ * G b d) = G a c * star (G b d)
  have hstar : star (ζ * G b d) = star ζ * star (G b d) :=
    (starRingEnd ℂ).map_mul ζ (G b d)
  rw [hstar]
  calc
    ζ * G a c * (star ζ * star (G b d)) =
        (ζ * star ζ) * (G a c * star (G b d)) := by ring
    _ = G a c * star (G b d) := by rw [hphase, one_mul]


/-- The cube-phase tensor satisfies equation `RFP-gauge` in arXiv:1606.00608,
lines 2100--2107, with a unit MPS amplitude phase. -/
private theorem cubePhaseTensor_isBlockedGaugePhaseFixedPoint :
    IsBlockedGaugePhaseFixedPoint cubePhaseTensor := by
  refine ⟨cubeSwapGauge, primitiveCubeRoot, norm_primitiveCubeRoot, ?_⟩
  exact cube_phase_blocked_gauge_identity

/-- The doubled cube-phase tensor satisfies the literal one-letter specialization of the
Appendix D `RFP-gauge` diagram. The MPS amplitude phase cancels after doubling.

Source: arXiv:1606.00608, Appendix D, equation `RFP-gauge`, lines 2091--2110. -/
theorem cubePhaseTensor_isPureOneLetterRFPViaTSUpToVirtualGauge :
    IsPureOneLetterRFPViaTSUpToVirtualGauge cubePhaseTensor :=
  isPureOneLetterRFPViaTSUpToVirtualGauge_of_isBlockedGaugePhaseFixedPoint
    cubePhaseTensor cubePhaseTensor_isBlockedGaugePhaseFixedPoint

/-- The cube-phase tensor is not an ordinary pure-state renormalization fixed point.

If its transfer map were idempotent, every positive power would equal the transfer map,
so the dyadic transfer orbit would converge. This contradicts the explicit cube-phase
oscillation proved in `cubePhaseTensor_not_tendsto_dyadic_transferMap`.

Source: arXiv:1606.00608, Appendix D, equation `RFP-gauge` and lines 2100--2107. -/
theorem cubePhaseTensor_not_isTransferIdempotent :
    ¬ IsTransferIdempotent cubePhaseTensor := by
  intro hRFP
  have hIdem : IsIdempotentElem (transferMap cubePhaseTensor) := by
    rw [IsIdempotentElem]
    apply LinearMap.ext
    intro ρ
    simpa [Module.End.mul_apply, LinearMap.comp_apply, IsTransferIdempotent] using
      LinearMap.congr_fun hRFP ρ
  exact cubePhaseTensor_not_tendsto_dyadic_transferMap.2.2 ⟨
    transferMap cubePhaseTensor, fun ρ =>
      tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => by
        dsimp
        rw [hIdem.pow_eq (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))])⟩

/-- The doubled cube-phase tensor is an MPDO in normalized CPSV canonical form,
satisfies the literal one-letter blocking-up-to-gauge diagram, and its underlying
transfer map is not idempotent.

Source: arXiv:1606.00608, Definition `RFPMixedTS`, lines 657--660, canonical-form
normalization at lines 238--246, and Appendix D, equation `RFP-gauge`, lines 2100--2107. -/
theorem cubePhaseTensor_normalized_canonical_gauge_not_rfp :
    MPOTensor.IsMPDO (doubledTensor cubePhaseTensor) ∧
      IsCPSVCanonicalForm (doubledTensor cubePhaseTensor).toMPSTensor ∧
      (∃ data : CPSVCanonicalFormData (doubledTensor cubePhaseTensor).toMPSTensor,
        data.IsWeightNormalized) ∧
      IsPureOneLetterRFPViaTSUpToVirtualGauge cubePhaseTensor ∧
      ¬ IsTransferIdempotent cubePhaseTensor :=
  ⟨cubePhaseDoubledTensor_isMPDO,
    cubePhaseDoubledTensor_isCPSVCanonicalForm,
    cubePhaseDoubledTensor_exists_weightNormalized,
    cubePhaseTensor_isPureOneLetterRFPViaTSUpToVirtualGauge,
    cubePhaseTensor_not_isTransferIdempotent⟩

/-- The normalized canonical-form pure-state equivalence asserted after equation
`RFP-gauge` in arXiv:1606.00608, lines 2100--2107, is false, already for tensors with
one physical letter. The canonical-form hypothesis is imposed on the doubled MPO tensor
$M=A\otimes\overline A$, as in Definition `RFPMixedTS`, lines 657--660. -/
theorem cpsv16_pure_rfp_gauge_equivalence_false :
    ¬ ∀ (D : ℕ) (A : MPSTensor 1 D),
      MPOTensor.IsMPDO (doubledTensor A) →
      IsCPSVCanonicalForm (doubledTensor A).toMPSTensor →
      (∃ data : CPSVCanonicalFormData (doubledTensor A).toMPSTensor,
        data.IsWeightNormalized) →
      (IsPureOneLetterRFPViaTSUpToVirtualGauge A ↔ IsTransferIdempotent A) := by
  intro hEquiv
  exact cubePhaseTensor_not_isTransferIdempotent
    ((hEquiv _ cubePhaseTensor
      cubePhaseTensor_normalized_canonical_gauge_not_rfp.1
      cubePhaseTensor_normalized_canonical_gauge_not_rfp.2.1
      cubePhaseTensor_normalized_canonical_gauge_not_rfp.2.2.1).mp
      cubePhaseTensor_normalized_canonical_gauge_not_rfp.2.2.2.1)

end MPSTensor
