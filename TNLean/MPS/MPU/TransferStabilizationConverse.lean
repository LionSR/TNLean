/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.RankOneSandwich
import QICLean.Channel.FixedPoint.MeanErgodicAdjoint
import QICLean.Channel.Irreducible.AdjointFamily
import QICLean.Channel.Irreducible.FromSpectral
import TNLean.MPS.MPU.TransferStabilization

/-!
# Converse to stabilization for an MPU in canonical form II

For an MPU, a positive diagonal matrix of trace one that factors a positive
power of the normalized transfer matrix determines canonical-form-II data for
the same tensor. The positive definite factor rules out an unused virtual
subspace.

Source: arXiv:1703.09188, Proposition `prop:normal-tensor`, lines 344–355,
and equation `Erightleft`, lines 269–281.
-/

open scoped Matrix BigOperators ComplexOrder Kraus

namespace MPOTensor

variable {d D : ℕ} {U : MPOTensor d D}

/-- A normalized rank-one power is already stationary when the next trace
moment is one. -/
private theorem rankOnePower_fixed
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Matrix ι ι ℂ) (v w : ι → ℂ) (J : ℕ)
    (hpair : w ⬝ᵥ v = 1)
    (hpower : E ^ J = Matrix.vecMulVec v w)
    (htrace : Matrix.trace (E ^ (J + 1)) = 1) :
    E * Matrix.vecMulVec v w = Matrix.vecMulVec v w ∧
      Matrix.vecMulVec v w * E = Matrix.vecMulVec v w := by
  let P := Matrix.vecMulVec v w
  have hidem : P * P = P := by
    simp [P, Matrix.vecMulVec_mul_vecMulVec, hpair]
  have hcomm : E * P = P * E := by
    change E * Matrix.vecMulVec v w = Matrix.vecMulVec v w * E
    rw [← hpower]
    exact (pow_succ' E J).symm.trans (pow_succ E J)
  have htraceEP : Matrix.trace (E * P) = 1 := by
    change Matrix.trace (E * Matrix.vecMulVec v w) = 1
    rw [← hpower, ← pow_succ']
    exact htrace
  have hsand : P * E * P = P := by
    simpa only [P, htraceEP, one_smul] using
      Matrix.vecMulVec_mul_mul_vecMulVec_eq_trace_smul v w E
  have hPEP : P * E * P = P * E := by
    calc
      P * E * P = E * (P * P) := by rw [← Matrix.mul_assoc, ← hcomm, Matrix.mul_assoc]
      _ = P * E := by rw [hidem, hcomm]
  have hPE : P * E = P := hPEP.symm.trans hsand
  exact ⟨hcomm.trans hPE, hPE⟩

/-- The second and third trace moments of an outer product are powers of its
single nonzero eigenvalue. -/
private theorem trace_rankOne_pow_two_three
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v w : ι → ℂ) (t : ℂ) (hpair : w ⬝ᵥ v = t) :
    Matrix.trace ((Matrix.vecMulVec v w) ^ 2) = t ^ 2 ∧
      Matrix.trace ((Matrix.vecMulVec v w) ^ 3) = t ^ 3 := by
  let P := Matrix.vecMulVec v w
  have hPtrace : Matrix.trace P = t := by
    change Matrix.trace (Matrix.vecMulVec v w) = t
    rw [Matrix.trace_vecMulVec, dotProduct_comm]
    exact hpair
  have hP2 : P ^ 2 = t • P := by
    rw [pow_two]
    change Matrix.vecMulVec v w * Matrix.vecMulVec v w =
      t • Matrix.vecMulVec v w
    rw [Matrix.vecMulVec_mul_vecMulVec, hpair, Matrix.vecMulVec_smul]
  have hP3 : P ^ 3 = t ^ 2 • P := by
    calc
      P ^ 3 = P ^ 2 * P := by rw [show (3 : ℕ) = 2 + 1 by omega, pow_succ]
      _ = (t • P) * P := by rw [hP2]
      _ = t • (P ^ 2) := by rw [Matrix.smul_mul, pow_two]
      _ = t ^ 2 • P := by rw [hP2, smul_smul, pow_two]
  constructor
  · rw [hP2, Matrix.trace_smul, hPtrace]
    ring
  · rw [hP3, Matrix.trace_smul, hPtrace]
    ring

/-- With no physical letters, the normalized transfer matrix vanishes. -/
private theorem normalizedTransferMatrix_phys_zero (U : MPOTensor 0 D) :
    transferMatrix (Kraus.transferMap U.normalizedFlattening) = 0 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [transferMatrix_apply, Kraus.transferMap_apply]
  simp

/-- An MPU on a nonempty physical alphabet has a nonempty bond space. -/
theorem IsMPU.neZero_bond [NeZero d] (hU : IsMPU U) : NeZero D := ⟨by
  intro hD
  subst D
  have hzero : mpo U 2 = 0 := by
    ext σ τ
    simp [mpo_apply, mpoMatrixEntry, Matrix.trace]
  have hunit := hU.mpo_mul_conjTranspose_mpo (N := 2) (by omega)
  rw [hzero] at hunit
  let c : Fin 2 → Fin d := fun _ => ⟨0, NeZero.pos d⟩
  have hentry := congrFun (congrFun hunit c) c
  simp at hentry⟩

/-- A normal left-canonical tensor with a diagonal positive fixed matrix is
already in one-block canonical form II in its given bond coordinates.

Source: arXiv:1606.00608, Appendix A, lines 1054–1077. -/
private noncomputable def oneBlockCFIIData {A : MPSTensor d D}
    [NeZero D] (hNormal : MPSTensor.IsNormalTensor A)
    (hLeft : MPSTensor.IsLeftCanonical A)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρpd : ρ.PosDef) (hρdiag : ρ.IsDiag)
    (hρfix : Kraus.transferMap A ρ = ρ) :
    MPSTensor.CPSVCanonicalFormIIData A := by
  classical
  refine {
    r := 1
    dim := fun _ => D
    dim_pos := fun _ => NeZero.pos D
    weights := fun _ => 1
    weights_ne_zero := fun _ => one_ne_zero
    blocks := fun _ => A
    blocks_normal := fun _ => hNormal
    total_dim_le := by simp
    ambient_coisometry := MPSTensor.blockInclusion (fun _ : Fin 1 => D) 0
    coisometric := ?_
    reconstruct := ?_
    blocks_left_canonical := fun _ => hLeft
    blocks_fixed_point := fun _ => ⟨ρ, hρpd, hρdiag, hρfix⟩ }
  · let V : Matrix (Fin (∑ _ : Fin 1, D)) (Fin D) ℂ :=
      MPSTensor.blockInclusion (fun _ : Fin 1 => D) 0
    have hV : (Vᴴ * V : Matrix (Fin D) (Fin D) ℂ) = 1 :=
      MPSTensor.blockInclusion_conjTranspose_mul_self _ _
    have hcard : Fintype.card (Fin D) = Fintype.card (Fin (∑ _ : Fin 1, D)) := by simp
    exact (Matrix.mul_eq_one_comm_of_card_eq _ _ ℂ
      (A := (Vᴴ : Matrix (Fin D) (Fin (∑ _ : Fin 1, D)) ℂ))
      (B := V) hcard).mp hV
  · intro i
    let V : Matrix (Fin (∑ _ : Fin 1, D)) (Fin D) ℂ :=
      MPSTensor.blockInclusion (fun _ : Fin 1 => D) 0
    have hV : (Vᴴ * V : Matrix (Fin D) (Fin D) ℂ) = 1 :=
      MPSTensor.blockInclusion_conjTranspose_mul_self _ _
    have hmul := MPSTensor.toTensorFromBlocks_mul_blockInclusion
      (fun _ : Fin 1 => (1 : ℂ)) (fun _ : Fin 1 => A) 0 i
    have hmul' : MPSTensor.toTensorFromBlocks (fun _ : Fin 1 => (1 : ℂ))
        (fun _ : Fin 1 => A) i * V = V * A i := by
      simpa only [one_smul] using hmul
    calc
      A i = (Vᴴ * V) * A i := by rw [hV, Matrix.one_mul]
      _ = Vᴴ * (MPSTensor.toTensorFromBlocks
            (fun _ : Fin 1 => (1 : ℂ)) (fun _ : Fin 1 => A) i * V) := by
              rw [hmul', Matrix.mul_assoc]
      _ = (Vᴴ * MPSTensor.toTensorFromBlocks (fun _ : Fin 1 => (1 : ℂ))
            (fun _ : Fin 1 => A) i) * V := by
              exact (Matrix.mul_assoc Vᴴ _ V).symm

/-- A trace-normalized positive diagonal factor of a positive stabilized power
gives canonical-form-II data for the original tensor, in its original bond
coordinates.

Source: arXiv:1703.09188, Proposition `prop:normal-tensor`, lines 344–355,
and equation `Erightleft`, lines 269–281. -/
private noncomputable def IsMPU.canonicalFormIIOfTransferPowerWithRho
    (hU : IsMPU U) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρpd : ρ.PosDef) (hρdiag : ρ.IsDiag)
    (hρtrace : Matrix.trace ρ = 1) (J : ℕ) (hJ : 0 < J)
    (hpower : transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ J =
      Matrix.vecMulVec ρ.vec (1 : Matrix (Fin D) (Fin D) ℂ).vec) :
    { hcfii : IsMPUCanonicalFormII U // hcfii.ρ = ρ } := by
  classical
  letI : NeZero D := ⟨by
    intro hD
    subst D
    simp [Matrix.trace] at hρtrace⟩
  letI : NeZero d := ⟨by
    intro hd
    subst d
    have hzero := normalizedTransferMatrix_phys_zero U
    rw [hzero] at hpower
    have hPzero : Matrix.vecMulVec ρ.vec
        (1 : Matrix (Fin D) (Fin D) ℂ).vec = 0 := by
      simpa only [zero_pow (Nat.ne_of_gt hJ)] using hpower.symm
    have htrP : Matrix.trace (Matrix.vecMulVec ρ.vec
        (1 : Matrix (Fin D) (Fin D) ℂ).vec) = 1 := by
      rw [Matrix.trace_vecMulVec, dotProduct_comm,
        Matrix.vec_one_dotProduct_vec_eq_trace]
      exact hρtrace
    rw [hPzero, Matrix.trace_zero] at htrP
    exact one_ne_zero htrP.symm⟩
  let A := U.normalizedFlattening
  let T := Kraus.transferMap A
  let E := transferMatrix T
  let v := ρ.vec
  let w := (1 : Matrix (Fin D) (Fin D) ℂ).vec
  let P := Matrix.vecMulVec v w
  have hpair : w ⬝ᵥ v = 1 := by
    simpa only [v, w, Matrix.vec_one_dotProduct_vec_eq_trace] using hρtrace
  have hstationary := rankOnePower_fixed E v w J hpair hpower
    (hU.trace_transferMatrix_normalizedFlattening_pow_eq_one (by omega : 1 < J + 1))
  have hrightP : P *ᵥ v = v := by
    change Matrix.vecMulVec v w *ᵥ v = v
    rw [Matrix.vecMulVec_mulVec, hpair, MulOpposite.op_one, one_smul]
  have hrightE : E *ᵥ v = v := by
    calc
      E *ᵥ v = E *ᵥ (P *ᵥ v) := by rw [hrightP]
      _ = (E * P) *ᵥ v := Matrix.mulVec_mulVec v E P
      _ = v := by rw [hstationary.1, hrightP]
  have hρfix : T ρ = ρ := by
    apply Matrix.vec_inj.mp
    simpa only [E, T, v, transferMatrix_mulVec_eq] using hrightE
  have hleftP : Matrix.vecMul w P = w := by
    change Matrix.vecMul w (Matrix.vecMulVec v w) = w
    rw [Matrix.vecMul_vecMulVec, hpair, one_smul]
  have hleftE : Matrix.vecMul w E = w := by
    calc
      Matrix.vecMul w E = Matrix.vecMul (Matrix.vecMul w P) E := by rw [hleftP]
      _ = Matrix.vecMul w (P * E) := by rw [Matrix.vecMul_vecMul]
      _ = w := by rw [hstationary.2, hleftP]
  have htracePres : IsTracePreservingMap T := by
    intro X
    calc
      Matrix.trace (T X) = w ⬝ᵥ (T X).vec := by
        exact (Matrix.vec_one_dotProduct_vec_eq_trace (T X)).symm
      _ = w ⬝ᵥ (E *ᵥ X.vec) := by
        exact congrArg (fun x => w ⬝ᵥ x) (transferMatrix_mulVec_eq T X).symm
      _ = Matrix.vecMul w E ⬝ᵥ X.vec := by rw [Matrix.dotProduct_mulVec]
      _ = Matrix.trace X := by
        rw [hleftE]
        exact Matrix.vec_one_dotProduct_vec_eq_trace X
  have hTP : MPSTensor.IsLeftCanonical A := by
    have hAdj := isTracePreservingMap_iff_traceAdjointMap_one.mp htracePres
    rw [Kraus.traceAdjointMap_mapLM_eq_mapLM_conjTranspose] at hAdj
    simpa [MPSTensor.IsLeftCanonical, Kraus.IsTP, Kraus.mapLM_apply] using hAdj
  have huniq : ∀ σ : Matrix (Fin D) (Fin D) ℂ,
      σ.PosSemidef → T σ = σ → ∃ c : ℂ, σ = c • ρ := by
    intro σ _hσ hσfix
    have hσvecfix : E *ᵥ σ.vec = σ.vec := by
      change transferMatrix T *ᵥ σ.vec = σ.vec
      rw [transferMatrix_mulVec_eq, hσfix]
    have hσpowfix_all (n : ℕ) : E ^ n *ᵥ σ.vec = σ.vec := by
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ, ← Matrix.mulVec_mulVec, hσvecfix, ih]
    have hσpowfix := hσpowfix_all J
    have hσeq : σ.vec = (Matrix.trace σ) • ρ.vec := by
      rw [hpower, Matrix.vecMulVec_mulVec,
        Matrix.vec_one_dotProduct_vec_eq_trace] at hσpowfix
      simpa only [op_smul_eq_smul] using hσpowfix.symm
    refine ⟨Matrix.trace σ, Matrix.vec_inj.mp ?_⟩
    simpa only [Matrix.vec_smul] using hσeq
  have hCh : IsChannel T := Kraus.isChannel_mapLM A hTP
  have hIrrMap : IsIrreducibleMap T :=
    isIrreducibleMap_of_channel_posDef_fixedPoint_unique T hCh ρ hρpd hρfix huniq
  have hIrr : Kraus.IsIrreducibleFamily A :=
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A hIrrMap
  have ⟨hrad, hprim⟩ :=
    spectralRadius_eq_one_and_isPrimitive_of_transferMatrix_shifted_trace T
      (fun N hN => hU.trace_transferMatrix_normalizedFlattening_pow_eq_one hN)
  have hnormal : MPSTensor.IsNormalTensor A := ⟨hIrr, hrad, hprim⟩
  let cfii := oneBlockCFIIData hnormal hTP ρ hρpd hρdiag hρfix
  refine ⟨{
    isMPU := hU
    cfii := cfii
    fullSupport_eq := by
      change (∑ _ : Fin 1, D) = D
      simp
    ρ := ρ
    ρ_posDef := hρpd
    ρ_isDiag := hρdiag
    ρ_trace := hρtrace
    ρ_fixed := hρfix }, rfl⟩

/-- The positive-power stabilization factor gives canonical form II for the
original tensor. The resulting presentation records the supplied matrix.

Source: arXiv:1703.09188, Proposition `prop:normal-tensor`, lines 344–355. -/
noncomputable def IsMPU.canonicalFormIIOfTransferPower
    (hU : IsMPU U) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρpd : ρ.PosDef) (hρdiag : ρ.IsDiag)
    (hρtrace : Matrix.trace ρ = 1) (J : ℕ) (hJ : 0 < J)
    (hpower : transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ J =
      Matrix.vecMulVec ρ.vec (1 : Matrix (Fin D) (Fin D) ℂ).vec) :
    IsMPUCanonicalFormII U :=
  (hU.canonicalFormIIOfTransferPowerWithRho ρ hρpd hρdiag hρtrace J hJ hpower).1

/-- A supplied positive diagonal fixed-pair power for a nonempty MPU has
trace-one weight, including when the supplied exponent is zero or one.

Source: arXiv:1703.09188, Proposition `prop:normal-tensor`, lines 349–354,
and equations `Erightleft`, lines 269–281. -/
theorem IsMPU.trace_eq_one_of_normalized_transfer_power [NeZero d]
    (hU : IsMPU U) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (K : ℕ)
    (hpower : transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ K =
      Matrix.vecMulVec ρ.vec (1 : Matrix (Fin D) (Fin D) ℂ).vec) :
    Matrix.trace ρ = 1 := by
  classical
  have : NeZero D := hU.neZero_bond
  let E := transferMatrix (Kraus.transferMap U.normalizedFlattening)
  let v := ρ.vec
  let w := (1 : Matrix (Fin D) (Fin D) ℂ).vec
  let P := Matrix.vecMulVec v w
  let t := Matrix.trace ρ
  have hpair : w ⬝ᵥ v = t := Matrix.vec_one_dotProduct_vec_eq_trace ρ
  have hPtrace : Matrix.trace P = t := by
    change Matrix.trace (Matrix.vecMulVec v w) = t
    rw [Matrix.trace_vecMulVec, dotProduct_comm]
    exact hpair
  by_cases hK0 : K = 0
  · subst K
    have hPone : P = 1 := by
      change E ^ 0 = P at hpower
      simpa only [pow_zero] using hpower.symm
    have hRank : D * D ≤ 1 := by
      have hrank := Matrix.rank_vecMulVec_le v w
      change P.rank ≤ 1 at hrank
      rw [hPone, Matrix.rank_one, Fintype.card_prod, Fintype.card_fin] at hrank
      exact hrank
    have hD1 : D = 1 := by
      have hDpos := NeZero.pos D
      nlinarith
    subst D
    have ht : t = 1 := by
      have htr : Matrix.trace P = 1 := by
        rw [hPone, Matrix.trace_one]
        simp
      exact hPtrace.symm.trans htr
    exact ht
  · by_cases hK1 : K = 1
    · subst K
      have hE : E = P := by
        change E ^ 1 = P at hpower
        simpa only [pow_one] using hpower
      have htr2 : Matrix.trace (E ^ 2) = 1 :=
        hU.trace_transferMatrix_normalizedFlattening_pow_eq_one (by omega)
      have htr3 : Matrix.trace (E ^ 3) = 1 :=
        hU.trace_transferMatrix_normalizedFlattening_pow_eq_one (by omega)
      rw [hE] at htr2 htr3
      obtain ⟨hp2, hp3⟩ := trace_rankOne_pow_two_three v w t hpair
      rw [hp2] at htr2
      rw [hp3] at htr3
      calc
        t = t * t ^ 2 := by rw [htr2]; ring
        _ = t ^ 3 := by ring
        _ = 1 := htr3
    · have hK : 1 < K := by omega
      have htr : Matrix.trace (E ^ K) = 1 :=
        hU.trace_transferMatrix_normalizedFlattening_pow_eq_one hK
      change E ^ K = P at hpower
      rw [hpower, hPtrace] at htr
      exact htr

/-- A positive diagonal factor of any normalized transfer power gives
canonical-form-II data for the same MPU. The exponent-zero case reduces to
bond dimension one and is replaced by the first power.

Source: arXiv:1703.09188, Proposition `prop:normal-tensor`, lines 344–355,
and equations `Erightleft`, lines 269–281. -/
private noncomputable def IsMPU.canonicalFormIIOfSuppliedTransferPowerWithRho [NeZero d]
    (hU : IsMPU U) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρpd : ρ.PosDef) (hρdiag : ρ.IsDiag) (K : ℕ)
    (hpower : transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ K =
      Matrix.vecMulVec ρ.vec (1 : Matrix (Fin D) (Fin D) ℂ).vec) :
    { hcfii : IsMPUCanonicalFormII U // hcfii.ρ = ρ } := by
  classical
  haveI : NeZero D := hU.neZero_bond
  have hρtrace := hU.trace_eq_one_of_normalized_transfer_power ρ K hpower
  by_cases hK : 0 < K
  · exact hU.canonicalFormIIOfTransferPowerWithRho
      ρ hρpd hρdiag hρtrace K hK hpower
  · have hK0 : K = 0 := by omega
    subst K
    let v := ρ.vec
    let w := (1 : Matrix (Fin D) (Fin D) ℂ).vec
    let P := Matrix.vecMulVec v w
    have hPone : P = 1 := by
      change (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) = P at hpower
      exact hpower.symm
    have hRank : D * D ≤ 1 := by
      have hrank := Matrix.rank_vecMulVec_le v w
      change P.rank ≤ 1 at hrank
      rw [hPone, Matrix.rank_one, Fintype.card_prod, Fintype.card_fin] at hrank
      exact hrank
    have hD1 : D = 1 := by
      have hDpos := NeZero.pos D
      nlinarith
    subst D
    have hEone := hU.normalized_transfer_matrix_eq_one_fin_one
    apply hU.canonicalFormIIOfTransferPowerWithRho
      ρ hρpd hρdiag hρtrace 1 (by omega)
    rw [hEone, one_pow]
    exact hPone.symm

/-- Any supplied normalized transfer power gives canonical form II for the
same MPU tensor.

Source: arXiv:1703.09188, Proposition `prop:normal-tensor`, lines 344–355. -/
noncomputable def IsMPU.canonicalFormIIOfSuppliedTransferPower [NeZero d]
    (hU : IsMPU U) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρpd : ρ.PosDef) (hρdiag : ρ.IsDiag) (K : ℕ)
    (hpower : transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ K =
      Matrix.vecMulVec ρ.vec (1 : Matrix (Fin D) (Fin D) ℂ).vec) :
    IsMPUCanonicalFormII U :=
  (hU.canonicalFormIIOfSuppliedTransferPowerWithRho ρ hρpd hρdiag K hpower).1

/-- A supplied positive diagonal transfer-power factor determines a
canonical-form-II presentation of the original MPU tensor, with that same
ambient fixed matrix.

Source: arXiv:1703.09188, Proposition `prop:normal-tensor`, lines 344–355,
and equation `Erightleft`, lines 269–281. -/
theorem IsMPU.exists_canonicalFormII_of_supplied_transfer_power [NeZero d]
    (hU : IsMPU U) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρpd : ρ.PosDef) (hρdiag : ρ.IsDiag) (K : ℕ)
    (hpower : transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ K =
      Matrix.vecMulVec ρ.vec (1 : Matrix (Fin D) (Fin D) ℂ).vec) :
    ∃ hcfii : IsMPUCanonicalFormII U, hcfii.ρ = ρ := by
  exact ⟨(hU.canonicalFormIIOfSuppliedTransferPowerWithRho
    ρ hρpd hρdiag K hpower).1,
    (hU.canonicalFormIIOfSuppliedTransferPowerWithRho
      ρ hρpd hρdiag K hpower).2⟩

end MPOTensor
