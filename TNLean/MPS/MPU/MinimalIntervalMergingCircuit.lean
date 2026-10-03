/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.MinimalIntervalCircuit
import TNLean.MPS.MPU.IntervalParentColumns
import TNLean.MPS.MPU.MinimalEncodedParentColumns
import TNLean.MPS.MPU.IntervalMergingSupport
import TNLean.MPS.MPU.IntervalInputRegrouping
import TNLean.MPS.MPU.EncodedJointColumns
import TNLean.MPS.MPU.InitializedEncodingCoordinates
import TNLean.MPS.MPU.JoiningSpectatorColumns
import TNLean.MPS.MPU.MinimalCutJoiningParent
import TNLean.MPS.MPU.PermutedEncodedMergingCircuit
import TNLean.MPS.MPU.UniformMergingResourceBounds

/-!
# Exact circuits merging the actual minimal intervals

Two actual interval circuit implementations are combined within their parent
support. The joining cut, packet placement, initialized-input coordinate
bijection, compatible output encoding, normalized parent isometry, and
uniform gate bound are all derived. No joint column identity, parent Gram
identity, probability, dilation, reflection, or routing witness is assumed.

The same coherent minimal bases and balanced metrics are retained throughout
this step. Their positive definiteness and affine-hull normalization are the
metric hypotheses; the global unitary supplies such a family separately.
All outside logical configurations are unrestricted. The common workspace
is returned exactly to zero for every logical input.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSTensor MPSPreparation QuantumCircuit
open scoped Matrix Kronecker ComplexOrder MatrixOrder

namespace MPUCircuit

open scoped Classical in
/-- Two actual child circuits give an exact supported parent circuit with one
reusable clean workspace. Its complete initialized columns are the weighted
parent interval with unchanged arbitrary outside states, and its gate count
satisfies the uniform two-child recurrence.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem exists_minimalInterval_merging_circuit {d D N : ℕ} [NeZero d]
    (hd : 2 ≤ d) (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutRank (operatorCoefficientTensor U) j.val ≤ D)
    (B : ∀ t, Module.Basis (Fin (cutRank (operatorCoefficientTensor U) t))
      ℂ (cutColumnSpace (operatorCoefficientTensor U) t))
    (P : ∀ t : Fin (N + 1), Matrix (Fin (cutRank (operatorCoefficientTensor U) t.val))
      (Fin (cutRank (operatorCoefficientTensor U) t.val)) ℂ)
    (hPhull : ∀ t, P t ∈ prefixGramAffineHull
      (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B t.val aa bb q))
    (hPpos : ∀ t, (P t).PosDef)
    (hPnorm : ∀ t, ∀ X ∈ prefixGramAffineHull
      (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B t.val aa bb q),
      trace (X * dualGramMetric (P t)) = 1)
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
    (KL KR : ℕ)
    (ZL ZR : Matrix (Cfg d (logicalSiteCount d D N)) (Cfg d (logicalSiteCount d D N)) ℂ)
    (CL CR : Matrix (Cfg d (globalSiteCount d D N)) (Cfg d (globalSiteCount d D N)) ℂ)
    (hL : IsMinimalIntervalCircuitImplementation hd U hU hbound B P j m hjm.le KL ZL CL)
    (hR : IsMinimalIntervalCircuitImplementation hd U hU hbound B P m k hmk.le KR ZR CR) :
    ∃ Z : Matrix (Cfg d (logicalSiteCount d D N)) (Cfg d (logicalSiteCount d D N)) ℂ,
    ∃ C : Matrix (Cfg d (globalSiteCount d D N)) (Cfg d (globalSiteCount d D N)) ℂ,
      IsMinimalIntervalCircuitImplementation hd U hU hbound B P j k
        (hjm.le.trans hmk.le)
        ((2 * D + 1) * (KL + KR) + amplificationTreeOverhead D
          (uniformNodeGateCount d D N) (uniformReflectionGateCount d D N)
            (uniformReflectionGateCount d D N)) Z C := by
  classical
  have hN : 2 ≤ N := by have := k.isLt; omega
  obtain ⟨c, rfl⟩ : ∃ c : Fin (N - 1), internalCutEmbedding N c = m := by
    refine ⟨⟨m.val - 1, by have := k.isLt; omega⟩, ?_⟩
    apply Fin.ext
    change m.val - 1 + 1 = m.val
    omega
  let r := cutRank (operatorCoefficientTensor U) (internalCutEmbedding N c).val
  have hr : 0 < r := cutRank_pos _
    (operatorCoefficientTensor_ne_zero (by omega : 0 < d) U hU) _
  let em := minimalCutBondRegisterEncoding hd U hU hbound (internalCutEmbedding N c)
  let ej := minimalCutBondRegisterEncoding hd U hU hbound j
  let ek := minimalCutBondRegisterEncoding hd U hU hbound k
  let τcfg := {s // s ∉ intervalJointOutsideFlagSet (d := d) (D := D) j
    (internalCutEmbedding N c) k hjm hmk} → Fin d
  let α := (CutIntervalConfig d N j.val (internalCutEmbedding N c).val ×
    CutIntervalConfig d N (internalCutEmbedding N c).val k.val) × τcfg
  let ρ := (((CutIntervalConfig d N j.val (internalCutEmbedding N c).val ×
    CutIntervalConfig d N (internalCutEmbedding N c).val k.val) ×
      (Fin (cutRank (operatorCoefficientTensor U) k.val) ×
        Fin (cutRank (operatorCoefficientTensor U) j.val))) × τcfg)
  let W := balancedIntervalChildren (minimalOperatorInterval U B hjm.le)
    (minimalOperatorInterval U B hmk.le) (CFC.sqrt (P j))
    (CFC.sqrt (dualGramMetric (P k))) (P (internalCutEmbedding N c))
  let V : Matrix (ρ × (Fin r × Fin r)) α ℂ := joiningSpectatorColumns W
  let Ein := intervalJointInputEmbedding (d := d) (D := D) j (internalCutEmbedding N c) k hjm hmk
  obtain ⟨a, hn, τsite, f, hτsite, hEncoding⟩ :=
    exists_regroupedIntervalJointOutput_product_coordinates hd hr c j k hjm hmk em ej ek
  let siteEq := (finCongr hn).trans τsite
  let S₀ := intervalAuxiliaryInitializationSupport d D N j.val k.val
  let sOld := logicalSupportSites S₀
  let s := sOld.trans siteEq.symm.toEmbedding
  let E' := pullbackBasisEmbedding Ein siteEq
  have hSelected : Set.range (s.trans siteEq.toEmbedding) = Set.range sOld := by
    ext x
    simp only [s, Function.Embedding.coe_trans, Equiv.coe_toEmbedding, Function.comp_def,
      Equiv.apply_symm_apply]
  have hRange : Set.range E' = Set.range (zeroFlagEmbedding (d := d) s) := by
    apply range_pullbackBasisEmbedding_eq_zeroFlagEmbedding Ein siteEq s (Set.range sOld)
      hSelected
    intro x
    rw [range_intervalJointInputEmbedding_eq_zeroFlagEmbedding,
      mem_range_zeroFlagEmbedding_iff]
    exact (Set.forall_mem_range (f := (sOld : Fin (Nat.card S₀) → _))
      (p := fun i ↦ x i = 0)).symm
  let u := basisEncodingEquivOfRangeEq E' (zeroFlagEmbedding (d := d) s) hRange
  let gInv := (outerSpectatorJoiningRegrouping
    ((CutIntervalConfig d N j.val (internalCutEmbedding N c).val ×
      CutIntervalConfig d N (internalCutEmbedding N c).val k.val) ×
      (Fin (cutRank (operatorCoefficientTensor U) k.val) ×
        Fin (cutRank (operatorCoefficientTensor U) j.val))) (Fin r × Fin r) τcfg).trans
    (Equiv.prodCongr intervalChildrenRegrouping.symm (Equiv.refl τcfg))
  let G := intervalJointOutputEmbedding j (internalCutEmbedding N c) k hjm hmk em ej ek
    (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j
      (internalCutEmbedding N c) k hjm hmk)
  let ec := Equiv.arrowCongr siteEq.symm (Equiv.refl (Fin d))
  have hInputMap : ∀ b, ec (Ein (u.symm b)) = zeroFlagEmbedding (d := d) s b := by
    intro b
    have hh := basisEncodingEquivOfRangeEq_apply E'
      (zeroFlagEmbedding (d := d) s) hRange (u.symm b)
    rw [show basisEncodingEquivOfRangeEq E' (zeroFlagEmbedding (d := d) s) hRange = u from rfl,
      u.apply_symm_apply] at hh
    exact hh.symm
  have hOutputMap : ∀ p, ec (G (gInv p)) =
      appendBasisEmbedding f ((joiningChildBasisEmbedding (r := r) hd).trans
        (compatibleBondDilationEmbedding hd em)) p := by
    intro p
    exact congrArg (fun E ↦ E p) hEncoding
  have hRaw := minimalIntervalJointInitializedChildColumns_of_supported_individual hd U hU
    hbound B P j (internalCutEmbedding N c) k hjm hmk ZL ZR hL.2.1 hR.2.1
    hL.2.2.2.2 hR.2.2.2.2
  let Wraw := (vectorizedWeightedInterval (minimalOperatorInterval U B hjm.le)
    (CFC.sqrt (P j)) (CFC.sqrt (dualGramMetric (P (internalCutEmbedding N c)))) ⊗ₖ
      vectorizedWeightedInterval (minimalOperatorInterval U B hmk.le)
        (CFC.sqrt (P (internalCutEmbedding N c))) (CFC.sqrt (dualGramMetric (P k)))) ⊗ₖ
      (1 : Matrix τcfg τcfg ℂ)
  have hTensor : Matrix.reindex gInv.symm u Wraw = V.submatrix id u.symm := by
    exact congrArg (fun M ↦ M.submatrix id u.symm)
      (regroupedWeightedChildren_joiningSpectatorColumns
        (τ := τcfg) (minimalOperatorInterval U B hjm.le) (minimalOperatorInterval U B hmk.le)
        (CFC.sqrt (P j)) (CFC.sqrt (dualGramMetric (P k))) (P (internalCutEmbedding N c)))
  have hEncoded := encodedJointColumns_of_coordinate_identities hd f em ec u gInv.symm
    Ein G (zeroFlagEmbedding (d := d) s) hInputMap hOutputMap ZL ZR _
    (V.submatrix id u.symm) hTensor hRaw
  have hParent := normalizedJoiningParent_minimalOperatorIntervals_isIsometry
    (by omega : 0 < d) U hU B hjm.le hmk.le (hPhull j) (hPpos j)
    (hPpos (internalCutEmbedding N c)) (hPpos k) (hPnorm k)
  have hParentEncoded := normalizedJoiningParent_spectator_reindex_isIsometry
    (τ := τcfg) hr (P (internalCutEmbedding N c)) W u hParent
  have hpool : Nat.card S₀ ≤ auxiliarySiteCount d D N :=
    card_intervalAuxiliaryInitializationSupport_le d D N j.val k.val
  have hpool₂ : 2 ≤ auxiliarySiteCount d D N := by
    dsimp [auxiliarySiteCount]
    have hfirst : 1 ≤ N - 1 := by omega
    have hsecond : 1 ≤ bondRegisterWidth d D + 1 := by omega
    have hprod := Nat.mul_le_mul hfirst hsecond
    nlinarith
  have he : em ⟨0, hr⟩ = fun _ ↦ Fin.castLE hd 0 := by
    calc
      em ⟨0, hr⟩ = 0 := minimalCutBondRegisterEncoding_zero hd U hU hbound _
      _ = _ := by funext i; rfl
  have hSupport := interval_children_mem_parent_supportedOperators hjm hmk hL.2.1 hR.2.1
  have hInputSupport := interval_initializedSites_range_subset_reindexed_parent
    (d := d) (D := D) (N := N) (j := j.val) (k := k.val) siteEq
  have hPacketSupport := interval_joiningSuffix_range_subset_reindexed_parent
    c j k hjm hmk hn τsite hτsite
  obtain ⟨Z, C, hZu, hZs, hCpair, hclean, hAmbient⟩ :=
    exists_permuted_encoded_uniform_merging_circuit hd hr f em he
      (hPpos (internalCutEmbedding N c)) siteEq s hpool hpool₂
      (intervalConsecutiveSupport d D N j.val k.val) hInputSupport hPacketSupport
      ZL ZR CL CR hL.2.2.1 hR.2.2.1 hL.2.2.2.1 hR.2.2.2.1
      hSupport.1 hSupport.2 (V.submatrix id u.symm)
      (by convert hEncoded using 1; all_goals congr!)
      (by convert hParentEncoded using 1; all_goals congr!)
  have hLogical := hclean.logical_columns_of_ambient (initializedBasisMatrix_isIsometry _)
    _ _ hAmbient
  have hJInput := initializedBasisMatrix_reindex_of_mapping ec u Ein
    (zeroFlagEmbedding (d := d) s) hInputMap
  have hInputColumns : (initializedBasisMatrix (zeroFlagEmbedding (d := d) s)).submatrix
      (fun x : Cfg d (logicalSiteCount d D N) ↦ x ∘ siteEq) u =
      initializedBasisMatrix Ein := by
    rw [← hJInput]
    simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Function.comp_def,
      Equiv.symm_apply_apply]
    change (initializedBasisMatrix Ein).submatrix (fun x ↦ ec.symm (ec x)) id = _
    simp only [Equiv.symm_apply_apply]
    rfl
  have hLogicalOld := congrArg (fun M ↦ M.submatrix id u) hLogical
  rw [Matrix.submatrix_mul _ _ id (Equiv.refl _) u (Equiv.refl _).bijective] at hLogicalOld
  simp only [Equiv.coe_refl, Matrix.submatrix_id_id, Matrix.submatrix_submatrix,
    Function.comp_id, Function.id_comp] at hLogicalOld
  rw [hInputColumns] at hLogicalOld
  have hq : cutBondRegisterWidth d D N (internalCutEmbedding N c) = bondRegisterWidth d D := by
    rw [cutBondRegisterWidth, ite_eq_right]
    intro h
    have := c.isLt
    change (c.val + 1 = 0 ∨ c.val + 1 = N) at h
    omega
  have hCost := permutedEncodedUniformMergingGateCount_le_uniform hd hN hpool hr
    (hbound (internalCutEmbedding N c)) KL KR
  have hCFinal := hCpair.mono (by simpa only [globalSiteCount, hq, r] using hCost)
  have hReturned := encodedJoiningParent_minimalIntervalColumns hd U hU hbound B P
    c j k hjm hmk siteEq f hEncoding (hPpos (internalCutEmbedding N c)) u
  have hParentJointColumns := hLogicalOld.trans hReturned
  have hFinalColumns := isMinimalIntervalColumnImplementation_of_joint_initialized_columns
    hd U hU hbound B P j (internalCutEmbedding N c) k hjm hmk Z hParentJointColumns
  exact ⟨Z, C, hZu, hZs, hCFinal, hclean, hFinalColumns⟩

end MPUCircuit
