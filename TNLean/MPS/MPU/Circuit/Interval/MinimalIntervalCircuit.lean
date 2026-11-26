/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Circuit.Interval.MinimalIntervalColumns
import QICLean.Circuit.Geometry.Graph
import QICLean.Circuit.Model.CleanWorkspace
import TNLean.MPS.MPU.Circuit.Bounds.TreeAmplificationGateBounds
import TNLean.MPS.MPU.Circuit.Interval.IntervalInputRegrouping
import TNLean.MPS.MPU.Circuit.Interval.MinimalEncodedParentColumns
import TNLean.MPS.MPU.Circuit.Registers.IntervalMergingSupport
import TNLean.MPS.MPU.Circuit.Interval.EncodedJointColumns
import TNLean.MPS.MPU.Circuit.Interval.IntervalJointSuffixFactorization
import TNLean.MPS.MPU.Circuit.Interval.JoiningSpectatorColumns
import TNLean.MPS.MPU.Circuit.Interval.MinimalCutJoiningParent
import TNLean.MPS.MPU.Circuit.Merging.PermutedEncodedMergingCircuit
import TNLean.MPS.MPU.Circuit.Bounds.UniformCircuitResourceBounds

/-!
# Circuit implementations of the actual minimal intervals

An interval implementation consists of a full logical unitary with the
prescribed interval support, an actual neighboring-pair circuit, its
all-input clean-workspace identity, and the actual weighted interval columns.
These are the induction data in the balanced interval construction. The
operator and circuit are matrices, and every identity includes its phase.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.

## Recursion for actual interval circuit implementations

Once single-site implementations and an adjacent-interval merging rule are
established for one fixed minimal basis and metric family, induction on an
actual consecutive interval partition gives its circuit. The induction retains
the full logical support, all-input workspace cleanup, and weighted interval
columns. Its gate count is the numerical count on that very partition.

This is a conditional recursion lemma. The leaf and merging constructions,
and their derivation from a finite unitary, are separate results. It does not
assert the general MPU circuit theorem without those constructions.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.

It also contains the following results.

* `MPUCircuit.exists_minimalInterval_merging_circuit`: exact circuits merging the actual minimal
  intervals.
-/

section MinimalIntervalCircuit

section

open Matrix MPSTensor MPSPreparation QuantumCircuit
open scoped Kronecker Matrix ComplexOrder MatrixOrder

namespace MPUCircuit

open scoped Classical in
/-- The complete circuit conditions for the actual weighted interval, with an
explicit gate budget and one reusable initialized workspace.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def IsMinimalIntervalCircuitImplementation {d D N : ℕ} [NeZero d]
    (hd : 2 ≤ d) (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutCoefficientRank (operatorCoefficientTensor U) j.val ≤ D)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (cutColumnSpace (operatorCoefficientTensor U) k))
    (P : ∀ j : Fin (N + 1), Matrix (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val))
      (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val)) ℂ)
    (j k : Fin (N + 1)) (hjk : j.val ≤ k.val) (K : ℕ)
    (Z : Matrix (Cfg d (logicalSiteCount d D N)) (Cfg d (logicalSiteCount d D N)) ℂ)
    (C : Matrix (Cfg d (globalSiteCount d D N)) (Cfg d (globalSiteCount d D N)) ℂ) :
    Prop :=
  Z ∈ unitary (Matrix (Cfg d (logicalSiteCount d D N))
      (Cfg d (logicalSiteCount d D N)) ℂ) ∧
    Z ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (intervalConsecutiveSupport d D N j.val k.val) ∧
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph (globalSiteCount d D N))) K C ∧
    IsCleanImplementation
      (basisInclusion (workspaceEmbedding (n := logicalSiteCount d D N)
        (0 : Fin (auxiliarySiteCount d D N) → Fin d))) C Z ∧
    IsMinimalIntervalColumnImplementation hd U hU hbound B P j k hjk Z

namespace IsMinimalIntervalCircuitImplementation

open scoped Classical in
/-- Increasing the gate budget preserves all actual interval and cleanup identities.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem mono {d D N K L : ℕ} [NeZero d]
    {hd : 2 ≤ d} {U : Matrix (Cfg d N) (Cfg d N) ℂ}
    {hU : U ∈ unitaryGroup (Cfg d N) ℂ}
    {hbound : ∀ j : Fin (N + 1), cutCoefficientRank (operatorCoefficientTensor U) j.val ≤ D}
    {B : ∀ k, Module.Basis (Fin (cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (cutColumnSpace (operatorCoefficientTensor U) k)}
    {P : ∀ j : Fin (N + 1), Matrix (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val))
      (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val)) ℂ}
    {j k : Fin (N + 1)} {hjk : j.val ≤ k.val}
    {Z : Matrix (Cfg d (logicalSiteCount d D N)) (Cfg d (logicalSiteCount d D N)) ℂ}
    {C : Matrix (Cfg d (globalSiteCount d D N)) (Cfg d (globalSiteCount d D N)) ℂ}
    (h : IsMinimalIntervalCircuitImplementation hd U hU hbound B P j k hjk K Z C)
    (hKL : K ≤ L) :
    IsMinimalIntervalCircuitImplementation hd U hU hbound B P j k hjk L Z C :=
  ⟨h.1, h.2.1, h.2.2.1.mono hKL, h.2.2.2.1, h.2.2.2.2⟩

end IsMinimalIntervalCircuitImplementation

end MPUCircuit

end

section

open Matrix MPSTensor MPSPreparation
open scoped Kronecker Matrix ComplexOrder MatrixOrder

namespace MPUCircuit

open scoped Classical in
/-- Actual leaf circuits and an actual adjacent-interval merging rule extend to
every consecutive interval partition, with precisely its recursively counted
gate budget. The same basis and metric family is used throughout.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem exists_minimalInterval_circuit_of_partition
    {d D N : ℕ} [NeZero d]
    (hd : 2 ≤ d) (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutCoefficientRank (operatorCoefficientTensor U) j.val ≤ D)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (cutColumnSpace (operatorCoefficientTensor U) k))
    (P : ∀ j : Fin (N + 1), Matrix (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val))
      (Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val)) ℂ)
    (K b M : ℕ)
    (hLeaves : ∀ i : Fin N,
      ∃ Z : Matrix (Cfg d (logicalSiteCount d D N))
          (Cfg d (logicalSiteCount d D N)) ℂ,
      ∃ C : Matrix (Cfg d (globalSiteCount d D N))
          (Cfg d (globalSiteCount d D N)) ℂ,
        IsMinimalIntervalCircuitImplementation hd U hU hbound B P i.castSucc i.succ
          (Nat.le_succ i.val) K Z C)
    (hMerge : ∀ (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
        (K₁ K₂ : ℕ)
        (Z₁ Z₂ : Matrix (Cfg d (logicalSiteCount d D N))
          (Cfg d (logicalSiteCount d D N)) ℂ)
        (C₁ C₂ : Matrix (Cfg d (globalSiteCount d D N))
          (Cfg d (globalSiteCount d D N)) ℂ),
      IsMinimalIntervalCircuitImplementation hd U hU hbound B P j m
        (Nat.le_of_lt hjm) K₁ Z₁ C₁ →
      IsMinimalIntervalCircuitImplementation hd U hU hbound B P m k
        (Nat.le_of_lt hmk) K₂ Z₂ C₂ →
      ∃ Z : Matrix (Cfg d (logicalSiteCount d D N))
          (Cfg d (logicalSiteCount d D N)) ℂ,
      ∃ C : Matrix (Cfg d (globalSiteCount d D N))
          (Cfg d (globalSiteCount d D N)) ℂ,
        IsMinimalIntervalCircuitImplementation hd U hU hbound B P j k
          ((Nat.le_of_lt hjm).trans (Nat.le_of_lt hmk)) (b * (K₁ + K₂) + M) Z C)
    {start len : ℕ} {t : BinaryTree ℕ}
    (hpartition : IsIntervalPartition start len t) :
    ∀ hlimit : start + len ≤ N,
      ∃ Z : Matrix (Cfg d (logicalSiteCount d D N))
          (Cfg d (logicalSiteCount d D N)) ℂ,
      ∃ C : Matrix (Cfg d (globalSiteCount d D N))
          (Cfg d (globalSiteCount d D N)) ℂ,
        IsMinimalIntervalCircuitImplementation hd U hU hbound B P
          ⟨start, by omega⟩ ⟨start + len, by omega⟩
          (by change start ≤ start + len; omega)
          (treeGateCount K b M t) Z C := by
  induction hpartition with
  | leaf start =>
    intro hlimit
    obtain ⟨Z, C, hC⟩ := hLeaves ⟨start, by omega⟩
    exact ⟨Z, C, hC⟩
  | @node start l r left right hl hr hleft hright ihleft ihright =>
    intro hlimit
    obtain ⟨Z₁, C₁, hC₁⟩ := ihleft (by omega)
    obtain ⟨Z₂, C₂, hC₂⟩ := ihright (by omega)
    let j : Fin (N + 1) := ⟨start, by omega⟩
    let m : Fin (N + 1) := ⟨start + l, by omega⟩
    let k : Fin (N + 1) := ⟨start + (l + r), by omega⟩
    have hjm : j.val < m.val := by dsimp [j, m]; omega
    have hmk : m.val < k.val := by dsimp [m, k]; omega
    have hleftCircuit : IsMinimalIntervalCircuitImplementation hd U hU hbound B P
        j m (Nat.le_of_lt hjm) (treeGateCount K b M left) Z₁ C₁ := hC₁
    have hrightCircuit : IsMinimalIntervalCircuitImplementation hd U hU hbound B P
        m k (Nat.le_of_lt hmk) (treeGateCount K b M right) Z₂ C₂ := by
      simpa only [j, m, k, Nat.add_assoc] using hC₂
    obtain ⟨Z, C, hC⟩ := hMerge j m k hjm hmk
      (treeGateCount K b M left) (treeGateCount K b M right) Z₁ Z₂ C₁ C₂
      hleftCircuit hrightCircuit
    exact ⟨Z, C, hC⟩

end MPUCircuit

end

end MinimalIntervalCircuit

section MinimalIntervalMergingCircuit

/-!
## Exact circuits merging the actual minimal intervals

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
    (hbound : ∀ j : Fin (N + 1), cutCoefficientRank (operatorCoefficientTensor U) j.val ≤ D)
    (B : ∀ t, Module.Basis (Fin (cutCoefficientRank (operatorCoefficientTensor U) t))
      ℂ (cutColumnSpace (operatorCoefficientTensor U) t))
    (P : ∀ t : Fin (N + 1), Matrix (Fin (cutCoefficientRank (operatorCoefficientTensor U) t.val))
      (Fin (cutCoefficientRank (operatorCoefficientTensor U) t.val)) ℂ)
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
  let r := cutCoefficientRank (operatorCoefficientTensor U) (internalCutEmbedding N c).val
  have hr : 0 < r := cutCoefficientRank_pos _
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
      (Fin (cutCoefficientRank (operatorCoefficientTensor U) k.val) ×
        Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val))) × τcfg)
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
      (Fin (cutCoefficientRank (operatorCoefficientTensor U) k.val) ×
        Fin (cutCoefficientRank (operatorCoefficientTensor U) j.val))) (Fin r × Fin r) τcfg).trans
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
  have hLogical := hclean.logical_columns_of_ambient (basisInclusion_isIsometry _)
    _ _ hAmbient
  have hJInput := basisInclusion_reindex_of_mapping ec u Ein
    (zeroFlagEmbedding (d := d) s) hInputMap
  have hInputColumns : (basisInclusion (zeroFlagEmbedding (d := d) s)).submatrix
      (fun x : Cfg d (logicalSiteCount d D N) ↦ x ∘ siteEq) u =
      basisInclusion Ein := by
    rw [← hJInput]
    simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Function.comp_def,
      Equiv.symm_apply_apply]
    change (basisInclusion Ein).submatrix (fun x ↦ ec.symm (ec x)) id = _
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

end MinimalIntervalMergingCircuit
