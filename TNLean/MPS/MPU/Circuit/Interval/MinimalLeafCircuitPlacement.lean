/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Circuit.Interval.MinimalLeafCircuits
import QICLean.Circuit.Compile.ChainPlacement

/-!
# Placement of the actual leaf circuits in the common workspace

For chains of length at least two, the common workspace contains a site for
the leaf construction. Placement of the derived local circuits gives actual
neighboring-pair circuits on the complete register. Cleanup holds on every
logical input, and the logical operators act only on their leaf intervals.
The normalized metrics, interval identities, and exact full-root equation
are retained in the simultaneous existence theorem.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSTensor MPSPreparation QuantumCircuit
open scoped Matrix ComplexOrder MatrixOrder

open ManyBody (interval cutMatrix cutRank RegionConfig ComplConfig)

namespace MPUCircuit

/-- A chain with at least two physical sites has a nonempty common auxiliary and workspace
register.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem auxiliarySiteCount_pos_of_two_le {d D N : ℕ} (hN : 2 ≤ N) :
    0 < auxiliarySiteCount d D N := by
  unfold auxiliarySiteCount
  have hcut : 0 < N - 1 := by omega
  positivity

/-- One reusable workspace site inside the common initialized workspace register.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def leafWorkspaceSites (d D N : ℕ) (hN : 2 ≤ N) : Fin 1 ↪ Fin (auxiliarySiteCount d D N) where
  toFun _ := ⟨0, auxiliarySiteCount_pos_of_two_le hN⟩
  inj' _ _ _ := Subsingleton.elim _ _

/-- Placement of a leaf logical packet and its one workspace site in the complete register.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def leafCleanPlacementSites (d D N : ℕ) (hN : 2 ≤ N) (i : Fin N) :
    Fin ((1 + (cutBondRegisterWidth d D N i.succ +
      cutBondRegisterWidth d D N i.castSucc)) + 1) ↪ Fin (globalSiteCount d D N) :=
  cleanImplementationSites (leafConsecutiveSites d D N i) (leafWorkspaceSites d D N hN)

/-- An actual clean leaf circuit, placed in the common workspace, remains clean on every logical
input and has an explicit neighboring-pair gate bound.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem placed_leaf_circuit_isCleanImplementation {d D N K : ℕ} [NeZero d]
    (hN : 2 ≤ N) (i : Fin N)
    {Z : Matrix
      (Cfg d (1 + (cutBondRegisterWidth d D N i.succ + cutBondRegisterWidth d D N i.castSucc)))
      (Cfg d (1 + (cutBondRegisterWidth d D N i.succ + cutBondRegisterWidth d D N i.castSucc))) ℂ}
    {C : Matrix
      (Cfg d ((1 + (cutBondRegisterWidth d D N i.succ +
        cutBondRegisterWidth d D N i.castSucc)) + 1))
      (Cfg d ((1 + (cutBondRegisterWidth d D N i.succ +
        cutBondRegisterWidth d D N i.castSucc)) + 1)) ℂ}
    (hC : IsGateProduct (Geometry.graph (SimpleGraph.pathGraph
      ((1 + (cutBondRegisterWidth d D N i.succ + cutBondRegisterWidth d D N i.castSucc)) + 1))) K C)
    (hclean : IsCleanImplementation
      (basisInclusion (workspaceEmbedding
        (n := 1 + (cutBondRegisterWidth d D N i.succ + cutBondRegisterWidth d D N i.castSucc))
        (0 : Fin 1 → Fin d))) C Z) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph (globalSiteCount d D N)))
        (K * (2 * globalSiteCount d D N))
        (ManyBody.placeAlong (X := fun _ ↦ Fin d) (leafCleanPlacementSites d D N hN i) C) ∧
      IsCleanImplementation
        (basisInclusion (workspaceEmbedding
          (n := logicalSiteCount d D N) (0 : Fin (auxiliarySiteCount d D N) → Fin d)))
        (ManyBody.placeAlong (X := fun _ ↦ Fin d) (leafCleanPlacementSites d D N hN i) C)
        (ManyBody.placeAlong (X := fun _ ↦ Fin d) (leafConsecutiveSites d D N i) Z) :=
  isGateProduct_isCleanImplementation_placeAlong (leafConsecutiveSites d D N i)
    (leafWorkspaceSites d D N hN) hC hclean


open scoped Classical in
/-- A finite unitary with bounded physical cut ranks admits one coherent normalized interval
family and actual clean leaf circuits in the complete register. Both the logical leaf operators
and the complete circuits are unitary; each logical operator acts only on its leaf support. The
common workspace is exactly erased on every logical input, and the gate bound is polynomial in the
bond bound and register size.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem exists_normalized_minimalInterval_family_with_placed_leaf_circuits_of_unitary
    {d D N : ℕ} [NeZero d]
    (hd : 2 ≤ d) (hN : 2 ≤ N)
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutRank (interval N 0 j.val) (operatorCoefficientTensor U) ≤ D) :
    ∃ B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) (operatorCoefficientTensor U)))
        ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k),
      (∀ q, (B 0 q).val = 1) ∧
      (∀ q, (B N q).val = MPSPreparation.fullCutVector (operatorCoefficientTensor U)) ∧
      ∃ P : ∀ j : Fin (N + 1),
          Matrix (Fin (cutRank (interval N 0 j.val) (operatorCoefficientTensor U)))
            (Fin (cutRank (interval N 0 j.val) (operatorCoefficientTensor U))) ℂ,
        (∀ j, P j ∈ prefixGramAffineHull
            (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j.val aa bb q) ∧
          (P j).PosDef ∧ (dualGramMetric (P j)).PosDef ∧
          (∀ X ∈ prefixGramAffineHull
              (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j.val aa bb q),
            trace (X * dualGramMetric (P j)) = 1) ∧
          trace ((dualGramMetric (P j))⁻¹ * (P j)⁻¹) =
            (cutRank (interval N 0 j.val) (operatorCoefficientTensor U) : ℂ) ^ 2) ∧
        (∀ (j k : Fin (N + 1)) (hjk : j.val ≤ k.val),
          (vectorizedWeightedInterval (minimalOperatorInterval U B hjk)
              (CFC.sqrt (P j)) (CFC.sqrt (dualGramMetric (P k))))ᴴ *
            vectorizedWeightedInterval (minimalOperatorInterval U B hjk)
              (CFC.sqrt (P j)) (CFC.sqrt (dualGramMetric (P k))) = 1) ∧
        P 0 = 1 ∧ P (Fin.last N) = 1 ∧
        (∀ (α : Fin (cutRank (interval N 0 0) (operatorCoefficientTensor U)))
          (β : Fin (cutRank (interval N 0 N) (operatorCoefficientTensor U))),
          (vectorizedWeightedInterval (minimalOperatorInterval U B (Nat.zero_le N))
            (CFC.sqrt (P 0)) (CFC.sqrt (dualGramMetric (P (Fin.last N))))).submatrix
            (fun x ↦ (fullCutIntervalConfigEquiv d N x, (β, α)))
            (fullCutIntervalConfigEquiv d N) = U) ∧
        ∀ i : Fin N,
          ∃ Z : Matrix
              (Cfg d (1 + (cutBondRegisterWidth d D N i.succ +
                cutBondRegisterWidth d D N i.castSucc)))
              (Cfg d (1 + (cutBondRegisterWidth d D N i.succ +
                cutBondRegisterWidth d D N i.castSucc))) ℂ,
          ∃ C : Matrix (Cfg d (globalSiteCount d D N)) (Cfg d (globalSiteCount d D N)) ℂ,
            Z ∈ unitary (Matrix
              (Cfg d (1 + (cutBondRegisterWidth d D N i.succ +
                cutBondRegisterWidth d D N i.castSucc)))
              (Cfg d (1 + (cutBondRegisterWidth d D N i.succ +
                cutBondRegisterWidth d D N i.castSucc))) ℂ) ∧
            Z * basisInclusion (leafInputEmbedding (d := d)
                (qρ := cutBondRegisterWidth d D N i.succ)
                (qσ := cutBondRegisterWidth d D N i.castSucc)) =
              basisInclusion (leafOutputEmbedding
                  (ρ := Fin (cutRank (interval N 0 (i.val + 1)) (operatorCoefficientTensor U)))
                  (σ := Fin (cutRank (interval N 0 i.val) (operatorCoefficientTensor U)))
                  (minimalCutBondRegisterEncoding hd U hU hbound i.succ)
                  (minimalCutBondRegisterEncoding hd U hU hbound i.castSucc)) *
                minimalLeafInterval U B P i ∧
            IsGateProduct (Geometry.graph (SimpleGraph.pathGraph (globalSiteCount d D N)))
              ((38 * (d ^ 4 * D ^ 2) ^ 6) * (2 * globalSiteCount d D N)) C ∧
            C ∈ unitary
              (Matrix (Cfg d (globalSiteCount d D N)) (Cfg d (globalSiteCount d D N)) ℂ) ∧
            IsCleanImplementation
              (basisInclusion (workspaceEmbedding
                (n := logicalSiteCount d D N) (0 : Fin (auxiliarySiteCount d D N) → Fin d)))
              C (ManyBody.placeAlong (X := fun _ ↦ Fin d) (leafConsecutiveSites d D N i) Z) ∧
            ManyBody.placeAlong (X := fun _ ↦ Fin d) (leafConsecutiveSites d D N i) Z ∈ unitary
              (Matrix (Cfg d (logicalSiteCount d D N)) (Cfg d (logicalSiteCount d D N)) ℂ) ∧
            ManyBody.placeAlong (X := fun _ ↦ Fin d) (leafConsecutiveSites d D N i) Z ∈
              ManyBody.supportedOperators (fun _ ↦ Fin d)
                  (intervalConsecutiveSupport d D N i.val (i.val + 1)) := by
  obtain ⟨B, hB0, hBN, P, hP, hIntervals, h0, hlast, hfull, hLeaves⟩ :=
    exists_normalized_minimalInterval_family_with_leaf_circuits_of_unitary
      hd (by omega : 0 < N) U hU hbound
  refine ⟨B, hB0, hBN, P, hP, hIntervals, h0, hlast, hfull, ?_⟩
  intro i
  obtain ⟨Z, C, hZ, hcolumns, hC, hclean⟩ := hLeaves i
  have hplaced := placed_leaf_circuit_isCleanImplementation hN i hC hclean
  have hD : 0 < D := (ManyBody.cutRank_pos (D := interval N 0 0)
    (operatorCoefficientTensor_ne_zero (by omega : 0 < d) U hU)).trans_le (hbound 0)
  have hdim := leaf_workspace_dimension_le_of_width_le hd hD
    (cutBondRegisterWidth_le d D N i.succ) (cutBondRegisterWidth_le d D N i.castSucc)
  have hcost := Nat.mul_le_mul_left 38 (Nat.pow_le_pow_left hdim 6)
  have hpair := hplaced.1.mono (Nat.mul_le_mul_right (2 * globalSiteCount d D N) hcost)
  exact ⟨Z, ManyBody.placeAlong (X := fun _ ↦ Fin d) (leafCleanPlacementSites d D N hN i) C,
    hZ, hcolumns, hpair, hpair.mem_unitaryGroup, hplaced.2,
    ManyBody.placeAlong_mem_unitaryGroup _ hZ,
    leaf_placeAlong_mem_supportedOperators i Z⟩

end MPUCircuit
