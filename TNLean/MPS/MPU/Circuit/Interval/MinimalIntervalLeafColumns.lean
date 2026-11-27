/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Circuit.Interval.MinimalIntervalColumns
import TNLean.MPS.MPU.Circuit.Interval.MinimalLeafCircuitPlacement

/-!
# Initialized columns of the actual minimal interval leaves

The one-site constructions order their outputs as a physical site, a right
bond register, and a left bond register. The canonical interval support
uses a different enumeration of the same sites. Transport of the basis
inclusions through this enumeration identifies the original leaf columns
with the actual weighted interval, including identity action on every
outside logical configuration.

The simultaneous existence theorem retains the minimal cut bases, balanced
metrics, placed leaf circuits, full clean action, supports, and gate bounds
of the existing leaf construction. It adds the actual interval column
identities for those same circuits. The circuits and their logical unitary
operators are unchanged.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open ManyBody (interval cutMatrix cutRank RegionConfig ComplConfig)


open Matrix MPSTensor MPSPreparation QuantumCircuit
open scoped Matrix Kronecker ComplexOrder MatrixOrder

namespace MPUCircuit

/-- The existing leaf order and the canonical interval order enumerate the same sites.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def leafIntervalSiteEquiv (d D N : ℕ) (i : Fin N) :
    Fin (1 + (cutBondRegisterWidth d D N i.succ + cutBondRegisterWidth d D N i.castSucc)) ≃
      Fin (intervalPacketCard d D N i.val (i.val + 1)) := by
  classical
  exact ((leafPacketSites d D N i).toEquivRange.trans
    (Set.equivOfEq (leafPacketSites_range i))).trans
      (Fintype.equivFin {s : LogicalSite d D N //
        s ∈ intervalLogicalSupport d D N i.val (i.val + 1)})

/-- The leaf-order equivalence leaves the actual logical site unchanged.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalPacketLogicalSite_leafIntervalSiteEquiv {d D N : ℕ} (i : Fin N)
    (s : Fin (1 + (cutBondRegisterWidth d D N i.succ +
      cutBondRegisterWidth d D N i.castSucc))) :
    intervalPacketLogicalSite d D N i.val (i.val + 1) (leafIntervalSiteEquiv d D N i s) =
      leafPacketSites d D N i s := by
  classical
  change ((Fintype.equivFin {t : LogicalSite d D N //
      t ∈ intervalLogicalSupport d D N i.val (i.val + 1)}).symm
    ((Fintype.equivFin {t : LogicalSite d D N //
      t ∈ intervalLogicalSupport d D N i.val (i.val + 1)})
      ((Set.equivOfEq (leafPacketSites_range i))
        ((leafPacketSites d D N i).toEquivRange s)))).val = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Reordering the leaf coordinates leaves its physical placement unchanged.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem leafConsecutiveSites_eq_comp_intervalPacketSites {d D N : ℕ} (i : Fin N) :
    (leafConsecutiveSites d D N i : _ → _) =
      intervalPacketSites d D N i.val (i.val + 1) ∘ leafIntervalSiteEquiv d D N i := by
  classical
  funext s
  change (logicalSiteEquivFin d D N) (leafPacketSites d D N i s) =
    (logicalSiteEquivFin d D N)
      (intervalPacketLogicalSite d D N i.val (i.val + 1) (leafIntervalSiteEquiv d D N i s))
  rw [intervalPacketLogicalSite_leafIntervalSiteEquiv]

/-- Reordering configurations into the canonical interval site order.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def leafIntervalConfigEquiv (d D N : ℕ) (i : Fin N) :
    Cfg d (1 + (cutBondRegisterWidth d D N i.succ + cutBondRegisterWidth d D N i.castSucc)) ≃
      Cfg d (intervalPacketCard d D N i.val (i.val + 1)) :=
  Equiv.arrowCongr (leafIntervalSiteEquiv d D N i) (Equiv.refl (Fin d))

/-- A change of site enumeration represents the same placed operator.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem placeAlong_reindex_siteEquiv {d a b n : ℕ} (e : Fin b ↪ Fin n)
    (η : Fin a ≃ Fin b) (Z : Matrix (Cfg d a) (Cfg d a) ℂ) :
    ManyBody.placeAlong (X := fun _ ↦ Fin d) (η.toEmbedding.trans e) Z =
      ManyBody.placeAlong (X := fun _ ↦ Fin d) e
        (Matrix.reindex (Equiv.arrowCongr η (Equiv.refl (Fin d)))
          (Equiv.arrowCongr η (Equiv.refl (Fin d))) Z) := by
  classical
  ext x y
  rw [ManyBody.placeAlong_apply, ManyBody.placeAlong_apply]
  have hag : (∀ v, (∀ u, (η.toEmbedding.trans e) u ≠ v) → x v = y v) ↔
      (∀ v, (∀ u, e u ≠ v) → x v = y v) := by
    constructor
    · intro h s hs
      exact h s (fun q ↦ hs (η q))
    · intro h s hs
      apply h s
      intro q
      obtain ⟨p, rfl⟩ := η.surjective q
      exact hs p
  by_cases h : ∀ v, (∀ u, e u ≠ v) → x v = y v
  · rw [ite_eq_left (hag.mpr h), ite_eq_left h]
    rfl
  · rw [ite_eq_right (mt hag.mp h), ite_eq_right h]

/-- The existing initialized leaf input is the canonical initialized interval
input after reindexing its sites.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem leafIntervalConfigEquiv_leafInput {d D N : ℕ} [NeZero d]
    (i : Fin N) (a : Fin d) :
    leafIntervalConfigEquiv d D N i
      (leafInputEmbedding (d := d) (qρ := cutBondRegisterWidth d D N i.succ)
        (qσ := cutBondRegisterWidth d D N i.castSucc) a) =
      intervalInputEmbedding (D := D) i.val (i.val + 1)
        (singleSiteIntervalConfigEquiv d N i a) := by
  classical
  funext s
  obtain ⟨t, rfl⟩ := (leafIntervalSiteEquiv d D N i).surjective s
  change (leafInputEmbedding (d := d) (qρ := cutBondRegisterWidth d D N i.succ)
      (qσ := cutBondRegisterWidth d D N i.castSucc) a)
      ((leafIntervalSiteEquiv d D N i).symm (leafIntervalSiteEquiv d D N i t)) =
    intervalPhysicalZeroConfig i.val (i.val + 1) (singleSiteIntervalConfigEquiv d N i a)
      (intervalPacketLogicalSite d D N i.val (i.val + 1) (leafIntervalSiteEquiv d D N i t))
  rw [Equiv.symm_apply_apply, intervalPacketLogicalSite_leafIntervalSiteEquiv]
  change Fin.append (fun _ : Fin 1 ↦ a)
    (0 : Cfg d (cutBondRegisterWidth d D N i.succ + cutBondRegisterWidth d D N i.castSucc)) t = _
  refine Fin.addCases (fun q ↦ ?_) (fun q ↦
    Fin.addCases (fun q ↦ ?_) (fun q ↦ ?_) q) t
  all_goals simp [leafPacketSites, leafLogicalSiteEmbedding,
    physicalSiteEmbedding, cutBondSiteEmbedding, bondSiteEmbedding,
    intervalPhysicalZeroConfig, singleSiteIntervalConfigEquiv]

/-- The existing encoded physical output and boundary labels are the canonical
interval output after reindexing its sites.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem leafIntervalConfigEquiv_leafOutput {d D N : ℕ} [NeZero d] {ρ σ : Type*}
    (i : Fin N) (eρ : ρ ↪ Cfg d (cutBondRegisterWidth d D N i.succ))
    (eσ : σ ↪ Cfg d (cutBondRegisterWidth d D N i.castSucc))
    (x : Fin d × (ρ × σ)) :
    leafIntervalConfigEquiv d D N i (leafOutputEmbedding eρ eσ x) =
      intervalOutputEmbedding i.castSucc i.succ eρ eσ
        (singleSiteIntervalConfigEquiv d N i x.1, x.2) := by
  classical
  funext s
  obtain ⟨t, rfl⟩ := (leafIntervalSiteEquiv d D N i).surjective s
  change (leafOutputEmbedding eρ eσ x)
      ((leafIntervalSiteEquiv d D N i).symm (leafIntervalSiteEquiv d D N i t)) =
    intervalBoundaryConfig i.castSucc i.succ eρ eσ
      (singleSiteIntervalConfigEquiv d N i x.1, x.2)
      (intervalPacketLogicalSite d D N i.val (i.val + 1) (leafIntervalSiteEquiv d D N i t))
  rw [Equiv.symm_apply_apply, intervalPacketLogicalSite_leafIntervalSiteEquiv]
  change Fin.append (fun _ : Fin 1 ↦ x.1) (Fin.append (eρ x.2.1) (eσ x.2.2)) t = _
  refine Fin.addCases (fun q ↦ ?_) (fun q ↦
    Fin.addCases (fun q ↦ ?_) (fun q ↦ ?_) q) t
  · convert (intervalBoundaryConfig_physical i.castSucc i.succ eρ eσ
      (singleSiteIntervalConfigEquiv d N i x.1, x.2) i
      (by change i.val ≤ i.val ∧ i.val < i.val + 1; omega)).symm using 1 <;>
      simp [leafPacketSites, leafLogicalSiteEmbedding, physicalSiteEmbedding,
        singleSiteIntervalConfigEquiv]
  · convert (congrFun (intervalBoundaryConfig_right i.castSucc i.succ eρ eσ
      (singleSiteIntervalConfigEquiv d N i x.1, x.2)) q).symm using 1 <;>
      simp [leafPacketSites, leafLogicalSiteEmbedding]
    rfl
  · convert (congrFun (intervalBoundaryConfig_left i.castSucc i.succ eρ eσ
      (singleSiteIntervalConfigEquiv d N i x.1, x.2)) q).symm using 1 <;>
      simp [leafPacketSites, leafLogicalSiteEmbedding]
    rfl

/-- Coordinate equivalences transport an initialized basis inclusion along the
corresponding basis embedding.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem basisInclusion_reindex_of_mapping {α β ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (f : α ≃ β) (g : α ↪ ι) (h : β ↪ κ)
    (hg : ∀ b, e (g (f.symm b)) = h b) :
    Matrix.reindex e f (basisInclusion g) = basisInclusion h := by
  ext x b
  change (if e.symm x = g (f.symm b) then (1 : ℂ) else 0) =
    (if x = h b then (1 : ℂ) else 0)
  simp only [e.symm_apply_eq, hg]

/-- The original leaf column equation, expressed in canonical interval coordinates.
This is a coordinate transport of the same logical matrix.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem leafColumns_reindex_interval {d D N : ℕ} [NeZero d] {ρ σ : Type*}
    [Fintype ρ] [Fintype σ]
    (i : Fin N) (eρ : ρ ↪ Cfg d (cutBondRegisterWidth d D N i.succ))
    (eσ : σ ↪ Cfg d (cutBondRegisterWidth d D N i.castSucc))
    (Z : Matrix
      (Cfg d (1 + (cutBondRegisterWidth d D N i.succ + cutBondRegisterWidth d D N i.castSucc)))
      (Cfg d (1 + (cutBondRegisterWidth d D N i.succ + cutBondRegisterWidth d D N i.castSucc))) ℂ)
    (V : Matrix (Fin d × (ρ × σ)) (Fin d) ℂ)
    (hcolumns : Z * basisInclusion (leafInputEmbedding (d := d)
      (qρ := cutBondRegisterWidth d D N i.succ)
      (qσ := cutBondRegisterWidth d D N i.castSucc)) =
      basisInclusion (leafOutputEmbedding eρ eσ) * V) :
    Matrix.reindex (leafIntervalConfigEquiv d D N i) (leafIntervalConfigEquiv d D N i) Z *
        basisInclusion (intervalInputEmbedding (D := D) i.val (i.val + 1)) =
      basisInclusion (show (ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (ManyBody.interval N i.val
          (i.val + 1)) × (ρ × σ)) ↪
        Cfg d (intervalPacketCard d D N i.val (i.val + 1)) from
          intervalOutputEmbedding i.castSucc i.succ eρ eσ) *
        Matrix.reindex (Equiv.prodCongr (singleSiteIntervalConfigEquiv d N i) (Equiv.refl _))
          (singleSiteIntervalConfigEquiv d N i) V := by
  let E := leafIntervalConfigEquiv d D N i
  let F := singleSiteIntervalConfigEquiv d N i
  let G := Equiv.prodCongr F (Equiv.refl (ρ × σ))
  have hin : Matrix.reindex E F (basisInclusion (leafInputEmbedding (d := d)
      (qρ := cutBondRegisterWidth d D N i.succ)
      (qσ := cutBondRegisterWidth d D N i.castSucc))) =
      basisInclusion (intervalInputEmbedding (D := D) i.val (i.val + 1)) := by
    apply basisInclusion_reindex_of_mapping E F
      (leafInputEmbedding (d := d)
        (qρ := cutBondRegisterWidth d D N i.succ)
        (qσ := cutBondRegisterWidth d D N i.castSucc))
      (intervalInputEmbedding (D := D) i.val (i.val + 1))
    intro b
    simpa only [E, F, Equiv.apply_symm_apply] using
      leafIntervalConfigEquiv_leafInput (D := D) i (F.symm b)
  have hout : Matrix.reindex E G (basisInclusion (leafOutputEmbedding eρ eσ)) =
      basisInclusion (show (ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (ManyBody.interval N i.val
          (i.val + 1)) × (ρ × σ)) ↪
        Cfg d (intervalPacketCard d D N i.val (i.val + 1)) from
          intervalOutputEmbedding i.castSucc i.succ eρ eσ) := by
    apply basisInclusion_reindex_of_mapping E G (leafOutputEmbedding eρ eσ)
      (show (ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (ManyBody.interval N i.val (i.val + 1)) ×
          (ρ × σ)) ↪
        Cfg d (intervalPacketCard d D N i.val (i.val + 1)) from
          intervalOutputEmbedding i.castSucc i.succ eρ eσ)
    rintro ⟨b, labels⟩
    change E ((leafOutputEmbedding eρ eσ) (F.symm b, labels)) =
      intervalOutputEmbedding i.castSucc i.succ eρ eσ (b, labels)
    simpa only [E, F, Equiv.apply_symm_apply] using
      leafIntervalConfigEquiv_leafOutput i eρ eσ (F.symm b, labels)
  have h := congrArg (Matrix.reindex E F) hcolumns
  have hm₁ := Matrix.reindexLinearEquiv_mul ℂ ℂ E E F Z
    (basisInclusion (leafInputEmbedding (d := d)
      (qρ := cutBondRegisterWidth d D N i.succ)
      (qσ := cutBondRegisterWidth d D N i.castSucc)))
  have hm₂ := Matrix.reindexLinearEquiv_mul ℂ ℂ E G F
    (basisInclusion (leafOutputEmbedding eρ eσ)) V
  simp only [Matrix.coe_reindexLinearEquiv] at hm₁ hm₂
  rw [← hm₁, ← hm₂, hin, hout] at h
  exact h

/-- Reindexing the actual leaf interval recovers the weighted one-site interval.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem minimalLeafInterval_reindex {d N : ℕ}
    (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) (operatorCoefficientTensor U)))
      ℂ (cutColumnSpace (operatorCoefficientTensor U) k))
    (P : ∀ j : Fin (N + 1), Matrix (Fin (cutRank (interval N 0 j.val)
        (operatorCoefficientTensor U)))
      (Fin (cutRank (interval N 0 j.val) (operatorCoefficientTensor U))) ℂ) (i : Fin N) :
    Matrix.reindex
      (Equiv.prodCongr (singleSiteIntervalConfigEquiv d N i) (Equiv.refl _))
      (singleSiteIntervalConfigEquiv d N i) (minimalLeafInterval U B P i) =
      vectorizedWeightedInterval (minimalOperatorInterval U B (Nat.le_succ i.val))
        (CFC.sqrt (P i.castSucc)) (CFC.sqrt (dualGramMetric (P i.succ))) := by
  ext ⟨o, β, α⟩ y
  simp [minimalLeafInterval, Matrix.reindex_apply]

open scoped Classical in
/-- The existing local leaf columns imply the actual canonical interval columns, including
identity action on every outside logical configuration.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem isMinimalIntervalColumnImplementation_leaf_of_columns {d D N : ℕ} [NeZero d]
    (hd : 2 ≤ d) (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutRank (interval N 0 j.val) (operatorCoefficientTensor U) ≤ D)
    (B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) (operatorCoefficientTensor U)))
      ℂ (cutColumnSpace (operatorCoefficientTensor U) k))
    (P : ∀ j : Fin (N + 1), Matrix (Fin (cutRank (interval N 0 j.val)
        (operatorCoefficientTensor U)))
      (Fin (cutRank (interval N 0 j.val) (operatorCoefficientTensor U))) ℂ)
    (i : Fin N)
    (Z : Matrix
      (Cfg d (1 + (cutBondRegisterWidth d D N i.succ + cutBondRegisterWidth d D N i.castSucc)))
      (Cfg d (1 + (cutBondRegisterWidth d D N i.succ + cutBondRegisterWidth d D N i.castSucc))) ℂ)
    (hcolumns : Z * basisInclusion (leafInputEmbedding (d := d)
      (qρ := cutBondRegisterWidth d D N i.succ)
      (qσ := cutBondRegisterWidth d D N i.castSucc)) =
      basisInclusion (leafOutputEmbedding
        (ρ := Fin (cutRank (interval N 0 (i.val + 1)) (operatorCoefficientTensor U)))
        (σ := Fin (cutRank (interval N 0 i.val) (operatorCoefficientTensor U)))
        (minimalCutBondRegisterEncoding hd U hU hbound i.succ)
        (minimalCutBondRegisterEncoding hd U hU hbound i.castSucc)) *
          minimalLeafInterval U B P i) :
    IsMinimalIntervalColumnImplementation hd U hU hbound B P i.castSucc i.succ
      (Nat.le_succ i.val)
      (ManyBody.placeAlong (X := fun _ ↦ Fin d) (leafConsecutiveSites d D N i) Z) := by
  have hlocal := leafColumns_reindex_interval
    (ρ := Fin (cutRank (interval N 0 (i.val + 1)) (operatorCoefficientTensor U)))
    (σ := Fin (cutRank (interval N 0 i.val) (operatorCoefficientTensor U))) i
    (minimalCutBondRegisterEncoding hd U hU hbound i.succ)
    (minimalCutBondRegisterEncoding hd U hU hbound i.castSucc) Z
    (minimalLeafInterval U B P i) hcolumns
  rw [minimalLeafInterval_reindex] at hlocal
  unfold IsMinimalIntervalColumnImplementation minimalIntervalInputEmbedding
    minimalIntervalOutputEmbedding
  have hemb : leafConsecutiveSites d D N i = (leafIntervalSiteEquiv d D N i).toEmbedding.trans
      (intervalPacketSites d D N i.val (i.val + 1)) :=
    DFunLike.coe_injective (leafConsecutiveSites_eq_comp_intervalPacketSites i)
  rw [hemb, placeAlong_reindex_siteEquiv]
  simp only [Fin.val_castSucc, Fin.val_succ]
  exact (placedColumns_iff_localColumns
    (intervalPacketSites d D N i.val (i.val + 1))
    (intervalInputEmbedding (D := D) i.val (i.val + 1))
    (intervalOutputEmbedding i.castSucc i.succ
      (minimalCutBondRegisterEncoding hd U hU hbound i.succ)
      (minimalCutBondRegisterEncoding hd U hU hbound i.castSucc))
    (Matrix.reindex (leafIntervalConfigEquiv d D N i)
      (leafIntervalConfigEquiv d D N i) Z)
    (vectorizedWeightedInterval (minimalOperatorInterval U B (Nat.le_succ i.val))
      (CFC.sqrt (P i.castSucc)) (CFC.sqrt (dualGramMetric (P i.succ))))).mpr hlocal

/-- For local dimension and chain length at least two, every unitary with the given cut-rank
bound has a simultaneous normalized interval family whose existing placed leaf circuits satisfy
the actual interval column equations. The circuit,
its logical unitary, its support, and its full clean action are unchanged by the coordinate
transport. No initialized-column witness is supplied.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem exists_normalized_minimalInterval_family_with_placed_leaf_columns_of_unitary
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
            (fun x ↦ ((MPSPreparation.finalCutPrefixEquiv d N).symm x, (β, α)))
            ((MPSPreparation.finalCutPrefixEquiv d N).symm) = U) ∧
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
                  (intervalConsecutiveSupport d D N i.val (i.val + 1)) ∧
            IsMinimalIntervalColumnImplementation hd U hU hbound B P i.castSucc i.succ
              (Nat.le_succ i.val)
              (ManyBody.placeAlong (X := fun _ ↦ Fin d) (leafConsecutiveSites d D N i) Z) := by
  obtain ⟨B, hB0, hBN, P, hP, hIntervals, h0, hlast, hfull, hLeaves⟩ :=
    exists_normalized_minimalInterval_family_with_placed_leaf_circuits_of_unitary
      hd hN U hU hbound
  refine ⟨B, hB0, hBN, P, hP, hIntervals, h0, hlast, hfull, ?_⟩
  intro i
  obtain ⟨Z, C, hZ, hcolumns, hpair, hC, hclean, hlogical, hsupport⟩ := hLeaves i
  exact ⟨Z, C, hZ, hcolumns, hpair, hC, hclean, hlogical, hsupport,
    isMinimalIntervalColumnImplementation_leaf_of_columns hd U hU hbound B P i Z hcolumns⟩

end MPUCircuit
