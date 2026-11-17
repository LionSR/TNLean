/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Algorithm.Cost
import TNLean.MPS.AreaLaw.Algorithm.ValidOracle

/-!
# The polynomial cost of the ground-state program under every valid oracle

The cost bound of the ground-state program holds for every valid oracle, with the same
budgets as for the honest oracle: the nets of a valid oracle have the standard point bound,
its filter factors have the standard count, and its sweep families have the cardinality
budget of the sweep. This is the running-time statement of Theorem 1 quantified over all
solvers of the convex programs, in the cost model of the query type.

**Scope restriction (cost model):** the bounds are on the declared oracle cost
`FreeM.cost o queryCost`, not on a proved running time of an implementation: each query is
charged a declared polynomial cost in the dimensions of its arguments, arithmetic is exact, and
nothing is proved about how a query is answered; see `docs/paper-gaps/lvv13_cost_model.tex`.

**Scope restriction (quantitative constants):** the step budgets use the library constant-cut
bond `constantCutBond`, the corrected net exponent and the size-trimming budget built from them,
not the printed quantitative bounds; see `docs/paper-gaps/lvv13_constant_bond.tex`.

**Local fix (trimming radius):** the bond-trimming budget uses the corrected quadratic radius
`bondTrimmingRadius` recorded at
<https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>.
-/

open Matrix Cslib
open scoped ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

variable {q : ℕ} {o : {ι : Type} → LinearAlgebraQuery q ι → ι}

open LinearAlgebraQuery

/-- Step 2 under a valid oracle costs at most the honest budget. -/
theorem cost_sizeTrimmingProgram_le_of_valid (hv : IsValidOracle o) (L k b : ℕ)
    (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q k)) :
    let c : ℝ := (Δ / 169) ^ 2
    let D := constantCutBond q 1 1 Δ c
    let K : ℕ := (2 * ⌈((q * D : ℕ) : ℝ) ^ 2 / (c / (2 * L))⌉₊ + 1) ^ (2 * (q * D) ^ 2)
    FreeM.cost o queryCost (sizeTrimmingProgram L k b h hq Δ S) ≤
      (D + 1) * (netCost q D (c / (2 * L)) + K * (2 * convexProgramCost L q b S.card D)) := by
  intro c D K
  let : NeZero q := ⟨by omega⟩
  have hη : 0 < c / (2 * L) :=
    div_pos (sq_pos_of_pos (div_pos hΔ (by norm_num))) (by positivity)
  simp only [sizeTrimmingProgram, cost_unionOver, FreeM.cost_liftBind, queryCost_boundaryNet]
  refine (List.sum_le_length_nsmul _
    (netCost q D (c / (2 * L)) + K * (2 * convexProgramCost L q b S.card D))
    fun x hx ↦ ?_).trans_eq ?_
  · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx
    refine Nat.add_le_add (netCost_mono (Nat.le_of_lt_succ m.isLt) hη.le) ?_
    refine (List.sum_le_length_nsmul _ (2 * convexProgramCost L q b S.card D)
      fun y hy ↦ ?_).trans ?_
    · obtain ⟨X, -, rfl⟩ := List.mem_map.mp hy
      have hcost : queryCost (LinearAlgebraQuery.feasible L k b S m.val (c / (2 * L)) X) +
          FreeM.cost o queryCost
            (if o (LinearAlgebraQuery.feasible L k b S m.val (c / (2 * L)) X) = true then do
              let u ← FreeM.lift (LinearAlgebraQuery.leadingVector L k b S
                (leftCutOperator k (h.cutLeftPart k)) m.val (c / (2 * L)) X)
              pure (leftColumnsOf u)
            else pure (∅ : Finset (LeftBlockVector L q k))) ≤
          2 * convexProgramCost L q b S.card m.val := by
        rw [queryCost_feasible]
        split_ifs
        · simp only [FreeM.cost_liftBind, FreeM.cost_pure, add_zero, queryCost_leadingVector]
          omega
        · simp only [FreeM.cost_pure, add_zero]
          omega
      exact hcost.trans
        (Nat.mul_le_mul_left 2 (convexProgramCost_mono L q b le_rfl (Nat.le_of_lt_succ m.isLt)))
    · rw [List.length_map, Finset.length_toList, smul_eq_mul]
      exact Nat.mul_le_mul_right _
        ((hv.boundaryNet_card (by omega) L k m.val _ hη).trans
          (netPointBound_mono (Nat.le_of_lt_succ m.isLt) hη.le))
  · rw [List.length_map, List.length_finRange, smul_eq_mul]

/-- Step 1, 3 and 4 under a valid oracle cost at most the honest budgets. -/
theorem cost_extensionProgram_le_of_valid (L i b : ℕ) (S : Finset (LeftBlockVector L q (i - 1))) :
    FreeM.cost o queryCost (extensionProgram L i b S) ≤ S.card * (q * extensionCost q b) := by
  rw [extensionProgram, cost_unionOver]
  refine (List.sum_le_length_nsmul _ (q * extensionCost q b) fun x hx ↦ ?_).trans_eq ?_
  · obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
    rw [cost_unionOver]
    refine (List.sum_le_length_nsmul _ (extensionCost q b) fun y hy ↦ ?_).trans_eq ?_
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hy
      simp only [FreeM.cost_liftBind, FreeM.cost_pure, add_zero, queryCost_extendSite, le_refl]
    · rw [List.length_map, List.length_finRange, smul_eq_mul]
  · rw [List.length_map, Finset.length_toList, smul_eq_mul]

theorem cost_bondTrimmingProgram_le_of_valid (L i : ℕ) (hi : i ≤ L) (b m : ℕ)
    (S : Finset (LeftBlockVector L q i)) :
    FreeM.cost o queryCost (bondTrimmingProgram L i hi b m S) ≤ S.card * schmidtTrimCost L q b := by
  rw [bondTrimmingProgram, cost_unionOver]
  refine (List.sum_le_length_nsmul _ (schmidtTrimCost L q b) fun x hx ↦ ?_).trans_eq ?_
  · obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx
    simp only [FreeM.cost_liftBind, FreeM.cost_pure, add_zero, queryCost_schmidtTrim, le_refl]
  · rw [List.length_map, Finset.length_toList, smul_eq_mul]

theorem cost_errorReductionProgram_le_of_valid (L i r b : ℕ) (F : Finset (LeftBlockMatrix L q i))
    (T : Finset (LeftBlockVector L q i)) :
    FreeM.cost o queryCost (errorReductionProgram L i r b F T) ≤
      F.card * (T.card * applyFactorCost L q r b) := by
  rw [errorReductionProgram, cost_unionOver]
  refine (List.sum_le_length_nsmul _ (T.card * applyFactorCost L q r b)
    fun x hx ↦ ?_).trans_eq ?_
  · obtain ⟨A, -, rfl⟩ := List.mem_map.mp hx
    rw [cost_unionOver]
    refine (List.sum_le_length_nsmul _ (applyFactorCost L q r b) fun y hy ↦ ?_).trans_eq ?_
    · obtain ⟨s, -, rfl⟩ := List.mem_map.mp hy
      simp only [FreeM.cost_liftBind, FreeM.cost_pure, add_zero, queryCost_applyFactor, le_refl]
    · rw [List.length_map, Finset.length_toList, smul_eq_mul]
  · rw [List.length_map, Finset.length_toList, smul_eq_mul]

/-- One step of the sweep under a valid oracle costs at most the honest step budget. -/
theorem cost_sweepStepProgram_le_of_valid (hv : IsValidOracle o) {L : ℕ} (hL : 0 < L)
    (hq : 2 ≤ q) (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) {i : ℕ} (hi : i + 1 ≤ L)
    (S : Finset (LeftBlockVector L q i)) :
    FreeM.cost o queryCost (sweepStepProgram hq h hs h0 h1 Delta hi S) ≤
      sweepStepCostBound q Delta L S.card := by
  classical
  let : NeZero q := ⟨by omega⟩
  have hc : 0 < lvvSuccessiveError Delta := lvvSuccessiveError_pos hDelta
  simp only [sweepStepProgram, FreeM.cost_bind, FreeM.eval_lift, eval_extensionProgram_of_valid hv,
    eval_sizeTrimmingProgram_of_valid hv, eval_bondTrimmingProgram_of_valid hv, FreeM.cost_lift,
    queryCost_gaussianFilterFactors, sweepStepCostBound]
  set chain := ChainHamiltonian.ofNearestNeighborPositive h hs h0 h1 with hchain
  set b := lvvSuccessiveBondBound q Delta L with hb
  set m := bondTrimmingRadius L (lvvReferenceBond q Delta L) with hm
  set c := lvvSuccessiveError Delta with hcdef
  set D := constantCutBond q 1 1 Delta c with hD
  set S₁ := AreaLaw.extend (i + 1) S with hS₁
  set S₂ := chain.sizeTrimmingSelectionWith hq Delta S₁
    (oracleNets o L (i + 1) ((Delta / 169) ^ 2 / (2 * L)))
    (oracleSolver o L (i + 1) b S₁ (leftCutOperator (i + 1) (chain.cutLeftPart (i + 1)))
      ((Delta / 169) ^ 2 / (2 * L))) with hS₂
  set S₃ := bondTrimSet hi m S₂ with hS₃
  set F := o (LinearAlgebraQuery.gaussianFilterFactors L (i + 1) (Nat.le_of_lt hq) h h0 c Delta)
    with hF
  set E := huangEnergyCount c Delta L with hE
  set Rk := huangFilterRankBound q c Delta L with hRk
  set size := lvvSizeTrimmingCoefficient q Delta * L ^ lvvSizeTrimmingDegree q Delta with hsize
  have hcard₁ : S₁.card ≤ q * S.card := card_extend_le (i + 1) S
  have hcard₂ : S₂.card ≤ size :=
    chain.card_sizeTrimmingSelectionWith_le_polynomial hL hq hDelta S₁ _
      (card_oracleNets_le hv hL hq hDelta)
  have hcard₃ : S₃.card ≤ S₂.card := card_bondTrimSet_le hi m S₂
  have hcardF : F.card ≤ E * Rk :=
    hv.gaussianFilterFactors_card L (i + 1) (Nat.le_of_lt hq) h hs h0 h1 _ _ hc hDelta
  have h₁ := cost_extensionProgram_le_of_valid (o := o) L (i + 1) b S
  have h₂ := cost_sizeTrimmingProgram_le_of_valid hv L (i + 1) b chain hL hq hDelta S₁
  have h₃ := cost_bondTrimmingProgram_le_of_valid (o := o) L (i + 1) hi b m S₂
  have h₅ := cost_errorReductionProgram_le_of_valid (o := o) L (i + 1) Rk (max 1 m) F S₃
  dsimp only at h₂
  have h₂' := h₂.trans (Nat.mul_le_mul_left (D + 1) (Nat.add_le_add_left (Nat.mul_le_mul_left _
    (Nat.mul_le_mul_left 2 (convexProgramCost_mono L q b hcard₁ le_rfl))) _))
  have h₃' := h₃.trans (Nat.mul_le_mul_right _ hcard₂)
  have h₅' := h₅.trans (Nat.mul_le_mul hcardF (Nat.mul_le_mul_right _ (hcard₃.trans hcard₂)))
  exact Nat.add_le_add h₁ (Nat.add_le_add h₂' (Nat.add_le_add h₃' (Nat.add_le_add le_rfl h₅')))

/-- The sweep under a valid oracle costs at most `i` honest step budgets. -/
theorem cost_sweepProgram_le_of_valid (hv : IsValidOracle o) {L : ℕ} (hL : 0 < L) (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) (i : ℕ) (hi : i ≤ L) :
    FreeM.cost o queryCost (sweepProgram hq h hs h0 h1 Delta i) ≤
      i * sweepStepCostBound q Delta L (max 1 (lvvSuccessiveCardBound q Delta L)) := by
  induction i with
  | zero => simp [sweepProgram]
  | succ i ih =>
    have hi' : i + 1 ≤ L := hi
    simp only [sweepProgram, hi', ↓reduceDIte, FreeM.cost_bind]
    have hstep := cost_sweepStepProgram_le_of_valid hv hL hq h hs h0 h1 hDelta hi'
      (FreeM.eval o (sweepProgram hq h hs h0 h1 Delta i))
    have hcard : (FreeM.eval o (sweepProgram hq h hs h0 h1 Delta i)).card ≤
        max 1 (lvvSuccessiveCardBound q Delta L) := by
      refine (sweepProgram_spec_of_valid hv hq h hs h0 h1 hDelta i (by omega)).1.trans ?_
      split_ifs <;> simp
    have hstep' := hstep.trans (sweepStepCostBound_mono q Delta L hcard)
    rw [Nat.succ_mul]
    exact Nat.add_le_add (ih (by omega)) hstep'

/-- The ground-state program under a valid oracle costs at most the honest budget. -/
theorem cost_groundStateProgram_le_of_valid (hv : IsValidOracle o) {L : ℕ} (hL : 1 ≤ L)
    (hq : 2 ≤ q) (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) (R : ℕ) :
    FreeM.cost o queryCost (groundStateProgram hq h hs h0 h1 Delta R) ≤
      groundStateCostBound q Delta (L + 2 * R ^ 2) := by
  classical
  have hg : 0 < min Delta 1 := lt_min hDelta zero_lt_one
  simp only [groundStateProgram, FreeM.cost_bind, FreeM.cost_lift, queryCost_energyMinimizer,
    groundStateCostBound]
  set N := L + 2 * R ^ 2 with hN
  have hi : L ≤ N := Nat.le_add_right _ _
  set z : Fin q := ⟨0, by omega⟩ with hz
  set e := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (leftConfigOfFinEquiv (q := q) hi) with he
  set S := FreeM.eval o (sweepProgram hq (paddedInteraction hi z h)
    (paddedInteraction_supported hi z h hs)
    (fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).1)
    (fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).2) (min Delta 1) L) with hS
  set B := sweepStepCostBound q (min Delta 1) N (max 1 (lvvSuccessiveCardBound q (min Delta 1) N))
    with hB
  have hsweep := cost_sweepProgram_le_of_valid hv (by omega) hq (paddedInteraction hi z h)
    (paddedInteraction_supported hi z h hs)
    (fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).1)
    (fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).2) hg L hi
  have hcard : (S.image fun w ↦ e.symm w).card ≤
      max 1 (lvvSuccessiveCardBound q (min Delta 1) N) := by
    refine Finset.card_image_le.trans ?_
    refine (sweepProgram_spec_of_valid hv hq (paddedInteraction hi z h)
      (paddedInteraction_supported hi z h hs)
      (fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).1)
      (fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).2) hg L hi).1.trans ?_
    split_ifs <;> simp
  have hmin := energyMinimizerCost_mono hi q (lvvSuccessiveBondBound q (min Delta 1) N) hcard
  exact Nat.add_le_add (hsweep.trans (Nat.mul_le_mul_right B hi)) hmin

/-- **The ground-state program has polynomial cost under every valid oracle** (LVV13,
Theorem 1, the running-time part, quantified over all solvers of the convex programs). The
constants are those of the honest oracle. -/
theorem exists_groundStateProgram_cost_polynomial_of_valid (hq : 2 ≤ q) {Delta : ℝ}
    (hDelta : 0 < Delta) :
    ∃ P d : ℕ, 1 ≤ P ∧ ∀ (o : {ι : Type} → LinearAlgebraQuery q ι → ι), IsValidOracle o →
      ∀ (L R : ℕ), 1 ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
          (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1),
      FreeM.countQueries o (groundStateProgram hq h hs h0 h1 Delta R) ≤
        FreeM.cost o queryCost (groundStateProgram hq h hs h0 h1 Delta R) ∧
      FreeM.cost o queryCost (groundStateProgram hq h hs h0 h1 Delta R) ≤
        P * (L + 2 * R ^ 2 + 1) ^ d := by
  obtain ⟨P, d, hP, hbound⟩ :=
    (isNatPolynomialBounded_groundStateCostBound hq hDelta).exists_one_le
  refine ⟨P, d, hP, fun o hv L R hL h hs h0 h1 ↦ ⟨?_, ?_⟩⟩
  · exact countQueries_le_cost o queryCost one_le_queryCost _
  · exact (cost_groundStateProgram_le_of_valid hv hL hq h hs h0 h1 hDelta R).trans
      (hbound (L + 2 * R ^ 2) (by omega))

end TNLean.MPS.AreaLaw
