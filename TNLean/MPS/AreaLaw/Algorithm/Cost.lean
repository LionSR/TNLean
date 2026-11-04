/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.NatPolynomialBound
import TNLean.MPS.AreaLaw.Algorithm.GroundStateProgram

/-!
# The polynomial cost of the ground-state program

With the declared costs of the queries, the ground-state program run with the honest oracle
has total cost at most `P (L + 2 R² + 1) ^ d`, where `P` and `d` depend only on the local
dimension and the gap parameter. This is the running-time part of Theorem 1 of Landau,
Vazirani and Vidick, `n^{c(d, ε)} poly(n / η)`, in the cost model of the query type: the
step at every cut issues polynomially many queries on data of polynomial dimension, because
the families of the sweep have polynomial cardinality and bond dimension.

The bound is stated for the honest oracle. The cardinalities of the families, and with them
the number of queries, are guaranteed only when every query is answered correctly; against
an arbitrary oracle the enumerated net or the family of filter factors could be anything.
A bound over all oracles, as in the upper bounds of CSLib, would require the program to
truncate every answer to its declared size, which the algorithm does not do.

Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, lines 213--219 (Theorem 1) and 652--668
(the polynomial number of steps); the cost model is recorded in
`docs/paper-gaps/lvv13_cost_model.tex`.
-/

open Matrix Cslib
open scoped ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

variable {q : ℕ}

open LinearAlgebraQuery

/-! ## Monotonicity of the declared costs -/

theorem netCost_mono {m m' : ℕ} (hm : m ≤ m') {η : ℝ} (hη : 0 ≤ η) :
    netCost q m η ≤ netCost q m' η := by
  unfold netCost
  have hbase : q * m ≤ q * m' := Nat.mul_le_mul_left q hm
  have hceil : ⌈((q * m : ℕ) : ℝ) ^ 2 / η⌉₊ ≤ ⌈((q * m' : ℕ) : ℝ) ^ 2 / η⌉₊ := by
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_right _ hη
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hbase) 2
  have h1 : (2 * ⌈((q * m : ℕ) : ℝ) ^ 2 / η⌉₊ + 1) ^ (2 * (q * m) ^ 2) ≤
      (2 * ⌈((q * m' : ℕ) : ℝ) ^ 2 / η⌉₊ + 1) ^ (2 * (q * m') ^ 2) :=
    (Nat.pow_le_pow_left (by omega) _).trans
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hbase 2)))
  exact Nat.add_le_add_left (Nat.mul_le_mul (Nat.pow_le_pow_left hbase 2) h1) 1

theorem convexProgramCost_mono (L q b : ℕ) {s s' m m' : ℕ} (hs : s ≤ s') (hm : m ≤ m') :
    convexProgramCost L q b s m ≤ convexProgramCost L q b s' m' :=
  Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul hs hm) 3)) 1

theorem energyMinimizerCost_mono {L L' : ℕ} (hL : L ≤ L') (q b : ℕ) {s s' : ℕ} (hs : s ≤ s') :
    energyMinimizerCost L q b s ≤ energyMinimizerCost L' q b s' :=
  Nat.add_le_add_left
    (Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hL)) (Nat.pow_le_pow_left hs 3))
    1

/-! ## The cost of each step -/

/-- Step 1 issues `q` extension queries per member of the family. -/
theorem cost_extensionProgram_le (L i b : ℕ) (S : Finset (LeftBlockVector L q (i - 1))) :
    FreeM.cost honestOracle queryCost (extensionProgram L i b S) ≤
      S.card * (q * extensionCost q b) := by
  rw [extensionProgram, cost_unionOver]
  refine (List.sum_le_length_nsmul _ (q * extensionCost q b) fun x hx ↦ ?_).trans_eq ?_
  · obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
    rw [cost_unionOver]
    refine (List.sum_le_length_nsmul _ (extensionCost q b) fun y hy ↦ ?_).trans_eq ?_
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hy
      simp only [FreeM.cost_liftBind, FreeM.cost_pure, add_zero, queryCost_extendSite, le_refl]
    · rw [List.length_map, List.length_finRange, smul_eq_mul]
  · rw [List.length_map, Finset.length_toList, smul_eq_mul]

/-- At one net point, step 2 issues the feasibility query and at most one leading-vector
query. -/
theorem cost_feasible_ite_le (L k b m : ℕ) (S : Finset (LeftBlockVector L q k))
    (HL : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ) (η : ℝ)
    (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ) :
    queryCost (LinearAlgebraQuery.feasible L k b S m η X) +
      FreeM.cost honestOracle queryCost
        (if honestOracle (LinearAlgebraQuery.feasible L k b S m η X) = true then do
          let u ← FreeM.lift (LinearAlgebraQuery.leadingVector L k b S HL m η X)
          pure (leftColumnsOf u)
        else pure (∅ : Finset (LeftBlockVector L q k))) ≤
      2 * convexProgramCost L q b S.card m := by
  rw [queryCost_feasible]
  split_ifs
  · simp only [FreeM.cost_liftBind, FreeM.cost_pure, add_zero, queryCost_leadingVector]
    omega
  · simp only [FreeM.cost_pure, add_zero]
    omega

/-- Step 2 issues, for every bond dimension up to the uniform cut bound, one net query and
at most two convex-program queries per net point. -/
theorem cost_sizeTrimmingProgram_le (L k b : ℕ) (h : ChainHamiltonian L q 1 1) (hL : 0 < L)
    (hq : 2 ≤ q) {Δ : ℝ} (hΔ : 0 < Δ) (S : Finset (LeftBlockVector L q k)) :
    let c : ℝ := (Δ / 169) ^ 2
    let D := constantCutBond q 1 1 Δ c
    let K : ℕ := (2 * ⌈((q * D : ℕ) : ℝ) ^ 2 / (c / (2 * L))⌉₊ + 1) ^ (2 * (q * D) ^ 2)
    FreeM.cost honestOracle queryCost (sizeTrimmingProgram L k b h hq Δ S) ≤
      (D + 1) * (netCost q D (c / (2 * L)) + K * (2 * convexProgramCost L q b S.card D)) := by
  intro c D K
  let : NeZero q := ⟨by omega⟩
  have hη : 0 < c / (2 * L) :=
    div_pos (sq_pos_of_pos (div_pos hΔ (by norm_num))) (by positivity)
  simp only [sizeTrimmingProgram, cost_unionOver, FreeM.cost_liftBind, queryCost_boundaryNet,
    honestOracle_boundaryNet]
  refine (List.sum_le_length_nsmul _
    (netCost q D (c / (2 * L)) + K * (2 * convexProgramCost L q b S.card D))
    fun x hx ↦ ?_).trans_eq ?_
  · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx
    refine Nat.add_le_add (netCost_mono (Nat.le_of_lt_succ m.isLt) hη.le) ?_
    refine (List.sum_le_length_nsmul _ (2 * convexProgramCost L q b S.card D)
      fun y hy ↦ ?_).trans ?_
    · obtain ⟨X, -, rfl⟩ := List.mem_map.mp hy
      exact (cost_feasible_ite_le L k b m.val S _ _ X).trans
        (Nat.mul_le_mul_left 2 (convexProgramCost_mono L q b le_rfl (Nat.le_of_lt_succ m.isLt)))
    · rw [List.length_map, Finset.length_toList, smul_eq_mul]
      exact Nat.mul_le_mul_right _
        (card_boundary_rectangularTraceNormNet_le (by omega) hη (Nat.le_of_lt_succ m.isLt))
  · rw [List.length_map, List.length_finRange, smul_eq_mul]

/-- Step 3 issues one trimming query per member of the family. -/
theorem cost_bondTrimmingProgram_le (L i : ℕ) (hi : i ≤ L) (b m : ℕ)
    (S : Finset (LeftBlockVector L q i)) :
    FreeM.cost honestOracle queryCost (bondTrimmingProgram L i hi b m S) ≤
      S.card * schmidtTrimCost L q b := by
  rw [bondTrimmingProgram, cost_unionOver]
  refine (List.sum_le_length_nsmul _ (schmidtTrimCost L q b) fun x hx ↦ ?_).trans_eq ?_
  · obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx
    simp only [FreeM.cost_liftBind, FreeM.cost_pure, add_zero, queryCost_schmidtTrim, le_refl]
  · rw [List.length_map, Finset.length_toList, smul_eq_mul]

/-- Step 4 issues one application query per factor and member. -/
theorem cost_errorReductionProgram_le (L i r b : ℕ) (F : Finset (LeftBlockMatrix L q i))
    (T : Finset (LeftBlockVector L q i)) :
    FreeM.cost honestOracle queryCost (errorReductionProgram L i r b F T) ≤
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

/-! ## The cost of one step of the sweep -/

/-- **The cost budget of one step of the sweep** on a family of at most `s` members: the
extension queries, the net and convex-program queries over all bond dimensions up to the
uniform cut bound, the trimming queries on the selection, the filter-factor query and the
application queries. -/
noncomputable def sweepStepCostBound (q : ℕ) (Delta : ℝ) (L s : ℕ) : ℕ :=
  let c := lvvSuccessiveError Delta
  let D := constantCutBond q 1 1 Delta c
  let K := (2 * ⌈((q * D : ℕ) : ℝ) ^ 2 / (c / (2 * L))⌉₊ + 1) ^ (2 * (q * D) ^ 2)
  let b := lvvSuccessiveBondBound q Delta L
  let m := bondTrimmingRadius L (lvvReferenceBond q Delta L)
  let E := huangEnergyCount c Delta L
  let Rk := huangFilterRankBound q c Delta L
  let size := lvvSizeTrimmingCoefficient q Delta * L ^ lvvSizeTrimmingDegree q Delta
  s * (q * extensionCost q b) +
    ((D + 1) * (netCost q D (c / (2 * L)) + K * (2 * convexProgramCost L q b (q * s) D)) +
    (size * schmidtTrimCost L q b + (filterFactorsCost L q E Rk +
    E * Rk * (size * applyFactorCost L q Rk (max 1 m)))))

theorem sweepStepCostBound_mono (q : ℕ) (Delta : ℝ) (L : ℕ) {s s' : ℕ} (hs : s ≤ s') :
    sweepStepCostBound q Delta L s ≤ sweepStepCostBound q Delta L s' := by
  simp only [sweepStepCostBound]
  have h1 := Nat.mul_le_mul_right (q * extensionCost q (lvvSuccessiveBondBound q Delta L)) hs
  have h2 := convexProgramCost_mono L q (lvvSuccessiveBondBound q Delta L)
    (Nat.mul_le_mul_left q hs)
    (le_refl (constantCutBond q 1 1 Delta (lvvSuccessiveError Delta)))
  exact Nat.add_le_add h1 (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 h2)) _)) le_rfl)

/-- One step of the sweep on a family `S` costs at most the budget at `|S|`. -/
theorem cost_sweepStepProgram_le {L : ℕ} (hL : 0 < L) (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) {i : ℕ} (hi : i + 1 ≤ L)
    (S : Finset (LeftBlockVector L q i)) :
    FreeM.cost honestOracle queryCost (sweepStepProgram hq h hs h0 h1 Delta hi S) ≤
      sweepStepCostBound q Delta L S.card := by
  classical
  have hc : 0 < lvvSuccessiveError Delta := lvvSuccessiveError_pos hDelta
  simp only [sweepStepProgram, FreeM.cost_bind, FreeM.eval_lift, eval_extensionProgram,
    eval_sizeTrimmingProgram, eval_bondTrimmingProgram, honestOracle_gaussianFilterFactors,
    sweepStepCostBound]
  set chain := ChainHamiltonian.ofNearestNeighborPositive h hs h0 h1 with hchain
  set b := lvvSuccessiveBondBound q Delta L with hb
  set m := bondTrimmingRadius L (lvvReferenceBond q Delta L) with hm
  set c := lvvSuccessiveError Delta with hcdef
  set D := constantCutBond q 1 1 Delta c with hD
  set S₁ := AreaLaw.extend (i + 1) S with hS₁
  set S₂ := chain.sizeTrimmingSelection hq Delta S₁ with hS₂
  set S₃ := bondTrimSet hi m S₂ with hS₃
  set F := gaussianFilterFactors (Nat.le_of_lt hq) h h0 c Delta (i + 1) with hF
  set E := huangEnergyCount c Delta L with hE
  set Rk := huangFilterRankBound q c Delta L with hRk
  set size := lvvSizeTrimmingCoefficient q Delta * L ^ lvvSizeTrimmingDegree q Delta with hsize
  have hcard₁ : S₁.card ≤ q * S.card := card_extend_le (i + 1) S
  have hcard₂ : S₂.card ≤ size :=
    ChainHamiltonian.card_sizeTrimmingSelection_le_polynomial chain hL hq hDelta S₁
  have hcard₃ : S₃.card ≤ S₂.card := card_bondTrimSet_le hi m S₂
  have hcardF : F.card ≤ E * Rk :=
    card_gaussianFilterFactors_le (Nat.le_of_lt hq) h hs h0 h1 hc hDelta
  have h₁ := cost_extensionProgram_le L (i + 1) b S
  have h₂ := cost_sizeTrimmingProgram_le L (i + 1) b chain hL hq hDelta S₁
  have h₃ := cost_bondTrimmingProgram_le L (i + 1) hi b m S₂
  have h₅ := cost_errorReductionProgram_le L (i + 1) Rk (max 1 m) F S₃
  dsimp only at h₂
  have h₂' := h₂.trans (Nat.mul_le_mul_left (D + 1) (Nat.add_le_add_left (Nat.mul_le_mul_left _
    (Nat.mul_le_mul_left 2 (convexProgramCost_mono L q b hcard₁ le_rfl))) _))
  have h₃' := h₃.trans (Nat.mul_le_mul_right _ hcard₂)
  have h₅' := h₅.trans (Nat.mul_le_mul hcardF (Nat.mul_le_mul_right _ (hcard₃.trans hcard₂)))
  exact Nat.add_le_add h₁ (Nat.add_le_add h₂' (Nat.add_le_add h₃' (Nat.add_le_add le_rfl h₅')))

/-! ## The cost of the sweep and of the ground-state program -/

/-- The sweep up to cut `i ≤ L` costs at most `i` steps at the uniform size budget. -/
theorem cost_sweepProgram_le {L : ℕ} (hL : 0 < L) (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) (i : ℕ) (hi : i ≤ L) :
    FreeM.cost honestOracle queryCost (sweepProgram hq h hs h0 h1 Delta i) ≤
      i * sweepStepCostBound q Delta L (max 1 (lvvSuccessiveCardBound q Delta L)) := by
  induction i with
  | zero => simp [sweepProgram]
  | succ i ih =>
    have hi' : i + 1 ≤ L := hi
    simp only [sweepProgram, hi', ↓reduceDIte, FreeM.cost_bind, eval_sweepProgram]
    have hstep := cost_sweepStepProgram_le hL hq h hs h0 h1 hDelta hi'
      (lvvSweep hq h hs h0 h1 Delta i)
    have hcard : (lvvSweep hq h hs h0 h1 Delta i).card ≤
        max 1 (lvvSuccessiveCardBound q Delta L) := by
      refine (lvvSweep_spec hq h hs h0 h1 hDelta i (by omega)).1.trans ?_
      split_ifs <;> simp
    have hstep' := hstep.trans (sweepStepCostBound_mono q Delta L hcard)
    rw [Nat.succ_mul]
    exact Nat.add_le_add (ih (by omega)) hstep'

/-- **The cost budget of the ground-state program** on the padded chain of `N` sites. -/
noncomputable def groundStateCostBound (q : ℕ) (Delta : ℝ) (N : ℕ) : ℕ :=
  N * sweepStepCostBound q (min Delta 1) N (max 1 (lvvSuccessiveCardBound q (min Delta 1) N)) +
    energyMinimizerCost N q (lvvSuccessiveBondBound q (min Delta 1) N)
      (max 1 (lvvSuccessiveCardBound q (min Delta 1) N))

/-- The ground-state program costs at most the budget on the padded chain. -/
theorem cost_groundStateProgram_le {L : ℕ} (hL : 1 ≤ L) (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) (R : ℕ) :
    FreeM.cost honestOracle queryCost (groundStateProgram hq h hs h0 h1 Delta R) ≤
      groundStateCostBound q Delta (L + 2 * R ^ 2) := by
  classical
  have hg : 0 < min Delta 1 := lt_min hDelta zero_lt_one
  simp only [groundStateProgram, FreeM.cost_bind, FreeM.cost_lift, eval_sweepProgram,
    queryCost_energyMinimizer, groundStateCostBound]
  set N := L + 2 * R ^ 2 with hN
  have hi : L ≤ N := Nat.le_add_right _ _
  set z : Fin q := ⟨0, by omega⟩ with hz
  set e := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (leftConfigOfFinEquiv (q := q) hi) with he
  set S := lvvSweep hq (paddedInteraction hi z h) (paddedInteraction_supported hi z h hs)
    (fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).1)
    (fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).2) (min Delta 1) L with hS
  set B := sweepStepCostBound q (min Delta 1) N (max 1 (lvvSuccessiveCardBound q (min Delta 1) N))
    with hB
  have hsweep := cost_sweepProgram_le (by omega) hq (paddedInteraction hi z h)
    (paddedInteraction_supported hi z h hs)
    (fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).1)
    (fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).2) hg L hi
  have hcard : (S.image fun w ↦ e.symm w).card ≤
      max 1 (lvvSuccessiveCardBound q (min Delta 1) N) := by
    refine Finset.card_image_le.trans ?_
    refine (lvvSweep_spec hq (paddedInteraction hi z h) (paddedInteraction_supported hi z h hs)
      (fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).1)
      (fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).2) hg L hi).1.trans ?_
    split_ifs <;> simp
  have hmin := energyMinimizerCost_mono hi q (lvvSuccessiveBondBound q (min Delta 1) N) hcard
  exact Nat.add_le_add (hsweep.trans (Nat.mul_le_mul_right B hi)) hmin

/-! ## Polynomial bounds -/

/-- The budget of one step at the uniform size budget is polynomial in the chain length. -/
theorem isNatPolynomialBounded_sweepStepCostBound (hq : 2 ≤ q) {Delta : ℝ}
    (hDelta : 0 < Delta) :
    IsNatPolynomialBounded fun L ↦
      sweepStepCostBound q Delta L (max 1 (lvvSuccessiveCardBound q Delta L)) := by
  have hc : 0 < lvvSuccessiveError Delta := lvvSuccessiveError_pos hDelta
  obtain ⟨P, d, -, hbud⟩ := exists_lvvSuccessive_uniform_polynomial (q := q) (by omega) hDelta
  have hs : IsNatPolynomialBounded fun L ↦ max 1 (lvvSuccessiveCardBound q Delta L) :=
    ⟨P, d, fun L hL ↦ (hbud L hL).1⟩
  have hb : IsNatPolynomialBounded fun L ↦ lvvSuccessiveBondBound q Delta L :=
    ⟨P, d, fun L hL ↦ (le_max_right _ _).trans (hbud L hL).2.1⟩
  have hER : IsNatPolynomialBounded fun L ↦
      huangEnergyCount (lvvSuccessiveError Delta) Delta L *
        huangFilterRankBound q (lvvSuccessiveError Delta) Delta L :=
    ⟨P, d, fun L hL ↦ (hbud L hL).2.2.2.1⟩
  have hR : IsNatPolynomialBounded fun L ↦
      huangFilterRankBound q (lvvSuccessiveError Delta) Delta L :=
    ⟨P, d, fun L hL ↦ (hbud L hL).2.2.2.2⟩
  set c := lvvSuccessiveError Delta with hcdef
  set D := constantCutBond q 1 1 Delta c with hD
  have hK : IsNatPolynomialBounded fun L ↦
      (2 * ⌈((q * D : ℕ) : ℝ) ^ 2 / (c / (2 * L))⌉₊ + 1) ^ (2 * (q * D) ^ 2) :=
    ⟨(2 * ⌈2 * ((q * D : ℕ) : ℝ) ^ 2 / c⌉₊ + 1) ^ (2 * (q * D) ^ 2), 2 * (q * D) ^ 2,
      fun L hL ↦ (boundaryNet_card_bound_le_polynomial (q := q) (D := D) hL hc).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ L) _))⟩
  have hsize : IsNatPolynomialBounded fun L ↦
      lvvSizeTrimmingCoefficient q Delta * L ^ lvvSizeTrimmingDegree q Delta :=
    ⟨lvvSizeTrimmingCoefficient q Delta, lvvSizeTrimmingDegree q Delta, fun L _ ↦
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ L) _)⟩
  have hm : IsNatPolynomialBounded fun L ↦
      max 1 (bondTrimmingRadius L (lvvReferenceBond q Delta L)) := by
    obtain ⟨M, r, -, hrad⟩ := exists_bondTrimmingRadius_lvvReferenceBond_polynomial q Delta
    refine IsNatPolynomialBounded.max_one ⟨⌈M⌉₊, r, fun L hL ↦ ?_⟩
    have h1 := hrad L hL
    have h2 : (M : ℝ) * (L : ℝ) ^ r ≤ (⌈M⌉₊ : ℝ) * ((L + 1 : ℕ) : ℝ) ^ r := by
      gcongr
      · exact Nat.le_ceil M
      · exact_mod_cast Nat.le_succ L
    exact_mod_cast h1.trans h2
  have hL : IsNatPolynomialBounded fun L ↦ L := IsNatPolynomialBounded.id
  have hone := IsNatPolynomialBounded.const 1
  have hext : IsNatPolynomialBounded fun L ↦
      max 1 (lvvSuccessiveCardBound q Delta L) *
        (q * (1 + q * lvvSuccessiveBondBound q Delta L ^ 2)) :=
    hs.mul ((IsNatPolynomialBounded.const q).mul (hone.add
      ((IsNatPolynomialBounded.const q).mul (hb.pow 2))))
  have hconv : IsNatPolynomialBounded fun L ↦ 1 + L * q * lvvSuccessiveBondBound q Delta L ^ 2 *
      (q * max 1 (lvvSuccessiveCardBound q Delta L) * D) ^ 3 :=
    hone.add (((hL.mul (IsNatPolynomialBounded.const q)).mul (hb.pow 2)).mul
      ((((IsNatPolynomialBounded.const q).mul hs).mul (IsNatPolynomialBounded.const D)).pow 3))
  have hnet : IsNatPolynomialBounded fun L ↦ (D + 1) * ((1 + (q * D) ^ 2 *
      (2 * ⌈((q * D : ℕ) : ℝ) ^ 2 / (c / (2 * L))⌉₊ + 1) ^ (2 * (q * D) ^ 2)) +
      (2 * ⌈((q * D : ℕ) : ℝ) ^ 2 / (c / (2 * L))⌉₊ + 1) ^ (2 * (q * D) ^ 2) *
        (2 * (1 + L * q * lvvSuccessiveBondBound q Delta L ^ 2 *
          (q * max 1 (lvvSuccessiveCardBound q Delta L) * D) ^ 3))) :=
    (IsNatPolynomialBounded.const (D + 1)).mul
      ((hone.add ((IsNatPolynomialBounded.const ((q * D) ^ 2)).mul hK)).add
        (hK.mul ((IsNatPolynomialBounded.const 2).mul hconv)))
  have htrim : IsNatPolynomialBounded fun L ↦
      lvvSizeTrimmingCoefficient q Delta * L ^ lvvSizeTrimmingDegree q Delta *
        (1 + L * q * lvvSuccessiveBondBound q Delta L ^ 3) :=
    hsize.mul (hone.add ((hL.mul (IsNatPolynomialBounded.const q)).mul (hb.pow 3)))
  have hfilt : IsNatPolynomialBounded fun L ↦ 1 + huangEnergyCount c Delta L *
      huangFilterRankBound q c Delta L * L * q ^ 2 :=
    hone.add ((hER.mul hL).mul (IsNatPolynomialBounded.const (q ^ 2)))
  have happly : IsNatPolynomialBounded fun L ↦ huangEnergyCount c Delta L *
      huangFilterRankBound q c Delta L *
      (lvvSizeTrimmingCoefficient q Delta * L ^ lvvSizeTrimmingDegree q Delta *
        (1 + L * q ^ 2 * huangFilterRankBound q c Delta L ^ 2 *
          max 1 (bondTrimmingRadius L (lvvReferenceBond q Delta L)) ^ 2)) :=
    hER.mul (hsize.mul (hone.add
      (((hL.mul (IsNatPolynomialBounded.const (q ^ 2))).mul (hR.pow 2)).mul (hm.pow 2))))
  simp only [sweepStepCostBound, extensionCost, netCost, convexProgramCost, schmidtTrimCost,
    filterFactorsCost, applyFactorCost]
  exact hext.add (hnet.add (htrim.add (hfilt.add happly)))

/-- The budget of the ground-state program is polynomial in the padded chain length. -/
theorem isNatPolynomialBounded_groundStateCostBound (hq : 2 ≤ q) {Delta : ℝ}
    (hDelta : 0 < Delta) : IsNatPolynomialBounded fun N ↦ groundStateCostBound q Delta N := by
  have hg : 0 < min Delta 1 := lt_min hDelta zero_lt_one
  obtain ⟨P, d, -, hbud⟩ := exists_lvvSuccessive_uniform_polynomial (q := q) (by omega) hg
  have hs : IsNatPolynomialBounded fun N ↦ max 1 (lvvSuccessiveCardBound q (min Delta 1) N) :=
    ⟨P, d, fun N hN ↦ (hbud N hN).1⟩
  have hb : IsNatPolynomialBounded fun N ↦ lvvSuccessiveBondBound q (min Delta 1) N :=
    ⟨P, d, fun N hN ↦ (le_max_right _ _).trans (hbud N hN).2.1⟩
  have hstep := isNatPolynomialBounded_sweepStepCostBound hq hg
  simp only [groundStateCostBound, energyMinimizerCost]
  exact (IsNatPolynomialBounded.id.mul hstep).add
    ((IsNatPolynomialBounded.const 1).add
      (((IsNatPolynomialBounded.id.mul (IsNatPolynomialBounded.const q)).mul (hb.pow 2)).mul
        (hs.pow 3)))

/-- **The ground-state program has polynomial cost** (LVV13, Theorem 1, the running-time
part, in the cost model of the query type). There are `P ≥ 1` and `d`, depending only on
the local dimension and the gap parameter, such that for every chain of `L ≥ 1` sites and
every accuracy parameter `R`, the program run with the honest oracle has declared cost at
most `P (L + 2 R² + 1) ^ d`, and issues at most that many queries. LVV13, `algo53.tex`,
lines 213--219 and 652--668. -/
theorem exists_groundStateProgram_cost_polynomial (hq : 2 ≤ q) {Delta : ℝ}
    (hDelta : 0 < Delta) :
    ∃ P d : ℕ, 1 ≤ P ∧ ∀ (L R : ℕ), 1 ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
          (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1),
      FreeM.countQueries honestOracle (groundStateProgram hq h hs h0 h1 Delta R) ≤
        FreeM.cost honestOracle queryCost (groundStateProgram hq h hs h0 h1 Delta R) ∧
      FreeM.cost honestOracle queryCost (groundStateProgram hq h hs h0 h1 Delta R) ≤
        P * (L + 2 * R ^ 2 + 1) ^ d := by
  obtain ⟨P, d, hP, hbound⟩ :=
    (isNatPolynomialBounded_groundStateCostBound hq hDelta).exists_one_le
  refine ⟨P, d, hP, fun L R hL h hs h0 h1 ↦ ⟨?_, ?_⟩⟩
  · exact countQueries_le_cost honestOracle queryCost one_le_queryCost _
  · exact (cost_groundStateProgram_le hL hq h hs h0 h1 hDelta R).trans
      (hbound (L + 2 * R ^ 2) (by omega))

end TNLean.MPS.AreaLaw
