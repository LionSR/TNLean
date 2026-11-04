/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Algorithm.GroundStateProgram
import TNLean.MPS.AreaLaw.ViableSet.SampledFactors

/-!
# Valid oracles

The honest oracle answers every query with the object chosen by the definitions of the
sweep. A solver of the algorithm is free to return any optimal solution of a convex
program, any trace-norm net and any cut decomposition of the filters; the deterministic
operations (extension, trimming, applying a factor) it must perform exactly. A *valid*
oracle, `IsValidOracle`, is one whose answers satisfy exactly these conditions. This module
shows that the programs of the Gaussian route are correct for every valid oracle: the sweep
is viable at every cut with the same size and bond bounds, and the ground-state program
outputs a unit matrix product state with the same overlap guarantee. The honest oracle is
valid, so the earlier statements are instances.

This lifts the honest-oracle restriction recorded in `docs/paper-gaps/lvv13_cost_model.tex`
for the correctness of the algorithm.

**Local fix (trimming radius):** bond trimming uses the corrected quadratic radius
`bondTrimmingRadius` recorded at
<https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>.

**Scope restriction (quantitative constants):** the size and bond budgets use the library
constant-cut bond `constantCutBond` and the corrected net exponent, not the printed quantitative
bounds; see `docs/paper-gaps/lvv13_constant_bond.tex`.

Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, lines 219 and 484--487 (the solver is any
polynomial-time solver of the convex programs), and the proof of Theorem 1, lines 652--678.
-/

open Matrix Cslib
open scoped InnerProductSpace ComplexOrder MatrixOrder Kronecker

namespace TNLean.MPS.AreaLaw

variable {q : ℕ}

open LinearAlgebraQuery

/-- The standard point bound of a trace-norm net of radius `η` on the boundary space of a
bond of dimension `m`. -/
noncomputable def netPointBound (q m : ℕ) (η : ℝ) : ℕ :=
  (2 * ⌈((q * m : ℕ) : ℝ) ^ 2 / η⌉₊ + 1) ^ (2 * (q * m) ^ 2)

theorem netPointBound_mono {m m' : ℕ} (hm : m ≤ m') {η : ℝ} (hη : 0 ≤ η) :
    netPointBound q m η ≤ netPointBound q m' η := by
  unfold netPointBound
  have hbase : q * m ≤ q * m' := Nat.mul_le_mul_left q hm
  have hceil : ⌈((q * m : ℕ) : ℝ) ^ 2 / η⌉₊ ≤ ⌈((q * m' : ℕ) : ℝ) ^ 2 / η⌉₊ := by
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_right _ hη
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hbase) 2
  exact (Nat.pow_le_pow_left (by omega) _).trans
    (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hbase 2)))

/-- The sampled factors contain the left factors of the decomposition of the sampled
projector into its scaled chosen word decompositions. -/
theorem isAdmissibleSampledFactors_sampledFactors {L : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ) {ℓ m : ℕ}
    (I : Fin ℓ → Fin m → Fin L) (i : ℕ) :
    ∃ (ι : Type) (J : Finset ι) (A : ι → LeftBlockMatrix L q i) (B : ι → RightBlockMatrix L q i),
      Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) (sampledProjector h E₀ I) =
          ∑ t ∈ J, A t ⊗ₖ B t ∧
        ∀ t ∈ J, A t ∈ AreaLaw.sampledFactors h E₀ I i := by
  classical
  refine ⟨(t : Fin ℓ) × Fin (operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
    (leftBlock L i) (bondComplementWord h (I t)))), Finset.univ,
    fun p ↦ sampledLeftFactor h E₀ I i p.1 p.2,
    fun p ↦ cutRightFactor (bondComplementWord h (I p.1)) p.2,
    cutOperator_sampledProjector_eq_sum h E₀ I i, fun p _ ↦ ?_⟩
  simp only [AreaLaw.sampledFactors, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image]
  exact ⟨p.1, p.2, rfl⟩

/-- **A valid oracle** answers the deterministic queries exactly, enumerates nets that cover
the boundary densities with the standard point bound, reports feasibility truthfully,
returns the leading vector of some optimal solution of every convex program, returns
admissible filter factors with the standard count and rank bounds, and returns a unit
vector of least energy for the final convex program. -/
structure LinearAlgebraQuery.IsValidOracle (o : {ι : Type} → LinearAlgebraQuery q ι → ι) :
    Prop where
  extendSite : ∀ (L i b : ℕ) (k : Fin q) (v : LeftBlockVector L q (i - 1)),
    o (LinearAlgebraQuery.extendSite L i b k v) = AreaLaw.extendSite i k v
  boundaryNet_cover : ∀ (L k m : ℕ) (η : ℝ), 0 < η →
    ∀ Y : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ,
      rectangularTraceNorm Y ≤ 1 →
      ∃ X ∈ o (LinearAlgebraQuery.boundaryNet L k m η), rectangularTraceNorm (Y - X) ≤ η
  boundaryNet_card : 1 ≤ q → ∀ (L k m : ℕ) (η : ℝ), 0 < η →
    (o (LinearAlgebraQuery.boundaryNet L k m η)).card ≤ netPointBound q m η
  feasible : ∀ (L k b : ℕ) (S : Finset (LeftBlockVector L q k)) (m : ℕ) (η : ℝ)
    (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ),
    o (LinearAlgebraQuery.feasible L k b S m η X) =
      honestOracle (LinearAlgebraQuery.feasible L k b S m η X)
  leadingVector : ∀ (L k b : ℕ) (S : Finset (LeftBlockVector L q k))
    (HL : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ)
    (m : ℕ) (η : ℝ),
    IsAdmissibleLeadingVector (S : Set (LeftBlockVector L q k)) HL m η
      (fun X ↦ o (LinearAlgebraQuery.leadingVector L k b S HL m η X))
  schmidtTrim : ∀ (L i : ℕ) (hi : i ≤ L) (b m : ℕ) (u : LeftBlockVector L q i),
    o (LinearAlgebraQuery.schmidtTrim L i hi b m u) = leftSchmidtTrim hi m u
  gaussianFilterFactors_admissible : ∀ (L i : ℕ) (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (h0 : ∀ j, 0 ≤ h j)
    (c Delta : ℝ),
    IsAdmissibleFilterFactors hq h h0 c Delta i
      (o (LinearAlgebraQuery.gaussianFilterFactors L i hq h h0 c Delta))
  gaussianFilterFactors_card : ∀ (L i : ℕ) (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (_hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (_h1 : ∀ j, h j ≤ 1)
    (c Delta : ℝ), 0 < c → 0 < Delta →
    (o (LinearAlgebraQuery.gaussianFilterFactors L i hq h h0 c Delta)).card ≤
      huangEnergyCount c Delta L * huangFilterRankBound q c Delta L
  gaussianFilterFactors_rank : ∀ (L i : ℕ) (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (_hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (_h1 : ∀ j, h j ≤ 1)
    (c Delta : ℝ), 0 < c → 0 < Delta → i ≤ L →
    ∀ A ∈ o (LinearAlgebraQuery.gaussianFilterFactors L i hq h h0 c Delta), ∀ k, k < i →
      operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
        (A.submatrix leftConfigOfFin leftConfigOfFin)) ≤ huangFilterRankBound q c Delta L
  sampledFactors : ∀ (L i : ℕ) (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (E₀ : ℝ) (ℓ m D : ℕ) (I : Fin ℓ → Fin m → Fin L),
    (∀ t k, operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k)
      (bondComplementWord h (I t))) ≤ D) →
    (∃ (ι : Type) (J : Finset ι) (A : ι → LeftBlockMatrix L q i) (B : ι → RightBlockMatrix L q i),
      Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) (sampledProjector h E₀ I) =
          ∑ t ∈ J, A t ⊗ₖ B t ∧
        ∀ t ∈ J, A t ∈ o (LinearAlgebraQuery.sampledFactors L i h E₀ ℓ m D I)) ∧
    (o (LinearAlgebraQuery.sampledFactors L i h E₀ ℓ m D I)).card ≤ ℓ * D ∧
    (i ≤ L → ∀ A ∈ o (LinearAlgebraQuery.sampledFactors L i h E₀ ℓ m D I), ∀ k, k < i →
      operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
        (A.submatrix leftConfigOfFin leftConfigOfFin)) ≤ D)
  applyFactor : ∀ (L i r b : ℕ) (A : LeftBlockMatrix L q i) (s : LeftBlockVector L q i),
    o (LinearAlgebraQuery.applyFactor L i r b A s) = toEuclideanLin A s
  energyMinimizer : ∀ (L b : ℕ) (H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (S : Finset (EuclideanSpace ℂ (Fin L → Fin q))),
    Submodule.span ℂ (S : Set (EuclideanSpace ℂ (Fin L → Fin q))) ≠ ⊥ →
    o (LinearAlgebraQuery.energyMinimizer L b H S) ∈
        Submodule.span ℂ (S : Set (EuclideanSpace ℂ (Fin L → Fin q))) ∧
      ‖o (LinearAlgebraQuery.energyMinimizer L b H S)‖ = 1 ∧
      ∀ w ∈ Submodule.span ℂ (S : Set (EuclideanSpace ℂ (Fin L → Fin q))), ‖w‖ = 1 →
        (⟪o (LinearAlgebraQuery.energyMinimizer L b H S),
          toEuclideanLin H (o (LinearAlgebraQuery.energyMinimizer L b H S))⟫_ℂ).re ≤
          (⟪w, toEuclideanLin H w⟫_ℂ).re

/-- The honest oracle is valid. -/
theorem LinearAlgebraQuery.isValidOracle_honestOracle :
    IsValidOracle (honestOracle (q := q)) where
  extendSite _ _ _ _ _ := rfl
  boundaryNet_cover _ _ _ _ hη Y hY := exists_mem_rectangularTraceNormNet hη Y hY
  boundaryNet_card hq _ _ _ _ hη := card_boundary_rectangularTraceNormNet_le hq hη le_rfl
  feasible _ _ _ _ _ _ _ := rfl
  leadingVector _ _ _ _ HL m η := isAdmissibleLeadingVector_boundaryLeadingVector _ HL m η
  schmidtTrim _ _ _ _ _ _ := rfl
  gaussianFilterFactors_admissible _ i hq h h0 c Delta :=
    isAdmissibleFilterFactors_gaussianFilterFactors hq h h0 c Delta i
  gaussianFilterFactors_card _ _ hq h hs h0 h1 _ _ hc hDelta :=
    card_gaussianFilterFactors_le hq h hs h0 h1 hc hDelta
  gaussianFilterFactors_rank _ _ hq h hs h0 h1 _ _ hc hDelta hi _ hA k hki :=
    operatorSchmidtRank_of_mem_gaussianFilterFactors hq h hs h0 h1 hc hDelta hi hA k hki
  sampledFactors _ i h E₀ _ _ _ I hrank :=
    ⟨isAdmissibleSampledFactors_sampledFactors h E₀ I i,
      card_sampledFactors_le h E₀ I i fun t ↦ hrank t i,
      fun hi _ hA k hki ↦ operatorSchmidtRank_of_mem_sampledFactors hi h E₀ I hrank hA k hki⟩
  applyFactor _ _ _ _ _ _ := rfl
  energyMinimizer _ _ H S hU := energyMinimizer_spec H S hU

/-! ## Evaluation under a valid oracle -/

variable {o : {ι : Type} → LinearAlgebraQuery q ι → ι}

/-- Under a valid oracle, the program at one net point returns the left columns of the
oracle's leading vector when the point is feasible, and nothing otherwise. -/
theorem eval_feasible_ite_of_valid (hv : IsValidOracle o) (L k b m : ℕ)
    (S : Finset (LeftBlockVector L q k))
    (HL : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ) (η : ℝ)
    (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ) :
    FreeM.eval o
      (if o (LinearAlgebraQuery.feasible L k b S m η X) = true then do
          let u ← FreeM.lift (LinearAlgebraQuery.leadingVector L k b S HL m η X)
          pure (leftColumnsOf u)
        else pure (∅ : Finset (LeftBlockVector L q k))) =
      open Classical in
      if (feasibleBoundaryDensities (S : Set (LeftBlockVector L q k)) m η X).Nonempty then
        leftColumnsOf (o (LinearAlgebraQuery.leadingVector L k b S HL m η X))
      else ∅ := by
  classical
  rw [hv.feasible]
  by_cases hX : (feasibleBoundaryDensities (S : Set (LeftBlockVector L q k)) m η X).Nonempty
  · simp only [honestOracle_feasible, hX, decide_true, ↓reduceIte, FreeM.eval_liftBind,
      FreeM.eval_pure]
  · simp only [honestOracle_feasible, hX, decide_false, Bool.false_eq_true, ↓reduceIte,
      FreeM.eval_pure]

/-- Under a valid oracle, step 1 computes the extended family. -/
theorem eval_extensionProgram_of_valid (hv : IsValidOracle o) (L i b : ℕ)
    (S : Finset (LeftBlockVector L q (i - 1))) :
    FreeM.eval o (extensionProgram L i b S) = AreaLaw.extend i S := by
  classical
  ext v
  simp only [extensionProgram, eval_unionOver, Finset.toList_toFinset, List.toFinset_finRange,
    FreeM.eval_liftBind, FreeM.eval_pure, hv.extendSite, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Finset.mem_singleton, AreaLaw.extend, Finset.mem_image₂]
  constructor <;> rintro ⟨s, hs, k, hv⟩ <;> exact ⟨s, hs, k, hv.symm⟩

/-- The nets of a valid oracle at the cut after `k` sites. -/
noncomputable def oracleNets (o : {ι : Type} → LinearAlgebraQuery q ι → ι) (L k : ℕ) (η : ℝ)
    (m : ℕ) : Finset (Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ) :=
  o (LinearAlgebraQuery.boundaryNet L k m η)

/-- The leading-vector assignments of a valid oracle for the family `S`. -/
noncomputable def oracleSolver (o : {ι : Type} → LinearAlgebraQuery q ι → ι) (L k b : ℕ)
    (S : Finset (LeftBlockVector L q k))
    (HL : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ) (η : ℝ)
    (m : ℕ) (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ) :
    EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m) :=
  o (LinearAlgebraQuery.leadingVector L k b S HL m η X)

/-- Under a valid oracle, step 2 computes the size-trimming selection of the oracle's nets
and solver. -/
theorem eval_sizeTrimmingProgram_of_valid (hv : IsValidOracle o) (L k b : ℕ)
    (h : ChainHamiltonian L q 1 1) (hq : 2 ≤ q) (Δ : ℝ) (S : Finset (LeftBlockVector L q k)) :
    FreeM.eval o (sizeTrimmingProgram L k b h hq Δ S) =
      haveI : NeZero q := ⟨by omega⟩
      h.sizeTrimmingSelectionWith hq Δ S (oracleNets o L k ((Δ / 169) ^ 2 / (2 * L)))
        (oracleSolver o L k b S (leftCutOperator k (h.cutLeftPart k))
          ((Δ / 169) ^ 2 / (2 * L))) := by
  classical
  let : NeZero q := ⟨by omega⟩
  simp only [sizeTrimmingProgram, ChainHamiltonian.sizeTrimmingSelectionWith, eval_unionOver,
    List.toFinset_finRange, FreeM.eval_liftBind, Finset.toList_toFinset, boundaryFamily,
    leftColumns_eq_biUnion, oracleNets, oracleSolver]
  refine Finset.biUnion_congr rfl fun m _ ↦ ?_
  ext v
  simp only [Finset.mem_biUnion, mem_feasibleBoundaryPoints]
  constructor
  · rintro ⟨X, hX, hv'⟩
    rw [eval_feasible_ite_of_valid hv] at hv'
    split_ifs at hv' with hP
    · exact ⟨X, ⟨hX, hP⟩, hv'⟩
    · exact absurd hv' (Finset.notMem_empty v)
  · rintro ⟨X, ⟨hX, hP⟩, hv'⟩
    exact ⟨X, hX, by rw [eval_feasible_ite_of_valid hv]; simpa only [hP, ↓reduceIte] using hv'⟩

/-- Under a valid oracle, step 3 computes the trimmed family. -/
theorem eval_bondTrimmingProgram_of_valid (hv : IsValidOracle o) (L i : ℕ) (hi : i ≤ L)
    (b m : ℕ) (S : Finset (LeftBlockVector L q i)) :
    FreeM.eval o (bondTrimmingProgram L i hi b m S) = bondTrimSet hi m S := by
  classical
  ext v
  simp only [bondTrimmingProgram, eval_unionOver, Finset.toList_toFinset, FreeM.eval_liftBind,
    FreeM.eval_pure, hv.schmidtTrim, Finset.mem_biUnion, Finset.mem_singleton, bondTrimSet,
    Finset.mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

/-- Under a valid oracle, step 4 computes the error-reduced family. -/
theorem eval_errorReductionProgram_of_valid (hv : IsValidOracle o) (L i r b : ℕ)
    (F : Finset (LeftBlockMatrix L q i)) (T : Finset (LeftBlockVector L q i)) :
    FreeM.eval o (errorReductionProgram L i r b F T) = errorReductionSet F id T := by
  classical
  ext v
  simp only [errorReductionProgram, eval_unionOver, Finset.toList_toFinset, FreeM.eval_liftBind,
    FreeM.eval_pure, hv.applyFactor, Finset.mem_biUnion, Finset.mem_singleton,
    errorReductionSet, Finset.mem_image₂, id]
  constructor
  · rintro ⟨A, hA, s, hs, rfl⟩
    exact ⟨A, hA, s, hs, rfl⟩
  · rintro ⟨A, hA, s, hs, rfl⟩
    exact ⟨A, hA, s, hs, rfl⟩

/-- Under a valid oracle, one step of the program is the step applied with the oracle's
filter factors to the size-trimming selection of the oracle's nets and solver. -/
theorem eval_sweepStepProgram_of_valid (hv : IsValidOracle o) {L : ℕ} (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    (Delta : ℝ) {i : ℕ} (hi : i + 1 ≤ L) (S : Finset (LeftBlockVector L q i)) :
    FreeM.eval o (sweepStepProgram hq h hs h0 h1 Delta hi S) =
      haveI : NeZero q := ⟨by omega⟩
      successiveStep hi (bondTrimmingRadius L (lvvReferenceBond q Delta L))
        (o (LinearAlgebraQuery.gaussianFilterFactors L (i + 1) (Nat.le_of_lt hq) h h0
          (lvvSuccessiveError Delta) Delta)) id
        ((ChainHamiltonian.ofNearestNeighborPositive h hs h0 h1).sizeTrimmingSelectionWith hq
          Delta (AreaLaw.extend (i + 1) S)
          (oracleNets o L (i + 1) ((Delta / 169) ^ 2 / (2 * L)))
          (oracleSolver o L (i + 1) (lvvSuccessiveBondBound q Delta L) (AreaLaw.extend (i + 1) S)
            (leftCutOperator (i + 1)
              ((ChainHamiltonian.ofNearestNeighborPositive h hs h0 h1).cutLeftPart (i + 1)))
            ((Delta / 169) ^ 2 / (2 * L)))) := by
  simp only [sweepStepProgram, FreeM.eval_bind, FreeM.eval_lift, eval_extensionProgram_of_valid hv,
    eval_sizeTrimmingProgram_of_valid hv, eval_bondTrimmingProgram_of_valid hv,
    eval_errorReductionProgram_of_valid hv, successiveStep]

/-! ## Correctness for every valid oracle -/

/-- The nets of a valid oracle are admissible. -/
theorem isAdmissibleNet_oracleNets (hv : IsValidOracle o) {L k : ℕ} (hL : 0 < L)
    (h : ChainHamiltonian L q 1 1) {Δ : ℝ} (hΔ : 0 < Δ) :
    h.IsAdmissibleNet Δ (oracleNets o L k ((Δ / 169) ^ 2 / (2 * L))) := by
  intro m _ Y hY
  have hη : 0 < (Δ / 169) ^ 2 / (2 * L) :=
    div_pos (sq_pos_of_pos (div_pos hΔ (by norm_num))) (by positivity)
  exact hv.boundaryNet_cover L k m _ hη Y hY

/-- The solver of a valid oracle is admissible. -/
theorem isAdmissibleSolver_oracleSolver (hv : IsValidOracle o) {L k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hq : 2 ≤ q) (Δ : ℝ) (b : ℕ)
    (S : Finset (LeftBlockVector L q k)) :
    haveI : NeZero q := ⟨by omega⟩
    h.IsAdmissibleSolver hq Δ S (oracleSolver o L k b S (leftCutOperator k (h.cutLeftPart k))
      ((Δ / 169) ^ 2 / (2 * L))) :=
  fun m ↦ hv.leadingVector L k b S _ m _

/-- The nets of a valid oracle have the standard point bound. -/
theorem card_oracleNets_le (hv : IsValidOracle o) {L k : ℕ} (hL : 0 < L) (hq : 2 ≤ q)
    {Δ : ℝ} (hΔ : 0 < Δ) :
    ∀ m ≤ constantCutBond q 1 1 Δ ((Δ / 169) ^ 2),
      (oracleNets o L k ((Δ / 169) ^ 2 / (2 * L)) m).card ≤
        (2 * ⌈((q * constantCutBond q 1 1 Δ ((Δ / 169) ^ 2) : ℕ) : ℝ) ^ 2 /
          ((Δ / 169) ^ 2 / (2 * L))⌉₊ + 1) ^
          (2 * (q * constantCutBond q 1 1 Δ ((Δ / 169) ^ 2)) ^ 2) := by
  intro m hm
  have hη : 0 < (Δ / 169) ^ 2 / (2 * L) :=
    div_pos (sq_pos_of_pos (div_pos hΔ (by norm_num))) (by positivity)
  exact (hv.boundaryNet_card (by omega) L k m _ hη).trans (netPointBound_mono hm hη.le)

/-- **One step of the program preserves viability under every valid oracle**, with the
cardinality and bond budgets of the sweep. -/
theorem sweepStepProgram_spec_of_valid (hv : IsValidOracle o) {L : ℕ} (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) {i : ℕ} (hi : i + 1 ≤ L)
    (S : Finset (LeftBlockVector L q i)) :
    let T := FreeM.eval o (sweepStepProgram hq h hs h0 h1 Delta hi S)
    T.card ≤ lvvSuccessiveCardBound q Delta L ∧
      (∀ v ∈ T, IsLeftOpenMPS (lvvSuccessiveBondBound q Delta L) v) ∧
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
        IsGappedGroundState (∑ j, h j) E₀ Γ Delta →
        IsViable Γ (lvvSuccessiveError Delta / L) (S : Set (LeftBlockVector L q i)) →
        IsViable Γ (lvvSuccessiveError Delta / L) (T : Set (LeftBlockVector L q (i + 1))) := by
  classical
  intro T
  let : NeZero q := ⟨by omega⟩
  have hL : 0 < L := by omega
  have hc : 0 < lvvSuccessiveError Delta := lvvSuccessiveError_pos hDelta
  let chain := ChainHamiltonian.ofNearestNeighborPositive h hs h0 h1
  have hT : T = successiveStep hi (bondTrimmingRadius L (lvvReferenceBond q Delta L))
      (o (LinearAlgebraQuery.gaussianFilterFactors L (i + 1) (Nat.le_of_lt hq) h h0
        (lvvSuccessiveError Delta) Delta)) id
      (chain.sizeTrimmingSelectionWith hq Delta (AreaLaw.extend (i + 1) S)
        (oracleNets o L (i + 1) ((Delta / 169) ^ 2 / (2 * L)))
        (oracleSolver o L (i + 1) (lvvSuccessiveBondBound q Delta L) (AreaLaw.extend (i + 1) S)
          (leftCutOperator (i + 1) (chain.cutLeftPart (i + 1))) ((Delta / 169) ^ 2 / (2 * L)))) :=
    eval_sweepStepProgram_of_valid hv hq h hs h0 h1 Delta hi S
  have hnet := isAdmissibleNet_oracleNets hv (k := i + 1) hL chain hDelta
  have hsol := isAdmissibleSolver_oracleSolver hv chain hq Delta (lvvSuccessiveBondBound q Delta L)
    (AreaLaw.extend (i + 1) S)
  have hcardF := hv.gaussianFilterFactors_card L (i + 1) (Nat.le_of_lt hq) h hs h0 h1 _ _ hc
    hDelta
  have hrankF := hv.gaussianFilterFactors_rank L (i + 1) (Nat.le_of_lt hq) h hs h0 h1 _ _ hc
    hDelta hi
  refine ⟨?_, ?_, ?_⟩
  · rw [hT]
    calc
      _ ≤ (o (LinearAlgebraQuery.gaussianFilterFactors L (i + 1) (Nat.le_of_lt hq) h h0
            (lvvSuccessiveError Delta) Delta)).card *
          (chain.sizeTrimmingSelectionWith hq Delta (AreaLaw.extend (i + 1) S) _ _).card :=
          card_successiveStep_le hi _ _ id _
      _ ≤ (huangEnergyCount (lvvSuccessiveError Delta) Delta L *
            huangFilterRankBound q (lvvSuccessiveError Delta) Delta L) *
          (lvvSizeTrimmingCoefficient q Delta * L ^ lvvSizeTrimmingDegree q Delta) :=
          Nat.mul_le_mul hcardF
            (chain.card_sizeTrimmingSelectionWith_le_polynomial hL hq hDelta _ _
              (card_oracleNets_le hv hL hq hDelta))
      _ = lvvSuccessiveCardBound q Delta L := by
        dsimp only [lvvSuccessiveCardBound]
        ring
  · intro v hv'
    rw [hT] at hv'
    exact isLeftOpenMPS_of_mem_successiveStep hi
      (fun _ hA k _ hki ↦ hrankF _ hA k hki) _ hv'
  · intro E₀ Γ hgs hviable
    rw [hT]
    have hpos (X) : (chain.term X).PosSemidef :=
      (ChainHamiltonian.ofNearestNeighborPositive_term_nonneg h hs h0 h1 X).posSemidef
    have hgsChain : IsGappedGroundState chain.operator E₀ Γ Delta := by
      simpa only [chain, ChainHamiltonian.ofNearestNeighborPositive_operator] using hgs
    obtain ⟨hΓ, hEig, hgap⟩ := isGappedGroundState_iff.mp hgs
    exact isViable_errorReductionSet_of_isAdmissibleFilterFactors (Nat.le_of_lt hq) h hs h0 h1
      hc hDelta (by omega) E₀ Γ hΓ hEig hgap
      (hv.gaussianFilterFactors_admissible L (i + 1) (Nat.le_of_lt hq) h h0 _ Delta) _
      (chain.isViable_bondTrimSet_sizeTrimmingSelectionWith hpos hL hq hi hDelta
        (AreaLaw.extend (i + 1) S) hnet hsol E₀ Γ hgsChain (hviable.extend (by omega) hi))

/-- **The sweep program is correct under every valid oracle**: at every cut its output is
viable for every ground pair with the prescribed gap, with the size and bond budgets of
the sweep. LVV13, `algo53.tex`, lines 652--668. -/
theorem sweepProgram_spec_of_valid (hv : IsValidOracle o) {L : ℕ} (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) (i : ℕ) (hi : i ≤ L) :
    let S := FreeM.eval o (sweepProgram hq h hs h0 h1 Delta i)
    S.card ≤ (if i = 0 then 1 else lvvSuccessiveCardBound q Delta L) ∧
      (∀ v ∈ S, IsLeftOpenMPS (if i = 0 then 1 else lvvSuccessiveBondBound q Delta L) v) ∧
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
        IsGappedGroundState (∑ j, h j) E₀ Γ Delta →
        IsViable Γ (lvvSuccessiveError Delta / L) (S : Set (LeftBlockVector L q i)) := by
  intro S
  induction i with
  | zero =>
    obtain ⟨hcard, hmps, hviable⟩ :=
      lvvSweep_spec hq h hs h0 h1 hDelta 0 (Nat.zero_le L)
    exact ⟨hcard, hmps, hviable⟩
  | succ i ih =>
    obtain ⟨-, -, hviable⟩ := ih (by omega)
    have hstep := sweepStepProgram_spec_of_valid hv hq h hs h0 h1 hDelta hi
      (FreeM.eval o (sweepProgram hq h hs h0 h1 Delta i))
    simp only [S, sweepProgram, hi, ↓reduceDIte, FreeM.eval_bind, Nat.succ_ne_zero, ↓reduceIte]
    exact ⟨hstep.1, hstep.2.1, fun E₀ Γ hgs ↦ hstep.2.2 E₀ Γ hgs (hviable E₀ Γ hgs)⟩

/-- **The ground-state program finds the ground state under every valid oracle.** For every
ground pair with gap `Δ > 0` and every `R ≥ 1`, the output of the program with any valid
oracle is a unit vector with overlap at least `1 - 4 L / (R² Δ)` with the ground state, and
an open-boundary matrix product state whose bond dimension is bounded by the cardinality
budget times the bond budget of the sweep on the padded chain. LVV13, `algo53.tex`, lines
213--216 and 652--678, for every solver returning optimal solutions. -/
theorem groundStateProgram_spec_of_valid (hv : IsValidOracle o) {L : ℕ} (hL : 1 ≤ L)
    (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {Delta : ℝ} (hDelta : 0 < Delta) {R : ℕ} (hR : 1 ≤ R)
    (E : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q))
    (hgs : IsGappedGroundState (∑ j, h j) E Γ Delta) :
    let N := L + 2 * R ^ 2
    let ψ := FreeM.eval o (groundStateProgram hq h hs h0 h1 Delta R)
    ‖ψ‖ = 1 ∧ 1 - 4 * L / (R ^ 2 * Delta) ≤ ‖⟪Γ, ψ⟫_ℂ‖ ∧
      IsOpenMPS L q (lvvSuccessiveCardBound q (min Delta 1) N *
        max 1 (lvvSuccessiveBondBound q (min Delta 1) N)) (fun x ↦ ψ x) := by
  classical
  intro N ψ
  have hi : L ≤ N := Nat.le_add_right _ _
  let z : Fin q := ⟨0, by omega⟩
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (leftConfigOfFinEquiv (q := q) hi)
  let hs' := paddedInteraction_supported hi z h hs
  let h0' := fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).1
  let h1' := fun j ↦ (paddedInteraction_nonneg_le_one hi z h h0 h1 j).2
  set S := FreeM.eval o (sweepProgram hq (paddedInteraction hi z h) hs' h0' h1' (min Delta 1) L)
    with hSdef
  have hψ : ψ = o (LinearAlgebraQuery.energyMinimizer L (lvvSuccessiveBondBound q (min Delta 1) N)
      (∑ j, h j) (S.image fun w ↦ e.symm w)) := by
    simp only [ψ, groundStateProgram, FreeM.eval_bind, FreeM.eval_lift]
    rfl
  have hg : 0 < min Delta 1 := lt_min hDelta zero_lt_one
  have hN : 1 ≤ N := hL.trans hi
  obtain ⟨hcard, hmps, hviable⟩ :=
    sweepProgram_spec_of_valid hv hq (paddedInteraction hi z h) hs' h0' h1' hg L hi
  simp only [show L ≠ 0 by omega, ↓reduceIte] at hcard hmps
  have hpad := isGappedGroundState_paddedInteraction hL hi z h hgs hDelta
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  set δ : ℝ := lvvSuccessiveError (min Delta 1) / N with hδdef
  have hδ1 : δ < 1 := by
    apply (div_lt_one hNreal).mpr
    exact (lvvSuccessiveError_min_lt_one hDelta).trans_le (by exact_mod_cast hN)
  have hδ0 : 0 ≤ δ := div_nonneg (lvvSuccessiveError_pos hg).le hNreal.le
  obtain ⟨w, hw, hwnorm, herror, hwmps⟩ :=
    (hviable E _ hpad).exists_prefix_mps_of_paddedGroundVector hi z hgs.1 hδ1 hmps
  -- The span of the final family, read on the original chain.
  set U := Submodule.span ℂ ((S.image fun w ↦ e.symm w : Finset _) :
    Set (EuclideanSpace ℂ (Fin L → Fin q))) with hUdef
  have hUmap : U = (Submodule.span ℂ (S : Set (LeftBlockVector N q L))).map
      e.symm.toLinearEquiv.toLinearMap := by
    rw [hUdef, Finset.coe_image, Submodule.map_span]
    rfl
  have hw'U : e.symm w ∈ U := by
    rw [hUmap]
    exact Submodule.mem_map_of_mem hw
  have hw'norm : ‖e.symm w‖ = 1 := by rw [e.symm.norm_map, hwnorm]
  have hUne : U ≠ ⊥ := by
    intro hbot
    have : e.symm w = 0 := by simpa only [hbot, Submodule.mem_bot] using hw'U
    rw [this, norm_zero] at hw'norm
    exact zero_ne_one hw'norm
  obtain ⟨hψU, hψnorm, hψmin⟩ :=
    hv.energyMinimizer L (lvvSuccessiveBondBound q (min Delta 1) N) (∑ j, h j)
      (S.image fun w ↦ e.symm w) hUne
  rw [← hψ] at hψU hψnorm hψmin
  refine ⟨hψnorm, ?_, ?_⟩
  · -- Overlap: least energy in the span, then the gap.
    obtain ⟨hΓ, hEig, hgap⟩ := isGappedGroundState_iff.mp hgs
    have hover : 1 - δ ≤ ‖⟪Γ, e.symm w⟫_ℂ‖ :=
      one_sub_le_norm_inner_of_norm_sub_sq_le hw'norm hgs.1 herror
    let chain := ChainHamiltonian.ofNearestNeighborPositive h hs h0 h1
    have hchain : chain.operator = ∑ j, h j :=
      ChainHamiltonian.ofNearestNeighborPositive_operator h hs h0 h1
    have hgsChain : IsGappedGroundState chain.operator E Γ Delta := by rwa [hchain]
    have henergy := chain.re_inner_sub_le_of_overlap_of_range_one hgsChain hw'norm hover
    rw [hchain] at henergy
    have hψenergy : (⟪ψ, toEuclideanLin (∑ j, h j) ψ⟫_ℂ).re - E ≤ 8 * L * δ :=
      (sub_le_sub_right (hψmin _ hw'U hw'norm) E).trans henergy
    have hbound := Entropy.norm_inner_ge_of_gap hDelta hgap hΓ hψnorm hψenergy
    refine le_trans ?_ hbound
    -- `8 L δ / Δ ≤ 4 L / (R² Δ)` since `δ ≤ 1 / (2 R²)`.
    have hR2 : (0 : ℝ) < (R : ℝ) ^ 2 := by positivity
    have hNR : 2 * (R : ℝ) ^ 2 ≤ N := by
      exact_mod_cast (show 2 * R ^ 2 ≤ N from Nat.le_add_left _ _)
    have hc1 : lvvSuccessiveError (min Delta 1) ≤ 1 := (lvvSuccessiveError_min_lt_one hDelta).le
    have hδle : δ ≤ 1 / (2 * (R : ℝ) ^ 2) := by
      rw [hδdef, div_le_div_iff₀ hNreal (by positivity)]
      nlinarith [lvvSuccessiveError_pos hg]
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have : 8 * L * δ / Delta ≤ 4 * L / (R ^ 2 * Delta) := by
      rw [div_le_div_iff₀ hDelta (by positivity)]
      calc 8 * L * δ * (R ^ 2 * Delta)
          ≤ 8 * L * (1 / (2 * (R : ℝ) ^ 2)) * (R ^ 2 * Delta) := by gcongr
        _ = 4 * L * Delta := by field_simp; ring
    linarith
  · -- The output is a matrix product state of the final span's bond dimension.
    have hψU' : ψ ∈ U := hψU
    rw [hUmap] at hψU'
    obtain ⟨v, hv, hvψ⟩ := Submodule.mem_map.mp hψU'
    have hvmps := isOpenMPS_leftChain_of_mem_span S hmps hv
    have hcoord : (fun x ↦ ψ x) = fun x ↦ v (leftConfigOfFin x) := by
      rw [← hvψ]
      rfl
    rw [hcoord]
    exact hvmps.mono (Nat.mul_le_mul_right _ hcard)

end TNLean.MPS.AreaLaw
