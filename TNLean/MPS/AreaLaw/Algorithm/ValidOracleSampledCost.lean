/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Algorithm.SampledCost
import TNLean.MPS.AreaLaw.Algorithm.ValidOracleCost
import TNLean.MPS.AreaLaw.Algorithm.ValidOracleSampled

/-!
# Theorem 1 on the sampled route under every valid oracle

On good words the sampled program costs at most its budget under every valid oracle: the
nets of a valid oracle have the standard point bound, its sampled factors number at most
`ℓ D`, and its sweep families have the cardinality budget of the sampled sweep. Combined
with correctness on good words, one event of probability at least `1 - 1/(2 n²)` carries
both the accuracy of the output and the polynomial cost of the run. This is Theorem 1 of
Landau, Vazirani and Vidick in the form "with probability at least `1 - 1/(2n²)` the
algorithm outputs a good approximation in polynomial time", for every solver of the convex
programs, in the cost model of the query type (`docs/paper-gaps/lvv13_cost_model.tex`) and the
documented scope of the ground-energy ratio
(`docs/paper-gaps/lvv13_runtime_ground_energy.tex`).

**Scope restriction (cost model):** the bounds are on the declared oracle cost
`FreeM.cost o queryCost`, not on a proved running time of an implementation: each query is
charged a declared polynomial cost in the dimensions of its arguments, arithmetic is exact, and
nothing is proved about how a query is answered; see `docs/paper-gaps/lvv13_cost_model.tex`.

Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, lines 213--219 and 652--678.
-/

open Matrix Cslib MeasureTheory
open scoped InnerProductSpace ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ} {o : {ι : Type} → LinearAlgebraQuery q ι → ι}

open LinearAlgebraQuery

/-- One sampled step under a valid oracle costs at most the budget at the cardinality of
the input, when every word has rank at most `D` at every cut. -/
theorem cost_sampledSweepStepProgram_le_of_valid (hv : IsValidOracle o) (hL : 0 < L)
    (hq : 2 ≤ q) (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) (E₀ : ℝ) {Δ : ℝ} (hΔ : 0 < Δ)
    {ℓ m : ℕ} (I : Fin ℓ → Fin m → Fin L) (b D : ℕ) {i : ℕ} (hi : i + 1 ≤ L)
    (S : Finset (LeftBlockVector L q i))
    (hrank : ∀ t k, operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L k) (bondComplementWord h (I t))) ≤ D) :
    FreeM.cost o queryCost (sampledSweepStepProgram hq h hs h0 h1 E₀ Δ I b D hi S) ≤
      sampledStepCostBound q Δ L ℓ D b S.card := by
  classical
  let : NeZero q := ⟨by omega⟩
  simp only [sampledSweepStepProgram, FreeM.cost_bind, FreeM.eval_lift,
    eval_extensionProgram_of_valid hv, eval_sizeTrimmingProgram_of_valid hv,
    eval_bondTrimmingProgram_of_valid hv, FreeM.cost_lift, queryCost_sampledFactors,
    sampledStepCostBound]
  set chain := ChainHamiltonian.ofBonds h hs h0 h1 with hchain
  set m' := bondTrimmingRadius L (lvvReferenceBond q Δ L) with hm'
  set c : ℝ := (Δ / 169) ^ 2 with hc
  set D' := constantCutBond q 1 1 Δ c with hD'
  set S₁ := AreaLaw.extend (i + 1) S with hS₁
  set S₂ := chain.sizeTrimmingSelectionWith hq Δ S₁
    (oracleNets o L (i + 1) ((Δ / 169) ^ 2 / (2 * L)))
    (oracleSolver o L (i + 1) b S₁ (leftCutOperator (i + 1) (chain.cutLeftPart (i + 1)))
      ((Δ / 169) ^ 2 / (2 * L))) with hS₂
  set S₃ := bondTrimSet hi m' S₂ with hS₃
  set F := o (LinearAlgebraQuery.sampledFactors L (i + 1) h E₀ ℓ m D I) with hF'
  set size := lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ with hsize
  have hcard₁ : S₁.card ≤ q * S.card := card_extend_le (i + 1) S
  have hcard₂ : S₂.card ≤ size :=
    chain.card_sizeTrimmingSelectionWith_le_polynomial hL hq hΔ S₁ _
      (card_oracleNets_le hv hL hq hΔ)
  have hcard₃ : S₃.card ≤ S₂.card := card_bondTrimSet_le hi m' S₂
  have hF : F.card ≤ ℓ * D := (hv.sampledFactors L (i + 1) h E₀ ℓ m D I hrank).2.1
  have h₁ := cost_extensionProgram_le_of_valid (o := o) L (i + 1) b S
  have h₂ := cost_sizeTrimmingProgram_le_of_valid hv L (i + 1) b chain hL hq hΔ S₁
  have h₃ := cost_bondTrimmingProgram_le_of_valid (o := o) L (i + 1) hi b m' S₂
  have h₅ := cost_errorReductionProgram_le_of_valid (o := o) L (i + 1) D (max 1 m') F S₃
  dsimp only at h₂
  have h₂' := h₂.trans (Nat.mul_le_mul_left (D' + 1) (Nat.add_le_add_left (Nat.mul_le_mul_left _
    (Nat.mul_le_mul_left 2 (convexProgramCost_mono L q b hcard₁ le_rfl))) _))
  have h₃' := h₃.trans (Nat.mul_le_mul_right _ hcard₂)
  have h₅' := h₅.trans (Nat.mul_le_mul hF (Nat.mul_le_mul_right _ (hcard₃.trans hcard₂)))
  exact Nat.add_le_add h₁ (Nat.add_le_add h₂' (Nat.add_le_add h₃' (Nat.add_le_add le_rfl h₅')))

/-- On good words, the sampled sweep under a valid oracle up to cut `i ≤ L` costs at most
`i` steps at the size budget. -/
theorem cost_sampledSweepProgram_le_of_valid (hv : IsValidOracle o) (hL : 0 < L) (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hgs : IsGappedGroundState (∑ j, h j) E₀ Γ Δ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδc : δ ≤ (Δ / 169) ^ 2 / L) {ℓ m κ : ℕ}
    (I : Fin L → Fin ℓ → Fin m → Fin L) (hm : ((L - E₀) / Δ) * Real.log (1 / (δ / 8)) ≤ m)
    (hgood : ∀ i, GoodWords h E₀ m (δ / 8) κ (I i)) (b : ℕ) (i : ℕ) (hi : i ≤ L) :
    FreeM.cost o queryCost (sampledSweepProgram hq h hs h0 h1 E₀ Δ I b (q ^ (2 * κ)) i) ≤
      i * sampledStepCostBound q Δ L ℓ (q ^ (2 * κ)) b
        (max 1 (sampledSizeBudget q Δ L ℓ (q ^ (2 * κ)))) := by
  induction i with
  | zero => simp [sampledSweepProgram]
  | succ i ih =>
    have hi' : i + 1 ≤ L := hi
    simp only [sampledSweepProgram, hi', ↓reduceDIte, FreeM.cost_bind]
    have hstep := cost_sampledSweepStepProgram_le_of_valid hv hL hq h hs h0 h1 E₀ hΔ
      (I ⟨i, by omega⟩) b (q ^ (2 * κ)) hi'
      (FreeM.eval o (sampledSweepProgram hq h hs h0 h1 E₀ Δ I b (q ^ (2 * κ)) i)) fun t k ↦
        operatorSchmidtRank_cutOperator_bondComplementWord_le_all (by omega) h hs _
          ((hgood ⟨i, by omega⟩).2 t) k
    have hcard : (FreeM.eval o (sampledSweepProgram hq h hs h0 h1 E₀ Δ I b (q ^ (2 * κ)) i)).card ≤
        max 1 (sampledSizeBudget q Δ L ℓ (q ^ (2 * κ))) := by
      refine (sampledSweepProgram_spec_of_valid hv hL hq h hs h0 h1 hΔ hgs hδ0 hδ1 hδc I hm hgood
        b i (by omega)).1.trans ?_
      unfold sampledSizeBudget
      split_ifs <;> simp
    have hstep' := hstep.trans (sampledStepCostBound_mono q Δ L le_rfl le_rfl le_rfl hcard)
    rw [add_one_mul i]
    exact Nat.add_le_add (ih (by omega)) hstep'

/-- On good words, the sampled ground-state program under a valid oracle costs at most its
budget. -/
theorem cost_sampledGroundStateProgram_le_of_valid (hv : IsValidOracle o) (hL : 0 < L)
    (hq : 2 ≤ q) (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hgs : IsGappedGroundState (∑ j, h j) E₀ Γ Δ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδc : δ ≤ (Δ / 169) ^ 2 / L) {ℓ m κ : ℕ}
    (I : Fin L → Fin ℓ → Fin m → Fin L) (hm : ((L - E₀) / Δ) * Real.log (1 / (δ / 8)) ≤ m)
    (hgood : ∀ i, GoodWords h E₀ m (δ / 8) κ (I i)) (b : ℕ) :
    FreeM.cost o queryCost (sampledGroundStateProgram hq h hs h0 h1 E₀ Δ I b (q ^ (2 * κ))) ≤
      sampledGroundStateCostBound q Δ L ℓ (q ^ (2 * κ)) b := by
  classical
  simp only [sampledGroundStateProgram, FreeM.cost_bind, FreeM.cost_lift,
    queryCost_energyMinimizer, sampledGroundStateCostBound]
  have hsweep := cost_sampledSweepProgram_le_of_valid hv hL hq h hs h0 h1 hΔ hgs hδ0 hδ1 hδc I
    hm hgood b L le_rfl
  have hcard : ((FreeM.eval o (sampledSweepProgram hq h hs h0 h1 E₀ Δ I b (q ^ (2 * κ)) L)).image
      fun w ↦ (fullLeftEquiv L q).symm w).card ≤
      max 1 (sampledSizeBudget q Δ L ℓ (q ^ (2 * κ))) := by
    refine Finset.card_image_le.trans ?_
    refine (sampledSweepProgram_spec_of_valid hv hL hq h hs h0 h1 hΔ hgs hδ0 hδ1 hδc I hm hgood
      b L le_rfl).1.trans ?_
    simp only [show L ≠ 0 by omega, ↓reduceIte]
    exact le_max_of_le_right le_rfl
  exact Nat.add_le_add hsweep (energyMinimizerCost_mono le_rfl q b hcard)

/-- **Theorem 1 on the sampled route under every valid oracle, with one event for accuracy
and running time.** Fix `q ≥ 2`, `Δ > 0`, a bound `B` on the ratio of ground energy to gap,
and an accuracy `η > 0`. There are `C, P ≥ 1` and `p, d`, chosen before the chain, such that
for every chain of `L ≥ 1` sites with a ground pair `(E₀, Γ)` of gap `Δ` and `E₀ / Δ ≤ B`, and
every valid oracle, with probability at least `1 - 1/(2 L²)` over the sampled words the
sampled ground-state program, with the bond budget `C L^p` and the rank budget of the words
declared, outputs a unit open-boundary matrix product state of bond dimension at most
`C L^p` with overlap at least `1 - η` with `Γ`, and its declared cost is at most
`P (L + 1)^d`. LVV13, `algo53.tex`, lines 213--219 and 657, in the cost model of the query
type and the documented scope of the ground-energy ratio. -/
theorem exists_sampledGroundStateProgram_success_cost_polynomial_of_valid (hq : 2 ≤ q)
    {Δ B η : ℝ} (hΔ : 0 < Δ) (hη : 0 < η) :
    ∃ C p P d : ℕ, 1 ≤ C ∧ 1 ≤ P ∧ ∀ (L : ℕ) [NeZero L]
      (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
      (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) (E₀ : ℝ)
      (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
      IsGappedGroundState (∑ j, h j) E₀ Γ Δ → E₀ / Δ ≤ B →
      ∀ o : {ι : Type} → LinearAlgebraQuery q ι → ι, IsValidOracle o →
      let δ := sampledPrecisionConstant Δ η / L
      1 - 1 / (2 * (L : ℝ) ^ 2) ≤
        (stepWordsMeasure L (sampledWordCount q L E₀ Δ δ) (sampledPower L E₀ Δ δ)).real
          {I | let ψ := FreeM.eval o
                (sampledGroundStateProgram hq h hs h0 h1 E₀ Δ I (C * L ^ p)
                  (sampledRankBound q L E₀ Δ δ))
            ‖ψ‖ = 1 ∧ 1 - η ≤ ‖⟪Γ, ψ⟫_ℂ‖ ∧ IsOpenMPS L q (C * L ^ p) (fun x ↦ ψ x) ∧
              FreeM.cost o queryCost
                  (sampledGroundStateProgram hq h hs h0 h1 E₀ Δ I (C * L ^ p)
                    (sampledRankBound q L E₀ Δ δ)) ≤ P * (L + 1) ^ d} := by
  obtain ⟨C, p, hC, hbond⟩ := exists_sampledBond_polynomial (B := B) hq hΔ hη
  obtain ⟨C₁, p₁, -, hbud⟩ := exists_sampled_budgets_polynomial (B := B) hq hΔ hη
  obtain ⟨P, d, hP, hpoly⟩ := (isNatPolynomialBounded_sampledGroundStateCostBound (q := q) hΔ
    C₁ p₁ C p).exists_one_le
  refine ⟨C, p, P, d, hC, hP, ?_⟩
  intro L _ h hs h0 h1 E₀ Γ hgs hEB o hv δ
  have hL : 1 ≤ L := Nat.pos_of_neZero L
  obtain ⟨hE₀, hE₀L⟩ := groundEnergy_nonneg_and_le h h0 h1 hgs
  obtain ⟨hδ0, hδ1, hδc, hover⟩ := sampledPrecision_spec hΔ hη hL
  obtain ⟨hℓD, hD⟩ := hbud L E₀ hL hE₀ hE₀L hEB
  have hD1 : 1 ≤ sampledRankBound q L E₀ Δ δ := Nat.one_le_pow _ _ (by omega)
  have hℓ : sampledWordCount q L E₀ Δ δ ≤ C₁ * L ^ p₁ :=
    (Nat.le_mul_of_pos_right _ hD1).trans hℓD
  refine (measureReal_forall_goodWords_ge h h0 h1 hgs hΔ hδ0).trans (measureReal_mono ?_)
  intro I hI
  obtain ⟨hψ1, hψover, hψmps⟩ := sampledGroundStateProgram_spec_of_valid hv
    (Nat.pos_of_neZero L) hq h hs h0 h1 hΔ hgs hδ0 hδ1 hδc I (Nat.le_ceil _) hI (C * L ^ p)
  have hcost := cost_sampledGroundStateProgram_le_of_valid hv (Nat.pos_of_neZero L) hq h hs h0 h1
    hΔ hgs hδ0 hδ1 hδc I (Nat.le_ceil _) hI (C * L ^ p)
  refine ⟨hψ1, le_trans (by linarith) hψover, hψmps.mono (hbond L E₀ hL hE₀ hE₀L hEB), ?_⟩
  exact hcost.trans ((sampledGroundStateCostBound_mono q Δ L hℓ hD le_rfl).trans (hpoly L hL))

end TNLean.MPS.AreaLaw
