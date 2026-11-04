/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Algorithm.Cost
import TNLean.MPS.AreaLaw.Algorithm.SampledProgram

/-!
# The polynomial cost of the sampled ground-state program

On good words, the sampled program issues polynomially many queries of polynomial declared
cost, because the families of the sampled sweep then have polynomial cardinality and bond
dimension. The bound is uniform over ground energies with `ε₀ / Δ ≤ B`, with the exponent
depending on the ground-energy ratio as in the published form of Theorem 1; see
`docs/paper-gaps/lvv13_runtime_ground_energy.tex` and `docs/paper-gaps/lvv13_cost_model.tex`.
Combined with the success probability, this is the "probabilistic polynomial time" of
LVV13, `algo53.tex`, line 657.
-/

open Matrix Cslib
open scoped ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

open LinearAlgebraQuery

/-- **The cost budget of one sampled step** on a family of at most `s` members, with `ℓ`
words, rank budget `D` and bond budget `b` declared. -/
noncomputable def sampledStepCostBound (q : ℕ) (Δ : ℝ) (L ℓ D b s : ℕ) : ℕ :=
  let c : ℝ := (Δ / 169) ^ 2
  let D' := constantCutBond q 1 1 Δ c
  let K := (2 * ⌈((q * D' : ℕ) : ℝ) ^ 2 / (c / (2 * L))⌉₊ + 1) ^ (2 * (q * D') ^ 2)
  let m := bondTrimmingRadius L (lvvReferenceBond q Δ L)
  let size := lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ
  s * (q * extensionCost q b) +
    ((D' + 1) * (netCost q D' (c / (2 * L)) + K * (2 * convexProgramCost L q b (q * s) D')) +
    (size * schmidtTrimCost L q b + (filterFactorsCost L q ℓ D +
    ℓ * D * (size * applyFactorCost L q D (max 1 m)))))

theorem sampledStepCostBound_mono (q : ℕ) (Δ : ℝ) (L : ℕ) {ℓ ℓ' D D' b b' s s' : ℕ}
    (hℓ : ℓ ≤ ℓ') (hD : D ≤ D') (hb : b ≤ b') (hs : s ≤ s') :
    sampledStepCostBound q Δ L ℓ D b s ≤ sampledStepCostBound q Δ L ℓ' D' b' s' := by
  simp only [sampledStepCostBound, extensionCost, convexProgramCost, schmidtTrimCost,
    filterFactorsCost, applyFactorCost]
  gcongr

/-- One sampled step costs at most the budget at the cardinality of the input, when the
sampled factors number at most `ℓ D`. -/
theorem cost_sampledSweepStepProgram_le (hL : 0 < L) (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) (E₀ : ℝ) {Δ : ℝ} (hΔ : 0 < Δ)
    {ℓ m : ℕ} (I : Fin ℓ → Fin m → Fin L) (b D : ℕ) {i : ℕ} (hi : i + 1 ≤ L)
    (S : Finset (LeftBlockVector L q i)) (hF : (sampledFactors h E₀ I (i + 1)).card ≤ ℓ * D) :
    FreeM.cost honestOracle queryCost (sampledSweepStepProgram hq h hs h0 h1 E₀ Δ I b D hi S) ≤
      sampledStepCostBound q Δ L ℓ D b S.card := by
  classical
  simp only [sampledSweepStepProgram, FreeM.cost_bind, FreeM.eval_lift, eval_extensionProgram,
    eval_sizeTrimmingProgram, eval_bondTrimmingProgram, honestOracle_sampledFactors,
    FreeM.cost_lift, queryCost_sampledFactors, sampledStepCostBound]
  set chain := ChainHamiltonian.ofBonds h hs h0 h1 with hchain
  set m' := bondTrimmingRadius L (lvvReferenceBond q Δ L) with hm'
  set c : ℝ := (Δ / 169) ^ 2 with hc
  set D' := constantCutBond q 1 1 Δ c with hD'
  set S₁ := AreaLaw.extend (i + 1) S with hS₁
  set S₂ := chain.sizeTrimmingSelection hq Δ S₁ with hS₂
  set S₃ := bondTrimSet hi m' S₂ with hS₃
  set F := sampledFactors h E₀ I (i + 1) with hF'
  set size := lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ with hsize
  have hcard₁ : S₁.card ≤ q * S.card := card_extend_le (i + 1) S
  have hcard₂ : S₂.card ≤ size :=
    ChainHamiltonian.card_sizeTrimmingSelection_le_polynomial chain hL hq hΔ S₁
  have hcard₃ : S₃.card ≤ S₂.card := card_bondTrimSet_le hi m' S₂
  have h₁ := cost_extensionProgram_le L (i + 1) b S
  have h₂ := cost_sizeTrimmingProgram_le L (i + 1) b chain hL hq hΔ S₁
  have h₃ := cost_bondTrimmingProgram_le L (i + 1) hi b m' S₂
  have h₅ := cost_errorReductionProgram_le L (i + 1) D (max 1 m') F S₃
  dsimp only at h₂
  have h₂' := h₂.trans (Nat.mul_le_mul_left (D' + 1) (Nat.add_le_add_left (Nat.mul_le_mul_left _
    (Nat.mul_le_mul_left 2 (convexProgramCost_mono L q b hcard₁ le_rfl))) _))
  have h₃' := h₃.trans (Nat.mul_le_mul_right _ hcard₂)
  have h₅' := h₅.trans (Nat.mul_le_mul hF (Nat.mul_le_mul_right _ (hcard₃.trans hcard₂)))
  exact Nat.add_le_add h₁ (Nat.add_le_add h₂' (Nat.add_le_add h₃' (Nat.add_le_add le_rfl h₅')))

/-- The size budget of the sampled sweep at every positive cut. -/
noncomputable def sampledSizeBudget (q : ℕ) (Δ : ℝ) (L ℓ D : ℕ) : ℕ :=
  ℓ * D * (lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ)

/-- On good words, the sampled sweep up to cut `i ≤ L` costs at most `i` steps at the size
budget, with the rank bound `q^{2κ}` declared at least as large as the rank of the words. -/
theorem cost_sampledSweepProgram_le (hL : 0 < L) (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hgs : IsGappedGroundState (∑ j, h j) E₀ Γ Δ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδc : δ ≤ (Δ / 169) ^ 2 / L) {ℓ m κ : ℕ}
    (I : Fin L → Fin ℓ → Fin m → Fin L) (hm : ((L - E₀) / Δ) * Real.log (1 / (δ / 8)) ≤ m)
    (hgood : ∀ i, GoodWords h E₀ m (δ / 8) κ (I i)) (b D : ℕ) (hD : q ^ (2 * κ) ≤ D)
    (i : ℕ) (hi : i ≤ L) :
    FreeM.cost honestOracle queryCost (sampledSweepProgram hq h hs h0 h1 E₀ Δ I b D i) ≤
      i * sampledStepCostBound q Δ L ℓ D b (max 1 (sampledSizeBudget q Δ L ℓ (q ^ (2 * κ)))) := by
  induction i with
  | zero => simp [sampledSweepProgram]
  | succ i ih =>
    have hi' : i + 1 ≤ L := hi
    simp only [sampledSweepProgram, hi', ↓reduceDIte, FreeM.cost_bind, eval_sampledSweepProgram]
    have hF : (sampledFactors h E₀ (I ⟨i, by omega⟩) (i + 1)).card ≤ ℓ * D :=
      (card_sampledFactors_le h E₀ (I ⟨i, by omega⟩) (i + 1) fun t ↦
        operatorSchmidtRank_cutOperator_bondComplementWord_le_all (by omega) h hs _
          ((hgood ⟨i, by omega⟩).2 t) (i + 1)).trans (Nat.mul_le_mul_left ℓ hD)
    have hstep := cost_sampledSweepStepProgram_le hL hq h hs h0 h1 E₀ hΔ (I ⟨i, by omega⟩) b D
      hi' (sampledSweep hq h hs h0 h1 E₀ Δ I i) hF
    have hcard : (sampledSweep hq h hs h0 h1 E₀ Δ I i).card ≤
        max 1 (sampledSizeBudget q Δ L ℓ (q ^ (2 * κ))) := by
      refine (sampledSweep_spec hL hq h hs h0 h1 hΔ hgs hδ0 hδ1 hδc I hm hgood i
        (by omega)).1.trans ?_
      unfold sampledSizeBudget
      split_ifs <;> simp
    have hstep' := hstep.trans (sampledStepCostBound_mono q Δ L le_rfl le_rfl le_rfl hcard)
    rw [Nat.succ_mul]
    exact Nat.add_le_add (ih (by omega)) hstep'

/-- **The cost budget of the sampled ground-state program.** -/
noncomputable def sampledGroundStateCostBound (q : ℕ) (Δ : ℝ) (L ℓ D b : ℕ) : ℕ :=
  L * sampledStepCostBound q Δ L ℓ D b (max 1 (sampledSizeBudget q Δ L ℓ D)) +
    energyMinimizerCost L q b (max 1 (sampledSizeBudget q Δ L ℓ D))

theorem sampledGroundStateCostBound_mono (q : ℕ) (Δ : ℝ) (L : ℕ) {ℓ ℓ' D D' b b' : ℕ}
    (hℓ : ℓ ≤ ℓ') (hD : D ≤ D') (hb : b ≤ b') :
    sampledGroundStateCostBound q Δ L ℓ D b ≤ sampledGroundStateCostBound q Δ L ℓ' D' b' := by
  have hsize : sampledSizeBudget q Δ L ℓ D ≤ sampledSizeBudget q Δ L ℓ' D' :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul hℓ hD)
  have hmax : max 1 (sampledSizeBudget q Δ L ℓ D) ≤ max 1 (sampledSizeBudget q Δ L ℓ' D') :=
    max_le_max le_rfl hsize
  unfold sampledGroundStateCostBound
  exact Nat.add_le_add (Nat.mul_le_mul_left L (sampledStepCostBound_mono q Δ L hℓ hD hb hmax))
    (Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 2))
      (Nat.pow_le_pow_left hmax 3)) 1)

/-- On good words, the sampled ground-state program costs at most its budget, with the rank
bound `q^{2κ}` declared. -/
theorem cost_sampledGroundStateProgram_le (hL : 0 < L) (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hgs : IsGappedGroundState (∑ j, h j) E₀ Γ Δ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδc : δ ≤ (Δ / 169) ^ 2 / L) {ℓ m κ : ℕ}
    (I : Fin L → Fin ℓ → Fin m → Fin L) (hm : ((L - E₀) / Δ) * Real.log (1 / (δ / 8)) ≤ m)
    (hgood : ∀ i, GoodWords h E₀ m (δ / 8) κ (I i)) (b D : ℕ) (hD : q ^ (2 * κ) ≤ D) :
    FreeM.cost honestOracle queryCost (sampledGroundStateProgram hq h hs h0 h1 E₀ Δ I b D) ≤
      sampledGroundStateCostBound q Δ L ℓ D b := by
  classical
  simp only [sampledGroundStateProgram, FreeM.cost_bind, FreeM.cost_lift,
    eval_sampledSweepProgram, queryCost_energyMinimizer, sampledGroundStateCostBound]
  have hsweep := cost_sampledSweepProgram_le hL hq h hs h0 h1 hΔ hgs hδ0 hδ1 hδc I hm hgood b D hD
    L le_rfl
  have hcard : ((sampledSweep hq h hs h0 h1 E₀ Δ I L).image fun w ↦
      (fullLeftEquiv L q).symm w).card ≤ max 1 (sampledSizeBudget q Δ L ℓ D) := by
    refine Finset.card_image_le.trans ?_
    refine (sampledSweep_spec hL hq h hs h0 h1 hΔ hgs hδ0 hδ1 hδc I hm hgood L le_rfl).1.trans ?_
    simp only [show L ≠ 0 by omega, ↓reduceIte]
    exact le_max_of_le_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left ℓ hD))
  have hsize : max 1 (sampledSizeBudget q Δ L ℓ (q ^ (2 * κ))) ≤
      max 1 (sampledSizeBudget q Δ L ℓ D) :=
    max_le_max le_rfl (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left ℓ hD))
  exact Nat.add_le_add
    (hsweep.trans (Nat.mul_le_mul_left L (sampledStepCostBound_mono q Δ L le_rfl le_rfl le_rfl
      hsize)))
    (energyMinimizerCost_mono le_rfl q b hcard)

/-- The budget is polynomial in the chain length when `ℓ`, `D` and `b` are replaced by
polynomials. -/
theorem isNatPolynomialBounded_sampledGroundStateCostBound {Δ : ℝ}
    (hΔ : 0 < Δ) (C₁ p₁ C₂ p₂ : ℕ) :
    IsNatPolynomialBounded fun L ↦
      sampledGroundStateCostBound q Δ L (C₁ * L ^ p₁) (C₁ * L ^ p₁) (C₂ * L ^ p₂) := by
  have hc : 0 < (Δ / 169) ^ 2 := sq_pos_of_pos (div_pos hΔ (by norm_num))
  set D' := constantCutBond q 1 1 Δ ((Δ / 169) ^ 2) with hD'
  have hK : IsNatPolynomialBounded fun L ↦
      (2 * ⌈((q * D' : ℕ) : ℝ) ^ 2 / ((Δ / 169) ^ 2 / (2 * L))⌉₊ + 1) ^ (2 * (q * D') ^ 2) :=
    ⟨(2 * ⌈2 * ((q * D' : ℕ) : ℝ) ^ 2 / (Δ / 169) ^ 2⌉₊ + 1) ^ (2 * (q * D') ^ 2),
      2 * (q * D') ^ 2, fun L hL ↦
      (boundaryNet_card_bound_le_polynomial (q := q) (D := D') hL hc).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ L) _))⟩
  have hsize : IsNatPolynomialBounded fun L ↦
      lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ :=
    ⟨lvvSizeTrimmingCoefficient q Δ, lvvSizeTrimmingDegree q Δ, fun L _ ↦
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ L) _)⟩
  have hm : IsNatPolynomialBounded fun L ↦
      max 1 (bondTrimmingRadius L (lvvReferenceBond q Δ L)) := by
    obtain ⟨M, r, -, hrad⟩ := exists_bondTrimmingRadius_lvvReferenceBond_polynomial q Δ
    refine IsNatPolynomialBounded.max_one ⟨⌈M⌉₊, r, fun L hL ↦ ?_⟩
    have h1 := hrad L hL
    have h2 : (M : ℝ) * (L : ℝ) ^ r ≤ (⌈M⌉₊ : ℝ) * ((L + 1 : ℕ) : ℝ) ^ r := by
      gcongr
      · exact Nat.le_ceil M
      · exact_mod_cast Nat.le_succ L
    exact_mod_cast h1.trans h2
  have hpoly : ∀ (C p : ℕ), IsNatPolynomialBounded fun L ↦ C * L ^ p := fun C p ↦
    ⟨C, p, fun L _ ↦ Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ L) _)⟩
  have hℓ := hpoly C₁ p₁
  have hb := hpoly C₂ p₂
  have hL : IsNatPolynomialBounded fun L ↦ L := IsNatPolynomialBounded.id
  have hone := IsNatPolynomialBounded.const 1
  have hs : IsNatPolynomialBounded fun L ↦
      max 1 (C₁ * L ^ p₁ * (C₁ * L ^ p₁) *
        (lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ)) :=
    ((hℓ.mul hℓ).mul hsize).max_one
  have hext : IsNatPolynomialBounded fun L ↦
      max 1 (C₁ * L ^ p₁ * (C₁ * L ^ p₁) *
        (lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ)) *
        (q * (1 + q * (C₂ * L ^ p₂) ^ 2)) :=
    hs.mul ((IsNatPolynomialBounded.const q).mul (hone.add
      ((IsNatPolynomialBounded.const q).mul (hb.pow 2))))
  have hconv : IsNatPolynomialBounded fun L ↦ 1 + L * q * (C₂ * L ^ p₂) ^ 2 *
      (q * max 1 (C₁ * L ^ p₁ * (C₁ * L ^ p₁) *
        (lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ)) * D') ^ 3 :=
    hone.add (((hL.mul (IsNatPolynomialBounded.const q)).mul (hb.pow 2)).mul
      ((((IsNatPolynomialBounded.const q).mul hs).mul (IsNatPolynomialBounded.const D')).pow 3))
  have hnet : IsNatPolynomialBounded fun L ↦ (D' + 1) * ((1 + (q * D') ^ 2 *
      (2 * ⌈((q * D' : ℕ) : ℝ) ^ 2 / ((Δ / 169) ^ 2 / (2 * L))⌉₊ + 1) ^ (2 * (q * D') ^ 2)) +
      (2 * ⌈((q * D' : ℕ) : ℝ) ^ 2 / ((Δ / 169) ^ 2 / (2 * L))⌉₊ + 1) ^ (2 * (q * D') ^ 2) *
        (2 * (1 + L * q * (C₂ * L ^ p₂) ^ 2 *
          (q * max 1 (C₁ * L ^ p₁ * (C₁ * L ^ p₁) *
            (lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ)) * D') ^ 3))) :=
    (IsNatPolynomialBounded.const (D' + 1)).mul
      ((hone.add ((IsNatPolynomialBounded.const ((q * D') ^ 2)).mul hK)).add
        (hK.mul ((IsNatPolynomialBounded.const 2).mul hconv)))
  have htrim : IsNatPolynomialBounded fun L ↦
      lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ *
        (1 + L * q * (C₂ * L ^ p₂) ^ 3) :=
    hsize.mul (hone.add ((hL.mul (IsNatPolynomialBounded.const q)).mul (hb.pow 3)))
  have hfilt : IsNatPolynomialBounded fun L ↦ 1 + C₁ * L ^ p₁ * (C₁ * L ^ p₁) * L * q ^ 2 :=
    hone.add (((hℓ.mul hℓ).mul hL).mul (IsNatPolynomialBounded.const (q ^ 2)))
  have happly : IsNatPolynomialBounded fun L ↦ C₁ * L ^ p₁ * (C₁ * L ^ p₁) *
      (lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ *
        (1 + L * q ^ 2 * (C₁ * L ^ p₁) ^ 2 *
          max 1 (bondTrimmingRadius L (lvvReferenceBond q Δ L)) ^ 2)) :=
    (hℓ.mul hℓ).mul (hsize.mul (hone.add
      (((hL.mul (IsNatPolynomialBounded.const (q ^ 2))).mul (hℓ.pow 2)).mul (hm.pow 2))))
  have hstep : IsNatPolynomialBounded fun L ↦
      sampledStepCostBound q Δ L (C₁ * L ^ p₁) (C₁ * L ^ p₁) (C₂ * L ^ p₂)
        (max 1 (sampledSizeBudget q Δ L (C₁ * L ^ p₁) (C₁ * L ^ p₁))) := by
    simp only [sampledStepCostBound, sampledSizeBudget, extensionCost, netCost,
      convexProgramCost, schmidtTrimCost, filterFactorsCost, applyFactorCost]
    exact hext.add (hnet.add (htrim.add (hfilt.add happly)))
  have hfinal : IsNatPolynomialBounded fun L ↦ 1 + L * q * (C₂ * L ^ p₂) ^ 2 *
      max 1 (C₁ * L ^ p₁ * (C₁ * L ^ p₁) *
        (lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ)) ^ 3 :=
    hone.add (((hL.mul (IsNatPolynomialBounded.const q)).mul (hb.pow 2)).mul (hs.pow 3))
  simp only [sampledGroundStateCostBound, energyMinimizerCost, sampledSizeBudget]
  exact (hL.mul hstep).add hfinal

/-- **The sampled program has polynomial cost on good words** (Theorem 1 on the sampled
route, the running-time part, in the cost model of the query type and the documented scope
of the ground-energy ratio). With the bond budget `C L^p` and the rank budget of the words
declared as in the success theorem, there
are `P ≥ 1` and `d` such that on every good family of words the program costs at most
`P (L + 1)^d` and issues at most that many queries. LVV13, `algo53.tex`, lines 213--219 and
657. -/
theorem exists_sampledGroundStateProgram_cost_polynomial (hq : 2 ≤ q) {Δ B η : ℝ}
    (hΔ : 0 < Δ) (hη : 0 < η) (C p : ℕ) :
    ∃ P d : ℕ, 1 ≤ P ∧ ∀ (L : ℕ) [NeZero L]
      (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
      (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) (E₀ : ℝ)
      (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
      IsGappedGroundState (∑ j, h j) E₀ Γ Δ → E₀ / Δ ≤ B →
      let δ := sampledPrecisionConstant Δ η / L
      ∀ I : Fin L → Fin (sampledWordCount q L E₀ Δ δ) → Fin (sampledPower L E₀ Δ δ) → Fin L,
        (∀ i, GoodWords h E₀ (sampledPower L E₀ Δ δ) (δ / 8) (sampledLetterBound q L E₀ Δ δ)
          (I i)) →
        FreeM.countQueries honestOracle
            (sampledGroundStateProgram hq h hs h0 h1 E₀ Δ I (C * L ^ p)
              (sampledRankBound q L E₀ Δ δ)) ≤
          FreeM.cost honestOracle queryCost
            (sampledGroundStateProgram hq h hs h0 h1 E₀ Δ I (C * L ^ p)
              (sampledRankBound q L E₀ Δ δ)) ∧
        FreeM.cost honestOracle queryCost
            (sampledGroundStateProgram hq h hs h0 h1 E₀ Δ I (C * L ^ p)
              (sampledRankBound q L E₀ Δ δ)) ≤
          P * (L + 1) ^ d := by
  obtain ⟨C₁, p₁, hC₁, hbud⟩ := exists_sampled_budgets_polynomial (B := B) hq hΔ hη
  obtain ⟨P, d, hP, hbound⟩ := (isNatPolynomialBounded_sampledGroundStateCostBound hΔ
    (max C₁ C) (max p₁ p) C p).exists_one_le
  refine ⟨P, d, hP, ?_⟩
  intro L _ h hs h0 h1 E₀ Γ hgs hEB δ I hgood
  refine ⟨countQueries_le_cost honestOracle queryCost one_le_queryCost _, ?_⟩
  have hL : 1 ≤ L := Nat.pos_of_neZero L
  obtain ⟨hE₀, hE₀L⟩ := groundEnergy_nonneg_and_le h h0 h1 hgs
  obtain ⟨hℓD, hD⟩ := hbud L E₀ hL hE₀ hE₀L hEB
  obtain ⟨hδ0, hδ1, hδc, -⟩ := sampledPrecision_spec hΔ hη hL
  have hD1 : 1 ≤ sampledRankBound q L E₀ Δ δ := Nat.one_le_pow _ _ (by omega)
  have hℓ : sampledWordCount q L E₀ Δ δ ≤ C₁ * L ^ p₁ :=
    (Nat.le_mul_of_pos_right _ hD1).trans hℓD
  have hpow' : C₁ * L ^ p₁ ≤ max C₁ C * L ^ max p₁ p :=
    Nat.mul_le_mul (le_max_left _ _) (Nat.pow_le_pow_right hL (le_max_left _ _))
  calc
    _ ≤ sampledGroundStateCostBound q Δ L (sampledWordCount q L E₀ Δ δ)
          (sampledRankBound q L E₀ Δ δ) (C * L ^ p) :=
        cost_sampledGroundStateProgram_le (Nat.pos_of_neZero L) hq h hs h0 h1 hΔ hgs hδ0 hδ1 hδc
          I (Nat.le_ceil _) hgood (C * L ^ p) (sampledRankBound q L E₀ Δ δ) le_rfl
    _ ≤ sampledGroundStateCostBound q Δ L (max C₁ C * L ^ max p₁ p) (max C₁ C * L ^ max p₁ p)
          (C * L ^ p) :=
        sampledGroundStateCostBound_mono q Δ L (hℓ.trans hpow') (hD.trans hpow') le_rfl
    _ ≤ P * (L + 1) ^ d := hbound L hL

end TNLean.MPS.AreaLaw
