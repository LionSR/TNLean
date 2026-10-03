/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.MinimalCutIntervals
import TNLean.MPS.MPU.EndpointGramNormalization

/-!
# Endpoint normalization of the minimal interval representation

The endpoint cut spaces have dimension one. Their normalized bases force the
actual endpoint Gram hulls to be the singleton identity. Consequently the
weighted full interval equals the original unitary, with its complex phase.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix
open scoped Matrix ComplexOrder

namespace MPUCircuit

private theorem trace_eq_entry_of_unique {r : Type*} [Fintype r] [Unique r]
    (M : Matrix r r ℂ) (x y : r) : trace M = M x y := by
  rw [Subsingleton.elim x default, Subsingleton.elim y default]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_unique]

private theorem prefixInputGram_eq_trace_smul_one_of_empty_cap
    {a b r : Type*} [Fintype a] [Fintype b] [Unique a] [Unique b] [Unique r]
    [DecidableEq r] (F : a → b → Matrix Unit r ℂ)
    (hF : ∀ a b q, F a b () q = 1) (ρ : Matrix b b ℂ) :
    prefixInputGram F ρ = trace ρ • 1 := by
  classical
  ext x y
  rw [trace_eq_entry_of_unique ρ default default]
  simp [prefixInputGram, intervalGramTransfer, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, hF, Subsingleton.elim x y]

private theorem prefixInputGram_eq_trace_smul_one_of_suffix_cap
    {a b e f r : Type*} [Fintype a] [Fintype b] [Fintype e]
    [Fintype r] [Unique e] [Unique f] [Unique r] [DecidableEq b] [DecidableEq f]
    [DecidableEq r] (F : a → Matrix b r ℂ) (G : e → Matrix r f ℂ)
    (hU : (MPUPrefixGram.factorizedOperator F G).IsIsometry)
    (hG : ∀ e q f, G e q f = 1) (ρ : Matrix b b ℂ) :
    prefixInputGram (fun aa bb (_ : Unit) q ↦ F aa bb q) ρ = trace ρ • 1 := by
  have hcap : MPUPrefixGram.suffixGram G (1 : Matrix f f ℂ) = 1 := by
    ext x y
    simp [MPUPrefixGram.suffixGram, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, hG, Matrix.one_apply,
      Subsingleton.elim x y]
  have ht := MPUPrefixGram.trace_prefixGram_mul_suffixGram_of_isIsometry
    F G ρ (1 : Matrix f f ℂ) hU
  rw [hcap, Matrix.mul_one, Matrix.trace_one, Fintype.card_unique, Nat.cast_one,
    mul_one, MPUPrefixGram.prefixGram_eq_prefixInputGram] at ht
  ext x y
  rw [← trace_eq_entry_of_unique
    (prefixInputGram (fun aa bb (_ : Unit) q ↦ F aa bb q) ρ) x y, ht]
  simp [Matrix.smul_apply, Subsingleton.elim x y]

private theorem prefixGramAffineHull_eq_singleton_one_of_gram_eq_trace
    {a b r : Type*} [Fintype a] [Fintype b] [Nonempty b] [DecidableEq r]
    (F : a → b → Matrix Unit r ℂ)
    (hF : ∀ ρ : Matrix b b ℂ, prefixInputGram F ρ = trace ρ • 1) :
    prefixGramAffineHull F = ({1} : AffineSubspace ℝ (Matrix r r ℂ)) := by
  classical
  have hset : densityPrefixGrams F = {1} := by
    ext P
    constructor
    · rintro ⟨ρ, _, ht, hP⟩
      rw [hF, ht, one_smul] at hP
      exact hP.symm
    · intro hP
      have hP' : P = 1 := hP
      subst P
      refine ⟨faithfulDensity b, (faithfulDensity_posDef b).posSemidef,
        faithfulDensity_trace b, ?_⟩
      rw [hF, faithfulDensity_trace, one_smul]
  rw [prefixGramAffineHull, hset, AffineSubspace.affineSpan_singleton]

end MPUCircuit

open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace MPUCircuit

/-- The initial prefix Gram is the trace of the input times the identity. The empty prefix and the
normalized initial cut basis both have dimension one.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem prefixInputGram_minimalOperatorPrefix_zero {d N : ℕ}
    (hd : 0 < d) (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k))
    (hB0 : ∀ q, (B 0 q).val = 1)
    (ρ : Matrix (MPSPreparation.CutPrefixConfig d N 0)
      (MPSPreparation.CutPrefixConfig d N 0) ℂ) :
    prefixInputGram (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B 0 aa bb q) ρ =
      trace ρ • 1 := by
  classical
  have hψ := operatorCoefficientTensor_ne_zero hd U hU
  let : Unique (MPSPreparation.CutPrefixConfig d N 0) := Classical.choice
    (Fintype.card_eq_one_iff_nonempty_unique.mp (MPSPreparation.card_cutPrefixConfig_zero d N))
  let : Unique (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) 0)) :=
    Equiv.unique (finCongr (MPSPreparation.cutCoefficientRank_zero (operatorCoefficientTensor U) hψ))
  apply prefixInputGram_eq_trace_smul_one_of_empty_cap
  intro aa bb q
  change (B 0 q).val (pairPhysicalConfig aa bb) = 1
  rw [hB0 q]
  rfl

/-- The final prefix Gram is the trace of the input times the identity. Global unitarity and the
normalized final cut basis determine this identity.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem prefixInputGram_minimalOperatorPrefix_last {d N : ℕ}
    (hd : 0 < d) (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k))
    (hBN : ∀ q, (B N q).val = MPSPreparation.fullCutVector (operatorCoefficientTensor U))
    (ρ : Matrix (MPSPreparation.CutPrefixConfig d N N)
      (MPSPreparation.CutPrefixConfig d N N) ℂ) :
    prefixInputGram (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B N aa bb q) ρ =
      trace ρ • 1 := by
  classical
  have hψ := operatorCoefficientTensor_ne_zero hd U hU
  let : Unique (MPSPreparation.CutSuffixConfig d N N) := Classical.choice
    (Fintype.card_eq_one_iff_nonempty_unique.mp (MPSPreparation.card_cutSuffixConfig_last d N))
  let : Unique (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) N)) :=
    Equiv.unique (finCongr (MPSPreparation.cutCoefficientRank_last (operatorCoefficientTensor U) hψ))
  apply prefixInputGram_eq_trace_smul_one_of_suffix_cap
    (minimalOperatorPrefixFactor U B N) (minimalOperatorSuffixFactor U B N)
    (minimalOperatorFactors_isIsometry U hU B N)
  intro aa q bb
  exact MPSPreparation.cutSuffixMatrix_last (operatorCoefficientTensor U) B hBN
    (pairPhysicalConfig aa bb) q

/-- The real affine hull of the initial prefix Grams is the singleton identity.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem prefixGramAffineHull_minimalOperatorPrefix_zero {d N : ℕ}
    (hd : 0 < d) (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k))
    (hB0 : ∀ q, (B 0 q).val = 1) :
    prefixGramAffineHull (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B 0 aa bb q) =
      ({1} : AffineSubspace ℝ
        (Matrix (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) 0))
          (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) 0)) ℂ)) := by
  let : Nonempty (MPSPreparation.CutPrefixConfig d N 0) := ⟨fun _ ↦ ⟨0, hd⟩⟩
  exact prefixGramAffineHull_eq_singleton_one_of_gram_eq_trace _
    (prefixInputGram_minimalOperatorPrefix_zero hd U hU B hB0)

/-- The real affine hull of the final prefix Grams is the singleton identity.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem prefixGramAffineHull_minimalOperatorPrefix_last {d N : ℕ}
    (hd : 0 < d) (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k))
    (hBN : ∀ q, (B N q).val = MPSPreparation.fullCutVector (operatorCoefficientTensor U)) :
    prefixGramAffineHull (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B N aa bb q) =
      ({1} : AffineSubspace ℝ
        (Matrix (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) N))
          (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) N)) ℂ)) := by
  let : Nonempty (MPSPreparation.CutPrefixConfig d N N) := ⟨fun _ ↦ ⟨0, hd⟩⟩
  exact prefixGramAffineHull_eq_singleton_one_of_gram_eq_trace _
    (prefixInputGram_minimalOperatorPrefix_last hd U hU B hBN)

/-- Every metric in the actual initial prefix Gram hull is the identity.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem eq_one_of_mem_minimalOperatorPrefixHull_zero {d N : ℕ}
    (hd : 0 < d) (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k))
    (hB0 : ∀ q, (B 0 q).val = 1)
    {P : Matrix (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) 0))
      (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) 0)) ℂ}
    (hP : P ∈ prefixGramAffineHull
      (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B 0 aa bb q)) : P = 1 := by
  rw [prefixGramAffineHull_minimalOperatorPrefix_zero hd U hU B hB0] at hP
  exact hP

/-- Every metric in the actual final prefix Gram hull is the identity.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem eq_one_of_mem_minimalOperatorPrefixHull_last {d N : ℕ}
    (hd : 0 < d) (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k))
    (hBN : ∀ q, (B N q).val = MPSPreparation.fullCutVector (operatorCoefficientTensor U))
    {P : Matrix (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) N))
      (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) N)) ℂ}
    (hP : P ∈ prefixGramAffineHull
      (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B N aa bb q)) : P = 1 := by
  rw [prefixGramAffineHull_minimalOperatorPrefix_last hd U hU B hBN] at hP
  exact hP

/-- The configurations of the full interval are exactly the configurations of the physical chain.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def fullCutIntervalConfigEquiv (d N : ℕ) :
    (Fin N → Fin d) ≃ MPSPreparation.CutIntervalConfig d N 0 N where
  toFun x := fun s ↦ x s.1
  invFun x := fun s ↦ x ⟨s, Nat.zero_le _, s.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The full interval tensor of the endpoint-normalized minimal representation recovers the
original unitary, including its complex phase.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem minimalOperatorInterval_full_apply {d N : ℕ}
    (hd : 0 < d) (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k))
    (hB0 : ∀ q, (B 0 q).val = 1)
    (hBN : ∀ q, (B N q).val = MPSPreparation.fullCutVector (operatorCoefficientTensor U))
    (x y : Fin N → Fin d)
    (α : Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) 0))
    (β : Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) N)) :
    minimalOperatorInterval U B (Nat.zero_le N)
      (fullCutIntervalConfigEquiv d N x) (fullCutIntervalConfigEquiv d N y) α β = U x y := by
  classical
  have hψ := operatorCoefficientTensor_ne_zero hd U hU
  let : Unique (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) 0)) :=
    Equiv.unique (finCongr (MPSPreparation.cutCoefficientRank_zero (operatorCoefficientTensor U) hψ))
  let u : MPSPreparation.CutPrefixConfig (d * d) N 0 :=
    fun s ↦ False.elim (Nat.not_lt_zero _ s.2)
  let w := pairPhysicalConfig (fullCutIntervalConfigEquiv d N x)
    (fullCutIntervalConfigEquiv d N y)
  have h := MPSPreparation.cutPrefixMatrix_interval (operatorCoefficientTensor U) B
    (Nat.zero_le N) u w β
  have hcfg : MPSPreparation.joinCutPrefix 0 N u w =
      MPSPreparation.cutPrefixRestriction (pairPhysicalConfig x y) N := by
    funext s
    simp [MPSPreparation.joinCutPrefix, w, fullCutIntervalConfigEquiv,
      pairPhysicalConfig, MPSPreparation.cutPrefixRestriction]
  rw [hcfg] at h
  simp only [MPSPreparation.cutPrefixMatrix, hB0, hBN, Pi.one_apply, Matrix.mul_apply,
    one_mul, Fintype.sum_unique] at h
  rw [MPSPreparation.fullCutVector_restriction] at h
  change operatorCoefficientTensor U (fun s ↦ finProdFinEquiv (x s, y s)) = _ at h
  rw [operatorCoefficientTensor_apply] at h
  change U x y = MPSPreparation.cutIntervalMatrix (operatorCoefficientTensor U) B
    (Nat.zero_le N) w default β at h
  rw [Subsingleton.elim (default : Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) 0)) α]
    at h
  exact h.symm

/-- The weighted full interval recovers the original unitary entrywise. Its two endpoint metrics
are derived from the actual prefix Gram hulls.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem weightedMinimalOperatorInterval_full_apply {d N : ℕ}
    (hd : 0 < d) (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k))
    (hB0 : ∀ q, (B 0 q).val = 1)
    (hBN : ∀ q, (B N q).val = MPSPreparation.fullCutVector (operatorCoefficientTensor U))
    {P : Matrix (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) 0))
      (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) 0)) ℂ}
    (hP : P ∈ prefixGramAffineHull
      (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B 0 aa bb q))
    {S : Matrix (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) N))
      (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) N)) ℂ}
    (hS : S ∈ prefixGramAffineHull
      (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B N aa bb q))
    (x y : Fin N → Fin d)
    (α : Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) 0))
    (β : Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) N)) :
    vectorizedWeightedInterval (minimalOperatorInterval U B (Nat.zero_le N))
      (CFC.sqrt P) (CFC.sqrt (dualGramMetric S))
      (fullCutIntervalConfigEquiv d N x, (β, α)) (fullCutIntervalConfigEquiv d N y) = U x y := by
  rw [eq_one_of_mem_minimalOperatorPrefixHull_zero hd U hU B hB0 hP,
    eq_one_of_mem_minimalOperatorPrefixHull_last hd U hU B hBN hS]
  have hc : Fintype.card (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) N)) = 1 := by
    simp only [Fintype.card_fin]
    exact MPSPreparation.cutCoefficientRank_last (operatorCoefficientTensor U)
      (operatorCoefficientTensor_ne_zero hd U hU)
  rw [dualGramMetric_one_of_card_eq_one hc]
  simp only [vectorizedWeightedInterval, CFC.sqrt_one, Matrix.one_mul, Matrix.mul_one]
  exact minimalOperatorInterval_full_apply hd U hU B hB0 hBN x y α β

/-- Removing the two one-dimensional endpoint coordinates from the weighted full interval gives
precisely the original unitary.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem weightedMinimalOperatorInterval_full_submatrix {d N : ℕ}
    (hd : 0 < d) (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ)
    (B : ∀ k, Module.Basis (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k))
      ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k))
    (hB0 : ∀ q, (B 0 q).val = 1)
    (hBN : ∀ q, (B N q).val = MPSPreparation.fullCutVector (operatorCoefficientTensor U))
    {P : Matrix (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) 0))
      (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) 0)) ℂ}
    (hP : P ∈ prefixGramAffineHull
      (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B 0 aa bb q))
    {S : Matrix (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) N))
      (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) N)) ℂ}
    (hS : S ∈ prefixGramAffineHull
      (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B N aa bb q))
    (α : Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) 0))
    (β : Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) N)) :
    (vectorizedWeightedInterval (minimalOperatorInterval U B (Nat.zero_le N))
      (CFC.sqrt P) (CFC.sqrt (dualGramMetric S))).submatrix
      (fun x ↦ (fullCutIntervalConfigEquiv d N x, (β, α)))
      (fullCutIntervalConfigEquiv d N) = U := by
  ext x y
  exact weightedMinimalOperatorInterval_full_apply hd U hU B hB0 hBN hP hS x y α β

open scoped Classical in
/-- Every finite unitary admits one coherent family of balanced minimal-cut metrics and interval
isometries, with identity endpoint metrics and full interval exactly equal to the unitary.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem exists_normalized_minimalInterval_family_of_unitary {d N : ℕ}
    (hd : 0 < d) (hN : 0 < N)
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ) :
    ∃ B : ∀ k, Module.Basis (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k))
        ℂ (MPSPreparation.cutColumnSpace (operatorCoefficientTensor U) k),
      (∀ q, (B 0 q).val = 1) ∧
      (∀ q, (B N q).val = MPSPreparation.fullCutVector (operatorCoefficientTensor U)) ∧
      ∃ P : ∀ j : Fin (N + 1),
          Matrix (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) j.val))
            (Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) j.val)) ℂ,
        (∀ j, P j ∈ prefixGramAffineHull
            (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j.val aa bb q) ∧
          (P j).PosDef ∧ (dualGramMetric (P j)).PosDef ∧
          (∀ X ∈ prefixGramAffineHull
              (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B j.val aa bb q),
            trace (X * dualGramMetric (P j)) = 1) ∧
          trace ((dualGramMetric (P j))⁻¹ * (P j)⁻¹) =
            (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) j.val : ℂ) ^ 2) ∧
        (∀ (j k : Fin (N + 1)) (hjk : j.val ≤ k.val),
          (vectorizedWeightedInterval (minimalOperatorInterval U B hjk)
              (CFC.sqrt (P j)) (CFC.sqrt (dualGramMetric (P k))))ᴴ *
            vectorizedWeightedInterval (minimalOperatorInterval U B hjk)
              (CFC.sqrt (P j)) (CFC.sqrt (dualGramMetric (P k))) = 1) ∧
        P 0 = 1 ∧ P (Fin.last N) = 1 ∧
        ∀ (α : Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) 0))
          (β : Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) N)),
          (vectorizedWeightedInterval (minimalOperatorInterval U B (Nat.zero_le N))
            (CFC.sqrt (P 0)) (CFC.sqrt (dualGramMetric (P (Fin.last N))))).submatrix
            (fun x ↦ (fullCutIntervalConfigEquiv d N x, (β, α)))
            (fullCutIntervalConfigEquiv d N) = U := by
  obtain ⟨B, hB0, hBN, P, hP, hIntervals⟩ :=
    exists_simultaneous_balanced_interval_isometries_of_unitary hd hN U hU
  have h0 := eq_one_of_mem_minimalOperatorPrefixHull_zero hd U hU B hB0 (hP 0).1
  have hlast := eq_one_of_mem_minimalOperatorPrefixHull_last hd U hU B hBN (hP (Fin.last N)).1
  refine ⟨B, hB0, hBN, P, hP, hIntervals, h0, hlast, ?_⟩
  intro α β
  exact weightedMinimalOperatorInterval_full_submatrix hd U hU B hB0 hBN
    (hP 0).1 (hP (Fin.last N)).1 α β

end MPUCircuit
