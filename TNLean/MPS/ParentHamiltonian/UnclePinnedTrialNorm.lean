/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleTrialTransferNorm
import TNLean.MPS.ParentHamiltonian.UncleWallGramBounds
import QICLean.Channel.Peripheral.UnitalKraus
import QICLean.Analysis.TraceNormNet

/-!
# Linear norm bounds for an actual trial with one pinned wall

A one-site wall interval pins that wall. The other interval retains its
actual moving-wall Kraus map. Source unital diagonal transfers contract
matrix operator norms, while the actual moving-wall Gram bound is linear
in its length. The exact finite transfer trace therefore bounds the actual
pinned trial norm linearly, uniformly in all three padding lengths.

Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296.
No state-norm growth or endpoint-energy rate is supplied as a hypothesis.
-/

noncomputable section

open scoped Matrix BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace MPSTensor

variable {d a b : ℕ}

private theorem norm_linearMap_trace_le_entry_bound
    (T : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ)
    (C : ℝ) (hT : ∀ X, ‖T X‖ ≤ C * ‖X‖) :
    ‖LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ) T‖ ≤ (a : ℝ) ^ 2 * C := by
  rw [Matrix.linearMap_trace_eq_sum_apply_single]
  calc
    _ ≤ ∑ i : Fin a, ‖∑ j : Fin a, T (Matrix.single i j 1) i j‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin a, ∑ j : Fin a, ‖T (Matrix.single i j 1) i j‖ :=
      Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _
    _ ≤ ∑ _i : Fin a, ∑ _j : Fin a, C := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ‖T (Matrix.single i j 1)‖ := Matrix.norm_apply_le_l2_opNorm _ i j
        _ ≤ C * ‖(Matrix.single i j 1 : Matrix (Fin a) (Fin a) ℂ)‖ := hT _
        _ = C := by rw [Matrix.l2_opNorm_single_one, mul_one]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- An actual one-site R interval and one moving L interval have a uniform
linear squared-norm bound, independently of every uniform padding length.
The stationary faithful density and mixed damping are the source normalized
block assumptions used for the actual L-wall Gram estimate.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
theorem norm_uncleTwoWallTrial_one_wall_sq_le_mul
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hA : Kraus.mapLM A 1 = 1) (hB : Kraus.mapLM B 1 = 1)
    (ρ : Matrix (Fin b) (Fin b) ℂ) (hρ : ρ.PosDef)
    (hρB : Kraus.adjointMap B ρ = ρ)
    (hSpect : Kraus.mixedMapSpectralRadius B A < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ p q s t : ℕ,
      ‖(WithLp.linearEquiv 2 ℂ (NSiteSpace d (p + 1 + q + s + t))).symm
          (uncleTwoWallTrial A B R L p 1 q s t)‖ ^ 2 ≤ C * s := by
  obtain ⟨C, hC, hL⟩ := uncleWallGramMap_apply_l2_opNorm_le_mul B A L ρ hρ hρB hA hSpect
  let S := (Matrix.trace (uncleWallGram A B R 1)).re
  have hS : 0 ≤ S :=
    (Complex.nonneg_iff.mp (uncleWallGram_posSemidef A B R 1).trace_nonneg).1
  let K := S + 1
  have hK : 0 < K := by dsimp [K]; linarith
  have hR (X : Matrix (Fin b) (Fin b) ℂ) :
      ‖uncleWallGramMap A B R 1 X‖ ≤ K * ‖X‖ := by
    change ‖Matrix.rectangularKrausMap
      (fun σ : Cfg d 1 ↦ uncleDomainWallWord A B R (List.ofFn σ)) X‖ ≤ _
    exact (uncleWallGramMap_apply_l2_opNorm_le_trace A B R 1 X).trans
      (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (norm_nonneg X))
  have hLbound (s : ℕ) (X : Matrix (Fin a) (Fin a) ℂ) :
      ‖uncleWallGramMap B A L s X‖ ≤ C * s * ‖X‖ := by
    exact hL s X
  have hTotal (p q s t : ℕ) (X : Matrix (Fin a) (Fin a) ℂ) :
      ‖uncleTwoWallTransfer A B R L p 1 q s t X‖ ≤ (K * C * s) * ‖X‖ := by
    change ‖((Kraus.mapLM A) ^ p)
      (uncleWallGramMap A B R 1 (((Kraus.mapLM B) ^ q)
        (uncleWallGramMap B A L s (((Kraus.mapLM A) ^ t) X))))‖ ≤ _
    calc
      _ ≤ ‖uncleWallGramMap A B R 1 (((Kraus.mapLM B) ^ q)
          (uncleWallGramMap B A L s (((Kraus.mapLM A) ^ t) X)))‖ :=
        norm_mapLM_pow_apply_le_of_mapLM_one A hA p _
      _ ≤ K * ‖((Kraus.mapLM B) ^ q)
          (uncleWallGramMap B A L s (((Kraus.mapLM A) ^ t) X))‖ := hR _
      _ ≤ K * ‖uncleWallGramMap B A L s (((Kraus.mapLM A) ^ t) X)‖ :=
        mul_le_mul_of_nonneg_left (norm_mapLM_pow_apply_le_of_mapLM_one B hB q _) hK.le
      _ ≤ K * (C * s * ‖((Kraus.mapLM A) ^ t) X‖) :=
        mul_le_mul_of_nonneg_left (hLbound s _) hK.le
      _ ≤ K * (C * s * ‖X‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_mapLM_pow_apply_le_of_mapLM_one A hA t X)
          (mul_nonneg hC.le (Nat.cast_nonneg s))) hK.le
      _ = _ := by ring
  let D := (a : ℝ) ^ 2 * K * C + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, fun p q s t ↦ ?_⟩
  rw [norm_uncleTwoWallTrial_sq_eq_trace_transfer]
  calc
    _ ≤ ‖LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
        (uncleTwoWallTransfer A B R L p 1 q s t)‖ := Complex.re_le_norm _
    _ ≤ (a : ℝ) ^ 2 * (K * C * s) :=
      norm_linearMap_trace_le_entry_bound _ _ (hTotal p q s t)
    _ = ((a : ℝ) ^ 2 * K * C) * s := by ring
    _ ≤ D * s := mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) (Nat.cast_nonneg s)

/-- The complementary actual trial with its second wall interval pinned
also has a uniform linear squared-norm bound in the first moving interval.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
theorem norm_uncleTwoWallTrial_second_wall_sq_le_mul
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hA : Kraus.mapLM A 1 = 1) (hB : Kraus.mapLM B 1 = 1)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.PosDef)
    (hρA : Kraus.adjointMap A ρ = ρ)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ p r q t : ℕ,
      ‖(WithLp.linearEquiv 2 ℂ (NSiteSpace d (p + r + q + 1 + t))).symm
          (uncleTwoWallTrial A B R L p r q 1 t)‖ ^ 2 ≤ C * r := by
  obtain ⟨C, hC, hR⟩ := uncleWallGramMap_apply_l2_opNorm_le_mul A B R ρ hρ hρA hB hSpect
  let S := (Matrix.trace (uncleWallGram B A L 1)).re
  have hS : 0 ≤ S :=
    (Complex.nonneg_iff.mp (uncleWallGram_posSemidef B A L 1).trace_nonneg).1
  let K := S + 1
  have hK : 0 < K := by dsimp [K]; linarith
  have hL (X : Matrix (Fin a) (Fin a) ℂ) :
      ‖uncleWallGramMap B A L 1 X‖ ≤ K * ‖X‖ := by
    exact (uncleWallGramMap_apply_l2_opNorm_le_trace B A L 1 X).trans
      (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (norm_nonneg X))
  have hTotal (p r q t : ℕ) (X : Matrix (Fin a) (Fin a) ℂ) :
      ‖uncleTwoWallTransfer A B R L p r q 1 t X‖ ≤ (C * K * r) * ‖X‖ := by
    change ‖((Kraus.mapLM A) ^ p)
      (uncleWallGramMap A B R r (((Kraus.mapLM B) ^ q)
        (uncleWallGramMap B A L 1 (((Kraus.mapLM A) ^ t) X))))‖ ≤ _
    calc
      _ ≤ ‖uncleWallGramMap A B R r (((Kraus.mapLM B) ^ q)
          (uncleWallGramMap B A L 1 (((Kraus.mapLM A) ^ t) X)))‖ :=
        norm_mapLM_pow_apply_le_of_mapLM_one A hA p _
      _ ≤ C * r * ‖((Kraus.mapLM B) ^ q)
          (uncleWallGramMap B A L 1 (((Kraus.mapLM A) ^ t) X))‖ := hR r _
      _ ≤ C * r * ‖uncleWallGramMap B A L 1 (((Kraus.mapLM A) ^ t) X)‖ :=
        mul_le_mul_of_nonneg_left (norm_mapLM_pow_apply_le_of_mapLM_one B hB q _)
          (mul_nonneg hC.le (Nat.cast_nonneg r))
      _ ≤ C * r * (K * ‖((Kraus.mapLM A) ^ t) X‖) :=
        mul_le_mul_of_nonneg_left (hL _) (mul_nonneg hC.le (Nat.cast_nonneg r))
      _ ≤ C * r * (K * ‖X‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_mapLM_pow_apply_le_of_mapLM_one A hA t X) hK.le)
          (mul_nonneg hC.le (Nat.cast_nonneg r))
      _ = _ := by ring
  let D := (a : ℝ) ^ 2 * C * K + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, fun p r q t ↦ ?_⟩
  rw [norm_uncleTwoWallTrial_sq_eq_trace_transfer]
  calc
    _ ≤ ‖LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
        (uncleTwoWallTransfer A B R L p r q 1 t)‖ := Complex.re_le_norm _
    _ ≤ (a : ℝ) ^ 2 * (C * K * r) :=
      norm_linearMap_trace_le_entry_bound _ _ (hTotal p r q t)
    _ = ((a : ℝ) ^ 2 * C * K) * r := by ring
    _ ≤ D * r := mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) (Nat.cast_nonneg r)

end MPSTensor
