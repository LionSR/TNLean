/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.SectorEncoderCompilation
import TNLean.MPS.Preparation.SectorEncoderPreparation
import TNLean.MPS.Preparation.SectorSpectralGap
import TNLean.MPS.Preparation.BlockSumUnitary
import TNLean.Spectral.MixedEigenvalueGap

/-!
# Coherent conversion of complete canonical sector encodings

Two explicitly matched normal sector families have one genuine nearest-neighbor conversion
circuit preserving every logical superposition and every finite external reference. The
canonical polar endpoint matrices depend only on the families and ring length. A single
partition and logical register encoding is shared by both approximate compilers; when its
accuracy scale exceeds the ring, the exact fixed-width whole-encoder construction applies.

## References

* Malz, Styliaris, Wei, and Cirac, arXiv:2307.01696, equation (25), the paragraph
  "Long-range MPS using measurements", and discussion and outlook. This whole-encoding
  result makes a precise enhancement and does not introduce a phase-equivalence predicate.
-/

open Matrix MPSTensor QuantumCircuit
open scoped BigOperators ComplexOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator

namespace MPSPreparation

/-- Matched canonical normal sector families admit all-accuracy coherent conversion in
logarithmic depth. The endpoint encoders are fixed independently of the accuracy, and the
same chosen physical unitary works for every logical input and finite reference system. -/
theorem exists_log_depth_coherent_sectorEncoder_conversion
    {d b : ℕ} (hd : 2 ≤ d) (hb : 0 < b) {DA DB : Fin b → ℕ}
    (A : (j : Fin b) → MPSTensor d (DA j)) (B : (j : Fin b) → MPSTensor d (DB j))
    (hAN : ∀ j, Kraus.IsNormal (A j)) (hBN : ∀ j, Kraus.IsNormal (B j))
    (hAL : ∀ j, IsLeftCanonical (A j)) (hBL : ∀ j, IsLeftCanonical (B j))
    {σA : (j : Fin b) → Matrix (Fin (DA j)) (Fin (DA j)) ℂ}
    {σB : (j : Fin b) → Matrix (Fin (DB j)) (Fin (DB j)) ℂ}
    (hσA : ∀ j, (σA j).PosDef) (hσB : ∀ j, (σB j).PosDef)
    (htrA : ∀ j, (σA j).trace = 1) (htrB : ∀ j, (σB j).trace = 1)
    (hfixA : ∀ j, Kraus.transferMap (A j) (σA j) = σA j)
    (hfixB : ∀ j, Kraus.transferMap (B j) (σB j) = σB j)
    (hmixA : ∀ i j, i ≠ j → Kraus.mixedMapSpectralRadius (A i) (A j) < 1)
    (hmixB : ∀ i j, i ≠ j → Kraus.mixedMapSpectralRadius (B i) (B j) < 1) :
    ∃ (N₀ : ℕ) (c : ℝ), 2 ≤ N₀ ∧ 0 < c ∧ ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      (sectorEncoder A N).IsIsometry ∧ (sectorEncoder B N).IsIsometry ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (T : ℕ),
          IsLocalCircuitOfDepth U T ∧ (T : ℝ) ≤ c * Real.log (N / ε) ∧
          ‖U * sectorEncoder A N - sectorEncoder B N‖ ≤ ε ∧
          ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (ξ : EuclideanSpace ℂ (Fin b × κ)),
            ‖WithLp.toLp 2 (((U ⊗ₖ (1 : Matrix κ κ ℂ)) *
                (sectorEncoder A N ⊗ₖ (1 : Matrix κ κ ℂ))) *ᵥ ξ) -
              WithLp.toLp 2 ((sectorEncoder B N ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ ξ)‖ ≤ ε * ‖ξ‖ := by
  classical
  have : NeZero d := ⟨by omega⟩
  have : NeZero b := ⟨hb.ne'⟩
  have hDA : ∀ j, NeZero (DA j) := fun j => Matrix.neZero_of_trace_eq_one (htrA j)
  have hDB : ∀ j, NeZero (DB j) := fun j => Matrix.neZero_of_trace_eq_one (htrB j)
  have hDApos : ∀ j, 0 < DA j := fun j => Nat.pos_of_ne_zero (hDA j).out
  have hDBpos : ∀ j, 0 < DB j := fun j => Nat.pos_of_ne_zero (hDB j).out
  obtain ⟨tA, htA0, htA1, hlamA, hmixleA⟩ := exists_forall_eigenvalue_norm_le_of_mixed hAN hAL
    hDA (fun i j hij μ hμ => mixedMap_eigenvalue_norm_lt_one_of_spectralRadius_lt_one
      (A i) (A j) (hmixA i j hij) hμ)
  obtain ⟨tB, htB0, htB1, hlamB, hmixleB⟩ := exists_forall_eigenvalue_norm_le_of_mixed hBN hBL
    hDB (fun i j hij μ hμ => mixedMap_eigenvalue_norm_lt_one_of_spectralRadius_lt_one
      (B i) (B j) (hmixB i j hij) hμ)
  set t := max tA tB
  have ht0 : 0 < t := lt_max_of_lt_left htA0
  have ht1 : t < 1 := max_lt htA1 htB1
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have htA : ‖(tA : ℂ)‖ ≤ ‖(t : ℂ)‖ := by
    rw [hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htA0]; exact le_max_left _ _
  have htB : ‖(tB : ℂ)‖ ≤ ‖(t : ℂ)‖ := by
    rw [hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htB0]; exact le_max_right _ _
  have hAlam := fun j μ hμ hne => (hlamA j μ hμ hne).trans htA
  have hBlam := fun j μ hμ hne => (hlamB j μ hμ hne).trans htB
  have hAμ := fun i j hij μ hμ => (hmixleA i j hij μ hμ).trans htA
  have hBμ := fun i j hij μ hμ => (hmixleB i j hij μ hμ).trans htB
  let ιA := flatCoord DA
  let ιB := flatCoord DB
  have hιA : ∀ j, Function.Injective (ιA j) := fun j => flatCoord_injective j
  have hιB : ∀ j, Function.Injective (ιB j) := fun j => flatCoord_injective j
  have hdisjA : ∀ i j, i ≠ j → ∀ a c, ιA i a ≠ ιA j c := fun i j h => flatCoord_ne h
  have hdisjB : ∀ i j, i ≠ j → ∀ a c, ιB i a ≠ ιB j c := fun i j h => flatCoord_ne h
  have hDAs : 0 < ∑ j, DA j := Finset.sum_pos (fun j _ => hDApos j)
    ⟨0, Finset.mem_univ _⟩
  have hDBs : 0 < ∑ j, DB j := Finset.sum_pos (fun j _ => hDBpos j)
    ⟨0, Finset.mem_univ _⟩
  obtain ⟨LA, hinjA⟩ := exists_isInjectiveOn_blockTensor_blockSum hιA hdisjA hAN hAL hσA htrA
    hfixA (lam₂ := (t : ℂ)) (by rwa [hnorm]) hAlam hAμ
  obtain ⟨LB, hinjB⟩ := exists_isInjectiveOn_blockTensor_blockSum hιB hdisjB hBN hBL hσB htrB
    hfixB (lam₂ := (t : ℂ)) (by rwa [hnorm]) hBlam hBμ
  set r₀ := (∑ j, DA j) + (∑ j, DB j) + b + 2
  have hr₀ : 2 ≤ r₀ := by omega
  have hpow : r₀ < d ^ r₀ := Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_left hd r₀)
  obtain ⟨digA⟩ : Nonempty (Fin (∑ j, DA j) ↪ Cfg d r₀) :=
    Function.Embedding.nonempty_of_card_le (by simp; omega)
  obtain ⟨digB⟩ : Nonempty (Fin (∑ j, DB j) ↪ Cfg d r₀) :=
    Function.Embedding.nonempty_of_card_le (by simp; omega)
  obtain ⟨dig₀⟩ : Nonempty (Fin b ↪ Cfg d r₀) :=
    Function.Embedding.nonempty_of_card_le (by simp; omega)
  set L := max LA LB + 3 * r₀ + 2
  have hL : 3 * r₀ ≤ L := by omega
  have hL2 : 2 ≤ L := by omega
  have hLA : LA ≤ L := by have := le_max_left LA LB; omega
  have hLB : LB ≤ L := by have := le_max_right LA LB; omega
  obtain ⟨CA, KA, hKA, hAp, hAe⟩ := exists_sectorEncoder_preparation_bounds A ιA hιA hdisjA
    hDApos hDAs hAN hAL hσA htrA hfixA ht0 ht1 hAlam hAμ
    hr₀ digA.injective dig₀.injective L hL (fun n hn => hinjA n (hLA.trans hn))
  obtain ⟨CB, KB, hKB, hBp, hBe⟩ := exists_sectorEncoder_preparation_bounds B ιB hιB hdisjB
    hDBpos hDBs hBN hBL hσB htrB hfixB ht0 ht1 hBlam hBμ
    hr₀ digB.injective dig₀.injective L hL (fun n hn => hinjB n (hLB.trans hn))
  set r := -(1 / 2 * Real.log t)
  have hr : 0 < r := by have := Real.log_neg ht0 ht1; dsimp [r]; linarith
  have happ : ∀ (N : ℕ) [NeZero N], L ≤ N → ∀ q : ℕ, L ≤ q → q ≤ N →
      (N : ℝ) * Real.exp (-(r * q)) ≤ 1 →
      ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (T : ℕ),
        IsLocalCircuitOfDepth U T ∧ T ≤ (CA + CB) * q ∧
        ‖U * sectorEncoder A N - sectorEncoder B N‖ ≤
          (KA + KB) * Real.sqrt ((N : ℝ) * Real.exp (-(r * q))) := by
    intro N _ _ q hLq hqN hsmall
    have hq0 : 0 < q := by omega
    obtain ⟨m, hm⟩ : ∃ m, N / q = m + 1 :=
      ⟨N / q - 1, (Nat.succ_pred_eq_of_pos (Nat.div_pos hqN hq0)).symm⟩
    let ℓ : Fin (m + 1) → ℕ := fun k => if k = Fin.last m then q + N % q else q
    have hsum : ∑ k, ℓ k = N := by
      rw [Fin.sum_univ_castSucc]
      simp only [ℓ, Fin.castSucc_ne_last, ite_false, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, ite_true]
      have := Nat.div_add_mod N q
      rw [hm] at this
      linarith
    have hℓ : ∀ k, q ≤ ℓ k := fun k => by simp only [ℓ]; split_ifs <;> omega
    have hℓ₂ : ∀ k, ℓ k ≤ 2 * q := fun k => by
      have := Nat.mod_lt N hq0
      simp only [ℓ]; split_ifs <;> omega
    obtain ⟨UA, TA, hUA, hTA, heA⟩ := hAp (m + 1) ℓ hsum q hLq hℓ hℓ₂ hsmall
    obtain ⟨UB, TB, hUB, hTB, heB⟩ := hBp (m + 1) ℓ hsum q hLq hℓ hℓ₂ hsmall
    let J := registerEncoder hsum (fun k => by have := hℓ k; omega) dig₀
    obtain ⟨hU, herr⟩ := hUA.norm_encoder_conversion_le hUB (sectorEncoder A N)
      (sectorEncoder B N) J
    refine ⟨UB * UAᴴ, TA + TB, hU, by nlinarith, ?_⟩
    exact (herr.trans (add_le_add heA heB)).trans_eq (by ring)
  have hexact : ∀ (N : ℕ) [NeZero N], L ≤ N →
      ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (T : ℕ),
        IsLocalCircuitOfDepth U T ∧ T ≤ (CA + CB) * N ∧
        U * sectorEncoder A N = sectorEncoder B N := by
    intro N _ hLN
    obtain ⟨UA, TA, hUA, hTA, heA⟩ := hAe N hLN
    obtain ⟨UB, TB, hUB, hTB, heB⟩ := hBe N hLN
    refine ⟨UB * UAᴴ, TA + TB, hUA.star.mul hUB, by nlinarith, ?_⟩
    let J : Matrix (Cfg d N) (Fin b) ℂ := registerEncoder
      (ℓ := fun _ : Fin 1 => N) (by simp) (fun _ => by omega) dig₀
    -- Normalize the `CStarMatrix` multiplication carried by the encoder hypotheses.
    have heA' : (UA * J : Matrix (Cfg d N) (Fin b) ℂ) = sectorEncoder A N := heA
    have heB' : (UB * J : Matrix (Cfg d N) (Fin b) ℂ) = sectorEncoder B N := heB
    have hunit : (UAᴴ * UA : Matrix (Cfg d N) (Cfg d N) ℂ) = 1 :=
      Unitary.star_mul_self_of_mem hUA.mem_unitary
    change (UB * UAᴴ : Matrix (Cfg d N) (Cfg d N) ℂ) * sectorEncoder A N =
      sectorEncoder B N
    rw [← heA', ← Matrix.mul_assoc, Matrix.mul_assoc UB UAᴴ UA, hunit, Matrix.mul_one]
    exact heB'
  obtain ⟨c, hc, hconv⟩ := exists_log_depth_sectorEncoder_conversion_of_block_approximation
    A B L L (CA + CB) hL2 (KA + KB) r (by linarith) hr happ hexact
  refine ⟨L, c, hL2, hc, fun N _ hLN => ⟨?_, ?_, fun ε hε hε1 => ?_⟩⟩
  · exact isIsometry_sectorEncoder A N
      (injective_sectorColumnMatrix_of_isInjectiveOn A ιA hιA hdisjA
        hDApos (NeZero.ne N) (hinjA N (hLA.trans hLN)))
  · exact isIsometry_sectorEncoder B N
      (injective_sectorColumnMatrix_of_isInjectiveOn B ιB hιB hdisjB
        hDBpos (NeZero.ne N) (hinjB N (hLB.trans hLN)))
  · obtain ⟨U, T, hU, hT, herr⟩ := hconv ε hε hε1 N hLN
    exact ⟨U, T, hU, hT, herr, fun κ _ _ ξ =>
      Matrix.norm_encoder_conversion_reference_le U (sectorEncoder A N) (sectorEncoder B N) herr ξ⟩

end MPSPreparation
