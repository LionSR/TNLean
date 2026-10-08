/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.ExactSectorEncoder
import TNLean.MPS.Preparation.SectorEncoderRates

/-!
# Uniform genuine-unitary preparation of a sector encoder from its logical seed

For fixed physical registers and a common transfer bound, the same canonical endpoint has
both a square-root exponential block approximation and an exact linear-depth whole-ring
encoding. The constants precede the partition, length, and requested accuracy. The logical
seed is only an intermediate isometry; no product-state preparation cost is assigned to it.

## References

* Malz, Styliaris, Wei, and Cirac, arXiv:2307.01696, equation (25),
  "Long-range MPS using measurements", and discussion and outlook.
-/

open Matrix MPSTensor QuantumCircuit
open scoped BigOperators ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

namespace MPSPreparation

/-- One canonical family has uniform approximate and exact coherent encodings from fixed
registers. The approximation retains all logical phases and uses no measurements. -/
theorem exists_sectorEncoder_preparation_bounds
    {d D b r₀ : ℕ} [NeZero d] {Dj : Fin b → ℕ}
    (A : (j : Fin b) → MPSTensor d (Dj j)) (ι : (j : Fin b) → Fin (Dj j) → Fin D)
    (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ i j, i ≠ j → ∀ a c, ι i a ≠ ι j c)
    (hDj : ∀ j, 0 < Dj j) (hD : 0 < D)
    (hnormal : ∀ j, Kraus.IsNormal (A j)) (hA : ∀ j, IsLeftCanonical (A j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ}
    (hσ : ∀ j, (σ j).PosDef) (htr : ∀ j, (σ j).trace = 1)
    (hfix : ∀ j, Kraus.transferMap (A j) (σ j) = σ j)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hlam : ∀ j μ, Module.End.HasEigenvalue (Kraus.transferMap (A j)) μ →
      μ ≠ 1 → ‖μ‖ ≤ ‖(t : ℂ)‖)
    (hmix : ∀ i j, i ≠ j → ∀ μ, Module.End.HasEigenvalue (Kraus.mixedMapLM (A i) (A j)) μ →
      ‖μ‖ ≤ ‖(t : ℂ)‖)
    (hr₀ : 2 ≤ r₀) {dig : Fin D → Cfg d r₀} (hdig : Function.Injective dig)
    {dig₀ : Fin b → Cfg d r₀} (hdig₀ : Function.Injective dig₀)
    (L : ℕ) (hL : 3 * r₀ ≤ L)
    (hinj : ∀ n, L ≤ n → IsInjectiveOn (blockTensor (blockSum A ι fun _ => 1) n)
      (blockPairs ι : Set (Fin D × Fin D))) :
    ∃ (C : ℕ) (K : ℝ), 1 ≤ K ∧
      (∀ (M : ℕ) [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N]
        (hN : ∑ k, ℓ k = N) (q : ℕ) (hLq : L ≤ q) (hℓ : ∀ k, q ≤ ℓ k),
        (∀ k, ℓ k ≤ 2 * q) → (N : ℝ) * Real.exp (-(-(1 / 2 * Real.log t) * q)) ≤ 1 →
        ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (T : ℕ),
          IsLocalCircuitOfDepth U T ∧ T ≤ C * q ∧
          ‖sectorEncoder A N - U * registerEncoder hN
            (fun k => by have := hℓ k; omega) dig₀‖ ≤
              K * Real.sqrt ((N : ℝ) * Real.exp (-(-(1 / 2 * Real.log t) * q)))) ∧
      (∀ (N : ℕ) [NeZero N] (hLN : L ≤ N),
        ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (T : ℕ),
          IsLocalCircuitOfDepth U T ∧ T ≤ C * N ∧
          U * registerEncoder (ℓ := fun _ : Fin 1 => N) (by simp)
            (fun _ => by omega) dig₀ = sectorEncoder A N) := by
  classical
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have ht : ‖(t : ℂ)‖ < 1 := by rwa [hnorm]
  obtain ⟨KG, hKG, hG⟩ := exists_norm_gram_sectorColumnMatrix_sub_one_le hnormal hA hσ htr
    hfix ht hlam hmix (γ := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨KZ, hKZ, hZ⟩ := exists_norm_cross_blockIsometryEncoder_sectorColumnMatrix_sub_one_le
    hι hdisj hnormal hA hσ htr hfix ht hlam hmix (γ := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨Cp, hp⟩ := exists_isLocalCircuitOfDepth_registerEncoder hr₀ hdig hdig₀ hD
  obtain ⟨Ce, he⟩ := exists_isLocalCircuitOfDepth_sectorEncoder_exact hr₀ hdig hdig₀ hD
  set K := Real.sqrt (KG + 2 * KZ * Real.exp KZ) + KG + 1
  have hK : 1 ≤ K := by dsimp [K]; have := Real.sqrt_nonneg (KG + 2 * KZ * Real.exp KZ); linarith
  set r := -(1 / 2 * Real.log t)
  have hr : 0 < r := by have := Real.log_neg ht0 ht1; dsimp [r]; linarith
  have hexp : ∀ n : ℕ, Real.exp (-(1 / 2) / correlationLength (t : ℂ)) ^ n =
      Real.exp (-(r * n)) := fun n => by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [neg_div_correlationLength, hnorm]
    dsimp [r]
    ring
  set ω : Fin b → Fin D × Fin D → ℂ := fun j => embedPair (ι j) (fixedPointPair (σ j))
  have hω : ∀ i j, ∑ p, star (ω i p) * ω j p = if i = j then 1 else 0 := by
    intro i j
    split_ifs with hij
    · subst j
      rw [inner_embedPair_self (hι i), fixedPointPair_norm_sq (hσ i).posSemidef, htr i]
    · exact inner_embedPair_eq_zero_of_disjoint (hdisj i j hij) _ _
  have hωS : ∀ j {M : ℕ} (c : Fin M → Fin D × Fin D), pairProductState (ω j) c ≠ 0 →
      ∀ k, c k ∈ blockPairs ι := fun j M c hc k =>
    mem_blockPairs_of_pairProductState_embedPair_ne_zero j _ hc k
  refine ⟨2 * Cp + Ce, K, hK, ?_, ?_⟩
  · intro M _ ℓ N _ hN q hLq hℓ hℓ₂ hsmall
    have hq0 : q ≠ 0 := by omega
    have hqN : q ≤ N := by
      calc q ≤ ℓ 0 := hℓ 0
        _ ≤ ∑ k, ℓ k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
        _ = N := hN
    have hMN : M ≤ N := by
      calc M = ∑ _ : Fin M, 1 := by simp
        _ ≤ ∑ k, ℓ k := Finset.sum_le_sum fun k _ => by have := hℓ k; omega
        _ = N := hN
    have hℓr : ∀ k, 3 * r₀ ≤ ℓ k := fun k => hL.trans (hLq.trans (hℓ k))
    have hinjℓ := fun k => hinj (ℓ k) (hLq.trans (hℓ k))
    obtain ⟨U, T, hU, hT, hUJ, hW⟩ := hp (blockSum A ι fun _ => 1) (blockPairs ι) ω hω
      hωS ℓ hN (2 * q) hℓr hℓ₂ hinjℓ
    have hV := injective_sectorColumnMatrix_of_isInjectiveOn A ι hι hdisj hDj (NeZero.ne N)
      (hinj N (hLq.trans hqN))
    have hGN := hG N
    rw [hexp] at hGN
    have hZN := hZ M ℓ hN q hq0 hℓ hinjℓ
    rw [hexp] at hZN
    have herr := norm_sectorEncoder_sub_blockIsometryEncoder_le_of_rates
      (blockSum A ι fun _ => 1) ω hN hV hW hKG hKZ.le hr.le (NeZero.pos N) hqN hMN
      hsmall hGN hZN
    refine ⟨U, T, hU, hT.trans (by nlinarith), ?_⟩
    rw [hUJ]
    refine herr.trans ?_
    gcongr
    dsimp [K]
    linarith
  · intro N _ hLN
    obtain ⟨U, T, hU, hT, heq⟩ := he A ι hι hdisj hDj N (hL.trans hLN) (hinj N hLN)
    exact ⟨U, T, hU, hT.trans (by nlinarith), heq⟩

end MPSPreparation
