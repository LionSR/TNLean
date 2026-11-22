/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.BlockSum.OverlappingBlockStates
import TNLean.MPS.Preparation.SectorEncoder.SectorEncoder
import TNLean.MPS.Preparation.SectorEncoder.ExactSectorEncoder

/-!
# Phase-sensitive rates for complete sector encoders

The transfer estimates control the Gram matrix of the actual periodic sector columns and
the full complex cross matrix with their simultaneous blocked-polar approximation. The
entry sums run over the fixed logical dimension, never over the growing physical space
or an external reference.

## References

* Malz, Styliaris, Wei, and Cirac, arXiv:2307.01696, Supplemental Material,
  equations (S2)–(S7), Lemma 1'(ii), and discussion and outlook.

## Uniform genuine-unitary preparation of a sector encoder from its logical seed

For fixed physical registers and a common transfer bound, the same canonical endpoint has
both a square-root exponential block approximation and an exact linear-depth whole-ring
encoding. The constants precede the partition, length, and requested accuracy. The logical
seed is only an intermediate isometry; no product-state preparation cost is assigned to it.

### References

* Malz, Styliaris, Wei, and Cirac, arXiv:2307.01696, equation (25),
  "Long-range MPS using measurements", and discussion and outlook.
-/

section

open Matrix QuantumCircuit
open scoped BigOperators ComplexOrder InnerProductSpace Matrix.Norms.L2Operator
open Kraus (blockTensor)

namespace MPSTensor

variable {d b : ℕ} {Dj : Fin b → ℕ} {A : (j : Fin b) → MPSTensor d (Dj j)}
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ}

/-- The Gram matrix of the actual sector columns tends to the logical identity, with a
constant independent of the physical ring length. -/
theorem exists_norm_gram_sectorColumnMatrix_sub_one_le
    (hnormal : ∀ j, Kraus.IsNormal (A j)) (hA : ∀ j, IsLeftCanonical (A j))
    (hσ : ∀ j, (σ j).PosDef) (htr : ∀ j, (σ j).trace = 1)
    (hfix : ∀ j, Kraus.transferMap (A j) (σ j) = σ j) {lam₂ : ℂ} (hl : ‖lam₂‖ < 1)
    (hlam : ∀ j μ, Module.End.HasEigenvalue (Kraus.transferMap (A j)) μ →
      μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    (hmix : ∀ j k, j ≠ k → ∀ μ, Module.End.HasEigenvalue (Kraus.mixedMapLM (A j) (A k)) μ →
      ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ,
      ‖(sectorColumnMatrix A N)ᴴ * sectorColumnMatrix A N - 1‖ ≤
        K * Real.exp (-γ / correlationLength lam₂) ^ N := by
  classical
  have hD : ∀ j, NeZero (Dj j) := fun j => Matrix.neZero_of_trace_eq_one (htr j)
  have hent : ∀ i j : Fin b, ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ,
      ‖((sectorColumnMatrix A N)ᴴ * sectorColumnMatrix A N - 1 : Matrix (Fin b) (Fin b) ℂ) i j‖ ≤
        K * Real.exp (-γ / correlationLength lam₂) ^ N := by
    intro i j
    by_cases hij : i = j
    · subst j
      obtain ⟨K, hK, h⟩ := exists_abs_norm_mpvState_sq_sub_one_le (A i) (hnormal i) (hA i)
        (hσ i) (htr i) (hfix i) (hlam i) hγ0 hγ
      refine ⟨K, hK, fun N => ?_⟩
      rw [Matrix.sub_apply, Matrix.one_apply_eq, gram_sectorColumnMatrix_apply,
        inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, ← RCLike.ofReal_one,
        ← RCLike.ofReal_sub, RCLike.norm_ofReal]
      exact h N
    · obtain ⟨K, hK, h⟩ := exists_norm_mpvOverlap_le_of_mixedMapLM (A j) (A i) hl
        (hmix j i (Ne.symm hij)) hγ0 hγ
      refine ⟨K, hK, fun N => ?_⟩
      simpa [Matrix.sub_apply, Matrix.one_apply, hij, gram_sectorColumnMatrix_apply,
        mpvOverlap, PiLp.inner_apply, RCLike.inner_apply, mpvState_apply, mul_comm] using h N
  choose K hK h using hent
  refine ⟨∑ i, ∑ j, K i j * ‖(Matrix.single i j 1 : Matrix (Fin b) (Fin b) ℂ)‖,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hK i j) (norm_nonneg _)), fun N => ?_⟩
  refine (Matrix.l2_opNorm_le_sum_norm_entry _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  calc ‖((sectorColumnMatrix A N)ᴴ * sectorColumnMatrix A N - 1 : Matrix (Fin b) (Fin b) ℂ) i j‖ *
      ‖(Matrix.single i j 1 : Matrix (Fin b) (Fin b) ℂ)‖
      ≤ (K i j * Real.exp (-γ / correlationLength lam₂) ^ N) *
          ‖(Matrix.single i j 1 : Matrix (Fin b) (Fin b) ℂ)‖ := by
        exact mul_le_mul_of_nonneg_right (h i j N) (norm_nonneg _)
    _ = _ := by ring

/-- The full complex cross matrix tends to the identity for one common partition.
In particular the estimate retains the relative phases between logical sectors. -/
theorem exists_norm_cross_blockIsometryEncoder_sectorColumnMatrix_sub_one_le
    {D : ℕ} {ι : (j : Fin b) → Fin (Dj j) → Fin D}
    (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j k, j ≠ k → ∀ a c, ι j a ≠ ι k c)
    (hnormal : ∀ j, Kraus.IsNormal (A j)) (hA : ∀ j, IsLeftCanonical (A j))
    (hσ : ∀ j, (σ j).PosDef) (htr : ∀ j, (σ j).trace = 1)
    (hfix : ∀ j, Kraus.transferMap (A j) (σ j) = σ j) {lam₂ : ℂ} (hl : ‖lam₂‖ < 1)
    (hlam : ∀ j μ, Module.End.HasEigenvalue (Kraus.transferMap (A j)) μ →
      μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    (hmix : ∀ j k, j ≠ k → ∀ μ, Module.End.HasEigenvalue (Kraus.mixedMapLM (A j) (A k)) μ →
      ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (M : ℕ) [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ}
      (hN : ∑ k, ℓ k = N) (q : ℕ), q ≠ 0 → (∀ k, q ≤ ℓ k) →
      (∀ k, IsInjectiveOn (blockTensor (blockSum A ι fun _ => 1) (ℓ k))
        (blockPairs ι : Set (Fin D × Fin D))) →
      ‖(blockIsometryEncoder (blockSum A ι fun _ => 1)
          (fun j => embedPair (ι j) (fixedPointPair (σ j))) hN)ᴴ * sectorColumnMatrix A N - 1‖ ≤
        K * (M * Real.exp (-γ / correlationLength lam₂) ^ q) *
          Real.exp (K * (M * Real.exp (-γ / correlationLength lam₂) ^ q)) := by
  classical
  choose C hC h using fun i j => exists_norm_trace_prod_blockPosTensor_sub_le hι hdisj
    hnormal hA hσ htr hfix hl hlam hmix hγ0 hγ i j
  let w := fun i j => ‖(Matrix.single i j 1 : Matrix (Fin b) (Fin b) ℂ)‖
  have hw : ∀ i j, 0 ≤ w i j := fun i j => norm_nonneg _
  have hsum : 0 ≤ ∑ i, ∑ j, C i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => (hC i j).le
  have hsumw : 0 ≤ ∑ i, ∑ j, C i j * w i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hC i j).le (hw i j)
  set K := 1 + (∑ i, ∑ j, C i j) + ∑ i, ∑ j, C i j * w i j
  have hK : 0 < K := by dsimp [K]; linarith
  have hCK : ∀ i j, C i j ≤ K := by
    intro i j
    have h1 : C i j ≤ ∑ j, C i j :=
      Finset.single_le_sum (fun j _ => (hC i j).le) (Finset.mem_univ j)
    have h2 : (∑ j, C i j) ≤ ∑ i, ∑ j, C i j :=
      Finset.single_le_sum (f := fun i : Fin b => ∑ j, C i j)
        (fun i _ => Finset.sum_nonneg fun j _ => (hC i j).le) (Finset.mem_univ i)
    dsimp [K]
    linarith
  refine ⟨K, hK, fun M _ ℓ N hN q hq hℓ hinj => ?_⟩
  set y := (M : ℝ) * Real.exp (-γ / correlationLength lam₂) ^ q
  have hy : 0 ≤ y := by positivity
  have hent : ∀ i j,
      ‖((blockIsometryEncoder (blockSum A ι fun _ => 1)
          (fun j => embedPair (ι j) (fixedPointPair (σ j))) hN)ᴴ *
            sectorColumnMatrix A N - 1 : Matrix (Fin b) (Fin b) ℂ) i j‖ ≤
        C i j * y * Real.exp (K * y) := by
    intro i j
    rw [Matrix.sub_apply, Matrix.one_apply,
      cross_blockIsometryEncoder_sectorColumnMatrix_apply,
      inner_blockIsometryState_embedPair_mpvState hι hdisj (fun j => (hσ j).posSemidef)
        i j hN (fun k => by have := hℓ k; omega) hinj]
    exact (h i j M ℓ q hq hℓ).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hCK i j) hy))
      (mul_nonneg (hC i j).le hy))
  refine (Matrix.l2_opNorm_le_sum_norm_entry _).trans ?_
  calc (∑ i, ∑ j, ‖((blockIsometryEncoder (blockSum A ι fun _ => 1)
          (fun j => embedPair (ι j) (fixedPointPair (σ j))) hN)ᴴ *
            sectorColumnMatrix A N - 1 : Matrix (Fin b) (Fin b) ℂ) i j‖ * w i j)
      ≤ ∑ i, ∑ j, (C i j * y * Real.exp (K * y)) * w i j := by
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hent i j) (hw i j)
    _ = (∑ i, ∑ j, C i j * w i j) * y * Real.exp (K * y) := by
      simp only [Finset.sum_mul]
      congr 1
      ext i
      congr 1
      ext j
      ring
    _ ≤ K * y * Real.exp (K * y) := by
      gcongr
      dsimp [K]
      linarith

/-- Gram and complex cross rates give a square-root exponential estimate for the fixed
polar endpoint. The only entry sums used to obtain these hypotheses have logical size. -/
theorem norm_sectorEncoder_sub_blockIsometryEncoder_le_of_rates
    {D M N q : ℕ} (B : MPSTensor d D) (ω : Fin b → Fin D × Fin D → ℂ)
    {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N)
    (hV : Function.Injective (sectorColumnMatrix A N).mulVec)
    (hW : (blockIsometryEncoder B ω hN).IsIsometry)
    {KG KZ r : ℝ} (hKG : 0 ≤ KG) (hKZ : 0 ≤ KZ) (hr : 0 ≤ r)
    (hN1 : 1 ≤ N) (hqN : q ≤ N) (hMN : M ≤ N)
    (hsmall : (N : ℝ) * Real.exp (-(r * q)) ≤ 1)
    (hG : ‖(sectorColumnMatrix A N)ᴴ * sectorColumnMatrix A N - 1‖ ≤
      KG * Real.exp (-(r * N)))
    (hZ : ‖(blockIsometryEncoder B ω hN)ᴴ * sectorColumnMatrix A N - 1‖ ≤
      KZ * (M * Real.exp (-(r * q))) * Real.exp (KZ * (M * Real.exp (-(r * q))))) :
    ‖sectorEncoder A N - blockIsometryEncoder B ω hN‖ ≤
      (Real.sqrt (KG + 2 * KZ * Real.exp KZ) + KG) *
        Real.sqrt ((N : ℝ) * Real.exp (-(r * q))) := by
  set y := (N : ℝ) * Real.exp (-(r * q))
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 := hsmall
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hη : ‖(sectorColumnMatrix A N)ᴴ * sectorColumnMatrix A N - 1‖ ≤ KG * y := by
    refine hG.trans ?_
    calc KG * Real.exp (-(r * N)) ≤ KG * Real.exp (-(r * q)) := by gcongr
         _ ≤ KG * y := mul_le_mul_of_nonneg_left
           (le_mul_of_one_le_left (Real.exp_pos _).le hN1') hKG
  have hMy : (M : ℝ) * Real.exp (-(r * q)) ≤ y := by dsimp [y]; gcongr
  have hζ : ‖(blockIsometryEncoder B ω hN)ᴴ * sectorColumnMatrix A N - 1‖ ≤
      KZ * y * Real.exp KZ := by
    refine hZ.trans ?_
    gcongr
    nlinarith [hMy.trans hy1]
  have hpolar := Matrix.norm_polarIso_sub_isometry_le (sectorColumnMatrix A N) hV hW
  have hframe : ‖sectorEncoder A N - blockIsometryEncoder B ω hN‖ ≤
      Real.sqrt (KG * y + 2 * (KZ * y * Real.exp KZ)) + KG * y := by
    refine hpolar.trans ?_
    gcongr
  have hysqrt : y ≤ Real.sqrt y := by
    have := Real.sq_sqrt hy0
    have := Real.sqrt_nonneg y
    nlinarith
  calc ‖sectorEncoder A N - blockIsometryEncoder B ω hN‖
      ≤ Real.sqrt (KG * y + 2 * (KZ * y * Real.exp KZ)) + KG * y := hframe
    _ = Real.sqrt (KG + 2 * KZ * Real.exp KZ) * Real.sqrt y + KG * y := by
      rw [show KG * y + 2 * (KZ * y * Real.exp KZ) =
        (KG + 2 * KZ * Real.exp KZ) * y by ring, Real.sqrt_mul (by positivity)]
    _ ≤ (Real.sqrt (KG + 2 * KZ * Real.exp KZ) + KG) * Real.sqrt y := by
      nlinarith [mul_le_mul_of_nonneg_left hysqrt hKG]

end MPSTensor

end

section

open Matrix MPSTensor QuantumCircuit
open scoped BigOperators ComplexOrder InnerProductSpace Matrix.Norms.L2Operator
open Kraus (blockTensor)

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
          IsUnitaryCircuit (Geometry.ring N) T U ∧ T ≤ C * q ∧
          ‖sectorEncoder A N - U * registerEncoder hN
            (fun k => by have := hℓ k; omega) dig₀‖ ≤
              K * Real.sqrt ((N : ℝ) * Real.exp (-(-(1 / 2 * Real.log t) * q)))) ∧
      (∀ (N : ℕ) [NeZero N] (hLN : L ≤ N),
        ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (T : ℕ),
          IsUnitaryCircuit (Geometry.ring N) T U ∧ T ≤ C * N ∧
          U * registerEncoder (ℓ := fun _ : Fin 1 => N) (by simp)
            (fun _ => by omega) dig₀ = sectorEncoder A N) := by
  classical
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have ht : ‖(t : ℂ)‖ < 1 := by rwa [hnorm]
  obtain ⟨KG, hKG, hG⟩ := exists_norm_gram_sectorColumnMatrix_sub_one_le hnormal hA hσ htr
    hfix ht hlam hmix (γ := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨KZ, hKZ, hZ⟩ := exists_norm_cross_blockIsometryEncoder_sectorColumnMatrix_sub_one_le
    hι hdisj hnormal hA hσ htr hfix ht hlam hmix (γ := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨Cp, hp⟩ := exists_isUnitaryCircuit_registerEncoder hr₀ hdig hdig₀ hD
  obtain ⟨Ce, he⟩ := exists_isUnitaryCircuit_sectorEncoder_exact hr₀ hdig hdig₀ hD
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

end
