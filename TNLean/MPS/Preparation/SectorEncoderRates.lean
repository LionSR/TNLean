/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OverlappingBlockStates
import TNLean.MPS.Preparation.SectorEncoder

/-!
# Phase-sensitive rates for complete sector encoders

The transfer estimates control the Gram matrix of the actual periodic sector columns and
the full complex cross matrix with their simultaneous blocked-polar approximation. The
entry sums run over the fixed logical dimension, never over the growing physical space
or an external reference.

## References

* Malz, Styliaris, Wei, and Cirac, arXiv:2307.01696, Supplemental Material,
  equations (S2)–(S7), Lemma 1'(ii), and discussion and outlook.
-/

open Matrix QuantumCircuit
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

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
      simpa [Matrix.sub_apply, Matrix.one_apply, gram_sectorColumnMatrix_apply,
        inner_self_eq_norm_sq_to_K, ← Complex.ofReal_sub] using h N
    · obtain ⟨K, hK, h⟩ := exists_norm_mpvOverlap_le_of_mixedMapLM (A j) (A i) hl
        (hmix j i hij.symm) hγ0 hγ
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
