/-
# Prototype: Kernel invariance for eigenvector_det_ne_zero

Goal: From ∑ A_i * X * (B_i)ᴴ = μ • X and ∑ (A_i)ᴴ * A_i = 1,
show: if X *ᵥ v = 0 then ∀ k, X *ᵥ ((B k)ᴴ *ᵥ v) = 0.

## Results proved in this file:
* `eigvec_applied_to_ker` — easy direction
* `trace_preserved` — |μ|=1 preserves HS norm
* `block_psd_zero_corner` — [[0,Z],[Z†,Q]] ≥ 0 → Z = 0
* `mult_domain_of_ks_equality` — KS equality → multiplicative domain

## Key sorry items (need ~150-200 lines of infrastructure):
* `block_ks_gap_psd` — 2×2 block KS gap is PSD (~80 lines, uses 2-positivity)
* `ks_gap_zero_of_peripheral_eigenvector` — |μ|=1 → ksGap=0 (~100-150 lines)
* `ker_invariant` — connecting multiplicative domain to kernel invariance (~50 lines)
-/
import TNLean.Channel.KadisonSchwarz
import TNLean.Spectral.MixedTransfer
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Matrix ComplexOrder BigOperators
open Matrix Finset

namespace KerInvariance

variable {d D : ℕ}

/-! ## Preliminary lemmas -/

lemma mul_mulVec (A B : Matrix (Fin D) (Fin D) ℂ) (v : Fin D → ℂ) :
    (A * B) *ᵥ v = A *ᵥ (B *ᵥ v) := by
  rw [Matrix.mulVec_mulVec]

lemma sum_mulVec' {ι : Type*} (s : Finset ι) (M : ι → Matrix (Fin D) (Fin D) ℂ)
    (v : Fin D → ℂ) :
    (∑ i ∈ s, M i) *ᵥ v = ∑ i ∈ s, (M i) *ᵥ v := by
  rw [Matrix.sum_mulVec]

/-! ## Part A: Eigenvector equation applied to kernel vector (PROVED) -/

/-- From F_{AB}(X) = μX and Xv = 0:
  ∑ A_i *ᵥ (X *ᵥ ((B_i)ᴴ *ᵥ v)) = 0

This is the easy direction — we can decompose the product, but
can't conclude each summand is 0 without additional structure. -/
lemma eigvec_applied_to_ker
    (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hFX : MPSTensor.mixedTransferMap A B X = μ • X)
    (v : Fin D → ℂ) (hv : X *ᵥ v = 0) :
    ∑ i : Fin d, A i *ᵥ (X *ᵥ ((B i)ᴴ *ᵥ v)) = 0 := by
  have hFX' : ∑ i : Fin d, A i * X * (B i)ᴴ = μ • X := by
    rw [← MPSTensor.mixedTransferMap_apply]; exact hFX
  have h1 : (∑ i : Fin d, A i * X * (B i)ᴴ) *ᵥ v = 0 := by
    rw [hFX', Matrix.smul_mulVec, hv, smul_zero]
  rw [sum_mulVec'] at h1
  convert h1 using 1
  congr 1; ext i
  rw [mul_mulVec, mul_mulVec]

/-! ## Part B: HS norm preservation (PROVED) -/

/-- The HS norm is preserved under F_{AB} when |μ| = 1:
  tr(F(X)ᴴ F(X)) = tr(Xᴴ X). -/
lemma trace_preserved [NeZero D]
    (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hFX : MPSTensor.mixedTransferMap A B X = μ • X)
    (hμ : ‖μ‖ = 1) :
    ((MPSTensor.mixedTransferMap A B X)ᴴ *
     (MPSTensor.mixedTransferMap A B X)).trace = (Xᴴ * X).trace := by
  rw [hFX, conjTranspose_smul, Matrix.smul_mul, mul_smul_comm, smul_smul]
  have : star μ * μ = 1 := by
    have h := Complex.normSq_eq_conj_mul_self (z := μ)
    rw [show (starRingEnd ℂ) μ = star μ from rfl] at h
    rw [← h, Complex.normSq_eq_norm_sq, hμ]; simp
  rw [this, one_smul]

/-! ## Part C: Block PSD zero corner (PROVED) -/

/-- If [[0, Z], [Z†, Q]] is PSD with Q PSD, then Z = 0.

Proof: For any x, the block vector u=(x,0) satisfies ⟨u,Mu⟩=0.
By the PSD characterization, Mu=0, giving Z†x=0. -/
lemma block_psd_zero_corner
    (Z Q : Matrix (Fin D) (Fin D) ℂ)
    (h : (Matrix.fromBlocks (0 : Matrix (Fin D) (Fin D) ℂ) Z Zᴴ Q).PosSemidef) :
    Z = 0 := by
  -- Strategy: show Z†x = 0 for all x, hence Z† = 0, hence Z = 0.
  suffices hZtv : ∀ x : Fin D → ℂ, Zᴴ *ᵥ x = 0 by
    have hZt : Zᴴ = 0 := by
      ext i j; simp only [zero_apply]
      have h1 := congr_fun (hZtv (fun k => if k = j then 1 else 0)) i
      simp [mulVec, dotProduct] at h1
      rw [conjTranspose_apply]; rw [h1]; exact star_zero _
    rw [← conjTranspose_conjTranspose Z, hZt, conjTranspose_zero]
  intro x
  -- Form block vector u = (x, 0).
  let u : Fin D ⊕ Fin D → ℂ := Sum.elim x 0
  -- Step 1: ⟨u, Mu⟩ = 0
  have h_quad : star u ⬝ᵥ (fromBlocks (0 : Matrix (Fin D) (Fin D) ℂ) Z Zᴴ Q).mulVec u = 0 := by
    rw [fromBlocks_mulVec]
    simp only [u, Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_zero, add_zero]
    rw [dotProduct, Fintype.sum_sum_type]
    simp [Sum.elim_inl, Sum.elim_inr, star_zero,
          mul_zero, Finset.sum_const_zero]
  -- Step 2: M u = 0 by PSD + ⟨u,Mu⟩ = 0
  have h_Mu := h.dotProduct_mulVec_zero_iff u |>.mp h_quad
  -- Step 3: Extract inr component = Z† x from M u = 0
  have h_inr : ∀ i : Fin D,
      ((fromBlocks (0 : Matrix (Fin D) (Fin D) ℂ) Z Zᴴ Q).mulVec u) (Sum.inr i) = 0 :=
    fun i => by rw [h_Mu]; rfl
  -- Step 4: Simplify inr component
  simp only [fromBlocks_mulVec, u, Sum.elim_comp_inl, Sum.elim_comp_inr,
             mulVec_zero, add_zero, Sum.elim_inr] at h_inr
  exact funext h_inr

/-! ## Part D: Definitions and KS gap -/

/-- The KS gap: Δ(Y) = E*(Y†Y) - E*(Y)†E*(Y). -/
noncomputable def ksGap (A : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (Y : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  krausAdjointMap A (Yᴴ * Y) - (krausAdjointMap A Y)ᴴ * krausAdjointMap A Y

/-- The KS gap is PSD. -/
lemma ksGap_psd (A : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hA : IsTPKraus A) (Y : Matrix (Fin D) (Fin D) ℂ) :
    (ksGap A Y).PosSemidef :=
  kadison_schwarz_adjoint A hA Y

/-! ## Part E: The 2×2 block KS gap is PSD (SORRY — ~80 lines) -/

/-- The 2×2 block KS gap is PSD. This is the block-matrix extension of KS.

For any X, Y and TP Kraus operators A:
  [[E*(X†X)-E*(X)†E*(X), E*(X†Y)-E*(X)†E*(Y)],
   [E*(Y†X)-E*(Y)†E*(X), E*(Y†Y)-E*(Y)†E*(Y)]] ≥ 0

Proof sketch: Apply the CP map E* blockwise to the Gram matrix
[[X†X, X†Y], [Y†X, Y†Y]] = [X†,Y†]ᵀ·[X,Y] ≥ 0, and subtract the
output's Gram matrix. Uses 2-positivity of CP maps.
Estimated: ~80 lines (mirrors the proof of kadison_schwarz). -/
lemma block_ks_gap_psd (A : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hA : IsTPKraus A)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    (Matrix.fromBlocks
      (krausAdjointMap A (Xᴴ * X) - (krausAdjointMap A X)ᴴ * krausAdjointMap A X)
      (krausAdjointMap A (Xᴴ * Y) - (krausAdjointMap A X)ᴴ * krausAdjointMap A Y)
      (krausAdjointMap A (Yᴴ * X) - (krausAdjointMap A Y)ᴴ * krausAdjointMap A X)
      (krausAdjointMap A (Yᴴ * Y) - (krausAdjointMap A Y)ᴴ * krausAdjointMap A Y)
    ).PosSemidef := by
  sorry

/-! ## Part F: Multiplicative domain from KS equality (PROVED modulo block_ks_gap_psd) -/

/-- **Multiplicative domain** (Wolf 2012, Theorem 5.7).
If the KS gap is zero for X, then E*(X†Y) = E*(X)†E*(Y) for all Y.

Proof: The 2×2 block KS gap has (1,1)=0 (by hypothesis) and is PSD.
By block_psd_zero_corner, the (1,2) block is also 0, giving the result. -/
theorem mult_domain_of_ks_equality
    (A : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hA : IsTPKraus A)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hKS : ksGap A X = 0)
    (Y : Matrix (Fin D) (Fin D) ℂ) :
    krausAdjointMap A (Xᴴ * Y) = (krausAdjointMap A X)ᴴ * krausAdjointMap A Y := by
  -- The block KS gap is PSD
  have h_block := block_ks_gap_psd A hA X Y
  -- Replace (1,1) block with 0 using hKS
  have h11 : krausAdjointMap A (Xᴴ * X) - (krausAdjointMap A X)ᴴ * krausAdjointMap A X = 0 := hKS
  rw [h11] at h_block
  -- Set Z = (1,2) block, Q = (2,2) block
  set Z_block := krausAdjointMap A (Xᴴ * Y) - (krausAdjointMap A X)ᴴ * krausAdjointMap A Y
  set Q_block := krausAdjointMap A (Yᴴ * Y) - (krausAdjointMap A Y)ᴴ * krausAdjointMap A Y
  -- Verify (2,1) = Z†: uses E*(Z)ᴴ = E*(Zᴴ)
  have h21 : krausAdjointMap A (Yᴴ * X) - (krausAdjointMap A Y)ᴴ * krausAdjointMap A X
      = Z_blockᴴ := by
    simp only [Z_block, conjTranspose_sub, Matrix.conjTranspose_mul,
               conjTranspose_conjTranspose]
    congr 1
    -- E*(X†Y)† = E*((X†Y)†) = E*(Y†X)
    simp only [krausAdjointMap, conjTranspose_sum, Matrix.conjTranspose_mul,
               conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [h21] at h_block
  -- Apply block_psd_zero_corner: [[0, Z], [Z†, Q]] ≥ 0 → Z = 0
  have hZ := block_psd_zero_corner Z_block Q_block h_block
  -- Z = 0 means E*(X†Y) = E*(X)†E*(Y)
  exact sub_eq_zero.mp hZ

/-! ## Part G: KS gap = 0 from peripheral eigenvector (KEY SORRY — ~100-150 lines) -/

/-- **KS gap vanishes for peripheral eigenvectors**.

From F_{AB}(X) = μX with |μ| = 1:
1. Pass to DS gauge A'_i = S⁻¹A_iS where S·S† = ρ (QPF fixed point)
2. In DS gauge: E' is doubly stochastic (unital + TP)
3. HS contraction: tr(E'*(Y)†E'*(Y)) ≤ tr(Y†Y)
4. |μ| = 1 forces equality: tr(E'*(X)†E'*(X)) = tr(X†X)
5. Since ksGap ≥ 0 (PSD) and tr(ksGap) = 0, we get ksGap = 0

Key sub-requirements:
- DS gauge is also TP (needs E*_A(ρ⁻¹) = ρ⁻¹, ~50 lines)
- Eigenvector equation transforms correctly in DS gauge (~30 lines)
- The trace argument (steps 3-5, ~40 lines)

Total: ~100-150 lines of new infrastructure. -/
lemma ks_gap_zero_of_peripheral_eigenvector [NeZero D]
    (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hA_tp : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_tp : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hFX : MPSTensor.mixedTransferMap A B X = μ • X)
    (hμ : ‖μ‖ = 1) :
    ksGap A X = 0 := by
  sorry

/-! ## Part H: Kernel invariance (KEY SORRY — ~50 lines) -/

/-- **Kernel invariance**: the main goal.

From the multiplicative domain property + eigenvector equation,
show ker(X) is B†-invariant.

The argument needs to connect E*_A (adjoint channel for A) with
the mixed transfer F_{AB}. This requires showing that in the
appropriate gauge, the multiplicative property translates to:
  A_i X = E*(X) A_i for each i
which then combines with F_{AB}(X) = μX to give kernel invariance.

Estimated: ~50 lines connecting the abstract properties to the
concrete kernel claim. -/
theorem ker_invariant [NeZero D]
    (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hA_tp : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_tp : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hFX : MPSTensor.mixedTransferMap A B X = μ • X)
    (hμ : ‖μ‖ = 1) :
    ∀ k : Fin d, ∀ v : Fin D → ℂ, X *ᵥ v = 0 → X *ᵥ ((B k)ᴴ *ᵥ v) = 0 := by
  sorry

/-! ## Summary

### Fully proved (no sorry):
1. `eigvec_applied_to_ker` — ∑ A_i *ᵥ (X *ᵥ ((B_i)ᴴ *ᵥ v)) = 0
2. `trace_preserved` — tr(F(X)†F(X)) = tr(X†X) when |μ| = 1
3. `block_psd_zero_corner` — [[0,Z],[Z†,Q]] PSD → Z = 0
4. `mult_domain_of_ks_equality` — ksGap = 0 → E*(X†Y) = E*(X)†E*(Y)
   (modulo `block_ks_gap_psd` which is sorry)

### Sorry items needing infrastructure:
5. `block_ks_gap_psd` (~80 lines) — 2×2 block KS gap is PSD
   Uses 2-positivity (same technique as existing KS proof).
6. `ks_gap_zero_of_peripheral_eigenvector` (~100-150 lines) — HARDEST
   Requires DS gauge TP property + trace/norm argument.
7. `ker_invariant` (~50 lines) — connecting mult domain to kernel invariance.

### Total: ~230-280 lines more needed to close Sorry 1.
-/

end KerInvariance
