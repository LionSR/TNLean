/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexSqrt
import TNLean.Algebra.FinKronecker
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Examples.PVBS
import TNLean.MPS.Examples.WStatePrimeLengthBound

/-!
# Isometric blocking of the W vector

A qubit is encoded into a block by sending its vacuum to the block vacuum
and its excitation to the normalized W vector. The tensor power of this
isometry sends the normalized W vector to the normalized W vector
on the flattened physical chain.

This is elementary single-excitation algebra for the blocking device in
PGVWC07, arXiv:quant-ph/0608197, lines 2090–2097, applied to the W vector
of the review arXiv:2011.12127, Appendix A, lines 2348–2362. It supplies an
vector identity, not the period or quantitative injectivity estimate
needed for the review's general bond-dimension bound.
-/

open scoped Matrix BigOperators

namespace MPSTensor

private theorem wIndicator_cons_zero {N : ℕ} (σ : Cfg 2 N) :
    wIndicator (N + 1) (Fin.cons 0 σ) = wIndicator N σ := by
  simpa only [pvbsEdge_one, one_mul] using pvbsEdge_cons_zero 1 σ

private theorem wIndicator_cons_one {N : ℕ} (σ : Cfg 2 N) :
    wIndicator (N + 1) (Fin.cons 1 σ) = pvbsVacuum N σ := by
  simpa only [pvbsEdge_one] using pvbsEdge_cons_one 1 σ

private theorem wIndicator_vacuum (N : ℕ) : wIndicator N 0 = 0 := by
  simpa only [pvbsEdge_one] using pvbsEdge_zero 1 N

private theorem sum_norm_sq_wIndicator (N : ℕ) :
    ∑ σ : Cfg 2 N, ‖wIndicator N σ‖ ^ 2 = (N : ℝ) := by
  induction N with
  | zero => simp [wIndicator]
  | succ N ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (N + 1) => Fin 2)).sum_comp
      (fun σ => ‖wIndicator (N + 1) σ‖ ^ 2)]
    rw [Fintype.sum_prod_type]
    change (∑ i : Fin 2, ∑ σ : Cfg 2 N,
      ‖wIndicator (N + 1) (Fin.cons i σ)‖ ^ 2) = _
    rw [Fin.sum_univ_two]
    simp only [wIndicator_cons_zero, wIndicator_cons_one]
    have hvac : ∑ σ : Cfg 2 N, ‖pvbsVacuum N σ‖ ^ 2 = 1 := by
      rw [Finset.sum_eq_single (0 : Cfg 2 N)]
      · simp
      · intro σ _ hσ
        simp [pvbsVacuum, hσ]
      · simp
    rw [ih, hvac]
    push_cast
    ring

/-- The unnormalized W vector has squared norm equal to its number of sites.
Source: the single-excitation sum in arXiv:2011.12127, Appendix A, line 2350. -/
theorem norm_sq_wIndicator (N : ℕ) :
    ‖(WithLp.toLp 2 (wIndicator N) : MPVSpace 2 N)‖ ^ 2 = (N : ℝ) := by
  simpa only [EuclideanSpace.norm_sq_eq] using sum_norm_sq_wIndicator N

/-- The square-root normalization of the W vector. -/
theorem norm_wIndicator (N : ℕ) :
    ‖(WithLp.toLp 2 (wIndicator N) : MPVSpace 2 N)‖ = Real.sqrt N := by
  rw [← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 (wIndicator N) : MPVSpace 2 N)),
    norm_sq_wIndicator]

/-- Dividing the W vector by the square root of a positive length gives a unit vector. -/
theorem norm_normalized_wIndicator {N : ℕ} (hN : 0 < N) :
    ‖((Real.sqrt N : ℂ)⁻¹) •
      (WithLp.toLp 2 (wIndicator N) : MPVSpace 2 N)‖ = 1 := by
  rw [norm_smul, norm_wIndicator, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hN))

private theorem vacuum_eq_count_zero {N : ℕ} (σ : Cfg 2 N) :
    pvbsVacuum N σ = if (List.ofFn σ).count 1 = 0 then 1 else 0 := by
  have h : (List.ofFn σ).count 1 = 0 ↔ σ = 0 := by
    rw [List.count_eq_zero]
    constructor
    · intro h
      funext i
      have hi : σ i ≠ 1 := fun hi => h (List.mem_ofFn.mpr ⟨i, hi⟩)
      apply Fin.ext
      have hne : (σ i).val ≠ 1 := fun hv => hi (Fin.ext hv)
      have hlt := (σ i).isLt
      change (σ i).val = 0
      omega
    · rintro rfl
      simp
  simp only [pvbsVacuum, Pi.single_apply, h]

private theorem count_flatten_cons {m k : ℕ} (I : Fin (blockPhysDim 2 k))
    (σ : Fin m → Fin (blockPhysDim 2 k)) :
    (List.ofFn (blockedConfigEquiv 2 (m + 1) k (Fin.cons I σ))).count 1 =
      (List.ofFn (decodeBlock 2 k I)).count 1 +
        (List.ofFn (blockedConfigEquiv 2 m k σ)).count 1 := by
  simp only [ofFn_blockedConfigEquiv, List.ofFn_succ, flattenBlockedWord_cons,
    List.count_append, wordOfBlock, Kraus.wordOfBlock, Fin.cons_zero, Fin.cons_succ]

private theorem vacuum_flatten_cons {m k : ℕ} (I : Fin (blockPhysDim 2 k))
    (σ : Fin m → Fin (blockPhysDim 2 k)) :
    pvbsVacuum ((m + 1) * k) (blockedConfigEquiv 2 (m + 1) k (Fin.cons I σ)) =
      pvbsVacuum k (decodeBlock 2 k I) *
        pvbsVacuum (m * k) (blockedConfigEquiv 2 m k σ) := by
  simp only [vacuum_eq_count_zero, count_flatten_cons, Nat.add_eq_zero_iff]
  split_ifs <;> simp_all

private theorem wIndicator_flatten_cons {m k : ℕ} (I : Fin (blockPhysDim 2 k))
    (σ : Fin m → Fin (blockPhysDim 2 k)) :
    wIndicator ((m + 1) * k) (blockedConfigEquiv 2 (m + 1) k (Fin.cons I σ)) =
      wIndicator k (decodeBlock 2 k I) *
        pvbsVacuum (m * k) (blockedConfigEquiv 2 m k σ) +
      pvbsVacuum k (decodeBlock 2 k I) *
        wIndicator (m * k) (blockedConfigEquiv 2 m k σ) := by
  simp only [wIndicator_apply, vacuum_eq_count_zero, count_flatten_cons]
  rcases (List.ofFn (decodeBlock 2 k I)).count 1 with _ | _ | a <;>
    rcases (List.ofFn (blockedConfigEquiv 2 m k σ)).count 1 with _ | _ | b <;> (simp; try omega)

/-- Encode one qubit into the vacuum and normalized W vector of a physical block.
The row alphabet is the existing blocked physical alphabet. -/
noncomputable def wBlockEncoding (k : ℕ) : Matrix (Fin (blockPhysDim 2 k)) (Fin 2) ℂ :=
  fun I i => if i = 0 then pvbsVacuum k (decodeBlock 2 k I)
    else (Real.sqrt k : ℂ)⁻¹ * wIndicator k (decodeBlock 2 k I)

private theorem wIndicator_mass (k : ℕ) :
    ∑ σ : Cfg 2 k, star (wIndicator k σ) * wIndicator k σ = (k : ℂ) := by
  calc
    _ = ∑ σ : Cfg 2 k, ((‖wIndicator k σ‖ ^ 2 : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro σ _
      simp only [wIndicator_apply]
      split_ifs <;> simp
    _ = (k : ℂ) := by
      rw [← Complex.ofReal_sum, sum_norm_sq_wIndicator]
      norm_cast

private theorem wBlockEncoding_zero (k : ℕ) (I : Fin (blockPhysDim 2 k)) :
    wBlockEncoding k I 0 = pvbsVacuum k (decodeBlock 2 k I) :=
  ite_eq_left rfl

private theorem wBlockEncoding_one (k : ℕ) (I : Fin (blockPhysDim 2 k)) :
    wBlockEncoding k I 1 = (Real.sqrt k : ℂ)⁻¹ * wIndicator k (decodeBlock 2 k I) :=
  ite_eq_right (by decide)

private theorem star_pvbsVacuum {k : ℕ} (σ : Cfg 2 k) :
    star (pvbsVacuum k σ) = pvbsVacuum k σ := by
  by_cases hσ : σ = 0
  · rw [hσ, pvbsVacuum_zero, star_one]
  · simp [pvbsVacuum, hσ]

private theorem pvbsVacuum_mul_wIndicator {k : ℕ} (σ : Cfg 2 k) :
    pvbsVacuum k σ * wIndicator k σ = 0 := by
  by_cases hσ : σ = 0
  · rw [hσ, wIndicator_vacuum, mul_zero]
  · simp [pvbsVacuum, hσ]

/-- The two encoding columns are orthonormal at every positive block length. -/
theorem wBlockEncoding_conjTranspose_mul_self {k : ℕ} (hk : 0 < k) :
    (wBlockEncoding k)ᴴ * wBlockEncoding k = 1 := by
  have hkℂ : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hc : star ((Real.sqrt k : ℂ)⁻¹) = (Real.sqrt k : ℂ)⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hwv (σ : Cfg 2 k) : star (wIndicator k σ) * pvbsVacuum k σ = 0 := by
    have h := congrArg star (pvbsVacuum_mul_wIndicator σ)
    rwa [star_mul, star_pvbsVacuum, star_zero] at h
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← (decodeBlockEquiv 2 k).symm.sum_comp
    (fun I => star (wBlockEncoding k I i) * wBlockEncoding k I j)]
  revert i j
  simp only [Fin.forall_fin_two, wBlockEncoding_zero, wBlockEncoding_one,
    decodeBlock_decodeBlockEquiv_symm]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [Matrix.one_apply_eq, Finset.sum_eq_single (0 : Cfg 2 k)]
    · simp
    · intro σ _ hσ
      simp [pvbsVacuum, hσ]
    · simp
  · rw [Matrix.one_apply_ne (by decide)]
    refine Finset.sum_eq_zero fun σ _ ↦ ?_
    rw [star_pvbsVacuum, mul_left_comm, pvbsVacuum_mul_wIndicator, mul_zero]
  · rw [Matrix.one_apply_ne (by decide)]
    refine Finset.sum_eq_zero fun σ _ ↦ ?_
    rw [star_mul, hc, mul_right_comm, hwv, zero_mul]
  · have hterm (σ : Cfg 2 k) :
        star ((Real.sqrt k : ℂ)⁻¹ * wIndicator k σ) *
            ((Real.sqrt k : ℂ)⁻¹ * wIndicator k σ) =
          ((Real.sqrt k : ℂ)⁻¹ * (Real.sqrt k : ℂ)⁻¹) *
            (star (wIndicator k σ) * wIndicator k σ) := by
      rw [star_mul, hc]
      ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, wIndicator_mass,
      Complex.ofReal_sqrt_inv_mul_self (k : ℝ) (Nat.cast_nonneg _), Matrix.one_apply_eq,
      Complex.ofReal_natCast]
    exact inv_mul_cancel₀ hkℂ

/-- Every tensor power of the W-block encoding is an isometry. -/
theorem rectKronecker_wBlockEncoding_isometry {k : ℕ} (hk : 0 < k) (m : ℕ) :
    (Matrix.rectKronecker fun _ : Fin m => wBlockEncoding k)ᴴ *
      Matrix.rectKronecker (fun _ : Fin m => wBlockEncoding k) = 1 :=
  Matrix.rectKronecker_conjTranspose_mul_self (wBlockEncoding_conjTranspose_mul_self hk)

private theorem product_vacuum_blocks {k : ℕ} (m : ℕ)
    (σ : Fin m → Fin (blockPhysDim 2 k)) :
    (∏ i, pvbsVacuum k (decodeBlock 2 k (σ i))) =
      pvbsVacuum (m * k) (blockedConfigEquiv 2 m k σ) := by
  induction m with
  | zero =>
    have h : blockedConfigEquiv 2 0 k σ = 0 := funext fun i ↦ absurd i.isLt (by simp)
    rw [h, pvbsVacuum_zero, Fin.prod_univ_zero]
  | succ m ih =>
    refine Fin.consCases (fun I τ ↦ ?_) σ
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, vacuum_flatten_cons]
    rw [ih]

private theorem encoding_vacuum {k : ℕ} (m : ℕ)
    (σ : Fin m → Fin (blockPhysDim 2 k)) :
    (Matrix.rectKronecker (fun _ : Fin m => wBlockEncoding k) *ᵥ pvbsVacuum m) σ =
      pvbsVacuum (m * k) (blockedConfigEquiv 2 m k σ) := by
  change (∑ x : Cfg 2 m, Matrix.rectKronecker (fun _ : Fin m => wBlockEncoding k) σ x *
    (Pi.single (0 : Cfg 2 m) (1 : ℂ) : Cfg 2 m → ℂ) x) = _
  rw [Finset.sum_eq_single (0 : Cfg 2 m)]
  · rw [Pi.single_eq_same, mul_one, Matrix.rectKronecker_apply, ← product_vacuum_blocks m σ]
    exact Finset.prod_congr rfl fun i _ ↦ wBlockEncoding_zero k (σ i)
  · intro x _ hx
    simp [hx]
  · simp

/-- Blocking identity: the tensor power of the local W isometry sends
the unnormalized W vector to the flattened W vector divided by the square root
of the block length. No blocked-vector equation is supplied as a hypothesis. -/
theorem rectKronecker_wBlockEncoding_mulVec_wIndicator (k m : ℕ) :
    Matrix.rectKronecker (fun _ : Fin m => wBlockEncoding k) *ᵥ wIndicator m =
      (Real.sqrt k : ℂ)⁻¹ •
        fun σ => wIndicator (m * k) (blockedConfigEquiv 2 m k σ) := by
  induction m with
  | zero =>
    ext σ
    have h0 : wIndicator 0 = 0 := funext fun τ ↦ by simp [wIndicator]
    have hz (τ : Cfg 2 (0 * k)) : wIndicator (0 * k) τ = 0 := by
      rw [wIndicator_apply,
        List.eq_nil_of_length_eq_zero (by simp : (List.ofFn τ).length = 0)]
      simp
    simp only [h0, Matrix.mulVec_zero, Pi.zero_apply, Pi.smul_apply, hz, smul_zero]
  | succ m ih =>
    ext σ
    refine Fin.consCases (fun I τ ↦ ?_) σ
    simp only [Matrix.mulVec, dotProduct]
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 2)).sum_comp
      (fun x => Matrix.rectKronecker (fun _ : Fin (m + 1) => wBlockEncoding k)
        (Fin.cons I τ) x * wIndicator (m + 1) x)]
    rw [Fintype.sum_prod_type]
    change (∑ i : Fin 2, ∑ x : Cfg 2 m,
      Matrix.rectKronecker (fun _ : Fin (m + 1) => wBlockEncoding k)
        (Fin.cons I τ) (Fin.cons i x) * wIndicator (m + 1) (Fin.cons i x)) = _
    rw [Fin.sum_univ_two]
    simp only [Matrix.rectKronecker_apply, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ, wIndicator_cons_zero, wIndicator_cons_one]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    change wBlockEncoding k I 0 *
        (Matrix.rectKronecker (fun _ : Fin m => wBlockEncoding k) *ᵥ wIndicator m) τ +
      wBlockEncoding k I 1 *
        (Matrix.rectKronecker (fun _ : Fin m => wBlockEncoding k) *ᵥ pvbsVacuum m) τ = _
    rw [ih, encoding_vacuum]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [wIndicator_flatten_cons, wBlockEncoding_zero, wBlockEncoding_one]
    ring

/-- Normalized W vectors are related by the tensor power of the local
encoding. This retains all (mk) physical sites under the existing flattening
equivalence. Source: the blocking device of PGVWC07, lines 2090–2097,
applied to the review's W vector, lines 2348–2362. -/
theorem rectKronecker_wBlockEncoding_mulVec_normalized (k m : ℕ) :
    Matrix.rectKronecker (fun _ : Fin m => wBlockEncoding k) *ᵥ
      ((Real.sqrt m : ℂ)⁻¹ • wIndicator m) =
      (Real.sqrt (m * k : ℕ) : ℂ)⁻¹ •
        fun σ => wIndicator (m * k) (blockedConfigEquiv 2 m k σ) := by
  rw [Matrix.mulVec_smul, rectKronecker_wBlockEncoding_mulVec_wIndicator, smul_smul]
  congr 1
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m), Complex.ofReal_mul, mul_inv]

/-- Compressing the blocked physical leg of any periodic W representation
produces a shorter W representation with the same bond dimension. No canonical
form or preservation of block injectivity is assumed. Source context: PGVWC07,
lines 2090–2097 and 2182–2225; this is the explicit W-vector blocking calculation. -/
theorem mpv_wBlockCompression_of_eq_wIndicator {D k m : ℕ} (hk : 0 < k)
    (A : MPSTensor 2 D) {c : ℂ}
    (hW : ∀ σ : Cfg 2 (m * k), mpv A σ = c * wIndicator (m * k) σ) :
    ∀ τ : Cfg 2 m,
      mpv (rotatePhysical (wBlockEncoding k)ᴴ (blockTensor A k)) τ =
        (c * (Real.sqrt k : ℂ)) * wIndicator m τ := by
  have hroot : (Real.sqrt k : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hk))
  let E := Matrix.rectKronecker fun _ : Fin m => wBlockEncoding k
  let W : (Fin m → Fin (blockPhysDim 2 k)) → ℂ :=
    fun σ => wIndicator (m * k) (blockedConfigEquiv 2 m k σ)
  have hflat : W = (Real.sqrt k : ℂ) • (E *ᵥ wIndicator m) := by
    dsimp only [E]
    rw [rectKronecker_wBlockEncoding_mulVec_wIndicator, smul_smul,
      mul_inv_cancel₀ hroot, one_smul]
  have hpull : Matrix.rectKronecker (fun _ : Fin m => (wBlockEncoding k)ᴴ) *ᵥ W =
      (Real.sqrt k : ℂ) • wIndicator m := by
    rw [hflat, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    dsimp only [E]
    rw [← Matrix.rectKronecker_conjTranspose,
      rectKronecker_wBlockEncoding_isometry hk m, Matrix.one_mulVec]
  have hblock : ∀ σ : Fin m → Fin (blockPhysDim 2 k),
      mpv (blockTensor A k) σ = c * W σ := by
    intro σ
    rw [mpv, coeff, evalWord_blockTensor, ← ofFn_blockedConfigEquiv]
    exact hW (blockedConfigEquiv 2 m k σ)
  intro τ
  rw [mpv_rotatePhysical]
  simp_rw [hblock]
  change (Matrix.rectKronecker (fun _ : Fin m => (wBlockEncoding k)ᴴ) *ᵥ (c • W)) τ = _
  rw [Matrix.mulVec_smul, hpull]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- Every prime divisor of a positive chain length obeys the existing fifth-degree
W bound for any periodic W representation. The tensor may depend on the
original length. Compression retains its bond dimension and derives the shorter
W equation; no primitive-block hypothesis is added. This includes lengths such
as twice a large prime, beyond the earlier no-small-divisor regime. -/
theorem prime_divisor_lt_of_mpv_eq_smul_wIndicator {D N : ℕ}
    (A : MPSTensor 2 D) (hN : 0 < N) {c : ℂ} (hc : c ≠ 0)
    (hW : ∀ σ : Cfg 2 N, mpv A σ = c * wIndicator N σ)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) :
    p < 2 * max ((D ^ 2 + 1) ^ 2) (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1)) := by
  obtain ⟨k, rfl⟩ := hpN
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
  have hroot : (Real.sqrt k : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hk))
  exact lt_of_mpv_eq_smul_wIndicator_of_prime
    (rotatePhysical (wBlockEncoding k)ᴴ (blockTensor A k)) hp (mul_ne_zero hc hroot)
    (mpv_wBlockCompression_of_eq_wIndicator hk A hW)

end MPSTensor
