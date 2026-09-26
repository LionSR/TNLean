/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.CanonicalForm
import TNLean.MPS.FundamentalTheorem.UnitaryGauge
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.Symmetry.MPDO.Vectorized
import TNLean.MPS.Overlap.NormalTensorDichotomy

/-!
# Virtual unitary rigidity of canonical matrix product unitaries

Two full-support canonical-form-II representatives with identical periodic
operators at every length above one have equal bond dimensions and are related
letterwise by a unitary virtual similarity. This is the virtual-gauge part of
the local standard-form relation of arXiv:1703.09188, lines 624–652; it does
not establish the two physical rank-leg relations in that statement.

The proof first recovers length-one equality from the normal-tensor overlap
dichotomy. The phase thereby obtained is one because the normalized finite
chains of lengths two and three are nonzero and equal. Full support reduces
canonical form II to one ambient-dimensional block, whose weight has unit
modulus. Its left-canonical normalization then makes the virtual gauge
unitary.

**Scope restriction (supplied full-support canonical form II):** The two public
conclusions concern representatives with a supplied full-support presentation,
not arbitrary ambient MPU tensors. The restriction and the separate
representative-reduction obligation are recorded in
`docs/paper-gaps/mpu_canonical_form_full_support.tex`.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

/-- Equality of periodic operators beyond one site gives equality of the
normalized word traces at those lengths. -/
private theorem normalizedFlattening_mpv_eq_of_mpo_eq_gt_one
    {d D₁ D₂ : ℕ} {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    (hEq : ∀ N : ℕ, 1 < N → mpo U N = mpo V N) :
    ∀ N : ℕ, 1 < N → ∀ σ : Fin N → Fin (d * d),
      MPSTensor.mpv U.normalizedFlattening σ =
        MPSTensor.mpv V.normalizedFlattening σ := by
  intro N hN σ
  change MPSTensor.mpv (fun ij => ((Real.sqrt d : ℂ)⁻¹) • U.toMPSTensor ij) σ =
    MPSTensor.mpv (fun ij => ((Real.sqrt d : ℂ)⁻¹) • V.toMPSTensor ij) σ
  rw [MPSTensor.mpv_smul, MPSTensor.mpv_smul]
  congr 1
  rw [MPOTensor.mpv_toMPSTensor, MPOTensor.mpv_toMPSTensor, hEq N hN]

/-- The overlap dichotomy upgrades equality beyond one site to a unit-phase
relation at every positive length. -/
private theorem normalizedFlattening_exists_phase_of_mpo_eq_gt_one
    {d D₁ D₂ : ℕ} {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    (hEq : ∀ N : ℕ, 1 < N → mpo U N = mpo V N) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ N : ℕ, 0 < N → ∀ σ : Fin N → Fin (d * d),
      MPSTensor.mpv U.normalizedFlattening σ =
        a ^ N * MPSTensor.mpv V.normalizedFlattening σ := by
  let : NeZero d := hU.neZero_phys
  let : NeZero D₁ := hU.neZero_bond
  let : NeZero D₂ := hV.neZero_bond
  have hProp : MPSTensor.EventuallyNonzeroProportionalMPV₂
      U.normalizedFlattening V.normalizedFlattening := by
    filter_upwards [Filter.eventually_gt_atTop 1] with N hN
    exact ⟨1, one_ne_zero, fun σ => by
      simpa using normalizedFlattening_mpv_eq_of_mpo_eq_gt_one hEq N hN σ⟩
  exact hProp.exists_unit_phase_power_of_isNormalTensor
    hU.isNormalTensor_normalizedFlattening hV.isNormalTensor_normalizedFlattening

/-- A normalized MPU has a nonzero coefficient at every length above one. -/
private theorem normalizedFlattening_exists_mpv_ne_zero
    {d D : ℕ} {U : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) {N : ℕ} (hN : 1 < N) :
    ∃ σ : Fin N → Fin (d * d), MPSTensor.mpv U.normalizedFlattening σ ≠ 0 := by
  let : NeZero d := hU.neZero_phys
  let : NeZero D := hU.neZero_bond
  by_contra hzero
  push Not at hzero
  have hOverlap : MPSTensor.mpvOverlap U.normalizedFlattening U.normalizedFlattening N = 1 := by
    rw [← MPSTensor.trace_transferMatrix_transferMap_pow_eq_mpvOverlap]
    exact hU.isMPU.trace_transferMatrix_normalizedFlattening_pow_eq_one hN
  simp only [MPSTensor.mpvOverlap, hzero, star_zero, mul_zero, Finset.sum_const_zero] at hOverlap
  exact zero_ne_one hOverlap

/-- Equality beyond one site extends to every positive length for full-support
canonical MPU tensors. -/
private theorem normalizedFlattening_sameMPV₂Pos_of_mpo_eq_gt_one
    {d D₁ D₂ : ℕ} {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    (hEq : ∀ N : ℕ, 1 < N → mpo U N = mpo V N) :
    MPSTensor.SameMPV₂Pos U.normalizedFlattening V.normalizedFlattening := by
  obtain ⟨a, ha, hphase⟩ := normalizedFlattening_exists_phase_of_mpo_eq_gt_one hU hV hEq
  have hpow : ∀ N : ℕ, 1 < N → a ^ N = 1 := by
    intro N hN
    obtain ⟨σ, hσ⟩ := normalizedFlattening_exists_mpv_ne_zero hU hN
    have hEqσ := normalizedFlattening_mpv_eq_of_mpo_eq_gt_one hEq N hN σ
    have hVσ : MPSTensor.mpv V.normalizedFlattening σ ≠ 0 := by
      rw [← hEqσ]
      exact hσ
    have hrel := hphase N (by omega) σ
    rw [hEqσ] at hrel
    apply mul_right_cancel₀ hVσ
    simpa using hrel.symm
  have ha1 : a = 1 := by
    have htwo := hpow 2 (by omega)
    have hthree := hpow 3 (by omega)
    simpa [pow_succ, htwo] using hthree
  intro N hN σ
  simpa [ha1] using hphase N hN σ

/-- Positive-length equality gives a literal invertible virtual gauge after
identifying the two bond dimensions. -/
private theorem normalizedFlattening_exists_gauge_of_mpo_eq_gt_one
    {d D₁ D₂ : ℕ} {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    (hEq : ∀ N : ℕ, 1 < N → mpo U N = mpo V N) :
    ∃ hdim : D₁ = D₂,
      MPSTensor.GaugeEquiv
        (cast (congrArg (MPSTensor (d * d)) hdim) U.normalizedFlattening)
        V.normalizedFlattening := by
  let : NeZero d := hU.neZero_phys
  let : NeZero D₁ := hU.neZero_bond
  let : NeZero D₂ := hV.neZero_bond
  have hSame := normalizedFlattening_sameMPV₂Pos_of_mpo_eq_gt_one hU hV hEq
  have hPhase : MPSTensor.MPVBlockPhaseEquiv U.normalizedFlattening V.normalizedFlattening :=
    ⟨1, one_ne_zero, fun N hN σ => by simpa using (hSame N hN σ).symm⟩
  obtain ⟨hdim, X, ζ, hζ, hrel⟩ :=
    hPhase.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor
      hU.isNormalTensor_normalizedFlattening hV.isNormalTensor_normalizedFlattening
  have hζpow : ∀ N : ℕ, 1 < N → ζ ^ N = 1 := by
    intro N hN
    obtain ⟨σ, hVσ⟩ := normalizedFlattening_exists_mpv_ne_zero hV hN
    have hConj := MPSTensor.mpv_eq_pow_mul_of_gaugePhase
      (A := cast (congrArg (MPSTensor (d * d)) hdim) U.normalizedFlattening)
      (B := V.normalizedFlattening) X ζ hrel N σ
    rw [MPSTensor.mpv_cast_dim hdim U.normalizedFlattening N σ,
      hSame N (by omega) σ] at hConj
    apply mul_right_cancel₀ hVσ
    simpa using hConj.symm
  have hζone : ζ = 1 := by
    have htwo := hζpow 2 (by omega)
    have hthree := hζpow 3 (by omega)
    simpa [pow_succ, htwo] using hthree
  refine ⟨hdim, X, fun i => ?_⟩
  simpa [hζone] using hrel i

/-- A fully supported isometric inclusion transports left-canonical
normalization from a block to the ambient tensor. -/
private theorem leftCanonical_of_unitary_block_intertwining
    {p m D : ℕ} (A : MPSTensor p D) (B : MPSTensor p m)
    (W : Matrix (Fin D) (Fin m) ℂ)
    (hWstarW : Wᴴ * W = 1) (hWWstar : W * Wᴴ = 1)
    (hInter : ∀ i, A i * W = W * B i)
    (hB : MPSTensor.IsLeftCanonical B) : MPSTensor.IsLeftCanonical A := by
  have hA : ∀ i, A i = W * B i * Wᴴ := by
    intro i
    have h := congrArg (· * Wᴴ) (hInter i)
    simpa only [Matrix.mul_assoc, hWWstar, Matrix.mul_one] using h
  change ∑ i, (A i)ᴴ * A i = 1
  simp_rw [hA]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc, hWstarW, Matrix.one_mul]
  calc
    ∑ i, W * (B i)ᴴ * B i * Wᴴ =
        W * (∑ i, (B i)ᴴ * B i) * Wᴴ := by
          rw [Matrix.mul_sum, Matrix.sum_mul]
          simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hB]; simpa using hWWstar

/-- In a full-support canonical-form-II presentation of an MPU, the sole
block's weight has unit modulus, so the ambient normalized flattening is
left-canonical. Source: CPSV17, lines 269–281 and 344–356. -/
theorem IsMPUCanonicalFormII.isLeftCanonical_normalizedFlattening
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U) :
    MPSTensor.IsLeftCanonical U.normalizedFlattening := by
  let : NeZero d := hU.neZero_phys
  let : NeZero D := hU.neZero_bond
  let data := hU.cfii.toCPSVCanonicalFormData
  have htrace : ∀ N : ℕ, 1 < N →
      Matrix.trace (transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ N) = 1 :=
    fun _ hN => hU.isMPU.trace_transferMatrix_normalizedFlattening_pow_eq_one hN
  have hr : data.r = 1 := data.r_eq_one_of_shifted_transfer_trace htrace
  let k : Fin data.r := ⟨0, by omega⟩
  have hweight : data.weights k * starRingEnd ℂ (data.weights k) = 1 :=
    data.transferEigenvalue_eq_one htrace k
  have hnorm : ‖data.weights k‖ = 1 := by
    have hnormsq : ‖data.weights k‖ ^ 2 = 1 := by
      have hC : ((‖data.weights k‖ ^ 2 : ℝ) : ℂ) = 1 := by
        simpa [Complex.mul_conj, Complex.normSq_eq_norm_sq] using hweight
      exact Complex.ofReal_injective (by simpa using hC)
    nlinarith [norm_nonneg (data.weights k)]
  let W := data.ambientBlockInclusion k
  have hWstarW : Wᴴ * W = 1 := data.ambientBlockInclusion_conjTranspose_mul_self k
  have hWWstar : W * Wᴴ = 1 :=
    data.ambientBlockInclusion_mul_conjTranspose_eq_one hr hU.hasFullSupport k
  have hB : MPSTensor.IsLeftCanonical (fun i => data.weights k • data.blocks k i) :=
    MPSTensor.leftCanonical_smul_of_norm_one _ hnorm _ (hU.cfii.blocks_left_canonical k)
  exact leftCanonical_of_unitary_block_intertwining U.normalizedFlattening
    (fun i => data.weights k • data.blocks k i) W hWstarW hWWstar
    (data.mul_ambientBlockInclusion k) hB

private theorem normalizedFlattening_cast_dim
    {d D₁ D₂ : ℕ} (hdim : D₁ = D₂) (U : MPOTensor d D₁) :
    cast (congrArg (MPSTensor (d * d)) hdim) U.normalizedFlattening =
      (cast (congrArg (MPOTensor d) hdim) U).normalizedFlattening := by
  cases hdim
  rfl

/-- Two full-support canonical-form-II tensors generating equal periodic
unitaries have equal bond dimensions and differ by a unitary similarity on
the virtual bond. This is the virtual part of CPSV17, lines 624–652; the
relations between the two open standard-form factors are separate. -/
theorem IsMPUCanonicalFormII.exists_unitary_virtual_gauge_of_mpo_eq
    {d D₁ D₂ : ℕ} {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    (hEq : ∀ N : ℕ, 1 < N → mpo U N = mpo V N) :
    ∃ hdim : D₁ = D₂, ∃ z : Matrix.unitaryGroup (Fin D₂) ℂ,
      ∀ i j : Fin d,
        V i j = (z : Matrix (Fin D₂) (Fin D₂) ℂ) *
          (cast (congrArg (MPOTensor d) hdim) U) i j *
          (z : Matrix (Fin D₂) (Fin D₂) ℂ)ᴴ := by
  let : NeZero d := hU.neZero_phys
  let : NeZero D₁ := hU.neZero_bond
  let : NeZero D₂ := hV.neZero_bond
  obtain ⟨hdim, X, hGauge⟩ :=
    normalizedFlattening_exists_gauge_of_mpo_eq_gt_one hU hV hEq
  have hLeftU : MPSTensor.IsLeftCanonical
      (cast (congrArg (MPSTensor (d * d)) hdim) U.normalizedFlattening) :=
    (MPSTensor.leftCanonical_cast_dim hdim U.normalizedFlattening).2
      hU.isLeftCanonical_normalizedFlattening
  have hLeftV : MPSTensor.IsLeftCanonical V.normalizedFlattening :=
    hV.isLeftCanonical_normalizedFlattening
  have hIrrU : Kraus.IsIrreducibleFamily
      (cast (congrArg (MPSTensor (d * d)) hdim) U.normalizedFlattening) :=
    (MPSTensor.isIrreducibleTensor_cast_dim hdim U.normalizedFlattening).2
      hU.isNormalTensor_normalizedFlattening.no_invariant_proj
  have hIrrV : Kraus.IsIrreducibleFamily V.normalizedFlattening :=
    hV.isNormalTensor_normalizedFlattening.no_invariant_proj
  obtain ⟨z, _, hRel⟩ :=
    MPSTensor.exists_unitaryConj_of_gaugePhase_data_of_leftCanonical_irreducible
      X 1 one_ne_zero (by simpa using hGauge) hLeftU hLeftV hIrrU hIrrV
  refine ⟨hdim, z, ?_⟩
  intro i j
  have h := hRel (finProdFinEquiv (i, j))
  rw [normalizedFlattening_cast_dim hdim U] at h
  simp only [normalizedFlattening, toMPSTensor,
    MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat,
    one_smul] at h
  simp only [Matrix.mul_smul, Matrix.smul_mul] at h
  have hc : ((Real.sqrt d : ℂ)⁻¹) ≠ 0 := by
    apply inv_ne_zero
    exact Complex.ofReal_ne_zero.mpr
      ((Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))).ne')
  apply Matrix.ext
  intro a b
  have he := congrArg (fun M : Matrix (Fin D₂) (Fin D₂) ℂ => M a b) h
  simp only [Matrix.smul_apply, smul_eq_mul] at he
  exact (mul_left_cancel₀ hc) he

end MPOTensor
