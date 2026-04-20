/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Determinant.HeisenbergDual
import TNLean.Algebra.SkolemNoether
import TNLean.Channel.KrausRepresentation

/-!
# Unitary characterization of determinant saturation

This file completes the CPTP half of Wolf Theorem 6.1(2): a channel on
$M_d(\mathbb{C})$ has determinant of modulus `1` if and only if it is unitary
conjugation.

The proof combines the Heisenberg-dual multiplicativity result with the
Skolem--Noether theorem: multiplicativity makes the Heisenberg dual an inner
automorphism, and star-preservation shows that the implementing invertible matrix
can be normalized to a unitary.

## Main statements

* `channelDet_unitary_eq_one` — every unitary channel has determinant `1`.
* `channelDet_norm_eq_one_of_unitaryChannel` — every unitary channel saturates
  the determinant bound.
* `channelDet_norm_eq_one_iff_exists_unitaryChannel` — Wolf Theorem 6.1(2) for
  CPTP maps.
* `channelDet_norm_eq_one_iff_exists_unitaryChannel_of_channel` — the channel
  alias of the same characterization.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §6.1.1][Wolf2012QChannels]

## Tags

quantum channel, determinant, unitary channel, Skolem-Noether
-/
open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker Matrix.Norms.Frobenius
open Matrix

variable {d : ℕ}

open TNLean.Channel.Determinant.Internal

section WolfStatements

variable {T : MatrixEnd d}

/-- Extract a unitary from the Skolem–Noether inner form plus star-preservation.

Given `T(A) = P⁻¹AP` where `P ∈ GL_d(ℂ)`, and `T` preserves `*` (i.e. `Tᴴ = T†`),
`P†P` commutes with all matrices and is therefore scalar. Since `P†P` is PSD
and invertible, the scalar is positive real; defining `V = (√c)⁻¹ • P` makes
`V` unitary, and setting `U := Vᴴ` yields `T = unitaryChannel U`. -/
private theorem extract_unitary_from_inner_form [NeZero d]
    {T : MatrixEnd d} (_hT : IsChannel T)
    (P : GL (Fin d) ℂ)
    (hT_inner : ∀ A : MatrixAlg d,
        T A = (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) * A * (↑P : MatrixAlg d))
    (hP_star_comm : ∀ Y : MatrixAlg d,
        (↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d) * Y =
          Y * ((↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d))) :
    ∃ U : Matrix.unitaryGroup (Fin d) ℂ, T = unitaryChannel U := by
  -- GL identities
  have hPinvP : (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) * (↑P : MatrixAlg d) = 1 := by
    exact congrArg Units.val (inv_mul_cancel P)
  have hPPinv : (↑P : MatrixAlg d) * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) = 1 := by
    exact congrArg Units.val (mul_inv_cancel P)
  -- Step 1: P†P is in the center → is a scalar matrix
  have hPHP_center :
      (↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d) ∈
        Set.range (Matrix.scalar (Fin d) : ℂ →+* MatrixAlg d) := by
    rw [← Matrix.center_eq_range, Semigroup.mem_center_iff]
    exact fun Y => (hP_star_comm Y).symm
  obtain ⟨c, hc_eq⟩ := hPHP_center
  rw [Matrix.scalar_apply] at hc_eq
  have hPHP_smul :
      (↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d) = c • (1 : MatrixAlg d) := by
    rw [← hc_eq, ← Matrix.smul_one_eq_diagonal]
  -- Step 2: c ≥ 0 (from PSD)
  have hPHP_psd : ((↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d)).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self _
  have hc_nonneg : 0 ≤ c := by
    have := hPHP_psd.diag_nonneg (i := (0 : Fin d))
    simpa only [ge_iff_le, hPHP_smul, smul_apply, one_apply_eq, smul_eq_mul,
      mul_one] using this
  -- Step 3: c ≠ 0 (from invertibility of P)
  have hc_ne : c ≠ 0 := by
    intro hc0
    have h0 : (↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d) = 0 := by
      rw [hPHP_smul, hc0, zero_smul]
    have hPH_zero : (↑P : MatrixAlg d)ᴴ = 0 := by
      have := congr_arg (· * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)) h0
      simp only [zero_mul, Matrix.mul_assoc] at this
      rwa [hPPinv, mul_one] at this
    have hP_zero : (↑P : MatrixAlg d) = 0 := by
      rw [← conjTranspose_conjTranspose (↑P : MatrixAlg d),
        hPH_zero, conjTranspose_zero]
    exact one_ne_zero (show (1 : MatrixAlg d) = 0 by
      rw [← hPPinv, hP_zero, zero_mul])
  -- Step 4: c is a positive real number
  have hc_re_nonneg : 0 ≤ c.re := (Complex.nonneg_iff.mp hc_nonneg).1
  have hc_im_zero : c.im = 0 := (Complex.nonneg_iff.mp hc_nonneg).2.symm
  have hc_re_pos : 0 < c.re := by
    rcases lt_or_eq_of_le hc_re_nonneg with h | h
    · exact h
    · exact absurd (Complex.ext h.symm (by simp only [hc_im_zero, Complex.zero_im])) hc_ne
  -- Step 5: Define V = (√c)⁻¹ • P and prove V†V = 1
  set r := Real.sqrt c.re with hr_def
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hc_re_pos
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_pos.ne'
  have hr_sq : (↑r : ℂ) * (↑r : ℂ) = c := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc_re_nonneg]
    exact Complex.ext (Complex.ofReal_re _) (by simp only [Complex.ofReal_im, hc_im_zero])
  set V : MatrixAlg d := (↑r : ℂ)⁻¹ • (↑P : MatrixAlg d) with hV_def
  have hstar_r_inv : star ((↑r : ℂ)⁻¹) = (↑r : ℂ)⁻¹ := by
    rw [star_inv₀, show star (↑r : ℂ) = ↑r from RCLike.conj_ofReal r]
  have hVHV : Vᴴ * V = 1 := by
    simp only [hV_def, conjTranspose_smul, smul_mul_assoc, mul_smul_comm, hPHP_smul,
      hstar_r_inv, smul_smul]
    rw [show (↑r : ℂ)⁻¹ * ((↑r : ℂ)⁻¹ * c) = 1 from by
      field_simp; rw [sq]; exact hr_sq.symm]
    exact one_smul _ _
  -- Step 6: U = V† is unitary
  have hU_mem : Vᴴ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have : star Vᴴ = V := by
      rw [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
    rw [this]
    exact hVHV
  set U : Matrix.unitaryGroup (Fin d) ℂ := ⟨Vᴴ, hU_mem⟩
  -- Step 7: T = unitaryChannel U
  -- Key: Pm = ↑r • V and Pinvm = (↑r)⁻¹ • V†
  have hPm_eq : (↑P : MatrixAlg d) = (↑r : ℂ) • V := by
    simp only [hV_def, smul_smul, mul_inv_cancel₀ hr_ne, one_smul]
  have hPinvm_eq :
      (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) = (↑r : ℂ)⁻¹ • Vᴴ := by
    have hVPinv : V * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) =
        (↑r : ℂ)⁻¹ • (1 : MatrixAlg d) := by
      have h : (↑r : ℂ) • (V * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)) = 1 := by
        rw [← smul_mul_assoc, ← hPm_eq]; exact hPPinv
      rw [show V * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) =
          (↑r : ℂ)⁻¹ • (1 : MatrixAlg d) from by
        have := congr_arg ((↑r : ℂ)⁻¹ • ·) h
        simp only [smul_smul, inv_mul_cancel₀ hr_ne, one_smul] at this
        exact this]
    calc (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)
        = 1 * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) := (one_mul _).symm
      _ = (Vᴴ * V) * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) := by rw [hVHV]
      _ = Vᴴ * (V * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)) := by
          rw [Matrix.mul_assoc]
      _ = Vᴴ * ((↑r : ℂ)⁻¹ • (1 : MatrixAlg d)) := by rw [hVPinv]
      _ = (↑r : ℂ)⁻¹ • Vᴴ := by rw [mul_smul_comm, mul_one]
  refine ⟨U, LinearMap.ext fun A => ?_⟩
  simp only [unitaryChannel, LinearMap.coe_mk, AddHom.coe_mk]
  change T A = Vᴴ * A * (Vᴴ)ᴴ
  rw [conjTranspose_conjTranspose, hT_inner A, hPinvm_eq, hPm_eq,
    smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
    inv_mul_cancel₀ hr_ne, one_smul]

/-- **Wolf Thm 6.1(2), forward direction.** -/
private theorem forward_det_one_implies_unitaryChannel [NeZero d]
    (hT : IsChannel T) (hdet : ‖channelDet T‖ = 1) :
    ∃ U : Matrix.unitaryGroup (Fin d) ℂ, T = unitaryChannel U := by
  classical
  have hall := ChannelDeterminant.channel_all_eigenvalues_norm_one (d := d) hT hdet
  obtain ⟨r, K, hK⟩ := hT.cp
  have hK_tp : ∑ i : Fin r, (K i)ᴴ * K i = 1 :=
    kraus_sum_conjTranspose_mul_of_tp K T hK hT.tp
  -- Build the Heisenberg dual
  let Td : MatrixEnd d :=
    { toFun := fun X => ∑ i : Fin r, (K i)ᴴ * X * K i
      map_add' := fun X Y => by simp only [mul_add, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c X => by
        simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, RingHom.id_apply,
          Finset.smul_sum] }
  have hTd_def : ∀ X, Td X = ∑ i : Fin r, (K i)ᴴ * X * K i := fun _ => rfl
  have hTd_one : Td 1 = 1 := by
    change ∑ i : Fin r, (K i)ᴴ * 1 * K i = 1
    simp only [mul_one, hK_tp]
  have hTd_star : ∀ X : MatrixAlg d, Td Xᴴ = (Td X)ᴴ := by
    intro X
    change ∑ i, (K i)ᴴ * Xᴴ * K i = (∑ i, (K i)ᴴ * X * K i)ᴴ
    simp only [Matrix.mul_assoc, conjTranspose_sum, conjTranspose_mul,
      conjTranspose_conjTranspose]
  -- Td is multiplicative
  have hMul :=
    ChannelDeterminant.heisenberg_dual_multiplicative hT hdet hall K hK hK_tp Td hTd_def
  have hTd_ne : Td ≠ 0 := by
    intro h
    have := congr_fun (congr_arg DFunLike.coe h) 1
    simp only [hTd_one, LinearMap.zero_apply, one_ne_zero] at this
  -- Td is bijective (nonzero multiplicative map on simple algebra)
  have hTd_bij := MPSTensor.linear_mul_endomorphism_bijective Td hMul hTd_ne
  -- Skolem–Noether: Td(X) = PXP⁻¹
  let Td_alg := MPSTensor.linearMapToAlgHom Td hMul hTd_bij.2
  let Td_equiv : MatrixAlg d ≃ₐ[ℂ] MatrixAlg d := AlgEquiv.ofBijective Td_alg hTd_bij
  obtain ⟨P, hP⟩ := MPSTensor.skolemNoether_matrix Td_equiv
  -- Key identities for P
  have hPinvP : (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) * (↑P : MatrixAlg d) = 1 := by
    have : (P⁻¹ * P : GL (Fin d) ℂ) = 1 := inv_mul_cancel _
    exact congrArg Units.val this
  have hPPinv : (↑P : MatrixAlg d) * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) = 1 := by
    have : (P * P⁻¹ : GL (Fin d) ℂ) = 1 := mul_inv_cancel _
    exact congrArg Units.val this
  -- Trace adjointness: tr(T(A)*B) = tr(A*Td(B))
  have hAdj : ∀ A B : MatrixAlg d, trace (T A * B) = trace (A * Td B) := by
    intro A B
    simp only [hK, hTd_def]
    rw [Finset.sum_mul, trace_sum]
    conv_rhs => rw [Matrix.mul_sum, trace_sum]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [coe_units_inv, Matrix.mul_assoc] using
      (Matrix.trace_mul_cycle A ((K i)ᴴ * B) (K i)).symm
  -- Derive T(A) = P⁻¹AP from trace adjointness
  have hT_inner : ∀ A : MatrixAlg d,
      T A = (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) * A * (↑P : MatrixAlg d) := by
    intro A
    suffices h : ∀ B, trace ((T A -
        (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) * A * (↑P : MatrixAlg d)) * B) = 0 by
      exact sub_eq_zero.mp ((Matrix.trace_mul_right_eq_zero_iff _).mp h)
    intro B
    rw [sub_mul, trace_sub, hAdj A B]
    change trace (A * Td B) -
      trace ((↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) * A *
        (↑P : MatrixAlg d) * B) = 0
    rw [show Td B = Td_equiv B from rfl, hP B, sub_eq_zero]
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_cycle (A * (↑P : MatrixAlg d)) B
        ((↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)))
  -- `Pᴴ * P` commutes with all matrices, from star-preservation of `Td`.
  have hP_star_comm : ∀ Y : MatrixAlg d,
      (↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d) * Y =
        Y * ((↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d)) := by
    intro Y
    have hstar_inner : ∀ X : MatrixAlg d,
        (↑P : MatrixAlg d) * Xᴴ * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d) =
          (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)ᴴ * Xᴴ * (↑P : MatrixAlg d)ᴴ := by
      intro X
      have h := hTd_star X
      rw [show Td Xᴴ = Td_equiv Xᴴ from rfl, hP Xᴴ] at h
      rw [show Td X = Td_equiv X from rfl, hP X] at h
      simpa only [coe_units_inv, Matrix.mul_assoc, conjTranspose_mul] using h
    have hPstarPinvstar :
        (↑P : MatrixAlg d)ᴴ * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)ᴴ = 1 := by
      rw [← conjTranspose_mul, hPinvP, conjTranspose_one]
    specialize hstar_inner Yᴴ
    simp only [conjTranspose_conjTranspose] at hstar_inner
    calc
      (↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d) * Y
          = (↑P : MatrixAlg d)ᴴ *
              ((↑P : MatrixAlg d) * Y * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)) *
              (↑P : MatrixAlg d) := by
            simp only [Matrix.mul_assoc, coe_units_inv, inv_mul_of_invertible, mul_one]
      _ = (↑P : MatrixAlg d)ᴴ *
            ((↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)ᴴ * Y * (↑P : MatrixAlg d)ᴴ) *
            (↑P : MatrixAlg d) := by
            simpa only [coe_units_inv] using
              congrArg (fun Z : MatrixAlg d => (↑P : MatrixAlg d)ᴴ * Z *
                (↑P : MatrixAlg d)) hstar_inner
      _ = ((↑P : MatrixAlg d)ᴴ * (↑(P⁻¹ : GL (Fin d) ℂ) : MatrixAlg d)ᴴ) * Y *
            ((↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d)) := by
            simp only [coe_units_inv, Matrix.mul_assoc]
      _ = Y * ((↑P : MatrixAlg d)ᴴ * (↑P : MatrixAlg d)) := by
            rw [Matrix.mul_assoc, hPstarPinvstar, Matrix.one_mul]
  -- Extract unitary from inner form + P†P commuting with everything
  exact extract_unitary_from_inner_form hT P hT_inner hP_star_comm

/-- The determinant of a unitary channel equals `1`. -/
theorem channelDet_unitary_eq_one (U : Matrix.unitaryGroup (Fin d) ℂ) :
    channelDet (unitaryChannel U) = 1 := by
  let e : MatrixAlg d ≃ₗ[ℂ] (Fin d × Fin d → ℂ) := matrixVecLinearEquiv d
  let M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
    ((U : MatrixAlg d).map star) ⊗ₖ (U : MatrixAlg d)
  have hvec : ∀ X : MatrixAlg d,
      e (unitaryChannel U X) = Matrix.toLin' M (e X) := by
    intro X
    change Matrix.vec (((U : MatrixAlg d) * X * (U : MatrixAlg d)ᴴ) : MatrixAlg d) =
      M.mulVec (Matrix.vec X)
    symm
    simpa only [RCLike.star_def, conjTranspose] using
      (Matrix.kronecker_mulVec_vec (A := (U : MatrixAlg d)) (X := X)
        (B := (U : MatrixAlg d).map star))
  have hconj :
      ((e : MatrixAlg d →ₗ[ℂ] (Fin d × Fin d → ℂ)) ∘ₗ unitaryChannel U ∘ₗ
          ((e.symm : (Fin d × Fin d → ℂ) ≃ₗ[ℂ] MatrixAlg d) :
            (Fin d × Fin d → ℂ) →ₗ[ℂ] MatrixAlg d)) =
        Matrix.toLin' M := by
    apply LinearMap.ext
    intro w
    ext ij
    simpa only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      toLin'_apply, LinearEquiv.apply_symm_apply] using congrFun (hvec (e.symm w)) ij
  have hdet_map_star :
      ((U : MatrixAlg d).map star).det = star (Matrix.det (U : MatrixAlg d)) := by
    simpa only [RCLike.star_def, RingEquiv.mapMatrix_apply, starRingAut_apply] using
      (RingEquiv.map_det (starRingAut : ℂ ≃+* ℂ) (U : MatrixAlg d)).symm
  have hdet_unitary :
      star (Matrix.det (U : MatrixAlg d)) * Matrix.det (U : MatrixAlg d) = 1 := by
    have hU : ((U : MatrixAlg d)ᴴ) * (U : MatrixAlg d) = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
    have h := congrArg Matrix.det hU
    simpa only [RCLike.star_def, det_mul, det_conjTranspose, det_one] using h
  calc
    channelDet (unitaryChannel U) = LinearMap.det (unitaryChannel U) :=
      channelDet_eq_linearMap_det (T := unitaryChannel U)
    _ = LinearMap.det
          (((e : MatrixAlg d →ₗ[ℂ] (Fin d × Fin d → ℂ)) ∘ₗ unitaryChannel U ∘ₗ
            ((e.symm : (Fin d × Fin d → ℂ) ≃ₗ[ℂ] MatrixAlg d) :
              (Fin d × Fin d → ℂ) →ₗ[ℂ] MatrixAlg d))) :=
        (LinearMap.det_conj (f := unitaryChannel U) (e := e)).symm
    _ = LinearMap.det (Matrix.toLin' M) := by rw [hconj]
    _ = Matrix.det M := by rw [LinearMap.det_toLin']
    _ = ((U : MatrixAlg d).map star).det ^ d * Matrix.det (U : MatrixAlg d) ^ d := by
          simpa only [RCLike.star_def, Fintype.card_fin, M] using
            (Matrix.det_kronecker (A := (U : MatrixAlg d).map star)
              (B := (U : MatrixAlg d)))
    _ = (star (Matrix.det (U : MatrixAlg d)) * Matrix.det (U : MatrixAlg d)) ^ d := by
          rw [hdet_map_star, mul_pow]
    _ = 1 := by rw [hdet_unitary, one_pow]

/-- Every unitary channel has determinant of modulus `1`. -/
theorem channelDet_norm_eq_one_of_unitaryChannel (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ‖channelDet (unitaryChannel U)‖ = 1 := by
  simp only [channelDet_unitary_eq_one, one_mem, CStarRing.norm_of_mem_unitary]

/-- Wolf Thm 6.1(2) restricted to CPTP maps: `‖det T‖ = 1 ↔ ∃ U, T = unitaryChannel U`.

The transposition branch from Wolf's general Thm 6.1(2) for positive TP maps does not
appear for CPTP maps since the transpose map is not completely positive. -/
theorem channelDet_norm_eq_one_iff_exists_unitaryChannel
    (hT : IsChannel T) :
    ‖channelDet T‖ = 1 ↔ ∃ U : Matrix.unitaryGroup (Fin d) ℂ, T = unitaryChannel U := by
  constructor
  · intro h
    by_cases hd : d = 0
    · subst hd; exact ⟨1, Subsingleton.elim _ _⟩
    · haveI : NeZero d := ⟨hd⟩
      exact forward_det_one_implies_unitaryChannel hT h
  · rintro ⟨U, rfl⟩
    exact channelDet_norm_eq_one_of_unitaryChannel U

/-- CPTP specialization of the unitary characterization (alias of
`channelDet_norm_eq_one_iff_exists_unitaryChannel`). -/
theorem channelDet_norm_eq_one_iff_exists_unitaryChannel_of_channel
    (hT : IsChannel T) :
    ‖channelDet T‖ = 1 ↔ ∃ U : Matrix.unitaryGroup (Fin d) ℂ, T = unitaryChannel U :=
  channelDet_norm_eq_one_iff_exists_unitaryChannel hT

end WolfStatements
