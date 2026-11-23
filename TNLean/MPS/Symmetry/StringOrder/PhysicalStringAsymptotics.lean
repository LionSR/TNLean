/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.StringOrder.PureTwistedSpectrum
import TNLean.MPS.ParentHamiltonian.ProjectorDefect.FNWTransferDecay
import QICLean.Channel.Peripheral.Spectrum.AdjointSpectrum

/-!
# Phase-retaining asymptotics of the physical string correlator

For fixed physical endpoints and a fixed unitary twist, this module derives
the actual endpoint coefficients in PGWSVC08, arXiv:0802.0447, lines 241–255.
The leading term retains its length-dependent peripheral phase. The resulting
criterion concerns `HasPhysicalStringOrderWith`, not an existential choice of
nontrivial physical symmetry modulo scalar phases.

**Local fix (peripheral phase):** The complex limit printed in arXiv:0802.0447,
lines 249–250, omits the length-dependent phase. Here `(μ^N)⁻¹ S_N` converges,
while the unadjusted complex correlator need not. The correction is recorded in
`docs/paper-gaps/pgwsvc08_string_order_virtual_boundary.tex`.

**Scope restriction (fixed physical twist):** The twist and virtual intertwiner
are fixed; the full existential Theorem 1 is separate, as recorded in
`docs/paper-gaps/pgwsvc08_string_order_virtual_boundary.tex`.

## Geometric finite-length bounds for physical strings

The contracting branch of arXiv:0802.0447, lines 241–243, has a geometric bound
at every prescribed rate strictly above the twisted spectral radius. In the
symmetry branch, the phase-adjusted string differs from the product of its
physical endpoint coefficients by a geometrically decaying error. These bounds
retain Jordan blocks and the length-dependent peripheral phase.
-/

section

open scoped Matrix BigOperators ComplexOrder MatrixOrder TNOperatorSpace
open Filter

namespace MPSTensor

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Canonical transfer powers approach the stationary rank-one map at a
geometric rate, uniformly on virtual inputs, in the endomorphism norm induced
by the row-sum matrix norm. The faithful
canonical hypotheses imply the complementary spectral gap; no diagonalizability
or geometric bound is assumed. Positive lengths exclude the exceptional
zeroth-power identity. Source: arXiv:0802.0447, lines 241–255, using the
complementary remainder from FNW 1992, Lemma 5.2. -/
theorem canonical_transfer_pow_sub_stationary_le_geometric
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (hPrim : IsPrimitive (Kraus.transferMap A))
    (Λ : Mat) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ r < 1 ∧ ∀ N : ℕ, 1 ≤ N →
      ‖Module.End.toContinuousLinearMap Mat
        (Kraus.transferMap A ^ N - fnwLimitMap Λ (by simp [hΛtr]))‖ ≤ C * r ^ N := by
  let B : MPSTensor d D := fun i => (A i)ᴴ
  have hBnorm : ∑ i, (B i)ᴴ * B i = 1 := by
    simpa [B, Kraus.transferMap_apply] using hNorm
  have hIrrB : IsIrreducibleMap (Kraus.transferMap B) :=
    Kraus.isIrreducibleMap_mapLM_conjTranspose A hIrr
  have hPrimB : IsPrimitive (Kraus.transferMap B) := by
    change peripheralEigenvalues (Kraus.mapLM (fun i => (A i)ᴴ)) = {1}
    rw [Kraus.peripheralEigenvalues_mapLM_conjTranspose,
      show peripheralEigenvalues (Kraus.mapLM A) = {1} from hPrim]
    simp
  have hΛne : Λ ≠ 0 := by
    intro hΛ0
    simp [hΛ0] at hΛtr
  obtain ⟨htr, hgap⟩ :=
    spectralRadius_compl_lt_one_of_primitive_fixedPoint_of_irreducible_channel
      (Kraus.transferMap B) (Kraus.isChannel_mapLM B hBnorm) hIrrB hPrimB
      Λ hΛpos.posSemidef hΛne hΛfix
  have hP : Kraus.HasComplementaryFixedPointGap B Λ :=
    ⟨hBnorm, hΛne, hΛpos.posSemidef, hΛfix, hgap⟩
  let P := fnwLimitMap Λ hP.trace_ne_zero
  have hFnw : fnwTransferMap B = Kraus.transferMap A := by
    simp [fnwTransferMap, B]
  have hR : spectralRadius ℂ (Module.End.toContinuousLinearMap Mat
      (Kraus.transferMap A - P)) < 1 := by
    apply spectralRadius_lt_one_of_eigenvalues_lt_one
    intro ν hν
    exact hP.fnwRemainder_eigenvalue_norm_lt_one ν (by simpa [hFnw] using hν)
  obtain ⟨C, r, hC, hr, hr1, hbound⟩ :=
    geometric_bound_of_spectralRadius_lt_one _ hR
  refine ⟨C, r, hC, hr, hr1, fun N hN => ?_⟩
  have hid := hP.fnwTransferMap_sub_fnwLimitMap_pow hN
  rw [hFnw] at hid
  simpa only [← map_pow, hid, P] using hbound N

/-- The unital canonical transfer powers converge to the faithful stationary
trace functional. This follows from the operator-norm geometric estimate,
without diagonalizability. Source: arXiv:0802.0447, lines 241–255. -/
theorem canonical_transfer_pow_tendsto_stationary_trace
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (hPrim : IsPrimitive (Kraus.transferMap A))
    (Λ : Mat) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1) (X : Mat) :
    Tendsto (fun N : ℕ => (Kraus.transferMap A ^ N) X) atTop
      (nhds (Matrix.trace (Λ * X) • (1 : Mat))) := by
  obtain ⟨C, r, hC, hr, hr1, hbound⟩ :=
    canonical_transfer_pow_sub_stationary_le_geometric
      A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_
    (by simpa using ((tendsto_const_nhds (x := C)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1)).mul_const ‖X‖)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have h := (Module.End.toContinuousLinearMap Mat
    (Kraus.transferMap A ^ N - fnwLimitMap Λ (by simp [hΛtr]))).le_of_opNorm_le
      (hbound N hN) X
  change ‖(Kraus.transferMap A ^ N) X - fnwLimitMap Λ _ X‖ ≤ C * r ^ N * ‖X‖ at h
  simpa only [fnwLimitMap_apply_of_trace_eq_one Λ X hΛtr] using h

/-- The exact iterate identity behind the physical asymptotic formula.
It holds also at zero length and keeps the full phase `μ^N`.
Supporting result for arXiv:0802.0447, lines 241–255. -/
theorem twistedTransferIter_eq_phase_mul_transfer_pow
    (A : MPSTensor d D) (u : Matrix (Fin d) (Fin d) ℂ)
    (V : Mat) (μ : ℂ) (hV : V * Vᴴ = 1)
    (hInter : ∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ))
    (X : Mat) (N : ℕ) :
    twistedTransferIter A u N X = μ ^ N • (V * (Kraus.transferMap A ^ N) (Vᴴ * X)) := by
  have hV' : Vᴴ * V = 1 := mul_eq_one_comm.mp hV
  induction N with
  | zero => simp [twistedTransferIter, ← Matrix.mul_assoc, hV]
  | succ N ih =>
    rw [twistedTransferIter, pow_succ', Module.End.mul_apply]
    change twistedTransferMap A u (twistedTransferIter A u N X) = _
    rw [ih, map_smul, twistedTransfer_eq_phase_mul_transfer A u V μ hInter]
    simp [← Matrix.mul_assoc, hV', pow_succ', Module.End.mul_apply, smul_smul, mul_comm μ]

/-- After removing its peripheral phase, the twisted transfer iterate converges
on every virtual input to the rank-one stationary projection. Composing this
limit with physical endpoint maps covers endpoints of any finite support.

Source: arXiv:0802.0447, lines 241–255, with the peripheral phase retained. -/
theorem twistedTransferIter_phase_adjusted_tendsto
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (hPrim : IsPrimitive (Kraus.transferMap A))
    (Λ : Mat) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (u : Matrix (Fin d) (Fin d) ℂ) (V : Mat) (μ : ℂ)
    (hV : V * Vᴴ = 1) (hμ : ‖μ‖ = 1)
    (hInter : ∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ)) (Y : Mat) :
    Tendsto (fun N : ℕ => (μ ^ N)⁻¹ • twistedTransferIter A u N Y) atTop
      (nhds (Matrix.trace (Λ * Vᴴ * Y) • V)) := by
  have hμne : μ ≠ 0 := Complex.ne_zero_of_norm_eq_one hμ
  have hphase (N : ℕ) : (μ ^ N)⁻¹ • twistedTransferIter A u N Y =
      V * (Kraus.transferMap A ^ N) (Vᴴ * Y) := by
    rw [twistedTransferIter_eq_phase_mul_transfer_pow A u V μ hV hInter]
    rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero N hμne), one_smul]
  have hlim := canonical_transfer_pow_tendsto_stationary_trace
    A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm (Vᴴ * Y)
  have h : Tendsto (fun N : ℕ => V * (Kraus.transferMap A ^ N) (Vᴴ * Y))
      atTop (nhds (V * (Matrix.trace (Λ * (Vᴴ * Y)) • (1 : Mat)))) :=
    ((LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ V)).continuous.tendsto _).comp hlim
  simpa only [Matrix.mul_smul, Matrix.mul_one, ← hphase, Matrix.mul_assoc] using h

/-- The source physical correlator has a phase-retaining asymptotic coefficient.
The factor `(μ^N)⁻¹` is essential: the complex correlator itself need not converge.
Supporting result for arXiv:0802.0447, lines 241–255. -/
theorem physicalStringOrderParam_phase_adjusted_tendsto
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (hPrim : IsPrimitive (Kraus.transferMap A))
    (Λ : Mat) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (x y u : Matrix (Fin d) (Fin d) ℂ) (V : Mat) (μ : ℂ)
    (hV : V * Vᴴ = 1) (hμ : ‖μ‖ = 1)
    (hInter : ∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ)) :
    Tendsto (fun N : ℕ => (μ ^ N)⁻¹ * physicalStringOrderParam A Λ x y u N) atTop
      (nhds (Matrix.trace (Λ * Vᴴ * twistedTransferMap A y 1) *
        Matrix.trace (Λ * twistedTransferMap A x V))) := by
  let Φ : Mat →ₗ[ℂ] ℂ := (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
    ((LinearMap.mulLeft ℂ Λ).comp (twistedTransferMap A x))
  have hlim := twistedTransferIter_phase_adjusted_tendsto
    A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm u V μ hV hμ hInter
    (twistedTransferMap A y 1)
  have hΦ (Z : Mat) : Φ Z = Matrix.trace (Λ * twistedTransferMap A x Z) := rfl
  have h : Tendsto
      (fun N : ℕ => Φ ((μ ^ N)⁻¹ • twistedTransferIter A u N (twistedTransferMap A y 1)))
      atTop (nhds (Φ (Matrix.trace (Λ * Vᴴ * twistedTransferMap A y 1) • V))) :=
    ((LinearMap.toContinuousLinearMap Φ).continuous.tendsto _).comp hlim
  simp only [map_smul] at h
  simpa only [hΦ, physicalStringOrderParam, smul_eq_mul] using h

/-- The limiting magnitude of the actual physical string correlator is the
product of the two endpoint coefficient magnitudes. This retains arbitrary
unit peripheral phases without assuming convergence of the complex correlator.
Supporting result for arXiv:0802.0447, lines 241–255. -/
theorem physicalStringOrderParam_norm_tendsto
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (hPrim : IsPrimitive (Kraus.transferMap A))
    (Λ : Mat) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (x y u : Matrix (Fin d) (Fin d) ℂ) (V : Mat) (μ : ℂ)
    (hV : V * Vᴴ = 1) (hμ : ‖μ‖ = 1)
    (hInter : ∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ)) :
    Tendsto (fun N : ℕ => ‖physicalStringOrderParam A Λ x y u N‖) atTop
      (nhds (‖Matrix.trace (Λ * Vᴴ * twistedTransferMap A y 1)‖ *
        ‖Matrix.trace (Λ * twistedTransferMap A x V)‖)) := by
  have h := (physicalStringOrderParam_phase_adjusted_tendsto
    A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm x y u V μ hV hμ hInter).norm
  simpa [norm_mul, norm_inv, norm_pow, hμ] using h

/-- The physical selection rule for fixed endpoints, twist, and virtual
intertwiner: positive limiting magnitude is equivalent to the two actual
physical endpoint coefficients being nonzero.
Supporting result for arXiv:0802.0447, lines 241–255. -/
theorem hasPhysicalStringOrderWith_iff_endpoint_coefficients
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (hPrim : IsPrimitive (Kraus.transferMap A))
    (Λ : Mat) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (x y u : Matrix (Fin d) (Fin d) ℂ) (V : Mat) (μ : ℂ)
    (hV : V * Vᴴ = 1) (hμ : ‖μ‖ = 1)
    (hInter : ∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ)) :
    HasPhysicalStringOrderWith A Λ x y u ↔
      Matrix.trace (Λ * Vᴴ * twistedTransferMap A y 1) ≠ 0 ∧
      Matrix.trace (Λ * twistedTransferMap A x V) ≠ 0 := by
  have hlim := physicalStringOrderParam_norm_tendsto
    A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm x y u V μ hV hμ hInter
  constructor
  · rintro ⟨s, hs, hS⟩
    have heq := tendsto_nhds_unique hS hlim
    rw [heq] at hs
    constructor
    · intro hzero
      rw [hzero, norm_zero, zero_mul] at hs
      exact (lt_irrefl 0) hs
    · intro hzero
      rw [hzero, norm_zero, mul_zero] at hs
      exact (lt_irrefl 0) hs
  · rintro ⟨hy, hx⟩
    exact ⟨_, mul_pos (norm_pos_iff.mpr hy) (norm_pos_iff.mpr hx), hlim⟩

end MPSTensor

end

section

open scoped Matrix BigOperators ComplexOrder MatrixOrder TNOperatorSpace NNReal ENNReal

namespace MPSTensor

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- At every rate above the twisted spectral radius the physical string is
geometrically bounded, including zero middle length. Taking the rate below one
proves the exponential decay in arXiv:0802.0447, lines 241–243. -/
theorem physicalStringOrderParam_le_geometric
    (A : MPSTensor d D) (Λ : Mat) (x y u : Matrix (Fin d) (Fin d) ℂ)
    (rate : ℝ≥0) (hRate : spectralRadius ℂ
      (Module.End.toContinuousLinearMap Mat (twistedTransferMap A u)) <
        (rate : ℝ≥0∞)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖physicalStringOrderParam A Λ x y u N‖ ≤ C * (rate : ℝ) ^ N := by
  obtain ⟨C, hC, hpow⟩ := geometric_apply_bound_of_spectralRadius_lt
    (Module.End.toContinuousLinearMap Mat (twistedTransferMap A u)) rate hRate
  let ℓ : Mat →L[ℂ] ℂ := ((Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
    ((LinearMap.mulLeft ℂ Λ).comp (twistedTransferMap A x))).toContinuousLinearMap
  let Y := twistedTransferMap A y 1
  obtain ⟨M, hM, hℓ⟩ := ℓ.bound
  refine ⟨M * C * ‖Y‖ + 1, by positivity, fun N => ?_⟩
  have hp : ‖twistedTransferIter A u N Y‖ ≤ C * (rate : ℝ) ^ N * ‖Y‖ := by
    have h := hpow N Y
    rw [← map_pow] at h
    exact h
  exact (hℓ (twistedTransferIter A u N Y)).trans
    ((mul_le_mul_of_nonneg_left hp hM.le).trans (by
      nlinarith [pow_nonneg rate.coe_nonneg N]))

/-- In the canonical pure regime the physical endpoint coefficient formula
has a geometric error after removing the peripheral phase. The rate is
independent of the fixed endpoints. Source: arXiv:0802.0447, lines 249–255,
with the phase qualification recorded in
`docs/paper-gaps/pgwsvc08_string_order_virtual_boundary.tex`. -/
theorem physicalStringOrderParam_phase_adjusted_le_geometric
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (hPrim : IsPrimitive (Kraus.transferMap A))
    (Λ : Mat) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (u : Matrix (Fin d) (Fin d) ℂ) (V : Mat) (μ : ℂ)
    (hV : V * Vᴴ = 1) (hμ : ‖μ‖ = 1)
    (hInter : ∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ)) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x y : Matrix (Fin d) (Fin d) ℂ,
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
        ‖(μ ^ N)⁻¹ * physicalStringOrderParam A Λ x y u N -
          Matrix.trace (Λ * Vᴴ * twistedTransferMap A y 1) *
            Matrix.trace (Λ * twistedTransferMap A x V)‖ ≤ C * r ^ N := by
  obtain ⟨C, r, hC, hr, hr1, hpow⟩ :=
    canonical_transfer_pow_sub_stationary_le_geometric
      A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm
  refine ⟨r, hr, hr1, fun x y => ?_⟩
  let ℓ : Mat →ₗ[ℂ] ℂ := (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
    ((LinearMap.mulLeft ℂ Λ).comp
      ((twistedTransferMap A x).comp (LinearMap.mulLeft ℂ V)))
  have hℓ_apply (Z : Mat) : ℓ Z = Matrix.trace (Λ * twistedTransferMap A x (V * Z)) := rfl
  let Y := Vᴴ * twistedTransferMap A y 1
  obtain ⟨M, hM, hℓ⟩ := ℓ.toContinuousLinearMap.bound
  refine ⟨M * C * ‖Y‖ + 1, by positivity, fun N hN => ?_⟩
  have hphase : (μ ^ N)⁻¹ * physicalStringOrderParam A Λ x y u N =
      ℓ ((Kraus.transferMap A ^ N) Y) := by
    simp only [physicalStringOrderParam,
      twistedTransferIter_eq_phase_mul_transfer_pow A u V μ hV hInter,
      map_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero N
      (Complex.ne_zero_of_norm_eq_one hμ)), one_mul]
    rfl
  have hlimit : ℓ (fnwLimitMap Λ (by simp [hΛtr]) Y) =
      Matrix.trace (Λ * Vᴴ * twistedTransferMap A y 1) *
        Matrix.trace (Λ * twistedTransferMap A x V) := by
    rw [fnwLimitMap_apply_of_trace_eq_one Λ Y hΛtr, map_smul, hℓ_apply, smul_eq_mul]
    simp only [Y, Matrix.mul_one, Matrix.mul_assoc]
  rw [hphase, ← hlimit, ← map_sub]
  have hp := (Module.End.toContinuousLinearMap Mat
    (Kraus.transferMap A ^ N - fnwLimitMap Λ (by simp [hΛtr]))).le_of_opNorm_le
      (hpow N hN) Y
  change ‖(Kraus.transferMap A ^ N) Y - fnwLimitMap Λ _ Y‖ ≤ C * r ^ N * ‖Y‖ at hp
  exact (hℓ _).trans ((mul_le_mul_of_nonneg_left hp hM.le).trans (by
    nlinarith [pow_nonneg hr.le N]))

end MPSTensor

end
