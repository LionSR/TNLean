/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.PureTwistedSpectrum
import TNLean.MPS.ParentHamiltonian.FNWTransferDecay
import QICLean.Channel.Peripheral.AdjointSpectrum

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
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder TNOperatorSpace
open Filter

namespace MPSTensor

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The unital canonical transfer powers converge to the faithful stationary
trace functional. The proof reuses the FNW complementary-remainder machinery
on the conjugate-transposed family; no diagonalizability is assumed.
Supporting result for arXiv:0802.0447, lines 241–255. -/
theorem canonical_transfer_pow_tendsto_stationary_trace
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (hPrim : IsPrimitive (Kraus.transferMap A))
    (Λ : Mat) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1) (X : Mat) :
    Tendsto (fun N : ℕ => (Kraus.transferMap A ^ N) X) atTop
      (nhds (Matrix.trace (Λ * X) • (1 : Mat))) := by
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
  have hP : IsPrimitiveMPS B Λ :=
    ⟨hBnorm, hΛne, hΛpos.posSemidef, hΛfix, hgap⟩
  let P := fnwLimitMap Λ hP.trace_ne_zero
  have hFnw : fnwTransferMap B = Kraus.transferMap A := by
    simp [fnwTransferMap, B]
  have hR : spectralRadius ℂ (Module.End.toContinuousLinearMap Mat
      (Kraus.transferMap A - P)) < 1 := by
    apply spectralRadius_lt_one_of_eigenvalues_lt_one
    intro ν hν
    exact hP.fnwRemainder_eigenvalue_norm_lt_one ν (by simpa [hFnw] using hν)
  have hpow := pow_tendsto_zero_of_spectralRadius_lt_one _ hR
  have hRlim : Tendsto (fun N : ℕ => ((Kraus.transferMap A - P) ^ N) X)
      atTop (nhds 0) := by
    have h := ((ContinuousLinearMap.apply ℂ _ X).continuous.tendsto 0).comp hpow
    convert h using 1
    · funext N
      simp only [Function.comp_apply, ContinuousLinearMap.apply_apply, ← map_pow]
      rfl
    · simp only [map_zero]
      rfl
  have hlim : Tendsto
      (fun N : ℕ => P X + ((Kraus.transferMap A - P) ^ N) X) atTop (nhds (P X)) := by
    simpa using (tendsto_const_nhds (x := P X)).add hRlim
  have hresult : Tendsto (fun N : ℕ => (Kraus.transferMap A ^ N) X)
      atTop (nhds (P X)) := hlim.congr' (by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hid := hP.fnwTransferMap_sub_fnwLimitMap_pow hN
    rw [hFnw] at hid
    change P X + ((Kraus.transferMap A - P) ^ N) X = (Kraus.transferMap A ^ N) X
    rw [hid]
    simp only [LinearMap.sub_apply]
    abel)
  simpa [P, fnwLimitMap, hΛtr] using hresult

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
    ((LinearMap.mulLeft ℂ Λ).comp
      ((twistedTransferMap A x).comp (LinearMap.mulLeft ℂ V)))
  have hμne : μ ≠ 0 := Complex.ne_zero_of_norm_eq_one hμ
  have hphase (N : ℕ) : (μ ^ N)⁻¹ * physicalStringOrderParam A Λ x y u N =
      Φ ((Kraus.transferMap A ^ N) (Vᴴ * twistedTransferMap A y 1)) := by
    rw [physicalStringOrderParam,
      twistedTransferIter_eq_phase_mul_transfer_pow A u V μ hV hInter]
    simp only [map_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero N hμne), one_mul]
    rfl
  have hTransfer := canonical_transfer_pow_tendsto_stationary_trace
    A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm (Vᴴ * twistedTransferMap A y 1)
  have hlim := ((LinearMap.toContinuousLinearMap Φ).continuous.tendsto _).comp hTransfer
  have hFinal : Tendsto
      (fun N : ℕ => (μ ^ N)⁻¹ * physicalStringOrderParam A Λ x y u N) atTop
      (nhds (Φ (Matrix.trace (Λ * (Vᴴ * twistedTransferMap A y 1)) • (1 : Mat)))) := by
    apply hlim.congr'
    exact Filter.Eventually.of_forall fun N => (hphase N).symm
  have hvalue (c : ℂ) : Φ (c • (1 : Mat)) =
      c * Matrix.trace (Λ * twistedTransferMap A x V) := by
    change Matrix.trace (Λ * twistedTransferMap A x (V * (c • (1 : Mat)))) = _
    rw [Matrix.mul_smul, Matrix.mul_one, map_smul, Matrix.mul_smul, Matrix.trace_smul]
    rfl
  rw [hvalue] at hFinal
  simpa only [Matrix.mul_assoc] using hFinal

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
