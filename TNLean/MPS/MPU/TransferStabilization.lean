/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixStabilization
import QICLean.Algebra.MatrixPosDefTransport
import QICLean.Channel.KrausMap
import QICLean.Kraus.Transfer
import TNLean.MPS.MPU.CanonicalForm
import TNLean.MPS.MPU.TransferMatrix

/-!
# Stabilization of the normalized MPU transfer matrix

The exact characteristic polynomial of the normalized transfer matrix is
`X ^ (D * D - 1) * (X - 1)`. Cayley--Hamilton therefore makes its
`(D * D - 1)`-st and `D * D`-th powers equal. The stabilized power is an
idempotent of trace one, hence a rank-one projector with normalized left and
right fixed witnesses.

## Main definitions

* `MPOTensor.IsMPU.normalizedTransferStabilization` gives stabilized rank-one
  data for bond dimension greater than one.
* `MPOTensor.IsMPU.normalizedTransferStabilization_fin_one` gives the
  one-dimensional data at exponent one.

## Main results

* `MPOTensor.IsMPU.exists_normalized_transfer_stabilizes_to_rank_one` gives
  the source-shaped bounded stabilization theorem.
* `MPOTensor.IsMPU.normalized_transfer_power_eq_vecMulVec_of_reduced_cfii`
  identifies the stabilized power with the fixed pair supplied by chosen
  reduced canonical-form-II data.
* `MPOTensor.IsMPU.normalized_transfer_matrix_eq_one_fin_one` proves that the
  one-dimensional normalized transfer matrix is the identity.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, "Matrix Product Unitaries: Structure,
  Symmetries, and Topological Invariants", lines 397--409.
-/

open scoped Matrix BigOperators ComplexOrder
open Polynomial

namespace MPOTensor

/-! ### Normalized MPU transfer stabilization -/

variable {d D : ℕ}

/-- For an MPU of bond dimension `D > 1`, the normalized transfer matrix
stabilizes at the explicit positive exponent `J = D * D - 1`. Its stabilized
value is `|ρ)(Φ|`, with normalized left and right fixed witnesses, and every
power at least `J` has the same value.

Cayley--Hamilton applied to
`χ_E(X) = X^(D²-1)(X-1)` eliminates precisely the zero-primary component; no
ambient normality or diagonalizability is asserted.

Source: arXiv:1703.09188, lines 397--409. -/
noncomputable def IsMPU.normalizedTransferStabilization
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U) (hD : 1 < D) :
    Matrix.StabilizedRankOneData
      (transferMatrix (Kraus.transferMap U.normalizedFlattening)) (D * D - 1) := by
  let E := transferMatrix (Kraus.transferMap U.normalizedFlattening)
  have hDD : 4 ≤ D * D :=
    Nat.mul_le_mul (by omega : 2 ≤ D) (by omega : 2 ≤ D)
  have hchar : E.charpoly = X ^ (Fintype.card (Fin D × Fin D) - 1) * (X - 1) := by
    simpa [E, Fintype.card_prod, Fintype.card_fin] using hU.normalizedFlattening_charpoly
  have hpow :=
    Matrix.pow_card_eq_pow_pred_of_charpoly_eq_X_pow_pred_mul_X_sub_one E hchar
  have hstep : E ^ ((D * D - 1) + 1) = E ^ (D * D - 1) := by
    simpa [Fintype.card_prod, Fintype.card_fin,
      Nat.sub_add_cancel (by omega : 1 ≤ D * D)] using hpow
  exact Matrix.StabilizedRankOneData.of_power_succ_eq (D * D - 1) (D * D - 1)
    (by omega) le_rfl hstep
    (hU.trace_transferMatrix_normalizedFlattening_pow_eq_one (by omega))

/-- Source-shaped unbundled form of normalized transfer stabilization:
there are normalized left/right fixed witnesses and a positive
`J ≤ D * D - 1` such that `E^J = |ρ)(Φ|` and all later powers equal this
rank-one projector.

The proof removes the zero-primary component by Cayley--Hamilton; it does not
infer ambient normality from bare `IsMPU`.

Source: arXiv:1703.09188, lines 397--409. -/
theorem IsMPU.exists_normalized_transfer_stabilizes_to_rank_one
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U) (hD : 1 < D) :
    ∃ J : ℕ, 0 < J ∧ J ≤ D * D - 1 ∧
      ∃ ρ Φ : Fin D × Fin D → ℂ,
        Φ ⬝ᵥ ρ = 1 ∧
        transferMatrix (Kraus.transferMap U.normalizedFlattening) *ᵥ ρ = ρ ∧
        Matrix.vecMul Φ
          (transferMatrix (Kraus.transferMap U.normalizedFlattening)) = Φ ∧
        transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ J =
          Matrix.vecMulVec ρ Φ ∧
        ∀ k, J ≤ k →
          transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ k =
            transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ J := by
  let data := hU.normalizedTransferStabilization hD
  refine ⟨data.exponent, data.exponent_pos, data.exponent_le,
    data.right, data.left, ?_, data.right_fixed, data.left_fixed,
    data.power_eq, data.stable⟩
  rw [dotProduct_comm]
  exact data.pairing_eq_one

/-- A chosen reduced canonical-form-II representative supplies the positive
right fixed matrix and identity left fixed vector that factor the exact stabilized
normalized transfer power.

The unique block and the equation transporting its normalized diagonal fixed
matrix into the ambient bond space are retained explicitly in the conclusion.
The ambient matrix is positive definite, but is not asserted to be diagonal.

**Scope restriction (full support):** This is the reduced-representative
route in arXiv:1703.09188, equation `Erightleft` (lines 269--280) and lines
397--405. See `docs/paper-gaps/mpu_canonical_form_full_support.tex`. -/
theorem IsMPU.normalized_transfer_power_eq_vecMulVec_of_reduced_cfii
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U) (hD : 1 < D)
    (cfii : MPSTensor.CPSVCanonicalFormIIData U.normalizedFlattening)
    (hfull : cfii.toCPSVCanonicalFormData.HasFullSupport) :
    ∃ (k : Fin cfii.r)
      (Λ : Matrix (Fin (cfii.dim k)) (Fin (cfii.dim k)) ℂ)
      (ρ : Matrix (Fin D) (Fin D) ℂ),
      (∀ l : Fin cfii.r, l = k) ∧
      Λ.PosDef ∧ Λ.IsDiag ∧ Matrix.trace Λ = 1 ∧
      Kraus.transferMap (cfii.blocks k) Λ = Λ ∧
      ρ = cfii.ambientBlockInclusion k * Λ *
        (cfii.ambientBlockInclusion k)ᴴ ∧
      ρ.PosDef ∧ Matrix.trace ρ = 1 ∧
      Kraus.transferMap U.normalizedFlattening ρ = ρ ∧
      Matrix.vecMul (1 : Matrix (Fin D) (Fin D) ℂ).vec
        (transferMatrix (Kraus.transferMap U.normalizedFlattening)) =
          (1 : Matrix (Fin D) (Fin D) ℂ).vec ∧
      transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ (D * D - 1) =
        Matrix.vecMulVec ρ.vec (1 : Matrix (Fin D) (Fin D) ℂ).vec := by
  classical
  let base := cfii.toCPSVCanonicalFormData
  have htrace : ∀ N : ℕ, 1 < N →
      Matrix.trace
        (transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ N) = 1 :=
    fun N hN => hU.trace_transferMatrix_normalizedFlattening_pow_eq_one hN
  have hr : base.r = 1 :=
    base.r_eq_one_of_shifted_transfer_trace htrace
  let k : Fin base.r := ⟨0, by omega⟩
  obtain ⟨Λ₀, hΛ₀pd, hΛ₀diag, hΛ₀fix⟩ := cfii.blocks_fixed_point k
  let : Nonempty (Fin (cfii.dim k)) := Fin.pos_iff_nonempty.mp (cfii.dim_pos k)
  let Λ : Matrix (Fin (cfii.dim k)) (Fin (cfii.dim k)) ℂ :=
    (Matrix.trace Λ₀)⁻¹ • Λ₀
  have hΛtrace_pos : 0 < Matrix.trace Λ₀ := hΛ₀pd.trace_pos
  have hΛtrace_ne : Matrix.trace Λ₀ ≠ 0 := ne_of_gt hΛtrace_pos
  have hΛpd : Λ.PosDef := hΛ₀pd.smul (inv_pos.mpr hΛtrace_pos)
  have hΛdiag : Λ.IsDiag := hΛ₀diag.smul _
  have hΛtrace : Matrix.trace Λ = 1 := by
    simp [Λ, Matrix.trace_smul, hΛtrace_ne]
  have hΛfix : Kraus.transferMap (cfii.blocks k) Λ = Λ := by
    simp only [Λ, map_smul, hΛ₀fix]
  have hweight : base.transferEigenvalue k = 1 :=
    base.transferEigenvalue_eq_one htrace k
  have hweight' : cfii.weights k * starRingEnd ℂ (cfii.weights k) = 1 := by
    simpa [base, MPSTensor.CPSVCanonicalFormData.transferEigenvalue] using hweight
  have hweightedFix :
      Kraus.transferMap (fun i => cfii.weights k • cfii.blocks k i) Λ = Λ := by
    rw [MPSTensor.transferMap_smul, hΛfix, hweight', one_smul]
  let V := base.ambientBlockInclusion k
  let ρ : Matrix (Fin D) (Fin D) ℂ := V * Λ * Vᴴ
  have hVstarV : Vᴴ * V = 1 :=
    base.ambientBlockInclusion_conjTranspose_mul_self k
  have hVVstar : V * Vᴴ = 1 :=
    base.ambientBlockInclusion_mul_conjTranspose_eq_one hr hfull k
  have hρpd : ρ.PosDef :=
    hΛpd.mul_mul_conjTranspose_of_mul_conjTranspose_eq_one V hVVstar
  have hρtrace : Matrix.trace ρ = 1 := by
    change Matrix.trace (V * Λ * Vᴴ) = 1
    rw [Matrix.trace_mul_comm (V * Λ) Vᴴ, ← Matrix.mul_assoc, hVstarV,
      Matrix.one_mul, hΛtrace]
  have hρfix : Kraus.transferMap U.normalizedFlattening ρ = ρ := by
    change Kraus.transferMap U.normalizedFlattening (V * Λ * Vᴴ) = V * Λ * Vᴴ
    rw [MPSTensor.transferMap_conj_of_intertwine U.normalizedFlattening
      (fun i => cfii.weights k • cfii.blocks k i) V
      (base.mul_ambientBlockInclusion k) Λ, hweightedFix]
  have hweightedLeft :
      MPSTensor.IsLeftCanonical (fun i => cfii.weights k • cfii.blocks k i) := by
    unfold MPSTensor.IsLeftCanonical
    have hweightStar : cfii.weights k * star (cfii.weights k) = 1 := by
      simpa using hweight'
    have hweightStarComm : star (cfii.weights k) * cfii.weights k = 1 := by
      rw [mul_comm, hweightStar]
    calc
      ∑ i, (cfii.weights k • cfii.blocks k i)ᴴ *
          (cfii.weights k • cfii.blocks k i) =
          ∑ i, (star (cfii.weights k) * cfii.weights k) •
            ((cfii.blocks k i)ᴴ * cfii.blocks k i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      _ = (star (cfii.weights k) * cfii.weights k) • 1 := by
        rw [← Finset.smul_sum, cfii.blocks_left_canonical k]
      _ = 1 := by rw [hweightStarComm, one_smul]
  have hAeq : ∀ i, U.normalizedFlattening i =
      V * (cfii.weights k • cfii.blocks k i) * Vᴴ := by
    intro i
    calc
      U.normalizedFlattening i = U.normalizedFlattening i * 1 := by rw [Matrix.mul_one]
      _ = U.normalizedFlattening i * (V * Vᴴ) := by rw [hVVstar]
      _ = (U.normalizedFlattening i * V) * Vᴴ := by rw [Matrix.mul_assoc]
      _ = V * (cfii.weights k • cfii.blocks k i) * Vᴴ := by
        rw [base.mul_ambientBlockInclusion k]
  have hAleft : MPSTensor.IsLeftCanonical U.normalizedFlattening := by
    unfold MPSTensor.IsLeftCanonical at hweightedLeft ⊢
    calc
      ∑ i, (U.normalizedFlattening i)ᴴ * U.normalizedFlattening i =
          ∑ i, V * ((cfii.weights k • cfii.blocks k i)ᴴ *
            (cfii.weights k • cfii.blocks k i)) * Vᴴ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hAeq i, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
        simp only [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Vᴴ V, hVstarV, Matrix.one_mul]
      _ = V * (∑ i, (cfii.weights k • cfii.blocks k i)ᴴ *
            (cfii.weights k • cfii.blocks k i)) * Vᴴ := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
      _ = 1 := by rw [hweightedLeft, Matrix.mul_one, hVVstar]
  have hleft : Matrix.vecMul (1 : Matrix (Fin D) (Fin D) ℂ).vec
      (transferMatrix (Kraus.transferMap U.normalizedFlattening)) =
        (1 : Matrix (Fin D) (Fin D) ℂ).vec :=
    vecMul_vec_one_transferMatrix_eq_of_trace_preserving _
      (fun X => Kraus.isTracePreservingMap_mapLM_of_isTP U.normalizedFlattening hAleft X)
  have hright : transferMatrix (Kraus.transferMap U.normalizedFlattening) *ᵥ ρ.vec =
      ρ.vec := by
    rw [transferMatrix_mulVec_eq, hρfix]
  have hpair : (1 : Matrix (Fin D) (Fin D) ℂ).vec ⬝ᵥ ρ.vec = 1 := by
    rw [Matrix.vec_one_dotProduct_vec_eq_trace, hρtrace]
  have hpower := (hU.normalizedTransferStabilization hD).power_eq_vec_mul_vec_of_fixed
    ρ.vec (1 : Matrix (Fin D) (Fin D) ℂ).vec hpair hright hleft
  change transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ (D * D - 1) =
    Matrix.vecMulVec ρ.vec (1 : Matrix (Fin D) (Fin D) ℂ).vec at hpower
  have huniq : ∀ l : Fin cfii.r, l = k := fun l => Fin.ext (by
    change (l : ℕ) = 0
    have hl := l.isLt
    have hr' : cfii.r = 1 := hr
    omega)
  refine ⟨k, Λ, ρ, huniq, hΛpd, hΛdiag, hΛtrace,
    hΛfix, rfl, hρpd, hρtrace, hρfix, hleft, ?_⟩
  simpa using hpower

/-- In bond dimension one, the normalized transfer matrix of an MPU is the identity.

Source: arXiv:1703.09188, lines 397--409, specialized to `D = 1`. -/
theorem IsMPU.normalized_transfer_matrix_eq_one_fin_one
    [NeZero d] {U : MPOTensor d 1} (hU : IsMPU U) :
    transferMatrix (Kraus.transferMap U.normalizedFlattening) = 1 := by
  let E := transferMatrix (Kraus.transferMap U.normalizedFlattening)
  have hchar : E.charpoly = X ^ (Fintype.card (Fin 1 × Fin 1) - 1) * (X - 1) := by
    simpa [E, Fintype.card_prod, Fintype.card_fin] using hU.normalizedFlattening_charpoly
  have hpow :=
    Matrix.pow_card_eq_pow_pred_of_charpoly_eq_X_pow_pred_mul_X_sub_one E hchar
  have hE : E = 1 := by
    simpa [Fintype.card_prod, Fintype.card_fin] using hpow
  simpa [E] using hE

/-- In bond dimension one, the normalized transfer matrix stabilizes at exponent one.
This separate definition is necessary because no positive exponent can satisfy
`J ≤ D * D - 1 = 0`.

Source: arXiv:1703.09188, lines 397--409, specialized to `D = 1`. -/
noncomputable def IsMPU.normalizedTransferStabilization_fin_one
    [NeZero d] {U : MPOTensor d 1} (hU : IsMPU U) :
    Matrix.StabilizedRankOneData
      (transferMatrix (Kraus.transferMap U.normalizedFlattening)) 1 := by
  have hE := hU.normalized_transfer_matrix_eq_one_fin_one
  apply Matrix.StabilizedRankOneData.of_power_succ_eq 1 1 Nat.zero_lt_one le_rfl
  · rw [hE]
    simp
  · rw [hE]
    simp

end MPOTensor
