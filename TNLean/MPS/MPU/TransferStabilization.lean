/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Trace
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.MPU.TransferMatrix

/-!
# Jordan elimination for the normalized MPU transfer matrix

The exact characteristic polynomial of the normalized transfer matrix is
`X ^ (D * D - 1) * (X - 1)`. Cayley--Hamilton therefore makes its
`(D * D - 1)`-st and `D * D`-th powers equal. This is the coordinate-free
replacement for blocking by the largest zero-eigenvalue Jordan block in the
source. The stabilized power is an idempotent of trace one, hence a rank-one
projector with normalized left and right fixed witnesses.

## Main definitions

* `Matrix.StabilizedRankOneData` packages a positive stabilization exponent,
  its bound, normalized outer-product witnesses, and stabilization of all
  later powers.

## Main results

* `MPOTensor.IsMPU.normalizedTransferStabilization` eliminates the zero-primary
  component after the explicit exponent `D * D - 1` when `1 < D`.
* `MPOTensor.IsMPU.normalizedTransferStabilization_fin_one` treats the
  one-dimensional bond space separately.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, "Matrix Product Unitaries: Structure,
  Symmetries, and Topological Invariants", lines 397--409.
-/

open scoped Matrix BigOperators
open Polynomial

namespace Matrix

/-! ### Cayley--Hamilton elimination and rank-one factorization -/

variable {ι : Type*} [Fintype ι]

/-- If the characteristic polynomial is `X^(n-1) * (X-1)`, Cayley--Hamilton
kills the zero-primary component after exponent `n-1`.

This is the generalized-eigenspace/Jordan-elimination step used at
arXiv:1703.09188, lines 397--409, expressed without choosing a Jordan basis. -/
theorem pow_card_eq_pow_pred_of_charpoly_eq_X_pow_pred_mul_X_sub_one
    [DecidableEq ι] [Nonempty ι] (E : Matrix ι ι ℂ)
    (hchar : E.charpoly = X ^ (Fintype.card ι - 1) * (X - 1)) :
    E ^ Fintype.card ι = E ^ (Fintype.card ι - 1) := by
  have hCH := E.aeval_self_charpoly
  rw [hchar, map_mul, map_pow, aeval_X, map_sub, aeval_X, map_one] at hCH
  have hn : Fintype.card ι - 1 + 1 = Fintype.card ι := by
    have : 0 < Fintype.card ι := Fintype.card_pos
    omega
  rw [mul_sub, mul_one, ← pow_succ, hn] at hCH
  exact sub_eq_zero.mp hCH

/-- A complex idempotent matrix of trace one is an outer product.

The proof identifies the range of the idempotent with a one-dimensional
subspace and factors its columns through a generator. It is the matrix
factorization used after zero-primary elimination in arXiv:1703.09188,
lines 397--409. -/
theorem exists_eq_vecMulVec_of_mul_self_eq_self_of_trace_eq_one
    {T : Matrix ι ι ℂ} (hTT : T * T = T) (hTrace : Matrix.trace T = 1) :
    ∃ a b : ι → ℂ, T = Matrix.vecMulVec a b := by
  classical
  let f : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) := Matrix.toLin' T
  have hf : IsIdempotentElem f := by
    change Matrix.toLin' T ∘ₗ Matrix.toLin' T = Matrix.toLin' T
    rw [← Matrix.toLin'_mul, hTT]
  have hrank : Module.finrank ℂ (LinearMap.range f) = 1 := by
    have h := (LinearMap.isProj_range_iff_isIdempotentElem f).2 hf |>.trace
    rw [Matrix.trace_toLin'_eq, hTrace] at h
    exact_mod_cast h.symm
  rcases finrank_eq_one_iff'.mp hrank with ⟨u, _hu, hspan⟩
  let b : ι → ℂ := fun j ↦
    Classical.choose (hspan ⟨f (Pi.single j 1), LinearMap.mem_range_self f _⟩)
  refine ⟨u.1, b, ?_⟩
  ext i j
  have hb := Classical.choose_spec
    (hspan ⟨f (Pi.single j 1), LinearMap.mem_range_self f _⟩)
  have hb' := congrArg (fun x : LinearMap.range f ↦ x.1 i) hb
  have heval : f (Pi.single j 1) i = T i j := by
    simp [f, Matrix.toLin'_apply]
  change Classical.choose _ * u.1 i = f (Pi.single j 1) i at hb'
  rw [heval] at hb'
  simpa [b, Matrix.vecMulVec_apply, mul_comm] using hb'.symm

/-! ### Reusable stabilized-transfer package -/

/-- Data witnessing that a matrix stabilizes at a bounded positive power to a
normalized rank-one projector.

Here `right ⬝ᵥ left = 1` is the normalization `(Φ|ρ) = 1`, up to the harmless
commutation of complex scalars in the coordinate dot product. The equality
`power_eq` is the source formula `E^J = |ρ)(Φ|`.

Source: arXiv:1703.09188, lines 397--409. -/
structure StabilizedRankOneData [DecidableEq ι] (E : Matrix ι ι ℂ) (bound : ℕ) where
  /-- The blocking exponent that eliminates the zero-primary component. -/
  exponent : ℕ
  /-- The source blocking exponent is positive. -/
  exponent_pos : 0 < exponent
  /-- The exponent lies below the advertised ambient-dimensional bound. -/
  exponent_le : exponent ≤ bound
  /-- The normalized right fixed witness `ρ`. -/
  right : ι → ℂ
  /-- The normalized left fixed witness `Φ`. -/
  left : ι → ℂ
  /-- Normalization of the left/right pairing. -/
  pairing_eq_one : right ⬝ᵥ left = 1
  /-- The stabilized power is the outer product `|ρ)(Φ|`. -/
  power_eq : E ^ exponent = Matrix.vecMulVec right left
  /-- Every later power equals the stabilized projector. -/
  stable : ∀ k, exponent ≤ k → E ^ k = E ^ exponent

namespace StabilizedRankOneData

variable [DecidableEq ι] {E : Matrix ι ι ℂ} {bound : ℕ}

/-- The stabilized transfer matrix is idempotent. -/
theorem projector_idempotent (data : StabilizedRankOneData E bound) :
    E ^ data.exponent * E ^ data.exponent = E ^ data.exponent := by
  rw [← pow_add]
  exact data.stable _ (Nat.le_add_right _ _)

/-- The right witness is fixed by the original transfer matrix. -/
theorem right_fixed (data : StabilizedRankOneData E bound) :
    E *ᵥ data.right = data.right := by
  have hPright : E ^ data.exponent *ᵥ data.right = data.right := by
    rw [data.power_eq, Matrix.vecMulVec_mulVec, dotProduct_comm,
      data.pairing_eq_one]
    simp
  calc
    E *ᵥ data.right = E *ᵥ (E ^ data.exponent *ᵥ data.right) := by rw [hPright]
    _ = (E * E ^ data.exponent) *ᵥ data.right := by rw [Matrix.mulVec_mulVec]
    _ = E ^ (data.exponent + 1) *ᵥ data.right := by rw [← pow_succ']
    _ = E ^ data.exponent *ᵥ data.right := by
      rw [data.stable _ (Nat.le_succ data.exponent)]
    _ = data.right := hPright

/-- The left witness is fixed by the original transfer matrix. -/
theorem left_fixed (data : StabilizedRankOneData E bound) :
    Matrix.vecMul data.left E = data.left := by
  have hleftP : Matrix.vecMul data.left (E ^ data.exponent) = data.left := by
    rw [data.power_eq, Matrix.vecMul_vecMulVec, dotProduct_comm,
      data.pairing_eq_one, one_smul]
  calc
    Matrix.vecMul data.left E =
        Matrix.vecMul (Matrix.vecMul data.left (E ^ data.exponent)) E := by rw [hleftP]
    _ = Matrix.vecMul data.left (E ^ data.exponent * E) := by
      rw [Matrix.vecMul_vecMul]
    _ = Matrix.vecMul data.left (E ^ (data.exponent + 1)) := by rw [pow_succ]
    _ = Matrix.vecMul data.left (E ^ data.exponent) := by
      rw [data.stable _ (Nat.le_succ data.exponent)]
    _ = data.left := hleftP

/-- Any normalized pair of left and right fixed witnesses gives the same
outer-product factorization of the stabilized projector. -/
theorem power_eq_vecMulVec_of_fixed (data : StabilizedRankOneData E bound)
    (right' left' : ι → ℂ) (hpair : left' ⬝ᵥ right' = 1)
    (hright : E *ᵥ right' = right') (hleft : Matrix.vecMul left' E = left') :
    E ^ data.exponent = Matrix.vecMulVec right' left' := by
  have hright_pow : E ^ data.exponent *ᵥ right' = right' := by
    induction data.exponent with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hright]
  have hleft_pow : Matrix.vecMul left' (E ^ data.exponent) = left' := by
    induction data.exponent with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hleft]
  have hright' : (data.left ⬝ᵥ right') • data.right = right' := by
    rw [data.power_eq, Matrix.vecMulVec_mulVec] at hright_pow
    simpa [Algebra.smul_def, dotProduct_comm] using hright_pow
  have hleft' : (left' ⬝ᵥ data.right) • data.left = left' := by
    rw [data.power_eq, Matrix.vecMul_vecMulVec] at hleft_pow
    exact hleft_pow
  rw [data.power_eq]
  rw [← hright', ← hleft'] at hpair ⊢
  have hscalar :
      (data.left ⬝ᵥ right') * (left' ⬝ᵥ data.right) = 1 := by
    simpa [dotProduct_comm, mul_comm, mul_left_comm, mul_assoc,
      data.pairing_eq_one] using hpair
  ext i j
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  calc
    data.right i * data.left j =
        ((data.left ⬝ᵥ right') * (left' ⬝ᵥ data.right)) *
          (data.right i * data.left j) := by rw [hscalar, one_mul]
    _ = (data.left ⬝ᵥ right') * data.right i *
          ((left' ⬝ᵥ data.right) * data.left j) := by ring

/-- Construct stabilized rank-one data from one equality of consecutive powers
and the trace-one normalization at that power. -/
noncomputable def of_power_succ_eq [Nonempty ι]
    (J bound : ℕ) (hJpos : 0 < J) (hJle : J ≤ bound)
    (hstep : E ^ (J + 1) = E ^ J) (htrace : Matrix.trace (E ^ J) = 1) :
    StabilizedRankOneData E bound := by
  have hstable : ∀ k, J ≤ k → E ^ k = E ^ J := by
    intro k hk
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
    induction t with
    | zero => rfl
    | succ t iht =>
      rw [Nat.add_succ, pow_succ, iht (Nat.le_add_right _ _), ← pow_succ, hstep]
  have hidem : E ^ J * E ^ J = E ^ J := by
    rw [← pow_add]
    exact hstable _ (Nat.le_add_right _ _)
  let hex := Matrix.exists_eq_vecMulVec_of_mul_self_eq_self_of_trace_eq_one hidem htrace
  let right := Classical.choose hex
  let left := Classical.choose (Classical.choose_spec hex)
  have hfac : E ^ J = Matrix.vecMulVec right left :=
    Classical.choose_spec (Classical.choose_spec hex)
  refine ⟨J, hJpos, hJle, right, left, ?_, hfac, hstable⟩
  rw [← Matrix.trace_vecMulVec, ← hfac]
  exact htrace

end StabilizedRankOneData
end Matrix

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
      (transferMatrix (MPSTensor.transferMap U.normalizedFlattening)) (D * D - 1) := by
  let E := transferMatrix (MPSTensor.transferMap U.normalizedFlattening)
  have hD2 : 2 ≤ D := by omega
  have hDD : 4 ≤ D * D := Nat.mul_le_mul hD2 hD2
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
theorem IsMPU.exists_normalizedTransfer_stabilizes_to_rankOne
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U) (hD : 1 < D) :
    ∃ J : ℕ, 0 < J ∧ J ≤ D * D - 1 ∧
      ∃ ρ Φ : Fin D × Fin D → ℂ,
        Φ ⬝ᵥ ρ = 1 ∧
        transferMatrix (MPSTensor.transferMap U.normalizedFlattening) *ᵥ ρ = ρ ∧
        Matrix.vecMul Φ
          (transferMatrix (MPSTensor.transferMap U.normalizedFlattening)) = Φ ∧
        transferMatrix (MPSTensor.transferMap U.normalizedFlattening) ^ J =
          Matrix.vecMulVec ρ Φ ∧
        ∀ k, J ≤ k →
          transferMatrix (MPSTensor.transferMap U.normalizedFlattening) ^ k =
            transferMatrix (MPSTensor.transferMap U.normalizedFlattening) ^ J := by
  let data := hU.normalizedTransferStabilization hD
  refine ⟨data.exponent, data.exponent_pos, data.exponent_le,
    data.right, data.left, ?_, data.right_fixed, data.left_fixed,
    data.power_eq, data.stable⟩
  rw [dotProduct_comm]
  exact data.pairing_eq_one

/-- On a chosen reduced CPSV canonical-form-II representative, the
stabilized factorization uses the representative's normalized fixed witnesses
`ρ` and `Φ` themselves.

**Scope restriction (chosen reduced CFII representative):** The full-active-support
premise selects the reduced representative intended in arXiv:1703.09188,
lines 397--405. The formalization does not claim that a bare ambient `IsMPU`
representative is normal or already in CFII. See
`docs/paper-gaps/mpu_canonical_form_full_support.tex`. -/
theorem IsMPU.normalizedTransfer_pow_eq_vecMulVec_of_reduced_cpsvCFII
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U) (hD : 1 < D)
    (cfii : MPSTensor.CPSVCanonicalFormIIData U.normalizedFlattening)
    (_hfull : ∑ k : cfii.toCPSVCanonicalFormData.Active,
      cfii.dim k.1 = D)
    (ρ Φ : Fin D × Fin D → ℂ)
    (hpair : Φ ⬝ᵥ ρ = 1)
    (hright : transferMatrix (MPSTensor.transferMap U.normalizedFlattening) *ᵥ ρ = ρ)
    (hleft : Matrix.vecMul Φ
      (transferMatrix (MPSTensor.transferMap U.normalizedFlattening)) = Φ) :
    transferMatrix (MPSTensor.transferMap U.normalizedFlattening) ^ (D * D - 1) =
      Matrix.vecMulVec ρ Φ := by
  exact (hU.normalizedTransferStabilization hD).power_eq_vecMulVec_of_fixed
    ρ Φ hpair hright hleft

/-- In bond dimension one, the normalized transfer matrix is already the
identity and stabilizes at exponent one. This separate statement is necessary
because no positive exponent can satisfy `J ≤ D * D - 1 = 0`.

Source: arXiv:1703.09188, lines 397--409, specialized to `D = 1`. -/
noncomputable def IsMPU.normalizedTransferStabilization_fin_one
    [NeZero d] {U : MPOTensor d 1} (hU : IsMPU U) :
    Matrix.StabilizedRankOneData
      (transferMatrix (MPSTensor.transferMap U.normalizedFlattening)) 1 := by
  let E := transferMatrix (MPSTensor.transferMap U.normalizedFlattening)
  have hchar : E.charpoly = X ^ (Fintype.card (Fin 1 × Fin 1) - 1) * (X - 1) := by
    simpa [E, Fintype.card_prod, Fintype.card_fin] using hU.normalizedFlattening_charpoly
  have hpow :=
    Matrix.pow_card_eq_pow_pred_of_charpoly_eq_X_pow_pred_mul_X_sub_one E hchar
  have hE : E = 1 := by
    simpa [Fintype.card_prod, Fintype.card_fin] using hpow
  have hE' : transferMatrix (MPSTensor.transferMap U.normalizedFlattening) = 1 := by
    simpa [E] using hE
  apply Matrix.StabilizedRankOneData.of_power_succ_eq 1 1 Nat.zero_lt_one le_rfl
  · rw [hE']
    simp
  · rw [hE']
    simp

end MPOTensor
