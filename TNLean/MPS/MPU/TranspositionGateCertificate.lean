/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TimeReversalGateCertificate
import TNLean.Algebra.UnitPhaseScalar
import TNLean.MPS.MPU.ConjugationSymmetry

/-!
# The local certificate for transposition, without canonical form

Lemma `prop:local-char-transposition` of arXiv:1703.09188 (lines 1258--1288) characterizes
transposition by a local phase equation on the gates of a standard form. Its sufficiency proof
runs as for time reversal (lines 1277--1282, by analogy with lines 1214--1237). It uses only two
facts about the standard-form circuit:

* its transpose is the circuit of the gates `(vᵀ, uᵀ)`, translated by one site
  (`MPOTensor.twoSiteCircuit_transpose`);
* the periodic operator of a two-site block is invariant under that translation
  (`MPOTensor.mpo_blockTwo_submatrix_shifted`).

The local equation `A = c (x ⊗ xᵀ) Bᵀ` with `|c| = 1` relates `(Bᵀ, Aᵀ)` to `(A, B)` by a gate
gauge, so the operator equals its transpose. No canonical form or source factors of the tensor
are used.

## Main results

* `MPOTensor.TwoSiteStandardFormData.mpo_blockTwo_eq_transpose_of_local_phase`: the
  certificate for any standard form of a two-site block.
* `MPOTensor.mpo_even_eq_transpose_of_blockTwo`: the passage to even rings of the original
  tensor.
-/

open scoped Matrix Kronecker
open Matrix

namespace MPOTensor

variable {d ℓ r N : ℕ}

/-- A local phase `A = c (x ⊗ xᵀ) Bᵀ` with `|c| = 1` gives unitaries `X = x†` and
`Y = c̄ x̄` with `Bᵀ = (X ⊗ Y) A` and `Aᵀ = B (Y† ⊗ X†)`: the gate gauges relating the
standard form `(A, B)` to the transposed standard form `(Bᵀ, Aᵀ)`. Source: CPSV17, the
"(if)" case of the proof of `PropChiral`, lines 1230–1237, which
`prop:local-char-transposition` invokes by analogy at lines 1277–1282. -/
theorem transpose_gate_gauges_of_local_phase
    {q : ℕ} {P : Type*} (A : Matrix (Fin q × Fin q) P ℂ)
    (B : Matrix P (Fin q × Fin q) ℂ)
    (c : ℂ) (hc : ‖c‖ = 1) (x : Matrix.unitaryGroup (Fin q) ℂ)
    (hlocal : A = c • ((x : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ
      (x : Matrix (Fin q) (Fin q) ℂ)ᵀ) * Bᵀ) :
    ∃ X Y : Matrix.unitaryGroup (Fin q) ℂ,
      Bᵀ = ((X : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ
        (Y : Matrix (Fin q) (Fin q) ℂ)) * A ∧
      Aᵀ = B * ((Y : Matrix (Fin q) (Fin q) ℂ)ᴴ ⊗ₖ
        (X : Matrix (Fin q) (Fin q) ℂ)ᴴ) := by
  have hcc : c * star c = 1 := Complex.mul_star_self_of_norm_eq_one hc
  have hcc' : star c * c = 1 := Complex.star_mul_self_of_norm_eq_one hc
  let Xbar := (x : Matrix (Fin q) (Fin q) ℂ).map (starRingEnd ℂ)
  have hbar : Xbar.IsUnitaryBetween :=
    ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr x.property).map_star
  have hxt : ((x : Matrix (Fin q) (Fin q) ℂ)ᵀ).IsUnitaryBetween :=
    (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr
      (Matrix.transpose_mem_unitaryGroup_iff.mpr x.property)
  have hxtdag : (x : Matrix (Fin q) (Fin q) ℂ)ᵀᴴ = Xbar := rfl
  have hbardag : Xbarᴴ = (x : Matrix (Fin q) (Fin q) ℂ)ᵀ := by
    rw [← hxtdag, Matrix.conjTranspose_conjTranspose]
  let X := star x
  let Y : Matrix.unitaryGroup (Fin q) ℂ := ⟨star c • Xbar, by
    rw [Matrix.mem_unitaryGroup_iff']
    change (star c • Xbar)ᴴ * (star c • Xbar) = 1
    rw [Matrix.conjTranspose_smul, star_star, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hcc, one_smul]
    exact hbar.1⟩
  let K := (x : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ (x : Matrix (Fin q) (Fin q) ℂ)ᵀ
  have hK : Kᴴ * K = 1 :=
    ((Matrix.isUnitaryBetween_coe_unitaryGroup x).kronecker _ _ hxt).1
  have hXY : ((X : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ
      (Y : Matrix (Fin q) (Fin q) ℂ)) = star c • Kᴴ := by
    change (x : Matrix (Fin q) (Fin q) ℂ)ᴴ ⊗ₖ (star c • Xbar) = _
    rw [Matrix.kronecker_smul]
    simp only [K, Matrix.conjTranspose_kronecker, hxtdag]
  have hYX : ((Y : Matrix (Fin q) (Fin q) ℂ)ᴴ ⊗ₖ
      (X : Matrix (Fin q) (Fin q) ℂ)ᴴ) =
      c • ((x : Matrix (Fin q) (Fin q) ℂ)ᵀ ⊗ₖ (x : Matrix (Fin q) (Fin q) ℂ)) := by
    change (star c • Xbar)ᴴ ⊗ₖ (x : Matrix (Fin q) (Fin q) ℂ)ᴴᴴ = _
    rw [Matrix.conjTranspose_smul, star_star, hbardag,
      Matrix.conjTranspose_conjTranspose, Matrix.smul_kronecker]
  refine ⟨X, Y, ?_, ?_⟩
  · rw [hXY, hlocal]
    change Bᵀ = (star c • Kᴴ) * ((c • K) * Bᵀ)
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← Matrix.mul_assoc, hK, Matrix.one_mul, hcc', one_smul]
  · have h := congrArg Matrix.transpose hlocal
    simp only [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_transpose,
      ← Matrix.kroneckerMap_transpose] at h
    simpa only [hYX] using h

/-- **The transpose of a standard-form circuit.** The transpose of the circuit with unshifted
gate `u` and shifted gate `v` is the circuit with unshifted gate `vᵀ` and shifted gate `uᵀ`, read
on the pair configuration translated by one site. Source: arXiv:1703.09188,
`prop:local-char-transposition`, lines 1277--1282, by analogy with `UUdaggertrick`,
lines 1214--1226. -/
theorem twoSiteCircuit_transpose [NeZero N]
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) :
    (twoSiteShiftedLayer (N := N) v * twoSiteUnshiftedLayer (N := N) u)ᵀ =
      (twoSiteShiftedLayer (N := N) uᵀ * twoSiteUnshiftedLayer (N := N) vᵀ).submatrix
        (twoSiteShiftedPairEquiv (ℓ := d) (r := d))
        (twoSiteShiftedPairEquiv (ℓ := d) (r := d)) := by
  ext a b
  simp only [transpose_apply, mul_apply, submatrix_apply]
  rw [← (twoSiteShiftedPairEquiv (N := N) (ℓ := ℓ) (r := r)).symm.sum_comp]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [mul_comm]
  congr 1
  · simp only [twoSiteShiftedLayer, twoSiteUnshiftedLayer, transpose_apply]
    refine (Fintype.prod_equiv (Equiv.addRight 1) _ _ fun x ↦ ?_).symm
    simp [twoSiteShiftedPairEquiv]
  · simp only [twoSiteShiftedLayer, twoSiteUnshiftedLayer, transpose_apply]
    refine Finset.prod_congr rfl fun x _ ↦ ?_
    simp [twoSiteShiftedPairEquiv]

/-- **Local certificate for transposition.** Let the two-site block of `V` have a standard form
with gates `A, B` of equal ranks, satisfying the local phase equation `A = c (x ⊗ xᵀ) Bᵀ` with
`|c| = 1`. Then the periodic operator of the two-site block equals its transpose on every ring.

The transpose of the standard-form circuit is the circuit of the gates `(Bᵀ, Aᵀ)` translated by
one site; the local equation relates these gates to `(A, B)` by a gate gauge, and the operator of
a two-site block is invariant under that translation.

Source: arXiv:1703.09188, `prop:local-char-transposition` and `UUtransposetrick`,
lines 1266--1282. -/
theorem TwoSiteStandardFormData.mpo_blockTwo_eq_transpose_of_local_phase {D q : ℕ}
    {V : MPOTensor d D} {A : Matrix (Fin q × Fin q) (Fin d × Fin d) ℂ}
    {B : Matrix (Fin d × Fin d) (Fin q × Fin q) ℂ} (S : TwoSiteStandardFormData (blockTwo V) A B)
    (c : ℂ) (hc : ‖c‖ = 1) (x : Matrix.unitaryGroup (Fin q) ℂ)
    (hlocal : A = c • ((x : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ (x : Matrix (Fin q) (Fin q) ℂ)ᵀ) * Bᵀ)
    (N : ℕ) [NeZero N] :
    mpo (blockTwo V) N = (mpo (blockTwo V) N)ᵀ := by
  have hS := S.mpo_eq_shifted_mul_unshifted (N := N) _ A B
  obtain ⟨X, Y, h₁, h₂⟩ := transpose_gate_gauges_of_local_phase A B c hc x hlocal
  have hC : (twoSiteShiftedLayer (N := N) B * twoSiteUnshiftedLayer (N := N) A)ᵀ =
      twoSiteShiftedLayer (N := N) B * twoSiteUnshiftedLayer (N := N) A := by
    rw [twoSiteCircuit_transpose, h₁, h₂, ← Matrix.star_eq_conjTranspose,
      ← Matrix.star_eq_conjTranspose, twoSiteCircuit_eq_of_gate_gauges, ← hS,
      mpo_blockTwo_submatrix_shifted]
  apply (Matrix.reindex (twoSitePairConfigEquiv d N).symm
    (twoSitePairConfigEquiv d N).symm).injective
  rw [← transpose_reindex, hS, hC]

/-- Transpose symmetry of the two-site block's operator on `m` sites is transpose symmetry of the
original operator on `2m` sites. -/
theorem mpo_even_eq_transpose_of_blockTwo {D : ℕ} {V : MPOTensor d D}
    {m : ℕ} (h : mpo (blockTwo V) m = (mpo (blockTwo V) m)ᵀ) :
    mpo V (m + m) = (mpo V (m + m))ᵀ := by
  rw [mpo_blockTwo_eq_reindex_blockTensor, transpose_reindex] at h
  have h' := (Matrix.reindex _ _).injective h
  rw [mpo_blockTensor_eq_reindex, transpose_reindex] at h'
  have h'' := (Matrix.reindex _ _).injective h'
  rwa [Nat.mul_two] at h''

end MPOTensor
