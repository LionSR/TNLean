/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.IntrinsicBlockingParity
import TNLean.MPS.MPU.TimeReversalSignIntrinsic
import TNLean.MPS.MPU.SimpleBlocking
import TNLean.MPS.MPU.TwoSiteStandardForm

/-!
# Blocking parity of the time-reversal sign

Let `𝒰` be a time-reversal-invariant MPU in standard form described by `u`, `v`, and let its
`k`-site blocking `𝒰_k` be described by `u⁽ᵏ⁾`, `v⁽ᵏ⁾`. The sign `σ⁽ᵏ⁾` of equation
`UUdaggertrick-2`, computed from `u⁽ᵏ⁾` and `v⁽ᵏ⁾`, equals `σ⁽¹⁾` for odd `k` and `σ⁽²⁾` for even
`k`. This is Proposition `prop:sigma1-and-sigma2-equal` of arXiv:1703.09188, lines 1643--1655.

The tensor in standard form is read as in `PropChiral` and the trace formula
(`docs/paper-gaps/mpu_standard_form_canonical_convention.tex`): the standard form of `𝒰` has
gates on the two-site block `𝒰₂`, and the gates of `𝒰_k` are those of a standard form of
`(𝒰_k)₂`. Time-reversal invariance is self-adjointness of the operators of `𝒰₂` on rings of an
even number of two-site blocks, the hypothesis of `PropChiral` (lines 1201--1252), with lengths
counted as in `docs/paper-gaps/mpu_standard_form_parity_gap.tex`. The gates of each blocking are
supplied: the statement says "let the blocked MPU `𝒰_k` be described by `u⁽ᵏ⁾`, `v⁽ᵏ⁾`", and the
proof chooses them freely by Proposition `prop:sigma-well-defined` (lines 1657--1658).

**Local fix (proof route):** the source proves the identity by choosing the gates
`u⁽ᵏ⁾ = (1 ⊗ v^{⊗(k-1)} ⊗ 1) u^{⊗k}`, `v⁽ᵏ⁾ = 1^{⊗(k-1)} ⊗ v ⊗ 1^{⊗(k-1)}` and unwinding the
local relations, `σ⁽ᵏ⁾ = σ⁽¹⁾ ζ^{k-1}` (lines 1657--1732). Here the sign of every standard form
is identified with the intrinsic trace of the blocked periodic operators
(`TwoSiteStandardFormData.timeReversalSign_eq_intrinsic`), and the odd and even pattern is the
intrinsic blocking parity `IsMPU.intrinsic_blocking_trace_parity`. Statement and hypotheses are
the source's. Documented in `docs/paper-gaps/mpu_time_reversal_blocking_parity_route.tex`.

## Main results

* `MPOTensor.intrinsicTimeReversalSign_reindexPhysical`: the intrinsic trace sign is unchanged by
  a sitewise relabelling of the physical index.
* `MPOTensor.TwoSiteStandardFormData.timeReversalSign_blocking_parity`: the proposition.
-/

open scoped Matrix Kronecker

namespace MPOTensor

/-- The intrinsic trace sign is unchanged by a sitewise relabelling of the physical index: the
exchange of the two sites commutes with the same relabelling on both.

Source: arXiv:1703.09188, `eq:sigma-from-trace` and `prop:sigma-well-defined`,
lines 1595--1631. -/
theorem intrinsicTimeReversalSign_reindexPhysical {m m' D : ℕ} (e : Fin m' ≃ Fin m)
    (W : MPOTensor m D) :
    intrinsicTimeReversalSign (reindexPhysical e W) = intrinsicTimeReversalSign W := by
  have hm : m' = m := by simpa using Fintype.card_congr e
  subst hm
  rw [intrinsicTimeReversalSign, intrinsicTimeReversalSign, timeReversalPeriodicTrace,
    timeReversalPeriodicTrace, mpo_reindexPhysical]
  let P : Fin m' × Fin m' ≃ Fin m' × Fin m' := Equiv.prodCongr e e
  have hS : Matrix.swapMatrix m' = Matrix.reindex P.symm P.symm (Matrix.swapMatrix m') := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.swapMatrix_apply, P,
      Equiv.symm_symm, Equiv.prodCongr_apply, Prod.map, EmbeddingLike.apply_eq_iff_eq]
  have hM : Matrix.reindex (finTwoArrowEquiv (Fin m')) (finTwoArrowEquiv (Fin m'))
      (Matrix.reindex (reindexPhysicalConfigEquiv 2 e).symm (reindexPhysicalConfigEquiv 2 e).symm
        (mpo W 2)) =
      Matrix.reindex P.symm P.symm
        (Matrix.reindex (finTwoArrowEquiv (Fin m')) (finTwoArrowEquiv (Fin m')) (mpo W 2)) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, P, Equiv.prodCongr_symm,
      Equiv.symm_symm, Equiv.prodCongr_apply, Prod.map]
    congr 1 <;> funext t <;> fin_cases t <;> rfl
  rw [hM]
  congr 1
  set X := Matrix.reindex (finTwoArrowEquiv (Fin m')) (finTwoArrowEquiv (Fin m')) (mpo W 2)
  calc Matrix.trace (Matrix.swapMatrix m' * Matrix.reindex P.symm P.symm X)
      = Matrix.trace (Matrix.reindex P.symm P.symm (Matrix.swapMatrix m') *
          Matrix.reindex P.symm P.symm X) := by rw [← hS]
    _ = Matrix.trace (Matrix.reindex P.symm P.symm (Matrix.swapMatrix m' * X)) := by
        simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    _ = Matrix.trace (Matrix.swapMatrix m' * X) := Matrix.trace_reindex _ _

/-- **Blocking parity of the time-reversal sign.** Let `𝒰 = V` be a time-reversal-invariant MPU in
standard form described by `u`, `v`: the two-site block `V₂` carries standard-form data with
gates `u`, `v`, and the operators of `V₂` are self-adjoint on rings of an even number of
two-site blocks. For a blocking length `k > 0`, let the blocked MPU `𝒰_k` be described by
`u⁽ᵏ⁾`, `v⁽ᵏ⁾`, gates of a standard form of the two-site block of `V_k`, and let `u⁽²⁾`, `v⁽²⁾`
describe `𝒰₂`. With `σ⁽ᵏ⁾` the sign obtained from `u⁽ᵏ⁾` and `v⁽ᵏ⁾` by equation
`UUdaggertrick-2`,
`σ⁽ᵏ⁾ = σ⁽¹⁾` for odd `k` and `σ⁽ᵏ⁾ = σ⁽²⁾` for even `k`. No equality of `σ⁽¹⁾` and `σ⁽²⁾` is
asserted.

The time-reversal hypothesis is that of `PropChiral` (arXiv:1703.09188, lines 1201--1252), on
rings counted in two-site blocks (`docs/paper-gaps/mpu_standard_form_parity_gap.tex`). It
concerns `V₂`, not `V`: self-adjointness at every even number of original sites is a stronger
hypothesis, and under it all the signs `σ⁽ᵏ⁾` would agree with `σ⁽¹⁾`.

The proof follows the route recorded in the module docstring.

Source: arXiv:1703.09188, Proposition `prop:sigma1-and-sigma2-equal`, lines 1643--1655, with
the free choice of the blocked gates at lines 1657--1658. -/
theorem TwoSiteStandardFormData.timeReversalSign_blocking_parity {d D : ℕ} {V : MPOTensor d D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData (blockTwo V) u v)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo (blockTwo V) N = (mpo (blockTwo V) N)ᴴ)
    {u₂ v₂ : Matrix (Fin (Kraus.blockPhysDim d 2) × Fin (Kraus.blockPhysDim d 2))
      (Fin (Kraus.blockPhysDim d 2) × Fin (Kraus.blockPhysDim d 2)) ℂ}
    (S₂ : TwoSiteStandardFormData (blockTwo (MPOTensor.blockTensor V 2)) u₂ v₂)
    (k : ℕ) (hk : 0 < k)
    {uₖ vₖ : Matrix (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k))
      (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ}
    (Sₖ : TwoSiteStandardFormData (blockTwo (MPOTensor.blockTensor V k)) uₖ vₖ) :
    (Odd k → timeReversalSign uₖ vₖ = timeReversalSign u v) ∧
      (Even k → timeReversalSign uₖ vₖ = timeReversalSign u₂ v₂) := by
  have : NeZero D := ⟨S.bond_pos.ne'⟩
  have : NeZero (Kraus.blockPhysDim d 2) := ⟨by
    rw [Kraus.blockPhysDim_eq_pow]
    exact pow_ne_zero _ S.phys_pos.ne'⟩
  -- The two-site block is the length-two blocking after relabelling each physical index.
  have hW : blockTwo V = reindexPhysical (twoSiteBlockEquiv d) (MPOTensor.blockTensor V 2) :=
    blockTwo_eq_blockTensor_reindex V
  have hU :
      MPOTensor.blockTensor V 2 = reindexPhysical (twoSiteBlockEquiv d).symm (blockTwo V) := by
    rw [hW]
    funext i j
    simp [reindexPhysical]
  have hMPU : IsMPU (MPOTensor.blockTensor V 2) := by
    rw [hU]
    exact (TwoSiteStandardFormData.isMPU _ _ _ S).reindexPhysical _
  have hTR₂ : ∀ N : ℕ, 1 < N → Even N →
      mpo (MPOTensor.blockTensor V 2) N = (mpo (MPOTensor.blockTensor V 2) N)ᴴ := by
    intro N hN heven
    rw [hU, mpo_reindexPhysical, Matrix.conjTranspose_reindex, ← hTR N hN heven]
  -- Every sign is an intrinsic trace of a direct blocking of `V`.
  have hblock : ∀ n : ℕ, intrinsicTimeReversalSign
      (MPOTensor.blockTensor (MPOTensor.blockTensor V 2) n) =
        intrinsicTimeReversalSign (MPOTensor.blockTensor V (2 * n)) := fun n ↦ by
    rw [← reindexPhysical_blockTensor_blockTensor V 2 n, intrinsicTimeReversalSign_reindexPhysical]
  have hsign : ∀ (n : ℕ) {a b : Matrix (Fin (Kraus.blockPhysDim d n) ×
      Fin (Kraus.blockPhysDim d n)) (Fin (Kraus.blockPhysDim d n) ×
      Fin (Kraus.blockPhysDim d n)) ℂ},
      TwoSiteStandardFormData (blockTwo (MPOTensor.blockTensor V n)) a b →
        timeReversalSign a b = intrinsicTimeReversalSign (MPOTensor.blockTensor V (2 * n)) := by
    intro n a b T
    rw [T.timeReversalSign_eq_intrinsic, ← reindexPhysical_blockTwo_blockTensor_two_mul V n,
      intrinsicTimeReversalSign_reindexPhysical]
  have hfirst : timeReversalSign u v = intrinsicTimeReversalSign (MPOTensor.blockTensor V 2) := by
    rw [S.timeReversalSign_eq_intrinsic, hW, intrinsicTimeReversalSign_reindexPhysical]
  obtain ⟨hodd, heven⟩ := hMPU.intrinsic_blocking_trace_parity hTR₂ k hk
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [hsign k Sₖ, ← hblock k, hodd h, hfirst]
  · rw [hsign k Sₖ, ← hblock k, heven h, hblock 2, hsign 2 S₂]

end MPOTensor
