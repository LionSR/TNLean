/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.IrreducibleAction
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.FundamentalTheorem.Arbitrary.Basic
import TNLean.MPS.FundamentalTheorem.Arbitrary.FlagExistence
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlock
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace

/-!
# The asymmetric fundamental theorem as a corollary

Let `B'` be in the canonical form of arXiv:1606.00608 (`CPSVCanonicalFormData`), with normal blocks
`A_k` of positive bond dimensions `D_k` and nonzero weights `μ_k`. A tensor `B` has the same states
as `B'` exactly when
`B` has a multi-block reduction onto the weighted blocks `(μ_k A_k)_k`, and it then has
`D_B - ∑_k D_k` zero blocks. For a family of normal blocks of positive
bond dimension, the word traces of `B` are the sums of the word traces of the blocks exactly when
`B` has a reduction onto the family. Both follow from the theorem for admissible blocks
because normal blocks of positive bond dimension are admissible.

The fundamental theorem for normal blocks is
`MultiBlockCompression.z_eq_and_exists_equiv_isGaugeRelated`; the one-block theorem for a normal
target is the one-block theorem for admissible targets, because normal blocks of positive bond
dimension are admissible.

## Main results

* `MPSTensor.CPSVCanonicalFormData.sameMPV₂Pos_iff_exists_multiBlockCompression_z_eq`.
* `MPSTensor.forall_trace_evalWord_eq_sum_iff_nonempty_multiBlockCompression_of_isNormal`.
-/

namespace MPSTensor

variable {d DB : ℕ}

/-- The word traces of a tensor in canonical form are the sums of the word traces of its
weighted blocks (`mpv_eq_sum_weight_pow`). -/
private theorem trace_evalWord_eq_sum_smul_blocks {D : ℕ} {B' : MPSTensor d D}
    (data : CPSVCanonicalFormData B') {w : List (Fin d)} (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord B' w) =
      ∑ k, Matrix.trace (Kraus.evalWord (data.weights k • data.blocks k) w) := by
  have h := data.mpv_eq_sum_weight_pow (List.length_pos_iff.2 hw) w.get
  simp only [mpv_eq, coeff_eq, List.ofFn_get] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show data.weights k • data.blocks k = fun i => data.weights k • data.blocks k i from rfl,
    Kraus.evalWord_smul, Matrix.trace_smul, smul_eq_mul]

/-- **One tensor in canonical form**. If `B'` is in the canonical form of
arXiv:1606.00608 with normal blocks `A_k` and nonzero weights `μ_k`, a tensor `B` has the same
states as `B'` if and only if `B` has a multi-block reduction onto `(μ_k A_k)_k`; it then has `D_B -
∑_k D_k` zero blocks. -/
theorem CPSVCanonicalFormData.sameMPV₂Pos_iff_exists_multiBlockCompression_z_eq {D : ℕ}
    {B' : MPSTensor d D} (data : CPSVCanonicalFormData B') (B : MPSTensor d DB) :
    SameMPV₂Pos B B' ↔
      ∃ P : MultiBlockCompression (D := data.dim) B Finset.univ
          (fun k => data.weights k • data.blocks k),
        P.z = DB - ∑ k, data.dim k := by
  have hirr : ∀ k ∈ (Finset.univ : Finset (Fin data.r)),
      Matrix.IsIrreducibleAction (data.weights k • data.blocks k) := fun k _ =>
    isIrreducibleAction_smul ((Kraus.isIrreducibleAction_iff_isIrreducibleFamily _).2
      (data.blocks_normal k).no_invariant_proj) (data.weights_ne_zero k)
  have hlet : ∀ k ∈ (Finset.univ : Finset (Fin data.r)),
      ∃ i, (data.weights k • data.blocks k) i ≠ 0 := fun k _ => by
    have : NeZero (data.dim k) := ⟨(data.dim_pos k).ne'⟩
    exact exists_smul_apply_ne_zero (exists_ne_zero_of_isNormal (data.blocks_normal k).isNormal)
      (data.weights_ne_zero k)
  refine ⟨fun h => ?_, fun ⟨P, _⟩ => ?_⟩
  · exact exists_multiBlockCompression_z_eq_of_isIrreducibleAction Finset.univ _ hirr hlet B
      fun w hw => (h.trace_evalWord w hw).trans (trace_evalWord_eq_sum_smul_blocks data hw)
  · exact sameMPV₂Pos_iff_forall_trace_evalWord_eq.2 fun w hw =>
      (P.trace_evalWord_eq_sum w hw).trans (trace_evalWord_eq_sum_smul_blocks data hw).symm

/-- **Existence for normal blocks**. For a finite family of normal tensors
`C_s` of positive bond dimensions, the word traces of `B` are `∑_s tr C_s^w` on every nonempty
word if and only if `B` has a multi-block reduction onto the family. -/
theorem forall_trace_evalWord_eq_sum_iff_nonempty_multiBlockCompression_of_isNormal {ι : Type*}
    [DecidableEq ι] (S : Finset ι) {D : ι → ℕ} (C : ∀ s, MPSTensor d (D s))
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s) (B : MPSTensor d DB) :
    (∀ w : List (Fin d), w ≠ [] →
        Matrix.trace (Kraus.evalWord B w) = ∑ s ∈ S, Matrix.trace (Kraus.evalWord (C s) w)) ↔
      Nonempty (MultiBlockCompression B S C) := by
  refine ⟨fun htr => ?_, fun ⟨P⟩ => P.trace_evalWord_eq_sum⟩
  obtain ⟨P, -⟩ := exists_multiBlockCompression_z_eq_of_isIrreducibleAction S C
    (fun s hs => isIrreducibleAction_of_isNormal (C s) (hC s hs) (hD s hs))
    (fun s hs => by
      have : NeZero (D s) := ⟨(hD s hs).ne'⟩
      exact exists_ne_zero_of_isNormal (hC s hs)) B htr
  exact ⟨P⟩

end MPSTensor
