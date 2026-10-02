/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.MinimalPhysicalCuts
import TNLean.MPS.MPDO.OperatorFromWordTrace

/-!
# Consecutive operator cut ranks of periodic MPOs

Opening a periodic virtual contraction at a physical cut leaves two virtual
indices. The actual paired-letter coefficient flattening therefore factors
through a space of dimension `D * D`. This proves the cut-rank hypothesis used
by the finite-unitary circuit construction directly for ordinary periodic
MPOs, without trace normalization, positivity, or a canonical-form assumption.
An arbitrary fixed trace boundary has the same bound. A uniform tensor with
fixed scalar open-boundary matrices instead factors through one virtual bond
and has cut rank at most `D`.

The open-boundary statements here concern a repeated square tensor with fixed
left and right scalar boundary matrices. They do not assert a theorem about
the separately defined site-dependent rectangular `OBCChainTensor`.

Sources: arXiv:2508.08160v2, `references/2508.08160/main.tex`,
`eq:U_N_hom` and lines 812--816 (opening periodic boundary with dimension
`D * D`); Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix MPSPreparation
open scoped BigOperators

namespace MPUCircuit

private def prefixTuple {p N k : ℕ} (hk : k ≤ N)
    (u : CutPrefixConfig p N k) : Fin k → Fin p :=
  fun i ↦ u ⟨⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩, i.isLt⟩

private def suffixTuple {p N k : ℕ} (v : CutSuffixConfig p N k) :
    Fin (N - k) → Fin p :=
  fun i ↦ v ⟨⟨k + i.val, by omega⟩, Nat.le_add_right k i.val⟩

private theorem ofFn_join_cut_eq_append {p N k : ℕ} (hk : k ≤ N)
    (u : CutPrefixConfig p N k) (v : CutSuffixConfig p N k) :
    List.ofFn (fun s : Fin N ↦
      if h : s.val < k then u ⟨s, h⟩ else v ⟨s, Nat.le_of_not_lt h⟩) =
      List.ofFn (prefixTuple hk u) ++ List.ofFn (suffixTuple v) := by
  rw [List.ofFn_congr (show N = k + (N - k) by omega), List.ofFn_add]
  congr 1
  · apply congrArg List.ofFn
    funext i
    simp only [Fin.val_cast, Fin.val_castLE, i.isLt, ↓reduceDIte, prefixTuple]
    apply congrArg u
    apply Subtype.ext
    apply Fin.ext
    rfl
  · apply congrArg List.ofFn
    funext i
    simp only [Fin.val_cast, Fin.val_natAdd, Nat.not_lt_of_ge (Nat.le_add_right k i.val),
      ↓reduceDIte, suffixTuple]
    apply congrArg v
    apply Subtype.ext
    apply Fin.ext
    rfl

/-- The consecutive coefficient cut rank of a uniform square tensor with an
arbitrary fixed trace boundary is at most the number of pairs of virtual
indices. No nonzero, normalization, or unitarity hypothesis is required.
Source: arXiv:2508.08160v2, `eq:U_N_hom`, and the representation step in
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutRank_traceBoundary_le {p D N k : ℕ} (A : MPSTensor p D)
    (b : Matrix (Fin D) (Fin D) ℂ) (hk : k ≤ N) :
    cutRank (fun σ : Fin N → Fin p ↦
      Matrix.trace (b * Kraus.evalWord A (List.ofFn σ))) k ≤ D * D := by
  let F : Matrix (CutPrefixConfig p N k) (Fin D × Fin D) ℂ :=
    fun u ij ↦ (b * Kraus.evalWord A (List.ofFn (prefixTuple hk u))) ij.1 ij.2
  let G : Matrix (Fin D × Fin D) (CutSuffixConfig p N k) ℂ :=
    fun ij v ↦ Kraus.evalWord A (List.ofFn (suffixTuple v)) ij.2 ij.1
  have hfactor : cutCoefficientMatrix (fun σ : Fin N → Fin p ↦
      Matrix.trace (b * Kraus.evalWord A (List.ofFn σ))) k = F * G := by
    ext u v
    simp only [cutCoefficientMatrix, ofFn_join_cut_eq_append hk u v,
      Kraus.evalWord_append, ← Matrix.mul_assoc]
    change Matrix.trace ((b * Kraus.evalWord A (List.ofFn (prefixTuple hk u))) *
        Kraus.evalWord A (List.ofFn (suffixTuple v))) =
      ∑ ij : Fin D × Fin D, (b * Kraus.evalWord A (List.ofFn (prefixTuple hk u)))
        ij.1 ij.2 * Kraus.evalWord A (List.ofFn (suffixTuple v)) ij.2 ij.1
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  change (cutCoefficientMatrix _ k).rank ≤ D * D
  rw [hfactor]
  exact (Matrix.rank_mul_le_left F G).trans (by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Matrix.rank_le_card_width F)

/-- A periodic matrix product coefficient tensor of virtual dimension `D`
has consecutive cut rank at most `D * D`, including the endpoint cuts.
Source: the periodic-to-open-boundary observation in arXiv:2508.08160v2,
lines 812--816 of `references/2508.08160/main.tex`. -/
theorem cutRank_mpv_le {p D N k : ℕ} (A : MPSTensor p D) (hk : k ≤ N) :
    cutRank (A.mpv (N := N)) k ≤ D * D := by
  change cutRank (fun σ : Fin N → Fin p ↦
    Matrix.trace (Kraus.evalWord A (List.ofFn σ))) k ≤ D * D
  simpa only [Matrix.one_mul] using cutRank_traceBoundary_le A 1 hk

/-- Pairing the output and input letters of an ordinary periodic MPO yields
exactly the periodic coefficient tensor of its doubled-letter MPS view.
The identity retains the original scalar and global phase.
Source: the periodic representation in arXiv:2508.08160v2, `eq:U_N_hom`. -/
theorem operatorCoefficientTensor_mpo_eq_mpv {d D N : ℕ} (M : MPOTensor d D) :
    operatorCoefficientTensor (M.mpo N) = M.toMPSTensor.mpv (N := N) := by
  funext σ
  simp only [operatorCoefficientTensor, MPOTensor.mpo_apply_toMPSTensor,
    MPSTensor.mpv, MPSTensor.coeff]
  congr 3
  funext s
  exact Equiv.apply_symm_apply finProdFinEquiv (σ s)

/-- Every consecutive operator cut of an ordinary periodic MPO with virtual
dimension `D` has rank at most `D * D`. This is stated for the unnormalized
operator and the coefficient flattening used by the finite-unitary circuit
theorem, without any supplied decomposition witness.
Source: arXiv:2508.08160v2, lines 812--816 of the local source, and Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutRank_operatorCoefficientTensor_mpo_le {d D N k : ℕ}
    (M : MPOTensor d D) (hk : k ≤ N) :
    cutRank (operatorCoefficientTensor (M.mpo N)) k ≤ D * D := by
  rw [operatorCoefficientTensor_mpo_eq_mpv]
  exact cutRank_mpv_le M.toMPSTensor hk

/-- A uniform square tensor contracted between fixed scalar left and right
boundary matrices has consecutive coefficient cut rank at most `D`.
The factorization crosses only the single virtual bond at the cut.
Source: the scalar open-boundary representation in arXiv:2508.08160v2,
`eq:U_N_hom`, and Section 5 of the local circuit audit. -/
theorem cutRank_openBoundary_le {p D N k : ℕ} (A : MPSTensor p D)
    (l : Matrix Unit (Fin D) ℂ) (r : Matrix (Fin D) Unit ℂ) (hk : k ≤ N) :
    cutRank (fun σ : Fin N → Fin p ↦
      (l * Kraus.evalWord A (List.ofFn σ) * r) () ()) k ≤ D := by
  let F : Matrix (CutPrefixConfig p N k) (Fin D) ℂ :=
    fun u i ↦ (l * Kraus.evalWord A (List.ofFn (prefixTuple hk u))) () i
  let G : Matrix (Fin D) (CutSuffixConfig p N k) ℂ :=
    fun i v ↦ (Kraus.evalWord A (List.ofFn (suffixTuple v)) * r) i ()
  have hfactor : cutCoefficientMatrix (fun σ : Fin N → Fin p ↦
      (l * Kraus.evalWord A (List.ofFn σ) * r) () ()) k = F * G := by
    ext u v
    simp only [cutCoefficientMatrix, ofFn_join_cut_eq_append hk u v,
      Kraus.evalWord_append, ← Matrix.mul_assoc]
    change ((l * Kraus.evalWord A (List.ofFn (prefixTuple hk u))) *
      Kraus.evalWord A (List.ofFn (suffixTuple v)) * r) () () = (F * G) u v
    rw [Matrix.mul_assoc]
    rfl
  change (cutCoefficientMatrix _ k).rank ≤ D
  rw [hfactor]
  exact (Matrix.rank_mul_le_left F G).trans (by
    simpa only [Fintype.card_fin] using Matrix.rank_le_card_width F)

/-- An MPO with an arbitrary fixed trace boundary has consecutive operator
cut rank at most `D * D`. In particular, no invertibility condition on the
boundary matrix is needed for this algebraic upper bound.
Source: arXiv:2508.08160v2, `eq:U_N_hom`, and Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutRank_operatorCoefficientTensor_traceBoundary_le {d D N k : ℕ}
    (M : MPOTensor d D) (b : Matrix (Fin D) (Fin D) ℂ) (hk : k ≤ N) :
    cutRank (operatorCoefficientTensor (fun x y : Fin N → Fin d ↦
      Matrix.trace (b * MPOTensor.evalWord M (List.ofFn x) (List.ofFn y)))) k ≤
      D * D := by
  have hcoeff : operatorCoefficientTensor (fun x y : Fin N → Fin d ↦
      Matrix.trace (b * MPOTensor.evalWord M (List.ofFn x) (List.ofFn y))) =
      fun σ : Fin N → Fin (d * d) ↦
        Matrix.trace (b * Kraus.evalWord M.toMPSTensor (List.ofFn σ)) := by
    funext σ
    exact congrArg (fun X ↦ Matrix.trace (b * X))
      (MPOTensor.evalWord_toMPSTensor_ofFn M N σ).symm
  rw [hcoeff]
  exact cutRank_traceBoundary_le M.toMPSTensor b hk

/-- A uniform MPO contracted with fixed scalar left and right boundary
matrices has consecutive operator cut rank at most its virtual dimension.
This statement concerns the displayed uniform square-tensor representation;
it does not assume or conclude unitarity.
Source: arXiv:2508.08160v2, `eq:U_N_hom`, and Section 5 of the local circuit audit. -/
theorem cutRank_operatorCoefficientTensor_openBoundary_le {d D N k : ℕ}
    (M : MPOTensor d D) (l : Matrix Unit (Fin D) ℂ)
    (r : Matrix (Fin D) Unit ℂ) (hk : k ≤ N) :
    cutRank (operatorCoefficientTensor (fun x y : Fin N → Fin d ↦
      (l * MPOTensor.evalWord M (List.ofFn x) (List.ofFn y) * r) () ())) k ≤ D := by
  have hcoeff : operatorCoefficientTensor (fun x y : Fin N → Fin d ↦
      (l * MPOTensor.evalWord M (List.ofFn x) (List.ofFn y) * r) () ()) =
      fun σ : Fin N → Fin (d * d) ↦
        (l * Kraus.evalWord M.toMPSTensor (List.ofFn σ) * r) () () := by
    funext σ
    exact congrArg (fun X ↦ (l * X * r) () ())
      (MPOTensor.evalWord_toMPSTensor_ofFn M N σ).symm
  rw [hcoeff]
  exact cutRank_openBoundary_le M.toMPSTensor l r hk

/-- The bound on all consecutive operator cuts of an ordinary periodic MPO,
in the exact form consumed by the finite-unitary circuit theorem.
Source: arXiv:2508.08160v2, lines 812--816 of the local source, and Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutRank_operatorCoefficientTensor_mpo_le_all {d D N : ℕ}
    (M : MPOTensor d D) :
    ∀ k : Fin (N + 1), cutRank (operatorCoefficientTensor (M.mpo N)) k.val ≤ D * D := by
  intro k
  exact cutRank_operatorCoefficientTensor_mpo_le M (by omega)

end MPUCircuit
