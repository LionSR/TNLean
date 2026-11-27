/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.VaryingBond.MinimalPhysicalCuts
import TNLean.MPS.Operator.PairAlphabet

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

open ManyBody (interval mem_interval cutMatrix cutMatrix_apply cutRank RegionConfig ComplConfig)

namespace MPUCircuit

private def prefixTuple {p N k : ℕ} (hk : k ≤ N)
    (u : RegionConfig (fun _ : Fin N ↦ Fin p) (interval N 0 k)) : Fin k → Fin p :=
  fun i ↦ u ⟨⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩, mem_interval.mpr ⟨Nat.zero_le _, i.isLt⟩⟩

private def suffixTuple {p N k : ℕ} (v : ComplConfig (fun _ : Fin N ↦ Fin p) (interval N 0 k)) :
    Fin (N - k) → Fin p :=
  fun i ↦ v ⟨⟨k + i.val, by omega⟩, fun h ↦ by have := (mem_interval.mp h).2; dsimp at this; omega⟩

private theorem ofFn_join_cut_eq_append {p N k : ℕ} (hk : k ≤ N)
    (u : RegionConfig (fun _ : Fin N ↦ Fin p) (interval N 0 k))
    (v : ComplConfig (fun _ : Fin N ↦ Fin p) (interval N 0 k)) :
    List.ofFn ((ManyBody.cutEquiv (fun _ : Fin N ↦ Fin p) (interval N 0 k)).symm (u, v)) =
      List.ofFn (prefixTuple hk u) ++ List.ofFn (suffixTuple v) := by
  rw [cutEquiv_symm_interval_zero, List.ofFn_congr (show N = k + (N - k) by omega), List.ofFn_add]
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
    cutRank (interval N 0 k) (fun σ : Fin N → Fin p ↦
      Matrix.trace (b * Kraus.evalWord A (List.ofFn σ))) ≤ D * D := by
  let F : Matrix (RegionConfig (fun _ : Fin N ↦ Fin p) (interval N 0 k)) (Fin D × Fin D) ℂ :=
    fun u ij ↦ (b * Kraus.evalWord A (List.ofFn (prefixTuple hk u))) ij.1 ij.2
  let G : Matrix (Fin D × Fin D) (ComplConfig (fun _ : Fin N ↦ Fin p) (interval N 0 k)) ℂ :=
    fun ij v ↦ Kraus.evalWord A (List.ofFn (suffixTuple v)) ij.2 ij.1
  have hfactor : cutMatrix (interval N 0 k) (fun σ : Fin N → Fin p ↦
      Matrix.trace (b * Kraus.evalWord A (List.ofFn σ))) = F * G := by
    ext u v
    simp only [cutMatrix_apply, ofFn_join_cut_eq_append hk u v,
      Kraus.evalWord_append, ← Matrix.mul_assoc]
    change Matrix.trace ((b * Kraus.evalWord A (List.ofFn (prefixTuple hk u))) *
        Kraus.evalWord A (List.ofFn (suffixTuple v))) =
      ∑ ij : Fin D × Fin D, (b * Kraus.evalWord A (List.ofFn (prefixTuple hk u)))
        ij.1 ij.2 * Kraus.evalWord A (List.ofFn (suffixTuple v)) ij.2 ij.1
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  change (cutMatrix (interval N 0 k) _).rank ≤ D * D
  rw [hfactor]
  exact (Matrix.rank_mul_le_left F G).trans (by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Matrix.rank_le_card_width F)

/-- A periodic matrix product coefficient tensor of virtual dimension `D`
has consecutive cut rank at most `D * D`, including the endpoint cuts.
Source: the periodic-to-open-boundary observation in arXiv:2508.08160v2,
lines 812--816 of `references/2508.08160/main.tex`. -/
theorem cutRank_mpv_le {p D N k : ℕ} (A : MPSTensor p D) (hk : k ≤ N) :
    cutRank (interval N 0 k) (A.mpv (N := N)) ≤ D * D := by
  change cutRank (interval N 0 k) (fun σ : Fin N → Fin p ↦
    Matrix.trace (Kraus.evalWord A (List.ofFn σ))) ≤ D * D
  simpa only [Matrix.one_mul] using cutRank_traceBoundary_le A 1 hk

/-- Pairing the output and input letters of an ordinary periodic MPO yields
exactly the periodic coefficient tensor of its doubled-letter MPS view.
The identity retains the original scalar and global phase.
Source: the periodic representation in arXiv:2508.08160v2, `eq:U_N_hom`. -/
theorem operatorCoefficientTensor_mpo_eq_mpv {d D N : ℕ} (M : MPOTensor d D) :
    operatorCoefficientTensor (M.mpo N) =
      MPTensor.mpv (N := N)
        (Kraus.reindexPhysical finProdFinEquiv.symm M : MPSTensor (d * d) D) := by
  funext σ
  rw [operatorCoefficientTensor, MPOTensor.mpo_apply_eq_trace_kraus_evalWord,
    MPTensor.mpv_reindexPhysical, MPTensor.mpv_eq, MPTensor.coeff_eq]

/-- Every consecutive operator cut of an ordinary periodic MPO with virtual
dimension `D` has rank at most `D * D`. This is stated for the unnormalized
operator and the coefficient flattening used by the finite-unitary circuit
theorem, without any supplied decomposition witness.
Source: arXiv:2508.08160v2, lines 812--816 of the local source, and Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutRank_operatorCoefficientTensor_mpo_le {d D N k : ℕ}
    (M : MPOTensor d D) (hk : k ≤ N) :
    cutRank (interval N 0 k) (operatorCoefficientTensor (M.mpo N)) ≤ D * D := by
  rw [operatorCoefficientTensor_mpo_eq_mpv]
  exact cutRank_mpv_le
    (Kraus.reindexPhysical finProdFinEquiv.symm M : MPSTensor (d * d) D) hk

/-- A uniform square tensor contracted between fixed scalar left and right
boundary matrices has consecutive coefficient cut rank at most `D`.
The factorization crosses only the single virtual bond at the cut.
Source: the scalar open-boundary representation in arXiv:2508.08160v2,
`eq:U_N_hom`, and Section 5 of the local circuit audit. -/
theorem cutRank_openBoundary_le {p D N k : ℕ} (A : MPSTensor p D)
    (l : Matrix Unit (Fin D) ℂ) (r : Matrix (Fin D) Unit ℂ) (hk : k ≤ N) :
    cutRank (interval N 0 k) (fun σ : Fin N → Fin p ↦
      (l * Kraus.evalWord A (List.ofFn σ) * r) () ()) ≤ D := by
  let F : Matrix (RegionConfig (fun _ : Fin N ↦ Fin p) (interval N 0 k)) (Fin D) ℂ :=
    fun u i ↦ (l * Kraus.evalWord A (List.ofFn (prefixTuple hk u))) () i
  let G : Matrix (Fin D) (ComplConfig (fun _ : Fin N ↦ Fin p) (interval N 0 k)) ℂ :=
    fun i v ↦ (Kraus.evalWord A (List.ofFn (suffixTuple v)) * r) i ()
  have hfactor : cutMatrix (interval N 0 k) (fun σ : Fin N → Fin p ↦
      (l * Kraus.evalWord A (List.ofFn σ) * r) () ()) = F * G := by
    ext u v
    simp only [cutMatrix_apply, ofFn_join_cut_eq_append hk u v,
      Kraus.evalWord_append, ← Matrix.mul_assoc]
    change ((l * Kraus.evalWord A (List.ofFn (prefixTuple hk u))) *
      Kraus.evalWord A (List.ofFn (suffixTuple v)) * r) () () = (F * G) u v
    rw [Matrix.mul_assoc]
    rfl
  change (cutMatrix (interval N 0 k) _).rank ≤ D
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
    cutRank (interval N 0 k) (operatorCoefficientTensor (fun x y : Fin N → Fin d ↦
      Matrix.trace (b * MPOTensor.evalWord M (List.ofFn x) (List.ofFn y)))) ≤
      D * D := by
  have hcoeff : operatorCoefficientTensor (fun x y : Fin N → Fin d ↦
      Matrix.trace (b * MPOTensor.evalWord M (List.ofFn x) (List.ofFn y))) =
      fun σ : Fin N → Fin (d * d) ↦
        Matrix.trace (b * Kraus.evalWord (Kraus.reindexPhysical finProdFinEquiv.symm M)
          (List.ofFn σ)) := by
    funext σ
    rw [Kraus.evalWord_reindexPhysical, List.map_ofFn, MPOTensor.kraus_evalWord_ofFn]
    rfl
  rw [hcoeff]
  exact cutRank_traceBoundary_le _ b hk

/-- A uniform MPO contracted with fixed scalar left and right boundary
matrices has consecutive operator cut rank at most its virtual dimension.
This statement concerns the displayed uniform square-tensor representation;
it does not assume or conclude unitarity.
Source: arXiv:2508.08160v2, `eq:U_N_hom`, and Section 5 of the local circuit audit. -/
theorem cutRank_operatorCoefficientTensor_openBoundary_le {d D N k : ℕ}
    (M : MPOTensor d D) (l : Matrix Unit (Fin D) ℂ)
    (r : Matrix (Fin D) Unit ℂ) (hk : k ≤ N) :
    cutRank (interval N 0 k) (operatorCoefficientTensor (fun x y : Fin N → Fin d ↦
      (l * MPOTensor.evalWord M (List.ofFn x) (List.ofFn y) * r) () ())) ≤ D := by
  have hcoeff : operatorCoefficientTensor (fun x y : Fin N → Fin d ↦
      (l * MPOTensor.evalWord M (List.ofFn x) (List.ofFn y) * r) () ()) =
      fun σ : Fin N → Fin (d * d) ↦
        (l * Kraus.evalWord (Kraus.reindexPhysical finProdFinEquiv.symm M)
          (List.ofFn σ) * r) () () := by
    funext σ
    rw [Kraus.evalWord_reindexPhysical, List.map_ofFn, MPOTensor.kraus_evalWord_ofFn]
    rfl
  rw [hcoeff]
  exact cutRank_openBoundary_le _ l r hk

/-- The bound on all consecutive operator cuts of an ordinary periodic MPO,
in the exact form consumed by the finite-unitary circuit theorem.
Source: arXiv:2508.08160v2, lines 812--816 of the local source, and Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutRank_operatorCoefficientTensor_mpo_le_all {d D N : ℕ}
    (M : MPOTensor d D) :
    ∀ k : Fin (N + 1), cutRank (interval N 0 k.val) (operatorCoefficientTensor (M.mpo N)) ≤ D *
        D := by
  intro k
  exact cutRank_operatorCoefficientTensor_mpo_le M (by omega)

end MPUCircuit
