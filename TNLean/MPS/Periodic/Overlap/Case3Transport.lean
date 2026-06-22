/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Overlap.Case2

/-!
# Periodic overlap dichotomy: Case 3 transport

This module contains the one-site transport of cross-sector overlaps used in
the equal-period sector-match case of arXiv:1708.00029, Appendix A.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace
open Filter Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ### One-site rotation covariance of the cross sector overlap

The translation-operator step of arXiv:1708.00029, Appendix A (lines 985--1002)
moves the matched sector pair `(u, v)` to `(u+1, v+1)`.  Formalized below as a
single physical-site cyclic rotation of the underlying word: the single-site
off-diagonal shift `P_{k+1} A^i = A^i P_k` (eq:Aoffdiag, supplied by
`offDiag_shift_of_adjoint_cyclic_shift`) carries the cyclic index forward by one
per site, and the trace is invariant under cyclic rotation of the word, so the
cross overlap is unchanged by the simultaneous shift. -/

/-- One-site cyclic rotation of a configuration of length `L'+1`:
move the last letter to the front. -/
def rotateCfg {d L' : ℕ} : (Fin (L' + 1) → Fin d) ≃ (Fin (L' + 1) → Fin d) :=
  Equiv.arrowCongr (finRotate (L' + 1)) (Equiv.refl (Fin d))

/-- Word evaluation of the rotated configuration pulls the last letter to the front. -/
private lemma evalWord_ofFn_rotateCfg {L' : ℕ} (A : MPSTensor d D)
    (σ : Fin (L' + 1) → Fin d) :
    evalWord A (List.ofFn (rotateCfg σ)) =
      A (σ (Fin.last L')) * evalWord A (List.ofFn (Fin.init σ)) := by
  have hrotate : rotateCfg σ = Fin.cons (σ (Fin.last L')) (Fin.init σ) := by
    funext j
    refine Fin.cases ?_ ?_ j
    · change σ ((finRotate (L' + 1)).symm 0) = σ (Fin.last L')
      exact congrArg σ (Fin.ext (by simp))
    · intro i
      change σ ((finRotate (L' + 1)).symm i.succ) = σ i.castSucc
      exact congrArg σ (Fin.ext (by
        rw [finRotate_symm_apply]
        rw [Fin.val_sub_one_of_ne_zero (by simp)]
        simp))
  simp only [hrotate, List.ofFn_cons, evalWord_cons]

/-- Word evaluation of the original configuration pulls the last letter to the right. -/
private lemma evalWord_ofFn_eq_init_mul_last {L' : ℕ} (A : MPSTensor d D)
    (σ : Fin (L' + 1) → Fin d) :
    evalWord A (List.ofFn σ) =
      evalWord A (List.ofFn (Fin.init σ)) * A (σ (Fin.last L')) := by
  rw [List.ofFn_succ']
  rw [show (List.ofFn fun i => σ (Fin.castSucc i)) = List.ofFn (Fin.init σ) from rfl]
  rw [List.concat_eq_append, evalWord_append]
  simp [evalWord_cons, evalWord_nil]

/-- **Per-configuration trace covariance** under one-site rotation (eq:Aoffdiag,
arXiv:1708.00029 lines 985--1002).  Given the single-site off-diagonal shift
`P (k+1) * A i = A i * P k`, the projector-weighted trace at index `k+1` of the
rotated word equals the projector-weighted trace at index `k` of the original
word. -/
private lemma trace_proj_evalWord_rotateCfg {L' m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hShift : ∀ (k : Fin m) (i : Fin d), P (k + 1) * A i = A i * P k)
    (k : Fin m) (σ : Fin (L' + 1) → Fin d) :
    (P (k + 1) * evalWord A (List.ofFn (rotateCfg σ))).trace =
      (P k * evalWord A (List.ofFn σ)).trace := by
  rw [evalWord_ofFn_rotateCfg, evalWord_ofFn_eq_init_mul_last]
  -- `tr(P(k+1) * A(last) * W)`: apply the shift, then cycle the trace.
  rw [← Matrix.mul_assoc, hShift k (σ (Fin.last L'))]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]

/-- **Physical projector-overlap covariance** under one-site rotation.
The cross overlap built from projector-weighted traces is invariant under the
simultaneous one-step shift `(u, v) → (u+1, v+1)`, for any positive length
(arXiv:1708.00029 lines 985--1002, translation operator `T`). -/
private lemma sum_trace_proj_overlap_shift {L' m : ℕ} [NeZero m]
    (A B : MPSTensor d D)
    (P Q : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hShiftA : ∀ (k : Fin m) (i : Fin d), P (k + 1) * A i = A i * P k)
    (hShiftB : ∀ (k : Fin m) (i : Fin d), Q (k + 1) * B i = B i * Q k)
    (u v : Fin m) :
    (∑ σ : Fin (L' + 1) → Fin d,
        (P (u + 1) * evalWord A (List.ofFn σ)).trace *
          star ((Q (v + 1) * evalWord B (List.ofFn σ)).trace)) =
      ∑ σ : Fin (L' + 1) → Fin d,
        (P u * evalWord A (List.ofFn σ)).trace *
          star ((Q v * evalWord B (List.ofFn σ)).trace) := by
  rw [← Equiv.sum_comp (rotateCfg (d := d) (L' := L'))
    (fun σ => (P (u + 1) * evalWord A (List.ofFn σ)).trace *
      star ((Q (v + 1) * evalWord B (List.ofFn σ)).trace))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [trace_proj_evalWord_rotateCfg A P hShiftA u σ,
    trace_proj_evalWord_rotateCfg B Q hShiftB v σ]

/-- Equivalence between blocked configurations of length `N` and physical
configurations of length `N * m`, via `MPSTensor.decodeBlockEquiv`. -/
private noncomputable def blockedCfgEquiv (d N m : ℕ) :
    (Fin N → Fin (blockPhysDim d m)) ≃ (Fin (N * m) → Fin d) :=
  ((Equiv.arrowCongr (Equiv.refl (Fin N)) (decodeBlockEquiv d m)).trans
    (Equiv.curry (Fin N) (Fin m) (Fin d)).symm).trans
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl (Fin d)))

private lemma ofFn_blockedCfgEquiv (d N m : ℕ) (σ : Fin N → Fin (blockPhysDim d m)) :
    List.ofFn (blockedCfgEquiv d N m σ) = flattenBlockedWord d m (List.ofFn σ) := by
  have hfun : (blockedCfgEquiv d N m σ) =
      fun k : Fin (N * m) =>
        decodeBlock d m (σ (finProdFinEquiv.symm k).1) ((finProdFinEquiv.symm k).2) := by
    funext k
    simp [blockedCfgEquiv, Equiv.arrowCongr, Equiv.curry, decodeBlockEquiv_apply,
      Function.comp]
  rw [hfun, List.ofFn_mul]
  rw [flattenBlockedWord, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  -- The grouped index `⟨i*m+j⟩` decodes to `(i, j)` under `finProdFinEquiv`.
  have hsymm : ∀ j : Fin m,
      finProdFinEquiv.symm
          (⟨(i : ℕ) * m + (j : ℕ),
            by
              calc
                (i : ℕ) * m + (j : ℕ) < ((i : ℕ) + 1) * m := by
                  have := j.isLt; rw [Nat.add_mul, Nat.one_mul]; omega
                _ ≤ N * m := Nat.mul_le_mul_right _ (by have := i.isLt; omega)⟩ :
            Fin (N * m)) = (i, j) := by
    intro j
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    -- `finProdFinEquiv (i, j) = ⟨j + m * i, _⟩` by definition.
    change (i : ℕ) * m + (j : ℕ) = (j : ℕ) + m * (i : ℕ)
    rw [Nat.mul_comm m (i : ℕ), Nat.add_comm]
  simp only [hsymm]
  change (List.ofFn fun j : Fin m => decodeBlock d m (σ i) j) = (wordOfBlock d m ∘ σ) i
  simp [wordOfBlock, Function.comp]

/-- The cross overlap of two compressed cyclic sectors, expanded via the
`IsCyclicSectorDecomp` trace formula and reindexed to physical configurations
of length `N * m`. -/
private lemma sectorOverlap_eq_physical_sum {m : ℕ} [NeZero D] [NeZero m]
    (A B : MPSTensor d D)
    {dimA dimB : Fin m → ℕ}
    (blocksA : (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB : (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (PA PB : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hTraceA : ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
      mpv (blocksA k) σ = (PA k * evalWord (blockTensor A m) (List.ofFn σ)).trace)
    (hTraceB : ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
      mpv (blocksB k) σ = (PB k * evalWord (blockTensor B m) (List.ofFn σ)).trace)
    (u v : Fin m) (N : ℕ) :
    mpvOverlap (d := blockPhysDim d m) (blocksA u) (blocksB v) N =
      ∑ τ : Fin (N * m) → Fin d,
        (PA u * evalWord A (List.ofFn τ)).trace *
          star ((PB v * evalWord B (List.ofFn τ)).trace) := by
  classical
  rw [mpvOverlap]
  rw [← Equiv.sum_comp (blockedCfgEquiv d N m)
    (fun τ : Fin (N * m) → Fin d =>
      (PA u * evalWord A (List.ofFn τ)).trace *
        star ((PB v * evalWord B (List.ofFn τ)).trace))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hTraceA u N σ, hTraceB v N σ, ofFn_blockedCfgEquiv,
    ← evalWord_blockTensor, ← evalWord_blockTensor]

/-- **One-step transport of the cross sector overlap** (positive lengths,
arXiv:1708.00029 lines 985--1002).  For `N ≥ 1`, the cross overlap of compressed
cyclic sectors is invariant under the simultaneous index shift
`(u, v) → (u+1, v+1)`. -/
private lemma sectorOverlap_succ_eq {m : ℕ} [NeZero D] [NeZero m]
    (A B : MPSTensor d D)
    (hA_lc : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_lc : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    {dimA dimB : Fin m → ℕ}
    (blocksA : (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB : (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (PA PB : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hPAproj : ∀ k, IsOrthogonalProjection (PA k))
    (hPBproj : ∀ k, IsOrthogonalProjection (PB k))
    (hShiftA : ∀ k, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (PA (k + 1)) = PA k)
    (hShiftB : ∀ k, transferMap (d := d) (D := D) (fun i => (B i)ᴴ) (PB (k + 1)) = PB k)
    (hTraceA : ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
      mpv (blocksA k) σ = (PA k * evalWord (blockTensor A m) (List.ofFn σ)).trace)
    (hTraceB : ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
      mpv (blocksB k) σ = (PB k * evalWord (blockTensor B m) (List.ofFn σ)).trace)
    (u v : Fin m) (N : ℕ) (hN : 0 < N) :
    mpvOverlap (d := blockPhysDim d m) (blocksA (u + 1)) (blocksB (v + 1)) N =
      mpvOverlap (d := blockPhysDim d m) (blocksA u) (blocksB v) N := by
  have hLetterA := offDiag_shift_of_adjoint_cyclic_shift A hA_lc hPAproj hShiftA
  have hLetterB := offDiag_shift_of_adjoint_cyclic_shift B hB_lc hPBproj hShiftB
  rw [sectorOverlap_eq_physical_sum A B blocksA blocksB PA PB hTraceA hTraceB,
    sectorOverlap_eq_physical_sum A B blocksA blocksB PA PB hTraceA hTraceB]
  obtain ⟨L', hL'⟩ : ∃ L', N * m = L' + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.mul_ne_zero hN.ne' (NeZero.ne m))
  rw [hL']
  exact sum_trace_proj_overlap_shift A B PA PB hLetterA hLetterB u v

/-- **One-step transport of sector overlaps from cyclic-sector decompositions.**

For positive lengths, the cross overlap of the compressed cyclic sectors is
invariant under the simultaneous index shift (u, v) ↦ (u + 1, v + 1).
This is the formal overlap version of the translation-operator step in
arXiv:1708.00029, lines 985--1002. -/
lemma sectorOverlap_succ_eq_of_cyclicSectorDecomp {m : ℕ} [NeZero D] [NeZero m]
    (A B : MPSTensor d D)
    (hA_lc : IsLeftCanonical A) (hB_lc : IsLeftCanonical B)
    {dimA dimB : Fin m → ℕ}
    (blocksA : (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB : (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    (u v : Fin m) (N : ℕ) (hN : 0 < N) :
    mpvOverlap (d := blockPhysDim d m) (blocksA (u + 1)) (blocksB (v + 1)) N =
      mpvOverlap (d := blockPhysDim d m) (blocksA u) (blocksB v) N := by
  obtain ⟨PA, _φA, hPAproj, _hPAsum, hShiftA, _hCommA, hTraceA, _⟩ := hA_cyclic
  obtain ⟨PB, _φB, hPBproj, _hPBsum, hShiftB, _hCommB, hTraceB, _⟩ := hB_cyclic
  exact sectorOverlap_succ_eq A B hA_lc hB_lc blocksA blocksB PA PB
    hPAproj hPBproj hShiftA hShiftB hTraceA hTraceB u v N hN

end MPSTensor
