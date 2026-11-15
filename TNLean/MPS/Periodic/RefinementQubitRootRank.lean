/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausMap
import QICLean.Channel.WielandtLowDim
import TNLean.Algebra.KrausSpanRank
import TNLean.MPS.Periodic.RefinementRootIrreducibility
import TNLean.MPS.Periodic.RootWordSpan
import TNLean.MPS.Periodic.Symmetry.Theorem41Reverse

/-!
# Bounded roots for irreducible qubit channels

A trace-preserving irreducible family of `2 × 2` Kraus matrices has an
invertible element in its one-letter span. Consequently every channel root
of an irreducible qubit channel has Choi rank at most that of its power.
This proves the reverse implication of arXiv:1708.00029, Theorem 4.1,
for irreducible bond-dimension-two transfer maps, including singular ones.
The general higher-dimensional selection problem remains open; see
`docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`.
-/

open scoped Matrix BigOperators

private theorem anticommutator_of_det_eq_zero_fin_two
    {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.det = 0) (hB : B.det = 0) (hAB : (A + B).det = 0) :
    A * B + B * A = A.trace • B + B.trace • A := by
  simp only [Matrix.det_fin_two, Matrix.add_apply] at hA hB hAB
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.trace_fin_two, Matrix.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one]
  · linear_combination -hAB + hA + hB
  · ring
  · ring
  · linear_combination -hAB + hA + hB

namespace Kraus

/-- A trace-preserving irreducible qubit Kraus family has an invertible
matrix in its one-letter span. The proof rules out an all-singular span
using the polarized `2 × 2` determinant identity. This supplies a sufficient
root-span condition for arXiv:1708.00029, Theorem 4.1, converse. -/
theorem exists_isUnit_mem_wordSpan_one_fin_two
    {d : ℕ} (A : Fin d → Matrix (Fin 2) (Fin 2) ℂ)
    (hTP : IsTP A) (hIrr : IsIrreducibleFamily A) :
    ∃ X ∈ wordSpan A 1, IsUnit X := by
  classical
  by_contra! hNoUnit
  let S := wordSpan A 1
  have hLetter (i : Fin d) : A i ∈ S := by
    change A i ∈ wordSpan A 1
    rw [wordSpan_one]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hDet (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X ∈ S) : X.det = 0 := by
    have h := hNoUnit X hX
    rwa [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at h
  have hTrace (N : Matrix (Fin 2) (Fin 2) ℂ) (hN : N ∈ S)
      (hTr : N.trace = 0) : N = 0 := by
    let W := LinearMap.ker (Matrix.toLin' N)
    have hW : Matrix.IsInvariantSubmodule A W := by
      intro i v hv
      have hv' : N *ᵥ v = 0 := hv
      have h := anticommutator_of_det_eq_zero_fin_two
        (hDet N hN) (hDet (A i) (hLetter i))
        (hDet (N + A i) (S.add_mem hN (hLetter i)))
      rw [hTr, zero_smul, zero_add] at h
      have hVec := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M *ᵥ v) h
      change N *ᵥ (A i *ᵥ v) = 0
      simpa only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv',
        Matrix.mulVec_zero, add_zero, Matrix.smul_mulVec, smul_zero] using hVec
    rcases isIrreducibleAction_of_isIrreducibleFamily A hIrr W hW with hBot | hTop
    · obtain ⟨v, hv, hNv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (hDet N hN)
      have hvW : v ∈ W := hNv
      rw [hBot] at hvW
      exact False.elim (hv (by simpa using hvW))
    · have hLin : Matrix.toLin' N = 0 := LinearMap.ker_eq_top.mp hTop
      have h := congrArg LinearMap.toMatrix' hLin
      simpa using h
  obtain ⟨i, hi⟩ : ∃ i, A i ≠ 0 := by
    by_contra! hZero
    simp [IsTP, hZero] at hTP
  have hTr : (A i).trace ≠ 0 := by
    intro h
    exact hi (hTrace (A i) (hLetter i) h)
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (hDet (A i) (hLetter i))
  apply hv
  apply eq_zero_of_isTP_of_forall_mulVec_eq_zero A hTP
  intro j
  have hN : (A i).trace • A j - (A j).trace • A i = 0 := by
    apply hTrace _ (S.sub_mem (S.smul_mem _ (hLetter j)) (S.smul_mem _ (hLetter i)))
    simp [Matrix.trace_smul, smul_eq_mul, mul_comm]
  have hVec := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M *ᵥ v) hN
  have hScalar : (A i).trace • (A j *ᵥ v) = 0 := by
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, hAv, smul_zero,
      sub_zero, Matrix.zero_mulVec] using hVec
  exact (smul_eq_zero.mp hScalar).resolve_left hTr

end Kraus

namespace Channel

/-- Every channel root of an irreducible qubit channel has Choi rank no
larger than its power. Invertibility of the target is not required.
This proves a bond-dimension-two case of the root-rank step in
arXiv:1708.00029, Theorem 4.1, converse, lines 812--818. -/
theorem choiRank_le_pow_of_irreducible_fin_two
    {F : Module.End ℂ (Matrix (Fin 2) (Fin 2) ℂ)} (hF : IsChannel F)
    {p : ℕ} (hp : 0 < p) (hIrr : IsIrreducibleMap (F ^ p)) :
    choiRank F ≤ choiRank (F ^ p) := by
  obtain ⟨r, A, hA, hTP⟩ := hF.exists_kraus_map_eq_and_normalized
  have hPow : F ^ p = Kraus.transferMap (MPSTensor.blockTensor A p) := by
    rw [MPSTensor.transferMap_blockTensor, hA]
  have hBlock : Kraus.IsIrreducibleFamily (MPSTensor.blockTensor A p) := by
    apply Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM
    change IsIrreducibleMap (Kraus.transferMap (MPSTensor.blockTensor A p))
    rwa [← hPow]
  have hRoot := MPSTensor.isIrreducibleFamily_of_blockTensor A p hBlock
  obtain ⟨X, hX, hUnit⟩ := Kraus.exists_isUnit_mem_wordSpan_one_fin_two A hTP hRoot
  calc
    choiRank F = Module.finrank ℂ (Kraus.wordSpan A 1) := by
      rw [hA, choiRank_mapLM_eq_finrank_wordSpan_one]
    _ ≤ Module.finrank ℂ (Kraus.wordSpan A p) :=
      Kraus.wordSpan_one_finrank_le_of_isUnit_mem_wordSpan_one A hp hX hUnit
    _ = choiRank (Kraus.transferMap (MPSTensor.blockTensor A p)) := by
      rw [choiRank_mapLM_eq_finrank_wordSpan_one, Kraus.wordSpan_blockTensor_one]
    _ = choiRank (F ^ p) := congrArg choiRank hPow.symm

end Channel

namespace MPSTensor

/-- Channel divisibility gives a refinement for every irreducible
bond-dimension-two transfer map, including singular maps. This is a
dimension-two case of arXiv:1708.00029, Theorem 4.1, converse. No
additional bounded-root or invertible-root-span hypothesis is assumed. -/
theorem isPRefinable_of_isPDivisibleChannel_of_irreducible_fin_two
    {d p : ℕ} (B : MPSTensor d 2) (hp : 0 < p)
    (hB : IsIrreducibleMap (Kraus.transferMap B))
    (hDiv : IsPDivisibleChannel (Kraus.transferMap B) p) :
    IsPRefinable B p := by
  obtain ⟨F, hF, hpow⟩ := hDiv
  have hIrr : IsIrreducibleMap (F ^ p) := hpow ▸ hB
  have hRank : Channel.choiRank F ≤ d := by
    calc
      Channel.choiRank F ≤ Channel.choiRank (F ^ p) :=
        Channel.choiRank_le_pow_of_irreducible_fin_two hF hp hIrr
      _ = Channel.choiRank (Kraus.transferMap B) := congrArg Channel.choiRank hpow.symm
      _ ≤ d := Channel.choiRank_le_of_hasKrausCard ⟨B, by intro X; simp⟩
  exact isPRefinable_of_channel_root_hasKrausRankLE B hp F hpow
    ⟨Channel.choiRank F, hRank, Channel.hasKrausCard_choiRank_of_cp hF.cp⟩

end MPSTensor
