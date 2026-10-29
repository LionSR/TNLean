/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.QuasiLocalActionChoice
import TNLean.MPS.MPU.TwoSiteCanonicalPairImage
import TNLean.MPS.MPU.RepresentativeIndex

/-!
# The logarithmic MPU index and the actual QCA index

At an actual simple-block standard form, the derived canonical support
factor gives the positive rational QCA index. The existing canonical MPU
index is its negative base-two logarithm. Canonical replacement preserves
both actual objects: the public MPU index and the induced physical QCA.
Thus every positive-dimensional MPU has a derived nearest-neighbour
blocked presentation satisfying the source comparison.

**Local fix:** The sign and coefficient follow the source definition
one half of the logarithmic rank difference. The Appendix's extra factor
two and reversed dagger placement are corrected in
`docs/paper-gaps/mpu_qca_index_normalization.tex`.

Source: CPSV17, arXiv:1703.09188, def:index, lines 681--688,
and Appendix eq:original-index, lines 2329--2334.
-/

namespace SpinChain

variable {d D : ℕ} [NeZero d] {U : MPOTensor d D}

private theorem gnvwIndex_congr {b : ℕ} [NeZero b]
    {ω ω' : QuasiLocalAlgebra b ≃⋆ₐ[ℂ] QuasiLocalAlgebra b}
    (heq : ω = ω')
    (h : PropagatesWithin ω (Finset.Icc (-1) 1))
    (h' : PropagatesWithin ω' (Finset.Icc (-1) 1)) :
    PropagatesWithin.gnvwIndex h = PropagatesWithin.gnvwIndex h' := by
  cases heq
  rfl

/-- An actual canonical simple block gives nearest-neighbour propagation
for the blocked named MPU automorphism. Its support presentation is derived.
Source: CPSV17, Appendix, lines 2313--2334. -/
theorem canonicalMPU_blocked_propagatesWithin
    (hU : MPOTensor.IsMPUCanonicalFormII U) (k : ℕ) (hk : 0 < k) [NeZero k]
    (hS : MPOTensor.IsMPUSimple (MPOTensor.blockTensor U k)) :
    PropagatesWithin (blockedAutomorphism d k (mpuQuasiLocalEquiv hU.isMPU))
      (Finset.Icc (-1) 1) := by
  let S := (hU.blockTensor k hk).twoSiteStandardFormData hS
  rw [mpuQuasiLocalEquiv_eq_bufferedMPUQuasiLocalAut hU.isMPU k hk S]
  exact blocked_bufferedMPUQuasiLocalAut_propagatesWithin hU.isMPU k hk S

/-- The source MPU index equals the negative base-two logarithm of the
actual positive-rational QCA index at a concrete simple-block scale.
The actual least support algebra and its size are derived.
Source: CPSV17, def:index, lines 681--688; Appendix, lines 2329--2334. -/
theorem canonicalMPU_index_eq_neg_logb_gnvwIndex
    (hU : MPOTensor.IsMPUCanonicalFormII U) (k : ℕ) (hk : 0 < k) [NeZero k]
    (hS : MPOTensor.IsMPUSimple (MPOTensor.blockTensor U k)) :
    hU.index = -Real.logb 2
      ((PropagatesWithin.gnvwIndex
        (canonicalMPU_blocked_propagatesWithin hU k hk hS) : ℚ) : ℝ) := by
  let S := (hU.blockTensor k hk).twoSiteStandardFormData hS
  have hEq := mpuQuasiLocalEquiv_eq_bufferedMPUQuasiLocalAut hU.isMPU k hk S
  have hratio : ((PropagatesWithin.gnvwIndex
      (canonicalMPU_blocked_propagatesWithin hU k hk hS) : ℚ) : ℝ) =
      (MPOTensor.leftRank (MPOTensor.blockTensor U k) : ℝ) / (d ^ k : ℕ) := by
    have hidx := gnvwIndex_congr (congrArg (blockedAutomorphism d k) hEq)
      (canonicalMPU_blocked_propagatesWithin hU k hk hS)
      (blocked_bufferedMPUQuasiLocalAut_propagatesWithin hU.isMPU k hk S)
    rw [hidx]
    have hr := coe_gnvwIndex_blocked_bufferedMPUQuasiLocalAut hU.isMPU k hk S
    have hrReal : ((PropagatesWithin.gnvwIndex
        (blocked_bufferedMPUQuasiLocalAut_propagatesWithin hU.isMPU k hk S) : ℚ) : ℝ) =
        (MPOTensor.leftRank (MPOTensor.blockTensor U k) : ℝ) /
          (MPSTensor.blockPhysDim d k : ℝ) := by
      exact_mod_cast hr
    have hdim : (MPSTensor.blockPhysDim d k : ℝ) = (d ^ k : ℕ) := by
      exact_mod_cast MPSTensor.blockPhysDim_eq_pow d k
    simpa only [hdim] using hrReal
  rw [hratio]
  exact hU.index_eq_neg_logb_leftRank_div hk hS

/-- Every positive-dimensional MPU has an actual bounded blocking of its
named QCA whose GNVW index computes the public representative-defined MPU
index. The canonical representative, simple block, support factors and
nearest-neighbour propagation are all derived internally.
Source: CPSV17, canonical replacement, lines 319--356; def:index,
lines 681--688; Appendix eq:original-index, lines 2329--2334. -/
theorem exists_blocked_mpu_index_comparison [NeZero D] (hU : U.IsMPU) :
    ∃ (k : ℕ) (hk : 0 < k), k ≤ D * D ∧
      let : NeZero k := ⟨hk.ne'⟩
      ∃ hprop : PropagatesWithin (blockedAutomorphism d k (mpuQuasiLocalEquiv hU))
          (Finset.Icc (-1) 1),
        hU.index = -Real.logb 2 ((PropagatesWithin.gnvwIndex hprop : ℚ) : ℝ) := by
  classical
  obtain ⟨E, _, V, hV, hED, hMpo⟩ := hU.exists_reduced_cfii_representative
  obtain ⟨k, hk, hkE, hS, _, _⟩ := hV.exists_twoSiteStandardFormData_blockTensor
  let : NeZero k := ⟨hk.ne'⟩
  have heq : mpuQuasiLocalEquiv hU = mpuQuasiLocalEquiv hV.isMPU :=
    mpuQuasiLocalEquiv_eq_of_mpo_eq hU hV.isMPU
      (fun N hN => (hMpo N (Nat.zero_lt_of_lt hN)).symm)
  have hblocked := congrArg (blockedAutomorphism d k) heq
  have hprop : PropagatesWithin (blockedAutomorphism d k (mpuQuasiLocalEquiv hU))
      (Finset.Icc (-1) 1) := by
    rw [hblocked]
    exact canonicalMPU_blocked_propagatesWithin hV k hk hS
  refine ⟨k, hk, hkE.trans (Nat.mul_le_mul hED hED), hprop, ?_⟩
  have hidx := gnvwIndex_congr hblocked hprop
    (canonicalMPU_blocked_propagatesWithin hV k hk hS)
  rw [hidx, hU.index_eq_canonical_representative hV hMpo]
  exact canonicalMPU_index_eq_neg_logb_gnvwIndex hV k hk hS

end SpinChain
