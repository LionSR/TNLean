/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Equivalence
import TNLean.MPS.MPU.GeneralIndexContinuity
import TNLean.MPS.MPU.RepresentativeIndexOperations
import TNLean.MPS.MPU.RepresentativeIndexTensorProduct

/-!
# Equivalent matrix product unitaries have equal index

This file proves the "only if" half of clause (iv) of the Index Theorem,
arXiv:1703.09188, Theorem `IndexTh`, lines 852--857: tensors with different
indices are not equivalent. Equivalently, equivalent tensors have equal
index.

The argument is the source's. Adjoining unused bond directions does not change
the index (`IsMPU.index_padBond`), and neither does reindexing the physical
legs along the identity. By clause (iii) (`IsMPU.index_const_of_continuous`)
the index is constant along the path joining the two enlarged tensors, so
strictly equivalent tensors have equal index. Attaching an identity ancilla
(`IsMPU.index_tensorPhysicalId`) and blocking (`IsMPU.index_blockTensor`) do
not change the index, which gives the statement for equivalence.

The index used throughout is the representative index `IsMPU.index`; for a
tensor in canonical form it is the source index of Definition `def:index`
(`IsMPU.index_eq_logb_of_isMPUCanonicalForm`).

## Main statements

* `MPOTensor.StrictlyEquivalent.index_eq`: strictly equivalent tensors have
  equal index.
* `MPOTensor.Equivalent.index_eq`: equivalent tensors have equal index.
* `MPOTensor.not_equivalent_of_index_ne`: tensors with different indices are
  not equivalent, the source's formulation.
-/

namespace MPOTensor

variable {d da db Da Db : ℕ}

/-- The representative index depends only on the tensor, not on the supplied
proof that it generates matrix product unitaries. -/
private theorem IsMPU.index_congr [NeZero d] [NeZero Da]
    {U V : MPOTensor d Da} (hU : IsMPU U) (hV : IsMPU V) (h : U = V) :
    hU.index = hV.index := by
  subst h
  rfl

/-- Reindexing both physical legs along the identity equivalence `finCongr rfl`
does not change a tensor. -/
private theorem reindexPhysical_finCongr_refl (U : MPOTensor d Da) :
    reindexPhysical (finCongr (rfl : d = d)).symm U = U := by
  funext i j
  simp [reindexPhysical, finCongr_refl]

/-- **Strictly equivalent tensors have equal index.** If the canonical-form MPU
tensors \(\mathcal U\) and \(\mathcal V\) are strictly equivalent, their indices
coincide: the index is unchanged by adjoining unused bond directions and is
constant along the path of MPU tensors joining the enlarged tensors.

Source: arXiv:1703.09188, Theorem `IndexTh` (iv), "only if", lines 852--857,
using clause (iii) (Proposition `prop:continuity-index`, lines 739--818) and
Definition `def:strictly-equivalent-tensors`, lines 708--714. -/
theorem StrictlyEquivalent.index_eq [NeZero da] [NeZero db] [NeZero Da] [NeZero Db]
    {U : MPOTensor da Da} {V : MPOTensor db Db} {hphys : da = db}
    (hU : IsMPU U) (hV : IsMPU V) (h : StrictlyEquivalent U V hphys) :
    hU.index = hV.index := by
  obtain ⟨-, -, D', ha, hb, hpath⟩ := h
  subst hphys
  have : NeZero D' := ⟨by have := NeZero.pos Da; omega⟩
  rw [reindexPhysical_finCongr_refl] at hpath
  let γ := hpath.somePath
  have hγ : ∀ t, IsMPU (γ t) := hpath.somePath_mem
  calc
    hU.index = (hU.padBond D' ha).index := (hU.index_padBond D' ha).symm
    _ = (hγ 0).index := IsMPU.index_congr _ _ γ.source.symm
    _ = (hγ 1).index := IsMPU.index_const_of_continuous γ.continuous hγ 0 1
    _ = (hV.padBond D' hb).index := IsMPU.index_congr _ _ γ.target
    _ = hV.index := hV.index_padBond D' hb

/-- **Equivalent tensors have equal index.** If \(\mathcal U\) and
\(\mathcal V\) are equivalent, that is, \(\mathcal U^{(p_a)}_k\) and
\(\mathcal V^{(p_b)}_k\) are strictly equivalent for some positive blocking
length \(k\) and positive ancilla dimensions \(p_a\), \(p_b\), then their
indices coincide. Attaching an identity ancilla and blocking do not change the
index, and strictly equivalent tensors have equal index.

Source: arXiv:1703.09188, Theorem `IndexTh` (iv), "only if", lines 852--857,
using clauses (i)--(iii) and Definition `def:equivalent-tensors`,
lines 716--724. -/
theorem Equivalent.index_eq [NeZero da] [NeZero db] [NeZero Da] [NeZero Db]
    {U : MPOTensor da Da} {V : MPOTensor db Db}
    (hU : IsMPU U) (hV : IsMPU V) (h : Equivalent U V) :
    hU.index = hV.index := by
  obtain ⟨-, -, k, pa, pb, hk, hpa, hpb, -, hphys, hstrict⟩ := h
  have : NeZero pa := ⟨hpa.ne'⟩
  have : NeZero pb := ⟨hpb.ne'⟩
  let : NeZero (Kraus.blockPhysDim (da * pa) k) := ⟨by
    rw [Kraus.blockPhysDim_eq_pow]
    exact pow_ne_zero k (NeZero.ne (da * pa))⟩
  calc
    hU.index = (hU.tensorPhysicalId pa hpa).index := (hU.index_tensorPhysicalId pa).symm
    _ = ((hU.tensorPhysicalId pa hpa).blockTensor k hk).index :=
      ((hU.tensorPhysicalId pa hpa).index_blockTensor k hk).symm
    _ = ((hV.tensorPhysicalId pb hpb).blockTensor k hk).index :=
      StrictlyEquivalent.index_eq _ _ hstrict
    _ = (hV.tensorPhysicalId pb hpb).index :=
      (hV.tensorPhysicalId pb hpb).index_blockTensor k hk
    _ = hV.index := hV.index_tensorPhysicalId pb

/-- **Tensors with different indices are not equivalent.** This is the source's
formulation of the "only if" half of clause (iv) of the Index Theorem.

Source: arXiv:1703.09188, Theorem `IndexTh` (iv), "only if", lines 852--857. -/
theorem not_equivalent_of_index_ne [NeZero da] [NeZero db] [NeZero Da] [NeZero Db]
    {U : MPOTensor da Da} {V : MPOTensor db Db}
    (hU : IsMPU U) (hV : IsMPU V) (hne : hU.index ≠ hV.index) :
    ¬ Equivalent U V :=
  fun h ↦ hne (h.index_eq hU hV)

end MPOTensor
