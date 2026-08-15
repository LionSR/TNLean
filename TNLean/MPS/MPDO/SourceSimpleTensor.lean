/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.SimpleTensor

/-!
# Normalization-free Definition 4.7 simplicity

This module records the source-facing simplicity condition of arXiv:1606.00608,
Definition 4.7. After a positive physical blocking, the doubled-index tensor must
admit a CPSV basis of normal tensors, and the ket-against-bra contraction of every
basis element must be nonnilpotent. The interface requires a nonzero tensor that
generates MPDOs, but deliberately excludes the separate line-246 unit-weight
normalization.

## Main result

* `MPOTensor.IsSourceSimple`: normalization-free Definition 4.7 simplicity.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.7, lines 815--822
-/

namespace MPOTensor

variable {d D : ℕ}

/-- **Normalization-free Definition 4.7 simplicity.** A nonzero tensor
generating MPDOs is source-simple when, after some positive physical blocking,
its doubled-index tensor has a CPSV basis of normal tensors and no basis element
has nilpotent ket-against-bra contraction.

The nonzero condition records the source boundary that the tensor generates a
nontrivial density-operator family; in particular, the zero MPO tensor is not
simple. The BNT witness uses `MPSTensor.IsCPSVBasisOfNormalTensors`, rather than
an arbitrary family of canonical blocks. It does not impose the line-246
unit-weight normalization and makes no claim that every positive blocking has
such a witness.

Source: arXiv:1606.00608, Definition 4.7, lines 815--822. -/
def IsSourceSimple (M : MPOTensor d D) : Prop :=
  IsMPDO M ∧ M ≠ 0 ∧
    ∃ L : ℕ, 0 < L ∧
      ∃ g : ℕ,
        ∃ blocks : (j : Fin g) →
            Σ D' : ℕ, MPSTensor
              (MPSTensor.blockPhysDim d L * MPSTensor.blockPhysDim d L) D',
          MPSTensor.IsCPSVBasisOfNormalTensors (blockTensor M L).toMPSTensor blocks ∧
            ∀ j, ¬ IsNilpotent
              (doubledPhysTraceTransfer (MPSTensor.blockPhysDim d L) (blocks j).2)

end MPOTensor
