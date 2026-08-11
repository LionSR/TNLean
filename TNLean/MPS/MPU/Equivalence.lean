/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Topology.Connected.PathConnected
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.MPU.PhysicalAncilla

/-!
# Equivalence of matrix product unitary tensors

This file formalizes strict equivalence and equivalence after attaching physical
identity ancillas and then blocking, following arXiv:1703.09188, lines 706--724.

The virtual bond dimension is fixed along every path. The source does not specify
a stabilization that compares tensors of different virtual bond dimensions, so
no such relation is introduced here. Strict paths remain inside the MPU locus;
only the canonical-form condition from the paper is omitted along the path.

## Main definitions

* `MPOTensor.StrictlyEquivalent`: path connectedness inside the fixed-bond MPU locus.
* `MPOTensor.Equivalent`: strict equivalence after positive identity-ancilla
  attachment and a common positive blocking length.
-/

namespace MPOTensor

variable {da db D : ℕ}

/-- Two fixed-bond MPU tensors in canonical form are strictly equivalent when,
after explicitly identifying their physical dimensions, they are joined by a
continuous path all of whose points generate MPUs.

Canonical form is required only at the endpoints. The bond dimension \(D\) is
fixed throughout.

**Scope restriction (arXiv:1703.09188, lines 706--724):** the paper does not
specify a stabilization for unequal raw virtual bond dimensions, so this
definition only compares tensors in one fixed ambient bond dimension. See
`docs/paper-gaps/mpu_equivalence_fixed_bond.tex`.

Source: arXiv:1703.09188, Definition `def:strictly-equivalent-tensors`,
lines 708--714. -/
def StrictlyEquivalent (U : MPOTensor da D) (V : MPOTensor db D)
    (hphys : da = db) : Prop :=
  MPSTensor.IsCPSVCanonicalForm U.toMPSTensor ∧
    MPSTensor.IsCPSVCanonicalForm V.toMPSTensor ∧
      JoinedIn {W : MPOTensor db D | IsMPU W}
        (reindexPhysical (finCongr hphys).symm U) V

private theorem blockedAncillaPhysicalDim_eq (k : ℕ) {pa pb : ℕ}
    (hphys : pa * da = pb * db) :
    MPSTensor.blockPhysDim (da * pa) k = MPSTensor.blockPhysDim (db * pb) k := by
  simp only [MPSTensor.blockPhysDim_eq_pow]
  rw [Nat.mul_comm da pa, Nat.mul_comm db pb, hphys]

/-- Two fixed-bond MPU tensors are equivalent when positive coprime ancilla
sizes \(p_a\) and \(p_b\) make their enlarged physical dimensions equal and,
after attaching those ancillas, a common positive blocking length makes the
resulting tensors strictly equivalent.

Ancillas are attached before blocking. The physical-size condition is the source
equation \(p_a d_a = p_b d_b\); it supplies the explicit reindexing witness
needed by `StrictlyEquivalent` after blocking.

**Scope restriction (arXiv:1703.09188, lines 706--724):** the bond dimension
\(D\) is fixed. No heterogeneous raw-bond stabilization is asserted. See
`docs/paper-gaps/mpu_equivalence_fixed_bond.tex`.

Source: arXiv:1703.09188, Definition `def:equivalent-tensors`, lines 716--724. -/
def Equivalent (U : MPOTensor da D) (V : MPOTensor db D) : Prop :=
  IsMPU U ∧ IsMPU V ∧
    ∃ k pa pb : ℕ,
      0 < k ∧ 0 < pa ∧ 0 < pb ∧ Nat.Coprime pa pb ∧
        ∃ hphys : pa * da = pb * db,
          StrictlyEquivalent
            (blockTensor (tensorPhysicalId U pa) k)
            (blockTensor (tensorPhysicalId V pb) k)
            (blockedAncillaPhysicalDim_eq k hphys)

end MPOTensor
