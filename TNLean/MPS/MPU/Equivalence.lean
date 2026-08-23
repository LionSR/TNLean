/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Topology.Connected.PathConnected
import TNLean.MPS.MPU.MPUCanonicalForm
import TNLean.MPS.MPU.PhysicalAncilla

/-!
# Equivalence of matrix product unitary tensors

This file formalizes strict equivalence and equivalence after attaching physical
identity ancillas and then blocking, following arXiv:1703.09188, lines 706--724.
It also formalizes the symmetry-preserving versions from lines 1345--1364.

The virtual bond dimension is fixed along every path. The source does not specify
a stabilization that compares tensors of different virtual bond dimensions, so
no such relation is introduced here. Strict paths remain inside the MPU locus;
only the canonical-form condition from the paper is omitted along the path.

## Main definitions

* `MPOTensor.StrictlyEquivalent`: path connectedness inside the fixed-bond MPU locus.
* `MPOTensor.Equivalent`: strict equivalence after positive identity-ancilla
  attachment and a common positive blocking length.
* `MPOTensor.FiniteChainOperatorSymmetry`: an operator action at specified chain lengths.
* `MPOTensor.StrictlyEquivalentUnderSymmetry`: strict equivalence through invariant MPUs.
* `MPOTensor.EquivalentUnderSymmetry`: symmetry-preserving equivalence after ancillas
  and blocking.
-/

namespace MPOTensor

variable {da db D : ℕ}

/-- A finite-chain operator symmetry consists of an action on every finite-chain
operator space and a set of chain lengths on which that action is imposed.

The action is defined for every physical dimension, but no continuity, linearity,
or compatibility between different chain lengths is assumed at this abstract
level.

Source: arXiv:1703.09188, Definitions `def:strictly-equivalent-symmetry` and
`def:equivalent-symmetry`, lines 1345--1364. -/
structure FiniteChainOperatorSymmetry where
  applicable : Set ℕ
  action : {d N : ℕ} →
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →
      Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ

/-- A matrix product operator tensor is invariant under a finite-chain symmetry
when every applicable periodic operator satisfies
\(\mathcal S[W^{(N)}]=W^{(N)}\).

**Local fix (arXiv:1703.09188, line 1353):** the displayed source equation
repeats the transformed operator on both sides. The intended right-hand side is
the original operator. See `docs/paper-gaps/mpu_canonical_form_full_support.tex`.

Source: arXiv:1703.09188, Definition `def:strictly-equivalent-symmetry`,
lines 1345--1354. -/
def IsInvariantUnderSymmetry (S : FiniteChainOperatorSymmetry)
    (W : MPOTensor da D) : Prop :=
  ∀ ⦃N : ℕ⦄, N ∈ S.applicable → S.action (mpo W N) = mpo W N

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
  MPSTensor.IsMPUCanonicalForm U.toMPSTensor ∧
    MPSTensor.IsMPUCanonicalForm V.toMPSTensor ∧
      JoinedIn {W : MPOTensor db D | IsMPU W}
        (reindexPhysical (finCongr hphys).symm U) V

/-- Two fixed-bond canonical-form MPU tensors are strictly equivalent under
`S` when they are joined by a continuous path of MPUs invariant under `S` at
every applicable chain length.

Canonical form is required only at the endpoints. The physical dimension is
identified explicitly, and the virtual bond dimension remains fixed along the
path.

**Scope restriction (arXiv:1703.09188, lines 1345--1364):** the paper does not
specify a stabilization for unequal raw virtual bond dimensions, so this
definition only compares tensors in one fixed ambient bond dimension. See
`docs/paper-gaps/mpu_equivalence_fixed_bond.tex`.

Source: arXiv:1703.09188, Definition `def:strictly-equivalent-symmetry`,
lines 1345--1354. -/
def StrictlyEquivalentUnderSymmetry (S : FiniteChainOperatorSymmetry)
    (U : MPOTensor da D) (V : MPOTensor db D) (hphys : da = db) : Prop :=
  MPSTensor.IsMPUCanonicalForm U.toMPSTensor ∧
    MPSTensor.IsMPUCanonicalForm V.toMPSTensor ∧
      JoinedIn {W : MPOTensor db D | IsMPU W ∧ IsInvariantUnderSymmetry S W}
        (reindexPhysical (finCongr hphys).symm U) V

/-- Forgetting symmetry invariance from a strict symmetry-preserving path gives
ordinary strict equivalence.

Source: arXiv:1703.09188, Definitions `def:strictly-equivalent-tensors` and
`def:strictly-equivalent-symmetry`, lines 708--714 and 1345--1354. -/
theorem StrictlyEquivalentUnderSymmetry.toStrictlyEquivalent
    {S : FiniteChainOperatorSymmetry} {U : MPOTensor da D} {V : MPOTensor db D}
    {hphys : da = db} (h : StrictlyEquivalentUnderSymmetry S U V hphys) :
    StrictlyEquivalent U V hphys :=
  ⟨h.1, h.2.1, h.2.2.mono fun _ hW ↦ hW.1⟩

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

/-- Two fixed-bond MPU tensors are equivalent under `S` when positive coprime
identity ancillas equalize their physical dimensions and a common positive
blocking makes the enlarged tensors strictly equivalent under `S`.

Ancillas are attached before blocking. The virtual bond dimension is unchanged.

**Scope restriction (arXiv:1703.09188, lines 1345--1364):** the bond dimension
\(D\) is fixed. No heterogeneous raw-bond stabilization is asserted. See
`docs/paper-gaps/mpu_equivalence_fixed_bond.tex`.

Source: arXiv:1703.09188, Definition `def:equivalent-symmetry`,
lines 1356--1364. -/
def EquivalentUnderSymmetry (S : FiniteChainOperatorSymmetry)
    (U : MPOTensor da D) (V : MPOTensor db D) : Prop :=
  IsMPU U ∧ IsMPU V ∧
    ∃ k pa pb : ℕ,
      0 < k ∧ 0 < pa ∧ 0 < pb ∧ Nat.Coprime pa pb ∧
        ∃ hphys : pa * da = pb * db,
          StrictlyEquivalentUnderSymmetry S
            (blockTensor (tensorPhysicalId U pa) k)
            (blockTensor (tensorPhysicalId V pb) k)
            (blockedAncillaPhysicalDim_eq k hphys)

/-- Forgetting symmetry invariance from a stabilized symmetry-preserving path
gives ordinary MPU equivalence.

Source: arXiv:1703.09188, Definitions `def:equivalent-tensors` and
`def:equivalent-symmetry`, lines 716--724 and 1356--1364. -/
theorem EquivalentUnderSymmetry.toEquivalent {S : FiniteChainOperatorSymmetry}
    {U : MPOTensor da D} {V : MPOTensor db D}
    (h : EquivalentUnderSymmetry S U V) : Equivalent U V := by
  rcases h with ⟨hU, hV, k, pa, pb, hk, hpa, hpb, hcoprime, hphys, hstrict⟩
  exact ⟨hU, hV, k, pa, pb, hk, hpa, hpb, hcoprime, hphys,
    hstrict.toStrictlyEquivalent⟩

end MPOTensor
