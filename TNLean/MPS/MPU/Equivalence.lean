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
It also formalizes strict and stabilized equivalence under symmetry from
lines 1340--1366.

The virtual bond dimension is fixed along every path. The source does not specify
a stabilization that compares tensors of different virtual bond dimensions, so
no such relation is introduced here. Strict paths remain inside the MPU locus;
only the canonical-form condition from the paper is omitted along the path.

The symmetry used after adjoining an identity ancilla is supplied as part of a
coherent dimension-indexed family. This avoids extending an action arbitrarily
from operators of the form \(X\otimes I\) to the full enlarged operator algebra.
Blocking, by contrast, canonically conjugates the action along the finite-chain
configuration equivalence.

## Main definitions

* `MPOTensor.StrictlyEquivalent`: path connectedness inside the fixed-bond MPU locus.
* `MPOTensor.Equivalent`: strict equivalence after positive identity-ancilla
  attachment and a common positive blocking length.
* `MPOTensor.FiniteChainOperatorSymmetry`: an operator action at specified chain lengths.
* `MPOTensor.FiniteChainOperatorSymmetryFamily`: coherent actions across physical dimensions.
* `MPOTensor.StrictlyEquivalentUnderSymmetry`: strict equivalence through invariant MPUs.
* `MPOTensor.EquivalentUnderSymmetry`: stabilized equivalence through invariant MPUs.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d da db D : ℕ}

/-- A finite-chain operator symmetry at physical dimension \(d\) consists of an
action on every length-\(N\) operator space and a set of chain lengths on which
that action is imposed.

No continuity, linearity, or compatibility between different chain lengths is
assumed at this abstract level.

Source: arXiv:1703.09188, Definition `def:strictly-equivalent-symmetry`,
lines 1345--1354. -/
structure FiniteChainOperatorSymmetry (d : ℕ) where
  applicable : Set ℕ
  action : {N : ℕ} →
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
def IsInvariantUnderSymmetry (S : FiniteChainOperatorSymmetry d)
    (W : MPOTensor d D) : Prop :=
  ∀ ⦃N : ℕ⦄, N ∈ S.applicable → S.action (mpo W N) = mpo W N

/-- Attach an identity ancilla of dimension \(x\) to a finite-chain operator.

This is the canonical embedding \(X\mapsto X\otimes I\), written in the
sitewise product coordinates used by `tensorPhysicalId`.

Source: arXiv:1703.09188, Definition `def:equivalent-symmetry`, lines 1356--1364. -/
def tensorPhysicalIdOperator {d N : ℕ}
    (X : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) (x : ℕ) :
    Matrix (Fin N → Fin (d * x)) (Fin N → Fin (d * x)) ℂ :=
  Matrix.reindex (finTupleProdEquiv N d x).symm
    (finTupleProdEquiv N d x).symm
    (X ⊗ₖ (1 : Matrix (Fin N → Fin x) (Fin N → Fin x) ℂ))

/-- A physical-dimension-indexed family of finite-chain symmetries whose actions
commute with adjoining the canonical identity ancilla.

The applicable lengths are common to every physical dimension. The semiconjugacy
law specifies the enlarged-dimension action on the image of \(X\mapsto X\otimes I\),
while the action on the rest of the enlarged operator algebra remains supplied
data rather than an arbitrary extension.

Source: arXiv:1703.09188, Definition `def:equivalent-symmetry`, lines 1356--1364. -/
structure FiniteChainOperatorSymmetryFamily where
  applicable : Set ℕ
  action : {d N : ℕ} →
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →
      Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ
  tensorPhysicalId_semiconj : ∀ (d x N : ℕ),
    Function.Semiconj (fun X ↦ tensorPhysicalIdOperator X x)
      (@action d N) (@action (d * x) N)

/-- The component of a coherent symmetry family at physical dimension \(d\). -/
def FiniteChainOperatorSymmetryFamily.at
    (S : FiniteChainOperatorSymmetryFamily) (d : ℕ) :
    FiniteChainOperatorSymmetry d where
  applicable := S.applicable
  action := S.action

/-- Canonically transport a symmetry through blocking \(k\) consecutive sites.
Its applicable blocked lengths are exactly those \(N\) for which the original
length \(Nk\) is applicable.

Source: arXiv:1703.09188, line 1366. -/
noncomputable def FiniteChainOperatorSymmetry.block
    (S : FiniteChainOperatorSymmetry d) (k : ℕ) :
    FiniteChainOperatorSymmetry (MPSTensor.blockPhysDim d k) where
  applicable := {N | N * k ∈ S.applicable}
  action := fun {N} X ↦
    let e := MPSTensor.blockedConfigEquiv d N k
    Matrix.reindex e.symm e.symm (S.action (Matrix.reindex e e X))

/-- The blocked action is conjugation along the canonical blocked-configuration
equivalence.

Source: arXiv:1703.09188, line 1366. -/
theorem FiniteChainOperatorSymmetry.block_action
    (S : FiniteChainOperatorSymmetry d) (k N : ℕ)
    (X : Matrix (Fin N → Fin (MPSTensor.blockPhysDim d k))
      (Fin N → Fin (MPSTensor.blockPhysDim d k)) ℂ) :
    (S.block k).action X =
      Matrix.reindex (MPSTensor.blockedConfigEquiv d N k).symm
        (MPSTensor.blockedConfigEquiv d N k).symm
        (S.action (Matrix.reindex (MPSTensor.blockedConfigEquiv d N k)
          (MPSTensor.blockedConfigEquiv d N k) X)) := rfl

/-- Invariance transports through the canonical identity-ancilla embedding for
a coherent family of symmetries.

Source: arXiv:1703.09188, Definition `def:equivalent-symmetry`, lines 1356--1364. -/
theorem IsInvariantUnderSymmetry.tensorPhysicalId
    (S : FiniteChainOperatorSymmetryFamily) {U : MPOTensor d D}
    (hU : IsInvariantUnderSymmetry (S.at d) U) (x : ℕ) :
    IsInvariantUnderSymmetry (S.at (d * x)) (tensorPhysicalId U x) := by
  intro N hN
  rw [mpo_tensorPhysicalId]
  change S.action (tensorPhysicalIdOperator (mpo U N) x) =
    tensorPhysicalIdOperator (mpo U N) x
  calc
    S.action (tensorPhysicalIdOperator (mpo U N) x) =
        tensorPhysicalIdOperator (S.action (mpo U N)) x :=
      (S.tensorPhysicalId_semiconj d x N (mpo U N)).symm
    _ = tensorPhysicalIdOperator (mpo U N) x := congrArg (fun X ↦
      tensorPhysicalIdOperator X x) (hU hN)

/-- Invariance transports through blocking, with the blocked action and its
applicable lengths pulled back along \(N\mapsto Nk\).

Source: arXiv:1703.09188, line 1366. -/
theorem IsInvariantUnderSymmetry.blockTensor
    {S : FiniteChainOperatorSymmetry d} {U : MPOTensor d D}
    (hU : IsInvariantUnderSymmetry S U) (k : ℕ) :
    IsInvariantUnderSymmetry (S.block k) (blockTensor U k) := by
  intro N hN
  rw [mpo_blockTensor_eq_reindex]
  simp only [FiniteChainOperatorSymmetry.block_action]
  let e := MPSTensor.blockedConfigEquiv d N k
  have hreindex : Matrix.reindex e e
      (Matrix.reindex e.symm e.symm (mpo U (N * k))) = mpo U (N * k) := by
    ext σ τ
    simp [Matrix.reindex_apply]
  rw [hreindex, hU hN]

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

Lines 1340--1343 introduce this definition in full analogy with
`def:strictly-equivalent-tensors`, whose endpoints are in canonical form.
Canonical form is required only at the endpoints. The physical dimension is
identified explicitly, and the virtual bond dimension remains fixed along the
path.

**Scope restriction (arXiv:1703.09188, lines 1340--1354):** the paper does not
specify a stabilization for unequal raw virtual bond dimensions, so this
definition only compares tensors in one fixed ambient bond dimension. See
`docs/paper-gaps/mpu_equivalence_fixed_bond.tex`.

Source: arXiv:1703.09188, Definition `def:strictly-equivalent-symmetry`,
lines 1345--1354. -/
def StrictlyEquivalentUnderSymmetry (S : FiniteChainOperatorSymmetry db)
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
    {S : FiniteChainOperatorSymmetry db} {U : MPOTensor da D} {V : MPOTensor db D}
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

/-- Two fixed-bond MPU tensors are equivalent under a coherent symmetry family
when, after adjoining positive coprime identity ancillas and then applying a
common positive blocking length, they are strictly equivalent under the
canonically blocked enlarged-dimension symmetry.

The order is ancilla attachment followed by blocking. The component at the full
enlarged physical dimension is supplied by the coherent family; it is not an
extension chosen from the original-dimension action. The blocked applicable
lengths are exactly \(\{N\mid Nk\in A\}\).

**Scope restriction (arXiv:1703.09188, lines 1356--1366):** the bond dimension
\(D\) is fixed. The standard-form path criterion belongs to a separate result.
See `docs/paper-gaps/mpu_equivalence_fixed_bond.tex`.

Source: arXiv:1703.09188, Definition `def:equivalent-symmetry`, lines 1356--1366. -/
def EquivalentUnderSymmetry (S : FiniteChainOperatorSymmetryFamily)
    (U : MPOTensor da D) (V : MPOTensor db D) : Prop :=
  IsMPU U ∧ IsMPU V ∧
    ∃ k pa pb : ℕ,
      0 < k ∧ 0 < pa ∧ 0 < pb ∧ Nat.Coprime pa pb ∧
        ∃ hphys : pa * da = pb * db,
          StrictlyEquivalentUnderSymmetry
            ((S.at (db * pb)).block k)
            (blockTensor (tensorPhysicalId U pa) k)
            (blockTensor (tensorPhysicalId V pb) k)
            (blockedAncillaPhysicalDim_eq k hphys)

/-- Forgetting the symmetry from stabilized symmetry-preserving equivalence gives
ordinary stabilized equivalence.

Source: arXiv:1703.09188, Definitions `def:equivalent-tensors` and
`def:equivalent-symmetry`, lines 716--724 and 1356--1366. -/
theorem EquivalentUnderSymmetry.toEquivalent
    {S : FiniteChainOperatorSymmetryFamily}
    {U : MPOTensor da D} {V : MPOTensor db D}
    (h : EquivalentUnderSymmetry S U V) : Equivalent U V := by
  rcases h with ⟨hU, hV, k, pa, pb, hk, hpa, hpb, hcoprime, hphys, hstrict⟩
  exact ⟨hU, hV, k, pa, pb, hk, hpa, hpb, hcoprime, hphys,
    hstrict.toStrictlyEquivalent⟩

end MPOTensor
