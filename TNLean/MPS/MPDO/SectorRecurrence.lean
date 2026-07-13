/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.DirectedWalkCoboundary
import TNLean.Algebra.KroneckerFactorPositivity
import TNLean.MPS.MPDO.SectorEtaPositivity

/-!
# Recurrence of the nonzero sector support graph

The paper-gap note `docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`
records a four-sector scalar counterexample showing that positivity of every
cyclic tensor product `Ω_k = ⊗_n η_{k_n,k_{n+1}}`
(`MPOTensor.cyclicEtaTensorProduct_posSemidef`) is not by itself enough to
choose the neighboring operators `η_{k,h}` positive semidefinite by a single
coherent rescaling of the sectors. The obstruction is a nonzero directed edge
`k → h` of the sector support graph (`η_{k,h} ≠ 0`) that does not lie on any
nonzero directed cycle: a phase mismatch along such an edge cannot be
detected by any cyclic product, since every cyclic product containing the
edge also contains a compensating factor elsewhere.

This file formalizes the recurrence condition identified in the paper-gap
note: every nonzero directed edge lies on a nonzero directed cycle
(`MPOTensor.IsRecurrentSupport`). It also proves that positivity of the cyclic
product along one fixed cycle forces a compatible choice of phases on the
occurrences around that cycle: this is the content of
`MPOTensor.exists_pi_smul_posSemidef_of_cyclicEtaTensorProduct_posSemidef`,
obtained from the `N`-ary Kronecker rescaling
(`Matrix.exists_pi_smul_posSemidef_of_finKronecker_posSemidef`) applied to
the cyclic tensor product after reindexing along the horizontal bond fiber.

The recurrence declarations and the phase-uniqueness theorem
`Matrix.exists_pos_real_smul_eq_of_smul_posSemidef` prepare the coherent
rephasing argument in `TNLean.MPS.MPDO.RecurrentSectorRephasing`. That later
module combines the choices from different cycles under the recurrence
hypothesis. For the inverse-map physical-sector factorization, recurrence after
zero-weight reparameterization is derived from injectivity in
`TNLean.MPS.MPDO.InverseMapActiveSectorRecurrence`. The fixed-cycle theorem
below applies to a general neighboring-operator family and does not use
recurrence.

## Main declarations

- `MPOTensor.IsSectorEdge`: a nonzero directed edge `k → h` of the sector
  support graph of a neighboring-operator family.
- `MPOTensor.SectorReaches`: reachability by a (possibly empty) directed path
  of nonzero edges.
- `MPOTensor.IsRecurrentSupport`: every nonzero directed edge lies on a
  nonzero directed cycle.
- `MPOTensor.CycleFiber`, `MPOTensor.cycleFiberToSectorFiber`: the horizontal
  bond fiber around a cyclic sector assignment, and its reindexing into the
  vertex-indexed sector fiber of `cyclicEtaTensorProduct`.
- `MPOTensor.cyclicEtaTensorProduct_submatrix_eq_finKronecker`: the cyclic
  tensor product, reindexed along the horizontal bond fiber, is the finite
  Kronecker product of the consecutive neighboring operators around the
  cycle.
- `MPOTensor.exists_pi_smul_posSemidef_of_cyclicEtaTensorProduct_posSemidef`:
  positivity of a cyclic tensor product with every consecutive neighboring
  operator nonzero forces a coherent choice of phases around that cycle,
  with product equal to `1`.
- `MPOTensor.exists_pi_smul_posSemidef_of_sectorEta_cycle`: the preceding
  fixed-cycle result for the concrete inverse-map neighboring operators.

## Scope

For a general neighboring-operator family, recurrence remains a hypothesis.
Conditional on it, `TNLean.MPS.MPDO.RecurrentSectorRephasing` propagates the
per-cycle choices into a single vertex-indexed rephasing. The concrete
inverse-map family arising from an injective tensor satisfies recurrence after
zero-weight reparameterization, as proved in
`TNLean.MPS.MPDO.InverseMapActiveSectorRecurrence`.

## References

- [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1446--1471
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPOTensor

variable {d D N : ℕ}
variable {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}

/-! ### The nonzero sector support graph -/

/-- A nonzero directed edge of the sector support graph of a neighboring
operator family: `η_{k,h} ≠ 0`.

Source: `docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`, the
directed graph underlying the four-sector counterexample. -/
def IsSectorEdge {hη : EtaStructure ρ} (eta : etaOperators hη) (k h : Fin hη.m) : Prop :=
  eta k h ≠ 0

/-- Reachability in the sector support graph: `h` is reached from `k` by a
(possibly empty) directed path of nonzero edges. -/
def SectorReaches {hη : EtaStructure ρ} (eta : etaOperators hη) :
    Fin hη.m → Fin hη.m → Prop :=
  Relation.ReflTransGen (IsSectorEdge eta)

/-- **Recurrence of the sector support graph.** Every nonzero directed edge
`k → h` lies on a nonzero directed cycle: `h` can reach back to `k` by a
directed path of nonzero edges. Equivalently, the support graph is a
disjoint union of strongly connected components, with no edges between
distinct components.

This is the sufficient condition identified in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex` to rule out
the four-sector counterexample to a coherent positive choice of the
`η_{k,h}`.

This is an auxiliary condition from
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`; it is not an
additional hypothesis stated in arXiv:1606.00608. -/
def IsRecurrentSupport {hη : EtaStructure ρ} (eta : etaOperators hη) : Prop :=
  ∀ k h : Fin hη.m, IsSectorEdge eta k h → SectorReaches eta h k

/-- Reachability in the nonzero sector support is equivalently witnessed by a
finite directed walk of nonzero neighboring operators.

Source: `docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`,
the elimination plan for coherent sector rephasing. -/
theorem sectorReaches_iff_directedWalkReaches {hη : EtaStructure ρ}
    (eta : etaOperators hη) (k h : Fin hη.m) :
    SectorReaches eta k h ↔
      TNLean.Algebra.DirectedWalk.Reaches (IsSectorEdge eta) k h := by
  exact (TNLean.Algebra.DirectedWalk.reaches_iff_reflTransGen _).symm

/-- Recurrence of the nonzero sector support is exactly the return-walk
hypothesis for its directed edge relation.

Source: `docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`,
the elimination plan for coherent sector rephasing. -/
theorem isRecurrentSupport_iff_directedWalkReturns {hη : EtaStructure ρ}
    (eta : etaOperators hη) :
    IsRecurrentSupport eta ↔
      ∀ {k h : Fin hη.m}, IsSectorEdge eta k h →
        TNLean.Algebra.DirectedWalk.Reaches (IsSectorEdge eta) h k := by
  constructor
  · intro hrec k h hkh
    exact (sectorReaches_iff_directedWalkReaches eta h k).mp (hrec k h hkh)
  · intro hrec k h hkh
    exact (sectorReaches_iff_directedWalkReaches eta h k).mpr (hrec hkh)

/-! ### The horizontal bond fiber around a cyclic sector assignment -/

/-- The horizontal bond fiber around a cyclic sector assignment `k`: at each
position `n`, the shared virtual index between the right sector bond of site
`n` and the left sector bond of site `n + 1`. Its elements index the
individual factors `η_{k_n,k_{n+1}}` of the cyclic tensor product. -/
abbrev CycleFiber [NeZero N] (hη : EtaStructure ρ) (k : Fin N → Fin hη.m) : Type :=
  (n : Fin N) → Fin (hη.dR (k n)) × Fin (hη.dL (k (n + 1)))

/-- The reindexing from the horizontal bond fiber to the vertex-indexed
sector fiber of `cyclicEtaTensorProduct`: the left part of site `n` is
recovered from the right part of site `n - 1` (transported along the
resulting sector equality), and the right part of site `n` is read directly
off the fiber at `n`. -/
noncomputable def cycleFiberToSectorFiber [NeZero N] (hη : EtaStructure ρ)
    (k : Fin N → Fin hη.m) (y : CycleFiber hη k) : SectorFiber hη k :=
  fun n =>
    (Equiv.cast (congrArg (fun x => Fin (hη.dL (k x))) (by abel : n - 1 + 1 = n))
        (y (n - 1)).2,
      (y n).1)

/-- The right part of `cycleFiberToSectorFiber` at `n + 1` recovers the left
part of `y n`, transported along the resulting sector equality. This is the
key computation making `cycleFiberToSectorFiber` a correct reindexing for
`cyclicEtaTensorProduct`. -/
private theorem cycleFiberToSectorFiber_succ_fst [NeZero N] (hη : EtaStructure ρ)
    (k : Fin N → Fin hη.m) (y : CycleFiber hη k) (n : Fin N) :
    (cycleFiberToSectorFiber hη k y (n + 1)).1 = (y n).2 := by
  unfold cycleFiberToSectorFiber
  simp only
  have hn : n + 1 - 1 = n := by abel
  generalize_proofs h
  revert h
  rw [hn]
  intro h
  simp

/-- **The cyclic tensor product is the finite Kronecker product of its
neighboring operators.** Reindexed along the horizontal bond fiber, the
cyclic tensor product `Ω_k = ⊗_n η_{k_n,k_{n+1}}` is literally the finite
Kronecker product of the consecutive neighboring operators around the cycle.

Source: arXiv:1606.00608, Appendix C.2, lines 1446--1450 (equation defining
`Ω_k` as the cyclic tensor product). -/
theorem cyclicEtaTensorProduct_submatrix_eq_finKronecker
    [NeZero N] (hη : EtaStructure ρ) (eta : etaOperators hη) (k : Fin N → Fin hη.m) :
    (cyclicEtaTensorProduct hη eta k).submatrix
        (cycleFiberToSectorFiber hη k) (cycleFiberToSectorFiber hη k) =
      Matrix.finKronecker (fun n => eta (k n) (k (n + 1))) := by
  ext y z
  simp only [Matrix.submatrix_apply, Matrix.finKronecker_apply]
  change (∏ n : Fin N, eta (k n) (k (n + 1))
      ((cycleFiberToSectorFiber hη k y n).2, (cycleFiberToSectorFiber hη k y (n + 1)).1)
      ((cycleFiberToSectorFiber hη k z n).2, (cycleFiberToSectorFiber hη k z (n + 1)).1)) = _
  refine Finset.prod_congr rfl fun n _ => ?_
  have hy1 : (cycleFiberToSectorFiber hη k y n).2 = (y n).1 := rfl
  have hy2 : (cycleFiberToSectorFiber hη k y (n + 1)).1 = (y n).2 :=
    cycleFiberToSectorFiber_succ_fst hη k y n
  have hz1 : (cycleFiberToSectorFiber hη k z n).2 = (z n).1 := rfl
  have hz2 : (cycleFiberToSectorFiber hη k z (n + 1)).1 = (z n).2 :=
    cycleFiberToSectorFiber_succ_fst hη k z n
  rw [hy1, hy2, hz1, hz2]

/-- **Positive rescaling around one nonzero sector cycle.** If the cyclic
tensor product along a sector assignment is positive semidefinite and every
neighboring operator on that cycle is nonzero, then every factor can be
rescaled to a positive semidefinite matrix. The rescaling coefficients are
nonzero and have product one.

This theorem concerns one fixed cycle. It does not assert that the choices
obtained from two different cycles agree on their common edges.

This is a supporting lemma for the positive-choice step at arXiv:1606.00608,
Appendix C.2, lines 1446--1450. The recurrence route is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`. -/
theorem exists_pi_smul_posSemidef_of_cyclicEtaTensorProduct_posSemidef
    [NeZero N] (hη : EtaStructure ρ) (eta : etaOperators hη)
    (k : Fin N → Fin hη.m)
    (hpos : (cyclicEtaTensorProduct hη eta k).PosSemidef)
    (hne : ∀ n, eta (k n) (k (n + 1)) ≠ 0) :
    ∃ c : Fin N → ℂ, (∀ n, c n ≠ 0) ∧ (∏ n, c n = 1) ∧
      ∀ n, (c n • eta (k n) (k (n + 1))).PosSemidef := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  apply Matrix.exists_pi_smul_posSemidef_of_finKronecker_posSemidef hN
  · rw [← cyclicEtaTensorProduct_submatrix_eq_finKronecker hη eta k]
    exact hpos.submatrix _
  · exact hne

/-- **Positive rescaling around one nonzero sector cycle, for the
sector-adapted MPDO neighboring operators.** Given the injective sector
factorization data of a simple MPDO and a nonzero directed cycle of the
sector support graph, the concrete neighboring operators `sectorEta` around
the cycle have a compatible choice of phases: scalars, all nonzero, with
product `1`, rescaling every consecutive `η_{k_n,k_{n+1}}` to be positive
semidefinite.

This theorem concerns one fixed cycle. Conditional on recurrence,
`MPOTensor.exists_vertexPhase_smul_posSemidef` propagates these choices into
a single vertex-indexed rephasing over the whole support graph.

This is a supporting lemma for arXiv:1606.00608, Appendix C.2,
lines 1446--1450, not a separately stated result of the paper. -/
theorem exists_pi_smul_posSemidef_of_sectorEta_cycle
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ)
    (hρ : IsThreeSiteClosure K R ρ) (hη : EtaStructure ρ)
    {α₁ β₃ : Fin D} (hm : R β₃ α₁ ≠ 0) (hM : IsMPDO K)
    {N : ℕ} [NeZero N] (k : Fin N → Fin hη.m)
    (hne : ∀ n : Fin N, sectorEta K hK hη R α₁ β₃ (k n) (k (n + 1)) ≠ 0) :
    ∃ c : Fin N → ℂ, (∀ n, c n ≠ 0) ∧ (∏ n, c n = 1) ∧
      ∀ n, (c n • sectorEta K hK hη R α₁ β₃ (k n) (k (n + 1))).PosSemidef := by
  have hpos := cyclicEtaTensorProduct_posSemidef K hη
    (fun q => sectorTensorL K hK hη R α₁ β₃ q) (fun q => sectorTensorR K hK hη β₃ q)
    (fun β α => physicalSlice_sector_factorization K hK R ρ hρ hη hm β α)
    (hM N) k
  have hne' : ∀ n : Fin N, etaOfSectorTensors hη
      (fun q => sectorTensorL K hK hη R α₁ β₃ q) (fun q => sectorTensorR K hK hη β₃ q)
      (k n) (k (n + 1)) ≠ 0 := by
    intro n
    rw [← sectorEta_eq_etaOfSectorTensors]
    exact hne n
  obtain ⟨c, hc, hprod, hcpos⟩ :=
    exists_pi_smul_posSemidef_of_cyclicEtaTensorProduct_posSemidef hη _ k hpos hne'
  refine ⟨c, hc, hprod, fun n => ?_⟩
  rw [sectorEta_eq_etaOfSectorTensors]
  exact hcpos n

end MPOTensor
