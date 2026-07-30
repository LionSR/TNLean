/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.EventuallyConstantCycleWeights
import TNLean.MPS.RFP.BeigiGroundSpaceDimension
import TNLean.MPS.RFP.BeigiSectorGraph

/-!
# Eventually constant Beigi sector graphs

Beigi's finite-chain formula expresses the parent-ground-space dimension as
the weighted sum of ordered cycles in the sector graph.  If these dimensions
are eventually constant, the finite graph theorem shows that every cyclic
edge ground space is one-dimensional and every directed cycle is a repeated
loop.  Consequently the ground-space dimension at every length covered by
the parent formula equals the number of loops.

## References

* S. Beigi, *Classification of the phases of 1D spin chains with commuting
  Hamiltonians*, J. Phys. A 45 (2012) 025306, Section IV, equations (7)--(13).
-/

open scoped BigOperators

namespace MPSTensor.BeigiSectorGraphData

open FiniteWeightedDigraph

variable {d D : ℕ} {A : MPSTensor d D}

/-- The dimension of the ground space carried by a directed sector edge.

Source: Beigi, J. Phys. A 45 (2012) 025306, equation (4) and Section IV. -/
noncomputable def edgeWeight (F : BeigiSectorGraphData A)
    (a b : Fin F.sectorCount) : ℕ :=
  Module.finrank ℂ (F.edgeGroundSpace a b)

/-- A sector edge is present exactly when its edge-ground-space dimension is
nonzero.

Source: Beigi, J. Phys. A 45 (2012) 025306, equation (4) and Section IV. -/
theorem isEdge_iff_edgeWeight_ne_zero (F : BeigiSectorGraphData A)
    (a b : Fin F.sectorCount) :
    F.IsEdge a b ↔ F.edgeWeight a b ≠ 0 := by
  constructor
  · intro hedge hzero
    exact hedge (Submodule.finrank_eq_zero.mp hzero)
  · intro hweight hbot
    exact hweight (Submodule.finrank_eq_zero.mpr hbot)

private theorem next_eq_add_one {N : ℕ} [NeZero N] (hN : 0 < N) (i : Fin N) :
    FiniteWeightedDigraph.next hN i = i + 1 := by
  apply Fin.ext
  simp [FiniteWeightedDigraph.next, Fin.add_def]

/-- The abstract weighted-cycle sum agrees with Beigi's sum over ordered
sector cycles.

Source: Beigi, J. Phys. A 45 (2012) 025306, equation (4) and Section IV. -/
theorem cycleWeightSum_edgeWeight_eq (F : BeigiSectorGraphData A)
    {N : ℕ} (hN : 0 < N) :
    letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
    cycleWeightSum F.edgeWeight hN =
      ∑ c : F.OrderedCycle N,
        ∏ n : Fin N, F.edgeWeight (c.1 n) (c.1 (n + 1)) := by
  classical
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let weight : (Fin N → Fin F.sectorCount) → ℕ := fun k ↦
    ∏ n : Fin N, F.edgeWeight (k n) (k (n + 1))
  let cycle : (Fin N → Fin F.sectorCount) → Prop := fun k ↦
    ∀ n : Fin N, F.IsEdge (k n) (k (n + 1))
  unfold cycleWeightSum FiniteWeightedDigraph.cycleWeight
  simp_rw [next_eq_add_one hN]
  change ∑ k : Fin N → Fin F.sectorCount, weight k =
    ∑ c : {k // cycle k}, weight c.1
  calc
    ∑ k : Fin N → Fin F.sectorCount, weight k =
        ∑ k ∈ Finset.univ.filter cycle, weight k := by
      symm
      apply Finset.sum_subset (Finset.filter_subset cycle Finset.univ)
      intro k _ hk
      have hncycle : ¬cycle k := by simpa using hk
      simp only [cycle, not_forall] at hncycle
      obtain ⟨n, hn⟩ := hncycle
      change (∏ m : Fin N, F.edgeWeight (k m) (k (m + 1))) = 0
      rw [Finset.prod_eq_zero (Finset.mem_univ n)]
      exact not_ne_iff.mp ((F.isEdge_iff_edgeWeight_ne_zero _ _).not.mp hn)
    _ = ∑ c : {k // cycle k}, weight c.1 := by
      exact Finset.sum_subtype (Finset.univ.filter cycle) (by simp) weight

/-- Eventual constancy of the actual parent-ground-space dimension implies
eventual constancy of the numerical weighted-cycle sum.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV. -/
theorem hasEventuallyConstantCycleWeightSum_of_parentGroundSpace
    (F : BeigiSectorGraphData A)
    (hparent : ∃ c N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      Module.finrank ℂ (parentHamiltonianGroundSpaceES A 2 N) = c) :
    HasEventuallyConstantCycleWeightSum F.edgeWeight := by
  rcases hparent with ⟨c, N₀, hparent⟩
  refine ⟨c, max N₀ 2, ?_⟩
  intro N hN hNpos
  have hN₀ : N₀ < N := (Nat.le_max_left N₀ 2).trans_lt hN
  have htwo : 2 < N := (Nat.le_max_right N₀ 2).trans_lt hN
  rw [F.cycleWeightSum_edgeWeight_eq hNpos]
  simpa only [edgeWeight] using
    (F.parentHamiltonianGroundSpaceES_finrank_eq (Nat.le_of_lt htwo)).symm.trans
      (hparent N hN₀)

/-- If the parent-ground-space dimension is eventually constant, then at
every length greater than two it equals the number of positive sector loops.

Source: Beigi, J. Phys. A 45 (2012) 025306, equation (13). -/
theorem parentHamiltonianGroundSpaceES_finrank_eq_card_loop
    (F : BeigiSectorGraphData A)
    (hparent : ∃ c N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      Module.finrank ℂ (parentHamiltonianGroundSpaceES A 2 N) = c)
    {N : ℕ} (hN : 2 < N) :
    Module.finrank ℂ (parentHamiltonianGroundSpaceES A 2 N) =
      Fintype.card (Loop F.edgeWeight) := by
  have hNpos : 0 < N := by omega
  letI : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  have hconst := F.hasEventuallyConstantCycleWeightSum_of_parentGroundSpace hparent
  calc
    Module.finrank ℂ (parentHamiltonianGroundSpaceES A 2 N) =
        ∑ c : F.OrderedCycle N,
          ∏ n : Fin N,
            Module.finrank ℂ (F.edgeGroundSpace (c.1 n) (c.1 (n + 1))) :=
      F.parentHamiltonianGroundSpaceES_finrank_eq (Nat.le_of_lt hN)
    _ = cycleWeightSum F.edgeWeight hNpos := by
      simpa only [edgeWeight] using (F.cycleWeightSum_edgeWeight_eq hNpos).symm
    _ = Fintype.card (Loop F.edgeWeight) := cycleWeightSum_eq_card_loop hconst hNpos

/-- Transport to Euclidean-space coordinates preserves the dimension of the
parent ground space. -/
theorem parentHamiltonianGroundSpaceES_finrank_eq_ker
    (A : MPSTensor d D) (L N : ℕ) :
    Module.finrank ℂ (parentHamiltonianGroundSpaceES A L N) =
      Module.finrank ℂ (LinearMap.ker (parentHamiltonian A L N)) := by
  unfold parentHamiltonianGroundSpaceES
  exact LinearEquiv.finrank_map_eq
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm
    (LinearMap.ker (parentHamiltonian A L N))

/-- In the BNT nearest-neighbor parent-Hamiltonian setting, every finite-chain
dimension covered by Beigi's cycle formula equals the number of positive
sector loops.

Source: CPSV16, Definition 3.9 and Theorem 3.10, lines 517--540; Beigi,
J. Phys. A 45 (2012) 025306, Section IV. -/
theorem parentHamiltonianGroundSpaceES_finrank_eq_card_loop_of_hasBNTSectorData
    {P : SectorDecomposition d} (F : BeigiSectorGraphData P.toTensor)
    (hBNT : HasBNTSectorData P)
    (hNNCPH : HasNNCPHGroundSpaces P.toTensor P.basis)
    {N : ℕ} (hN : 2 < N) :
    Module.finrank ℂ (parentHamiltonianGroundSpaceES P.toTensor 2 N) =
      Fintype.card (Loop F.edgeWeight) := by
  rcases hBNT.eventually_parentHamiltonian_groundSpace_finrank_eq hNNCPH with
    ⟨N₀, hraw⟩
  have hparent : ∃ c N₁ : ℕ, ∀ M : ℕ, N₁ < M →
      Module.finrank ℂ (parentHamiltonianGroundSpaceES P.toTensor 2 M) = c := by
    refine ⟨P.basisCount, N₀, ?_⟩
    intro M hM
    rw [parentHamiltonianGroundSpaceES_finrank_eq_ker]
    exact hraw M hM
  exact F.parentHamiltonianGroundSpaceES_finrank_eq_card_loop hparent hN

end MPSTensor.BeigiSectorGraphData
