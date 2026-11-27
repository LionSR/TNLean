/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Commuting.Defs
import QICLean.Algebra.Combinatorics.EventuallyConstantCycleWeights
import TNLean.MPS.ParentHamiltonian.Commuting.SectorGraph.BeigiSectorGraph

/-!
# Eventual dimension of nearest-neighbor parent ground spaces

For a sector decomposition whose basis matrix product vectors are eventually
linearly independent, the all-chain nearest-neighbor ground-space spanning
condition makes the parent-Hamiltonian ground-space dimension eventually equal
to the number of basis sectors. This is the scale-invariance hypothesis used in
Beigi's classification of one-dimensional commuting Hamiltonians.

## Main statement

* `HasBNTSectorData.eventually_parentHamiltonian_groundSpace_finrank_eq`:
  the parent ground-space dimension is eventually the number of distinct BNT
  representatives.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Definition 3.9 and Theorem 3.10, lines 517--540.
* S. Beigi, *Classification of the phases of 1D spin chains with commuting
  Hamiltonians*, J. Phys. A 45 (2012) 025306, arXiv:1105.1019.

## Eventually constant Beigi sector graphs

Beigi's finite-chain formula expresses the parent-ground-space dimension as
the weighted sum of ordered cycles in the sector graph.  If these dimensions
are eventually constant, the finite graph theorem shows that every cyclic
edge ground space is one-dimensional and every directed cycle is a repeated
loop.  Consequently the ground-space dimension at every length covered by
the parent formula equals the number of loops.

### References

* S. Beigi, *Classification of the phases of 1D spin chains with commuting
  Hamiltonians*, J. Phys. A 45 (2012) 025306, Section IV, equations (7)--(13).
-/

open MPTensor

section

namespace MPSTensor

/-- If the basis-sector matrix product vectors are eventually linearly independent and
span every sufficiently long nearest-neighbor parent ground space, then the dimension of
that ground space is eventually the number of distinct basis sectors.

Comparison: arXiv:1606.00608, Definition 3.9 and Theorem 3.10, lines 517--540.
Those passages do not state this dimension count. It is a local consequence of
the all-chain spanning equality and eventual linear independence, and supplies
the eventual ground-state degeneracy used in Beigi, J. Phys. A 45 (2012)
025306, Section IV. Documented in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem HasBNTSectorData.eventually_parentHamiltonian_groundSpace_finrank_eq
    {d : ℕ} {P : SectorDecomposition (Fin d)}
    (hBNT : HasBNTSectorData P)
    (hNNCPH : HasNNCPHGroundSpaces P.toTensor P.basis) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      Module.finrank ℂ (LinearMap.ker (parentHamiltonian P.toTensor 2 N)) =
        P.basisCount := by
  rcases hBNT with ⟨N₁, hLI⟩
  refine ⟨max N₁ 2, ?_⟩
  intro N hN
  have hN₁ : N₁ < N := lt_of_le_of_lt (Nat.le_max_left _ _) hN
  have hTwo : 2 < N := lt_of_le_of_lt (Nat.le_max_right _ _) hN
  have hImage : LinearIndependent ℂ
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap ∘
        fun j : Fin P.basisCount ↦ (mpv (P.basis j) : NSiteSpace d N)) := by
    convert hLI N hN₁ using 1
    funext j
    ext σ
    simp [Function.comp_apply, mpvState_apply]
  have hCoefficients : LinearIndependent ℂ
      (fun j : Fin P.basisCount ↦ (mpv (P.basis j) : NSiteSpace d N)) :=
    LinearIndependent.of_comp
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap hImage
  rw [(hNNCPH N hTwo).groundSpaceSpanning, bntMPSVectorSpan]
  simpa using finrank_span_eq_card hCoefficients

end MPSTensor

end

section

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

private theorem next_eq_add_one {N : ℕ} (hN : 0 < N) (i : Fin N) :
    haveI : NeZero N := ⟨by omega⟩;
    FiniteWeightedDigraph.next hN i = i + 1 := by
  have : NeZero N := ⟨by omega⟩
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
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
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
    (hparent : ∃ c N₀ : ℕ, ∀ N : ℕ, ∀ hN : N₀ < N, haveI : NeZero N := ⟨Nat.ne_zero_of_lt hN⟩;
      Module.finrank ℂ (ManyBody.groundSpace (parentRingInteraction A 2 N).hamiltonian 0) = c) :
    HasEventuallyConstantCycleWeightSum F.edgeWeight := by
  rcases hparent with ⟨c, N₀, hparent⟩
  refine ⟨c, max N₀ 2, ?_⟩
  intro N hN hNpos
  have hN₀ : N₀ < N := (Nat.le_max_left N₀ 2).trans_lt hN
  have htwo : 2 < N := (Nat.le_max_right N₀ 2).trans_lt hN
  rw [F.cycleWeightSum_edgeWeight_eq hNpos]
  simpa only [edgeWeight] using
    (F.groundSpace_hamiltonian_parentRingInteraction_finrank_eq (Nat.le_of_lt htwo)).symm.trans
      (hparent N hN₀)

/-- If the parent-ground-space dimension is eventually constant, then at
every length greater than two it equals the number of positive sector loops.

Source: Beigi, J. Phys. A 45 (2012) 025306, equation (13). -/
theorem groundSpace_hamiltonian_parentRingInteraction_finrank_eq_card_loop
    (F : BeigiSectorGraphData A)
    (hparent : ∃ c N₀ : ℕ, ∀ N : ℕ, ∀ hN : N₀ < N, haveI : NeZero N := ⟨Nat.ne_zero_of_lt hN⟩;
      Module.finrank ℂ (ManyBody.groundSpace (parentRingInteraction A 2 N).hamiltonian 0) = c)
    {N : ℕ} (hN : 2 < N) :
    haveI : NeZero N := ⟨by omega⟩;
    Module.finrank ℂ (ManyBody.groundSpace (parentRingInteraction A 2 N).hamiltonian 0) =
      Fintype.card (Loop F.edgeWeight) := by
  have hNpos : 0 < N := by omega
  have : NeZero N := ⟨by omega⟩
  have hconst := F.hasEventuallyConstantCycleWeightSum_of_parentGroundSpace hparent
  calc
    Module.finrank ℂ (ManyBody.groundSpace (parentRingInteraction A 2 N).hamiltonian 0) =
        ∑ c : F.OrderedCycle N,
          ∏ n : Fin N,
            Module.finrank ℂ (F.edgeGroundSpace (c.1 n) (c.1 (n + 1))) :=
      F.groundSpace_hamiltonian_parentRingInteraction_finrank_eq (Nat.le_of_lt hN)
    _ = cycleWeightSum F.edgeWeight hNpos := by
      simpa only [edgeWeight] using (F.cycleWeightSum_edgeWeight_eq hNpos).symm
    _ = Fintype.card (Loop F.edgeWeight) := cycleWeightSum_eq_card_loop hconst hNpos

/-- In the BNT nearest-neighbor parent-Hamiltonian setting, every finite-chain
dimension covered by Beigi's cycle formula equals the number of positive
sector loops.

Source: CPSV16, Definition 3.9 and Theorem 3.10, lines 517--540; Beigi,
J. Phys. A 45 (2012) 025306, Section IV. -/
theorem groundSpace_hamiltonian_parentRingInteraction_finrank_eq_card_loop_of_hasBNTSectorData
    {P : SectorDecomposition (Fin d)} (F : BeigiSectorGraphData P.toTensor)
    (hBNT : HasBNTSectorData P)
    (hNNCPH : HasNNCPHGroundSpaces P.toTensor P.basis)
    {N : ℕ} (hN : 2 < N) :
    haveI : NeZero N := ⟨by omega⟩;
    Module.finrank ℂ
        (ManyBody.groundSpace (parentRingInteraction P.toTensor 2 N).hamiltonian 0) =
      Fintype.card (Loop F.edgeWeight) := by
  rcases hBNT.eventually_parentHamiltonian_groundSpace_finrank_eq hNNCPH with
    ⟨N₀, hraw⟩
  have hparent : ∃ c N₁ : ℕ, ∀ M : ℕ, ∀ hM : N₁ < M,
      haveI : NeZero M := ⟨Nat.ne_zero_of_lt hM⟩;
      Module.finrank ℂ
        (ManyBody.groundSpace (parentRingInteraction P.toTensor 2 M).hamiltonian 0) = c := by
    refine ⟨P.basisCount, N₀, ?_⟩
    intro M hM
    have : NeZero M := ⟨Nat.ne_zero_of_lt hM⟩
    rw [groundSpace_hamiltonian_parentRingInteraction_eq_map_ker]
    exact (LinearEquiv.finrank_map_eq (WithLp.linearEquiv 2 ℂ (NSiteSpace d M)).symm _).trans
      (hraw M hM)
  exact F.groundSpace_hamiltonian_parentRingInteraction_finrank_eq_card_loop hparent hN

end MPSTensor.BeigiSectorGraphData

end
