/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.CycleGroundSpace
import TNLean.PEPS.ParentHamiltonian.RegionPhysicalGroundSpaceTransport
import TNLean.MPS.ParentHamiltonian.ChainGroundSpace

/-!
# The full parent space of proper arcs on a cycle

The common regional PEPS ground space for all arcs of length `0<L<n` is
the actual periodic MPS chain ground space. This assembles the local
proper-arc identification using the same cyclic configurations on the
full physical space. No injectivity or positive physical or bond dimension
is required.

Source: arXiv:2011.12127, Section IV.C.1, the local MPS and graph parent
constructions at source lines 1987–2011.

**Scope restriction (cycle comparison):** The comparison uses `n≥3` and
`0<L<n`. The full-ring region has a different boundary prescription;
see `docs/paper-gaps/cpgsv21_physical_deformation_general_graph.tex`.
-/

namespace TNLean.PEPS

variable {n d D L : ℕ} [NeZero n]

private theorem cycle_offset_eq (s v : Fin n) :
    (v - s).val = (v.val + n - s.val) % n := by
  rw [val_sub_eq_ite]
  by_cases h : s.val ≤ v.val
  · rw [ite_eq_left h]
    have hsum : v.val + n - s.val = v.val - s.val + n := by omega
    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_right h, Nat.mod_eq_of_lt (by omega)]

/-- The regional assembly and cyclic-window assembly give the same full
configuration on a proper arc. Source: arXiv:2011.12127, local and graph
physical coordinates in Section IV.C.1, lines 1987–2011. -/
theorem assembleRegion_cycleArc_eq_cyclicCfg (hLn : L < n) (s : Fin n)
    (σ : Fin L → Fin d) (τ : Fin n → Fin d) :
    assembleRegionσ (cycleArcFrom s L) (cycleArcConfigEquiv hLn s σ)
        (fun v ↦ τ v.1) =
      MPSTensor.cyclicCfg (NeZero.pos n) L s σ τ := by
  funext v
  by_cases hv : v ∈ cycleArcFrom s L
  · have hoff : (v.val + n - s.val) % n < L := by
      rw [← cycle_offset_eq s v]
      exact mem_cycleArcFrom.mp hv
    simp only [assembleRegionσ, dite_eq_left hv, MPSTensor.cyclicCfg, dite_eq_left hoff]
    change σ ((arcSiteEquiv hLn s).symm ⟨v, hv⟩) = σ ⟨_, hoff⟩
    congr 1
    apply Fin.ext
    exact cycle_offset_eq s v
  · have hoff : ¬((v.val + n - s.val) % n < L) := by
      rw [← cycle_offset_eq s v]
      exact fun h ↦ hv (mem_cycleArcFrom.mpr h)
    simp [assembleRegionσ, hv, MPSTensor.cyclicCfg, hoff]

/-- Ordering a regional slice is the actual cyclic restriction of the full
state. Source: arXiv:2011.12127, Section IV.C.1, lines 1987–2011. -/
theorem cycleArcPhysical_regionSliceMap (hLn : L < n) (s : Fin n)
    (τ : Fin n → Fin d) (ψ : MPSTensor.NSiteSpace d n) :
    cycleArcPhysicalEquiv hLn s
        (regionSliceMap (cycleArcFrom s L) (fun v ↦ τ v.1) ψ) =
      MPSTensor.cyclicRestrictₗ (NeZero.pos n) L s τ ψ := by
  funext σ
  change ψ (assembleRegionσ (cycleArcFrom s L) (cycleArcConfigEquiv hLn s σ)
    (fun v ↦ τ v.1)) = ψ (MPSTensor.cyclicCfg (NeZero.pos n) L s σ τ)
  rw [assembleRegion_cycleArc_eq_cyclicCfg]

/-- A complementary assignment on a proper arc extends to a full background.
The exterior site supplies the filling value, so no nonzero physical-dimension
hypothesis is needed. Source: arXiv:2011.12127, the exterior factor in the
regional parent conditions, Section IV.C.1, lines 2003–2011. -/
theorem exists_cycleArc_complement_extension (hLn : L < n) (s : Fin n)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ cycleArcFrom s L)) :
    ∃ κ : Fin n → Fin d,
      (fun v : {v : Fin n // v ∈ Finset.univ \ cycleArcFrom s L} ↦ κ v.1) = τ := by
  let v : Fin n := s + ⟨L, hLn⟩
  have hv : v ∉ cycleArcFrom s L := by
    rw [mem_cycleArcFrom]
    change ¬((s + (⟨L, hLn⟩ : Fin n) - s).val < L)
    rw [add_sub_cancel_left]
    exact Nat.lt_irrefl L
  let outside : {v : Fin n // v ∈ Finset.univ \ cycleArcFrom s L} :=
    ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩⟩
  refine ⟨assembleRegionσ (cycleArcFrom s L) (fun _ ↦ τ outside) τ, ?_⟩
  funext w
  exact assembleRegionσ_notMem _ _ _ w

/-- Membership in the actual local arc ground space is equivalent to
membership in the MPS local space after ordering the sites.
Source: arXiv:2011.12127, Section IV.C.1, lines 1987–2011. -/
theorem mem_regionGroundSpace_cycleTensorOfMPS_iff (hn : 3 ≤ n) (hL : 0 < L)
    (hLn : L < n) (A : MPSTensor d D) (s : Fin n)
    (φ : RegionPhysicalConfig (d := d) (cycleArcFrom s L) → ℂ) :
    φ ∈ regionGroundSpace (cycleTensorOfMPS hn A) (cycleArcFrom s L) ↔
      cycleArcPhysicalEquiv hLn s φ ∈ MPSTensor.groundSpace A L := by
  rw [← map_regionGroundSpace_cycleTensorOfMPS hn hL hLn A s]
  constructor
  · intro hφ
    exact ⟨φ, hφ, rfl⟩
  · rintro ⟨χ, hχ, hχφ⟩
    exact (cycleArcPhysicalEquiv hLn s).injective hχφ ▸ hχ

/-- The actual common regional parent ground space on all nonempty proper
arcs equals the periodic MPS chain ground space, without injectivity or
positive physical or bond dimension. Source: arXiv:2011.12127,
Section IV.C.1, local and graph constructions at lines 1987–2011. -/
theorem regionParentGroundSpace_cycleTensorOfMPS (hn : 3 ≤ n) (hL : 0 < L)
    (hLn : L < n) (A : MPSTensor d D) :
    regionParentGroundSpace (cycleTensorOfMPS hn A) (fun s ↦ cycleArcFrom s L) =
      MPSTensor.chainGroundSpace A L n := by
  ext ψ
  rw [mem_regionParentGroundSpace_iff, MPSTensor.chainGroundSpace,
    dite_eq_left ⟨NeZero.pos n, Nat.le_of_lt hLn⟩]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  constructor
  · intro hψ s τ
    have hlocal := (mem_regionGroundSpace_cycleTensorOfMPS_iff hn hL hLn A s _).mp
      (hψ s (fun v ↦ τ v.1))
    rwa [cycleArcPhysical_regionSliceMap] at hlocal
  · intro hψ s τ
    obtain ⟨κ, hκ⟩ := exists_cycleArc_complement_extension hLn s τ
    apply (mem_regionGroundSpace_cycleTensorOfMPS_iff hn hL hLn A s _).mpr
    have hlocal := hψ s κ
    rw [← cycleArcPhysical_regionSliceMap hLn s κ ψ] at hlocal
    simpa only [hκ] using hlocal

end TNLean.PEPS
