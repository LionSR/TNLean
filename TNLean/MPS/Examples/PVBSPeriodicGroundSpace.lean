/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.PVBSGroundSpace
import TNLean.MPS.ParentHamiltonian.CyclicTranslation

/-!
# Periodic vacuum uniqueness for the PVBS parent Hamiltonian

The open PVBS ground space contains a geometric one-particle state. A cyclic
translation of any periodic ground vector must lie in that same open space.
Comparing its first two particle amplitudes forces `b = qᴺ b`. Thus the
periodic ground space is precisely the vacuum span when `qᴺ ≠ 1`.

Source: Bachmann and Nachtergaele, arXiv:1112.4097, Section II,
equations (4), (6)–(8); the periodic closure is an elementary consequence
of the printed local constraints.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- Periodic local constraints contain all nonwrapping constraints of the PVBS chain. -/
theorem chainGroundSpace_pvbs_le_groundSpace (q : ℂ) {N : ℕ} (hN : 2 ≤ N) :
    chainGroundSpace (pvbsTensor q) 2 N ≤ groundSpace (pvbsTensor q) N := by
  intro v hv
  have hN0 : 0 < N := by omega
  rw [chainGroundSpace, dite_eq_left ⟨hN0, hN⟩] at hv
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv
  apply contiguous_mem_groundSpace_pvbs q hN
  intro s hs τ
  have h := hv ⟨s, by omega⟩ τ
  rwa [cyclicRestrictₗ_eq_contiguousRestrictₗ _ hN hs] at h

/-- The product vacuum satisfies every periodic nearest-neighbour PVBS constraint. -/
theorem pvbsVacuum_mem_chainGroundSpace (q : ℂ) {N : ℕ} (hN : 2 ≤ N) :
    pvbsVacuum N ∈ chainGroundSpace (pvbsTensor q) 2 N := by
  have hN0 : 0 < N := by omega
  rw [chainGroundSpace, dite_eq_left ⟨hN0, hN⟩]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro i τ
  apply (mem_groundSpace_pvbs_two_iff q _).mpr
  have hz (ω : Cfg 2 2) (hω : ω ≠ 0) :
      cyclicRestrictₗ hN0 2 i τ (pvbsVacuum N) ω = 0 := by
    have hcfg : cyclicCfg hN0 2 i ω τ ≠ 0 := by
      intro h
      apply hω
      rw [← cyclicCfg_cyclicForwardSite hN0 hN i ω τ, h]
      rfl
    simp [cyclicRestrictₗ_apply, pvbsVacuum, hcfg]
  have h11 := hz (Fin.cons 1 (Fin.cons 1 0)) (by
    intro h
    have hh : (1 : Fin 2) = 0 := congrFun h 0
    exact one_ne_zero hh)
  have h01 := hz (Fin.cons 0 (Fin.cons 1 0)) (by
    intro h
    have hh : (1 : Fin 2) = 0 := congrFun h 1
    exact one_ne_zero hh)
  have h10 := hz (Fin.cons 1 (Fin.cons 0 0)) (by
    intro h
    have hh : (1 : Fin 2) = 0 := congrFun h 0
    exact one_ne_zero hh)
  exact ⟨h11, by rw [h01, h10, mul_zero]⟩

/-- Cyclic translation shifts the location of a single particle by the inverse offset. -/
theorem cyclicTranslateCfg_excitedAt {N : ℕ} [NeZero N] (s k : Fin N) :
    cyclicTranslateCfg s (excitedAt N k) = excitedAt N (k - s) := by
  ext j
  simp [cyclicTranslateCfg, excitedAt, eq_sub_iff_add_eq]

/-- Periodic closure forces the coefficient of the edge excitation to satisfy
`b = qᴺ b`. -/
theorem pvbs_periodic_particle_coefficient (q : ℂ) (N : ℕ) {a b : ℂ}
    (hv : a • pvbsVacuum (N + 2) + b • pvbsEdge q (N + 2) ∈
      chainGroundSpace (pvbsTensor q) 2 (N + 2)) :
    b = b * q ^ (N + 2) := by
  have ht := cyclicTranslateState_mem_chainGroundSpace (pvbsTensor q)
    (by omega : 0 < N + 2) (by omega : 2 ≤ N + 2) (1 : Fin (N + 2)) hv
  obtain ⟨c, e, he⟩ := (mem_groundSpace_pvbsTensor_iff q (N + 2) _).mp
    (chainGroundSpace_pvbs_le_groundSpace q (by omega) ht)
  have he0 := congrFun he (excitedAt (N + 2) 0)
  have he1 := congrFun he (excitedAt (N + 2) 1)
  have hlast : ((0 : Fin (N + 2)) - 1).val = N + 1 := by
    simp
  simp only [cyclicTranslateState, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, cyclicTranslateCfg_excitedAt, pvbsVacuum_excitedAt,
    pvbsEdge_excitedAt, zero_sub, sub_self, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, mul_zero, zero_add, mul_one] at he0 he1
  rw [← zero_sub (1 : Fin (N + 2)), hlast] at he0
  calc
    b = e * q := he1
    _ = (b * q ^ (N + 1)) * q := by rw [← he0]
    _ = b * q ^ (N + 2) := by simp only [pow_succ, mul_assoc]

/-- For a parameter with `qᴺ ≠ 1`, the periodic parent ground space has no
particle component and consists exactly of the product vacuum. -/
theorem chainGroundSpace_pvbs_eq_vacuum (q : ℂ) {N : ℕ} (hN : 2 ≤ N)
    (hq : q ^ N ≠ 1) :
    chainGroundSpace (pvbsTensor q) 2 N = Submodule.span ℂ {pvbsVacuum N} := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  refine le_antisymm ?_ (Submodule.span_le.mpr ?_)
  · intro v hv
    obtain ⟨a, b, rfl⟩ := (mem_groundSpace_pvbsTensor_iff q (n + 2) v).mp
      (chainGroundSpace_pvbs_le_groundSpace q hN hv)
    have h := pvbs_periodic_particle_coefficient q n hv
    have hb : b = 0 := by
      have hz : b * (q ^ (n + 2) - 1) = 0 := by linear_combination -h
      exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hq)
    simp only [hb, zero_smul, add_zero]
    exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton _))
  · intro v hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    exact pvbsVacuum_mem_chainGroundSpace q hN

/-- The zero-energy space of the periodic nearest-neighbour parent Hamiltonian
is the vacuum span whenever `qᴺ ≠ 1`. -/
theorem ker_parentHamiltonian_pvbs (q : ℂ) {N : ℕ} (hN : 2 ≤ N) (hq : q ^ N ≠ 1) :
    LinearMap.ker (parentHamiltonian (pvbsTensor q) 2 N) =
      Submodule.span ℂ {pvbsVacuum N} := by
  rw [ker_parentHamiltonian_eq_chainGroundSpace _ (by omega) hN]
  exact chainGroundSpace_pvbs_eq_vacuum q hN hq

/-- The periodic zero-energy space is one-dimensional away from a finite-ring resonance. -/
theorem finrank_ker_parentHamiltonian_pvbs (q : ℂ) {N : ℕ} (hN : 2 ≤ N)
    (hq : q ^ N ≠ 1) :
    Module.finrank ℂ (LinearMap.ker (parentHamiltonian (pvbsTensor q) 2 N)) = 1 := by
  rw [ker_parentHamiltonian_pvbs q hN hq]
  apply finrank_span_singleton
  intro h
  have hh := congrFun h (0 : Cfg 2 N)
  simp at hh

/-- Off the unit circle, no positive power of the hopping parameter equals one. -/
theorem pvbs_pow_ne_one_of_norm_ne_one (q : ℂ) (hq : ‖q‖ ≠ 1) {N : ℕ}
    (hN : 0 < N) : q ^ N ≠ 1 := by
  intro h
  apply hq
  have hn : ‖q‖ ^ N = (1 : ℝ) ^ N := by simpa using congrArg norm h
  exact (pow_left_inj₀ (norm_nonneg q) zero_le_one hN.ne').mp hn

/-- Away from the unit circle, every periodic chain of at least two sites has
only the vacuum as a zero-energy state.

**Local fix (critical parameter):** the review's unrestricted periodic-uniqueness
claim excludes the critical hopping value; see
`docs/paper-gaps/cpgsv21_pvbs_threshold.tex`. -/
theorem ker_parentHamiltonian_pvbs_of_norm_ne_one (q : ℂ) (hq : ‖q‖ ≠ 1)
    {N : ℕ} (hN : 2 ≤ N) :
    LinearMap.ker (parentHamiltonian (pvbsTensor q) 2 N) =
      Submodule.span ℂ {pvbsVacuum N} :=
  ker_parentHamiltonian_pvbs q hN (pvbs_pow_ne_one_of_norm_ne_one q hq (by omega))

/-- The critical two-site W vector satisfies both periodic local constraints. -/
theorem pvbsEdge_one_two_mem_chainGroundSpace :
    pvbsEdge 1 2 ∈ chainGroundSpace (pvbsTensor 1) 2 2 := by
  rw [chainGroundSpace, dite_eq_left ⟨by omega, le_rfl⟩]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro i τ
  apply (mem_groundSpace_pvbs_two_iff 1 _).mpr
  fin_cases i <;>
    simp [cyclicRestrictₗ_apply, cyclicCfg, pvbsEdge, pvbsVacuum, Fin.tail,
      Pi.single_apply, funext_iff, Fin.forall_fin_succ]

/-- At the critical parameter, a nonvacuum periodic zero-energy state exists
already on two sites, refuting unrestricted periodic vacuum uniqueness. -/
theorem pvbs_critical_periodic_counterexample :
    ∃ v ∈ LinearMap.ker (parentHamiltonian (pvbsTensor 1) 2 2),
      v ∉ Submodule.span ℂ {pvbsVacuum 2} := by
  refine ⟨pvbsEdge 1 2, ?_, ?_⟩
  · rw [ker_parentHamiltonian_eq_chainGroundSpace _ (by omega) le_rfl]
    exact pvbsEdge_one_two_mem_chainGroundSpace
  · intro h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
    have he := congrFun ha (excitedAt 2 0)
    simp [pvbsVacuum_excitedAt, pvbsEdge_excitedAt] at he

end MPSTensor
