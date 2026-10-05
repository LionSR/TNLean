/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.PVBS
import TNLean.MPS.ParentHamiltonian.KernelChainGroundSpace
import TNLean.MPS.ParentHamiltonian.Martingale.OpenHamiltonian

/-!
# Open ground space of the one-species PVBS chain

The nearest-neighbour parent constraints exclude adjacent particles and relate
`01` and `10` amplitudes by the parameter `q`. They select exactly the vacuum
and the geometric one-particle state on an open interval.

## References

- Bachmann and Nachtergaele, arXiv:1112.4097, Section II,
equations (4), (6)–(8); arXiv:1212.3718, Section 2.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- The two elementary nearest-neighbour constraints of a PVBS boundary state. -/
theorem pvbs_pair_constraints (q : ℂ) (N : ℕ) {v : NSiteSpace 2 (N + 2)}
    (hv : v ∈ groundSpace (pvbsTensor q) (N + 2)) :
    v (Fin.cons 1 (Fin.cons 1 0)) = 0 ∧
      v (Fin.cons 0 (Fin.cons 1 0)) = q * v (Fin.cons 1 (Fin.cons 0 0)) := by
  obtain ⟨a, b, rfl⟩ := (mem_groundSpace_pvbsTensor_iff q (N + 2) v).mp hv
  simp [pvbsVacuum_cons, mul_comm]

/-- The length-two MPS space is exactly the kernel of the two PVBS constraints. -/
theorem mem_groundSpace_pvbs_two_iff (q : ℂ) (v : NSiteSpace 2 2) :
    v ∈ groundSpace (pvbsTensor q) 2 ↔
      v (Fin.cons 1 (Fin.cons 1 0)) = 0 ∧
        v (Fin.cons 0 (Fin.cons 1 0)) = q * v (Fin.cons 1 (Fin.cons 0 0)) := by
  refine ⟨pvbs_pair_constraints q 0, ?_⟩
  rintro ⟨h11, h01⟩
  apply (mem_groundSpace_pvbsTensor_iff q 2 v).mpr
  have hc (i j : Fin 2) : (Fin.cons i (Fin.cons j (0 : Cfg 2 0)) : Cfg 2 2) = ![i, j] := by
    ext k
    fin_cases k <;> rfl
  simp only [hc] at h11 h01
  refine ⟨v ![0, 0], v ![1, 0], ?_⟩
  ext σ
  obtain ⟨i, j, rfl⟩ : ∃ i j : Fin 2, σ = ![i, j] := by
    refine ⟨σ 0, σ 1, ?_⟩
    ext k
    fin_cases k <;> rfl
  fin_cases i <;> fin_cases j <;>
    simp [pvbsVacuum, pvbsEdge, Pi.single_apply, funext_iff, Fin.forall_fin_succ,
      h11, h01, mul_comm]

/-- The PVBS spaces satisfy the intersection property from two sites onward,
although their tensor is not injective. -/
theorem groundSpace_pvbs_intersection (q : ℂ) (N : ℕ) :
    ((⨅ j : Fin 2, (groundSpace (pvbsTensor q) (N + 2)).comap (restrictLastₗ j)) ⊓
      (⨅ i : Fin 2, (groundSpace (pvbsTensor q) (N + 2)).comap (restrictFirstₗ i))) =
        groundSpace (pvbsTensor q) (N + 3) := by
  ext v
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
  constructor
  · rintro ⟨hl, hr⟩
    obtain ⟨a, b, h0⟩ := (mem_groundSpace_pvbsTensor_iff q (N + 2) _).mp (hr 0)
    obtain ⟨c, e, h1⟩ := (mem_groundSpace_pvbsTensor_iff q (N + 2) _).mp (hr 1)
    have hh := pvbs_pair_constraints q N (hl 0)
    have hzero : Fin.snoc (0 : Cfg 2 N) (0 : Fin 2) = (0 : Cfg 2 (N + 1)) := by
      funext k
      refine Fin.lastCases (by simp) (fun _ => by simp) k
    have he : e = 0 := by
      have h := hh.1
      simp only [restrictLastₗ, LinearMap.coe_mk, AddHom.coe_mk,
        ← Fin.cons_snoc_eq_snoc_cons, hzero] at h
      have heval := congrFun h1 (Fin.cons 1 0)
      simpa [restrictFirstₗ] using heval.symm.trans h
    have hb : b = q * c := by
      have h := hh.2
      simp only [restrictLastₗ, LinearMap.coe_mk, AddHom.coe_mk,
        ← Fin.cons_snoc_eq_snoc_cons, hzero] at h
      have h0eval := congrFun h0 (Fin.cons 1 0)
      have h1eval := congrFun h1 (Fin.cons 0 0)
      simpa [restrictFirstₗ, pvbsVacuum_cons, pvbsEdge, he] using
        h0eval.symm.trans (h.trans (congrArg (q * ·) h1eval))
    apply (mem_groundSpace_pvbsTensor_iff q (N + 3) v).mpr
    refine ⟨a, c, ?_⟩
    apply eq_of_forall_restrictFirst_eq
    intro i
    fin_cases i
    · ext σ
      have h := congrFun h0 σ
      simpa [restrictFirst_apply, restrictFirstₗ, pvbsVacuum_cons, hb,
        mul_assoc, mul_left_comm] using h
    · ext σ
      have h := congrFun h1 σ
      simpa [restrictFirst_apply, restrictFirstₗ, pvbsVacuum_cons, he] using h
  · intro hv
    exact ⟨groundSpace_inLeftGround _ _ hv, groundSpace_inRightGround _ _ hv⟩

/-- Every state satisfying the nonwrapping nearest-neighbour constraints is a
vacuum-particle superposition. This uses the existing general interval iteration. -/
theorem contiguous_mem_groundSpace_pvbs {N : ℕ} (q : ℂ) (hN : 2 ≤ N)
    {v : NSiteSpace 2 N}
    (hv : ∀ (s : ℕ) (hs : s + 2 ≤ N) (τ : Cfg 2 N),
      contiguousRestrictₗ s 2 hs τ v ∈ groundSpace (pvbsTensor q) 2) :
    v ∈ groundSpace (pvbsTensor q) N := by
  apply contiguous_mem_of_restriction_intersection_submodules
    (fun n => groundSpace (pvbsTensor q) n) (by omega) hN ?_ hv
  intro M hM
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 2 := ⟨M - 2, by omega⟩
  exact groundSpace_pvbs_intersection q n

/-- The open nearest-neighbour parent Hamiltonian has exactly the full PVBS
matrix-product space as its zero-energy space. -/
theorem ker_openParentHamiltonianES_pvbs (q : ℂ) {N : ℕ} (hN : 2 ≤ N) :
    LinearMap.ker (openParentHamiltonianES (pvbsTensor q) 2 N) =
      groundSpaceES (pvbsTensor q) N := by
  refine le_antisymm ?_ (groundSpaceES_le_ker_openParentHamiltonianES _ 2 N)
  intro v hv
  rw [mem_groundSpaceES_iff]
  apply contiguous_mem_groundSpace_pvbs q hN
  intro s hs τ
  have h := cyclicRestrictₗ_mem_groundSpace_of_mem_ker_openParentHamiltonianES
    (pvbsTensor q) hN hv ⟨s, by omega⟩ hs τ
  rwa [cyclicRestrictₗ_eq_contiguousRestrictₗ _ hN hs] at h

/-- There are exactly two independent zero-energy states on every open chain of
at least two sites, for every complex PVBS parameter. -/
theorem finrank_ker_openParentHamiltonianES_pvbs (q : ℂ) {N : ℕ} (hN : 2 ≤ N) :
    Module.finrank ℂ (LinearMap.ker (openParentHamiltonianES (pvbsTensor q) 2 N)) = 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [ker_openParentHamiltonianES_pvbs q hN, groundSpaceES, LinearEquiv.finrank_map_eq]
  exact finrank_groundSpace_pvbsTensor q n

end MPSTensor
