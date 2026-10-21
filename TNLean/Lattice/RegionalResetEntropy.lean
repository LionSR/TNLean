/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PermutationMatrixUnitary
import TNLean.Lattice.RegionalReset
import TNLean.Lattice.ReplicaSwap
import TNLean.Lattice.SupportedUnitaryEntropy

/-!
# Entropy comparison after a regional replica swap

A unitary supported away from two cores approximates the regional swap of two
identical normalized replicas. The swapped state has a product marginal on the
cores, so entropy continuity bounds their original mutual information.

Sources: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 419–435;
polynomial-PEPS, `02-information.tex`, lines 612–630.
-/

open Matrix QuantumCircuit

namespace TNLean.Lattice

/-- Entropy comparison for a supported unitary approximating the regional swap
of two identical replicas. The replica construction itself gives the product
marginal on the two cores. Source: TNLean one-dimensional note,
part2a_mps_information.tex, lines 419–435; polynomial-PEPS, 02-information.tex,
lines 612–630. -/
theorem mutualInformation_cores_le_of_reset_unitary
    {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ) (hq : 1 ≤ q)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    (D R₀ C₀ : Finset ι) (hR₀ : R₀ ⊆ D) (hC₀ : Disjoint C₀ D)
    (S : Finset ι) (hS : Disjoint S (R₀ ∪ C₀))
    (U : Matrix (ι → Fin (q * q)) (ι → Fin (q * q)) ℂ)
    (hUu : U ∈ Matrix.unitaryGroup _ ℂ)
    (hUs : U ∈ QuantumCircuit.supportedOperators (q * q) (S : Set ι)) (δ : ℝ) :
    let e := QuantumCircuit.sitePairConfigurationEquiv ι q q
    let ψ := fun c ↦ Ω (e.symm c).1 * Ω (e.symm c).2
    let F := Matrix.reindex e e (sheetSwapOp q D)
    ‖WithLp.toLp 2 (U *ᵥ ψ) - WithLp.toLp 2 (F *ᵥ ψ)‖ ≤ δ →
    FiniteProduct.mutualInformation (fun _ : ι ↦ Fin q) Ω R₀ C₀ ≤
      8 * Real.sqrt δ * Real.log (Real.exp 1 * (q : ℝ) ^ R₀.card) := by
  classical
  intro e ψ F hUerr
  have hΩsum : ∑ i, ‖WithLp.ofLp Ω i‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hΩ]
    norm_num
  have hψn : ‖WithLp.toLp 2 ψ‖ = 1 :=
    (EuclideanSpace.norm_toLp_comp_equiv e.symm (doubledVector (WithLp.ofLp Ω))).trans
      (Matrix.norm_doubledVector hΩsum)
  have hF : F ∈ unitaryGroup _ ℂ :=
    Matrix.reindex_mem_unitaryGroup e (sheetSwapOp q D)
      (sheetSwap q D).permMatrix_mem_unitaryGroup
  have hφn : ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 :=
    (Matrix.norm_toLp_mulVec_of_unitary hF ψ).trans hψn
  let Pe := sumArrowSitePair (ι) q
  let U' := Matrix.reindex Pe.symm Pe.symm U
  let Ψ := FiniteProduct.sumSitesProduct Ω Ω
  let Φ := FiniteProduct.relabelSites (replicaSwap D) Ψ
  have hΨ : Ψ = WithLp.toLp 2 (ψ ∘ Pe) := by
    apply WithLp.ofLp_injective 2
    exact (doubledVector_comp_sumArrow e Ω).symm
  have hΦ : Φ = WithLp.toLp 2 ((F *ᵥ ψ) ∘ Pe) := by
    apply WithLp.ofLp_injective 2
    exact (sheetSwapOp_mulVec_comp_sumArrow e D Ω).symm
  have hΨn : ‖Ψ‖ = 1 := by
    rw [hΨ, EuclideanSpace.norm_toLp_comp_equiv]
    exact hψn
  have hΦn : ‖Φ‖ = 1 := by
    rw [hΦ, EuclideanSpace.norm_toLp_comp_equiv]
    exact hφn
  have hU's := reindex_sumArrow_sitePair_mem_supportedOperators q hUs
  have hU'u : U'ᴴ * U' = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.reindex_mem_unitaryGroup Pe.symm U hUu)
  have hδ : ‖WithLp.toLp 2 (U' *ᵥ WithLp.ofLp Ψ) - Φ‖ ≤ δ := by
    have htransport := norm_reindex_mulVec_sub Pe.symm U ψ (F *ᵥ ψ)
    rw [Equiv.symm_symm] at htransport
    rw [hΨ, hΦ, WithLp.ofLp_toLp]
    exact htransport.trans_le hUerr
  have hXJ : Disjoint (R₀.disjSum (∅ : Finset ι)) (C₀.disjSum ∅) := by
    apply Finset.disjoint_left.mpr
    rintro (v | v) hv hv'
    · simp only [Finset.inl_mem_disjSum] at hv hv'
      exact Finset.disjoint_left.mp hC₀ hv' (hR₀ hv)
    · simp at hv
  have hSsum : Disjoint ((S.disjSum S : Finset (ι ⊕ ι)) : Set (ι ⊕ ι))
      ((R₀.disjSum ∅ ∪ C₀.disjSum ∅ : Finset (ι ⊕ ι)) : Set (ι ⊕ ι)) := by
    apply Set.disjoint_left.mpr
    rintro (v | v) hv hv'
    · simp only [Finset.mem_coe, Finset.inl_mem_disjSum] at hv
      have hcore : v ∈ R₀ ∪ C₀ := by
        simpa only [Finset.mem_coe, Finset.mem_union, Finset.inl_mem_disjSum] using hv'
      exact Finset.disjoint_left.mp hS hv hcore
    · simp at hv'
  have hprod := mutualInformation_relabelSites_replicaSwap_eq_zero hΩ hR₀
    hC₀
  have hent := TNLean.Lattice.mutualInformation_le_of_supported_unitary
    hΨn hΦn hXJ hSsum hU's hU'u hprod
  rw [FiniteProduct.mutualInformation_sumSitesProduct_inl hΩ hΩ] at hent
  have hcard : Fintype.card (FiniteProduct.Configuration
      (fun _ : ι ⊕ ι ↦ Fin q) (R₀.disjSum ∅)) = q ^ R₀.card := by
    simp only [FiniteProduct.Configuration, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_coe, Finset.card_disjSum, Finset.card_empty, add_zero]
  rw [hcard] at hent
  push_cast at hent
  have hlog0 : 0 ≤ Real.log (Real.exp 1 * (q : ℝ) ^ R₀.card) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le (Real.one_le_exp zero_le_one)
      (one_le_pow₀ (by exact_mod_cast hq)))
  exact hent.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hδ) (by norm_num)) hlog0)

end TNLean.Lattice
