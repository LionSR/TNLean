/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.SingletonGeneration

/-!
# Inverse locality inside a finite observable algebra

Forward commutators reflect through an actual finite star-automorphism.
The finite outside-singleton commutant then recovers exact support of the
inverse image. This argument does not require a previously constructed
inverse local family or a quasi-local automorphism.

Source context: arXiv:1703.09188, Appendix, lines 2292–2306; inverse locality
of one-dimensional cellular automata is derived in Schumacher–Werner,
quant-ph/0405174, Corollary 7.
-/

namespace SpinChain

/-- Forward commutation with every outside one-site algebra implies exact
finite support of the inverse image. This is commutator reflection through
the actual finite automorphism, followed by the finite relative commutant.
Source context: arXiv:1703.09188, Appendix, lines 2292–2306. -/
theorem inverse_mem_range_localInclusion_of_forward_commute
    {d : ℕ} [NeZero d] {K Γ : Finset ℤ} (hK : K ⊆ Γ)
    (e : LocalAlgebra d Γ ≃⋆ₐ[ℂ] LocalAlgebra d Γ) (B : LocalAlgebra d Γ)
    (hForward : ∀ (x : ℤ) (hx : x ∈ Γ \ K) (C : LocalAlgebra d {x}),
      Commute B (e (localInclusion
        (Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mp hx).1) C))) :
    e.symm B ∈ Set.range (localInclusion (d := d) hK) := by
  apply (mem_range_localInclusion_iff_commute_outside_singletons hK (e.symm B)).mpr
  intro x hx C
  simpa only [StarAlgEquiv.symm_apply_apply] using (hForward x hx C).map e.symm

/-- Forward support disjointness derives the inverse support bound in the
actual finite algebra. Only the forward images of outside single-site
observables are used. No inverse-locality or inverse-compatibility premise
is supplied. Source context: arXiv:1703.09188, Appendix, lines 2292–2306. -/
theorem inverse_mem_range_localInclusion_of_forward_support
    {d : ℕ} [NeZero d] {J K Γ : Finset ℤ} (hJ : J ⊆ Γ) (hK : K ⊆ Γ)
    (e : LocalAlgebra d Γ ≃⋆ₐ[ℂ] LocalAlgebra d Γ) (B : LocalAlgebra d J)
    (hForward : ∀ (x : ℤ) (hx : x ∈ Γ \ K) (C : LocalAlgebra d {x}),
      ∃ (Δ : Finset ℤ) (hΔ : Δ ⊆ Γ), Disjoint Δ J ∧
        e (localInclusion
          (Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mp hx).1) C) ∈
            Set.range (localInclusion (d := d) hΔ)) :
    e.symm (localInclusion hJ B) ∈ Set.range (localInclusion (d := d) hK) := by
  apply inverse_mem_range_localInclusion_of_forward_commute hK e
    (localInclusion hJ B)
  intro x hx C
  obtain ⟨Δ, hΔ, hDisjoint, A, hA⟩ := hForward x hx C
  rw [← hA]
  rw [commute_iff_eq]
  apply localObservable_injective d Γ
  rw [map_mul, map_mul, localObservable_localInclusion, localObservable_localInclusion]
  exact (localObservable_commute_of_disjoint hDisjoint A B).symm.eq

end SpinChain
