/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.IntervalCoordinates
import TNLean.Circuit.SiteEmbedding
import QICLean.ManyBody.Sites.PlaceAlong

/-!
# Finite local inclusions in numbered support coordinates

An arbitrary local inclusion into an integer interval is precisely the
placement `ManyBody.placeAlong` along the numbering of the retained sites
(`SpinChain.finiteChainRegionEmbedding`). Thus its
matrix belongs to the existing supported-operator algebra on the numbered
retained sites. No interval shape of the retained region is required.

Source: arXiv:1703.09188, Appendix, identity-tensor inclusions,
lines 2285–2295.
-/

namespace SpinChain

/-- The numbering of the sites of a region `Λ` inside the interval of `N` sites starting at
`a`, as an injection into the numbered sites. Source: arXiv:1703.09188, Appendix,
lines 2285–2295. -/
def finiteChainRegionEmbedding {N : ℕ} {a : ℤ} {Λ : Finset ℤ}
    (hΛ : Λ ⊆ finiteChainRegion a N) : Λ ↪ Fin N where
  toFun x := (finiteChainSiteEquiv a N).symm ⟨x.val, hΛ x.property⟩
  inj' x y hxy := by
    apply Subtype.ext
    have h := congrArg (fun i => (finiteChainSiteEquiv a N i).val) hxy
    simpa only [Equiv.apply_symm_apply] using h

theorem finiteChainRegionEmbedding_apply {N : ℕ} {a : ℤ} {Λ : Finset ℤ}
    (hΛ : Λ ⊆ finiteChainRegion a N) (x : Λ) :
    finiteChainRegionEmbedding hΛ x = (finiteChainSiteEquiv a N).symm ⟨x.val, hΛ x.property⟩ :=
  rfl

/-- Numbering an arbitrary finite local inclusion gives the placement along the numbering of
the region. Source: arXiv:1703.09188, Appendix, lines 2285–2295. -/
theorem intervalCoordinates_localInclusion_eq_placeAlong
    {d N : ℕ} {a : ℤ} {Λ : Finset ℤ} (hΛ : Λ ⊆ finiteChainRegion a N)
    (A : LocalAlgebra d Λ) :
    intervalCoordinates d a N (localInclusion hΛ A) =
      ManyBody.placeAlong (X := fun _ ↦ Fin d) (finiteChainRegionEmbedding hΛ)
        (CStarMatrix.ofMatrix.symm A) := by
  classical
  let E := finiteChainSiteEquiv a N
  let e := finiteChainRegionEmbedding hΛ
  ext σ τ
  have hAgree : (Config.splitEquiv hΛ (finiteChainConfigEquiv d N a σ)).2 =
      (Config.splitEquiv hΛ (finiteChainConfigEquiv d N a τ)).2 ↔
      ∀ i, (∀ x, e x ≠ i) → σ i = τ i := by
    constructor
    · intro h i hi
      have hx : (E i).val ∉ Λ := by
        intro hx
        exact hi ⟨(E i).val, hx⟩ (E.symm_apply_apply i)
      have h' := congrFun h ⟨(E i).val, Finset.mem_sdiff.mpr ⟨(E i).property, hx⟩⟩
      change σ (E.symm (E i)) = τ (E.symm (E i)) at h'
      simpa only [Equiv.symm_apply_apply] using h'
    · intro h
      funext x
      let i := E.symm ⟨x.val, (Finset.mem_sdiff.mp x.property).1⟩
      apply h i
      intro y hy
      have hyx : y.val = x.val := by
        have hval := congrArg (fun j => (E j).val) hy
        simpa only [E, e, i, finiteChainRegionEmbedding_apply, Equiv.apply_symm_apply] using
          hval
      exact (Finset.mem_sdiff.mp x.property).2 (hyx ▸ y.property)
  rw [intervalCoordinates_apply, localInclusion_apply, ManyBody.placeAlong_apply, mul_ite,
    mul_one, mul_zero]
  by_cases h : ∀ i, (∀ x, e x ≠ i) → σ i = τ i
  · rw [ite_eq_left (hAgree.mpr h), ite_eq_left h]
    rfl
  · rw [ite_eq_right (mt hAgree.mp h), ite_eq_right h]

/-- Every actual local inclusion is supported on the same numbered sites.
Source: arXiv:1703.09188, Appendix, lines 2285–2295. -/
theorem intervalCoordinates_localInclusion_mem_supportedOperators
    {d N : ℕ} {a : ℤ} {Λ : Finset ℤ} (hΛ : Λ ⊆ finiteChainRegion a N)
    (A : LocalAlgebra d Λ) :
    intervalCoordinates d a N (localInclusion hΛ A) ∈
      ManyBody.supportedOperators (fun _ ↦ Fin d)
        (Finset.univ.filter fun (i : Fin N) ↦ (finiteChainSiteEquiv a N i).val ∈ Λ) := by
  classical
  rw [intervalCoordinates_localInclusion_eq_placeAlong]
  apply ManyBody.supportedOperators_mono ?_
    (ManyBody.placeAlong_mem_supportedOperators (X := fun _ ↦ Fin d)
      (finiteChainRegionEmbedding hΛ) (CStarMatrix.ofMatrix.symm A))
  intro _ hx
  obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hx
  simpa only [finiteChainRegionEmbedding_apply, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.apply_symm_apply] using x.property

end SpinChain
