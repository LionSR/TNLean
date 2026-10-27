/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.DependentPhysicalProductRangeSupport

/-!
# Reindexing and permutation invariance of physical product maps

Local coordinate bijections preserve a physical product image. Products of
local left inverses recover its coefficients, so an injective common local map
reflects invariance under permutations of the sites.

These identities support the injective PEPS translation-invariance construction
in arXiv:1804.04964, Applications, lines 1891–1894.
-/

noncomputable section

open scoped BigOperators Matrix

namespace TNLean.Lattice

/-- A local change of virtual coordinates leaves the physical product image
unchanged when the coefficient function is reindexed simultaneously.
Supporting calculation for arXiv:1804.04964, lines 1891–1894. -/
theorem dependentPhysicalProductFamilyMap_reindex_input
    {Site : Type*} [Fintype Site] [DecidableEq Site]
    {In In' Out : Site → Type*} [∀ v, Fintype (In v)] [∀ v, Fintype (In' v)]
    (e : (v : Site) → In' v ≃ In v)
    (F : (v : Site) → Matrix (Out v) (In v) ℂ)
    (R : ((v : Site) → In v) → ℂ) :
    dependentPhysicalProductFamilyMap (fun v o i => F v o (e v i))
        (fun x => R (fun v => e v (x v))) =
      dependentPhysicalProductFamilyMap F R := by
  funext x
  simp only [dependentPhysicalProductFamilyMap_apply]
  exact (Equiv.piCongrRight e).sum_comp
    (fun σ : (v : Site) → In v => (∏ v, F v (x v) (σ v)) * R σ)

end TNLean.Lattice

namespace TNLean.Lattice

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- Local left inverses give a left inverse for the full product map.
Supporting calculation for arXiv:1804.04964, lines 1891–1894. -/
private theorem dependentPhysicalProductFamilyMap_leftInverse
    {In Out : Site → Type*} [∀ v, Fintype (In v)] [∀ v, Fintype (Out v)]
    [∀ v, DecidableEq (In v)]
    (F : (v : Site) → Matrix (Out v) (In v) ℂ)
    (L : (v : Site) → Matrix (In v) (Out v) ℂ)
    (hLF : ∀ v, L v * F v = 1) :
    Function.LeftInverse (dependentPhysicalProductFamilyMap L)
      (dependentPhysicalProductFamilyMap F) := by
  have hcomp : dependentPhysicalProductFamilyMap L ∘ₗ
      dependentPhysicalProductFamilyMap F = LinearMap.id := by
    rw [dependentPhysicalProductFamilyMap_comp]
    simp_rw [hLF]
    exact dependentPhysicalProductFamilyMap_one
  intro ψ
  exact LinearMap.congr_fun hcomp ψ

/-- A common local matrix preserves invariance under every specified
permutation of the sites. Supporting calculation for arXiv:1804.04964,
lines 1891–1894; no invariance of a chosen gauge family is assumed. -/
private theorem commonPhysicalProductFamilyMap_invariant
    {In Out : Type*} [Fintype In]
    (M : Matrix Out In ℂ) (τ : Equiv.Perm Site) (ψ : (Site → In) → ℂ)
    (hψ : ∀ σ, ψ (fun v => σ (τ v)) = ψ σ) (x : Site → Out) :
    dependentPhysicalProductFamilyMap (fun _ : Site => M) ψ (fun v => x (τ v)) =
      dependentPhysicalProductFamilyMap (fun _ : Site => M) ψ x := by
  classical
  let e : (Site → In) ≃ (Site → In) :=
    { toFun := fun σ v => σ (τ v)
      invFun := fun σ v => σ (τ.symm v)
      left_inv := fun σ => by funext v; simp
      right_inv := fun σ => by funext v; simp }
  simp only [dependentPhysicalProductFamilyMap_apply]
  calc
    _ = ∑ σ : Site → In,
          (∏ v : Site, M (x (τ v)) (σ (τ v))) * ψ (fun v => σ (τ v)) :=
        (e.sum_comp (fun σ : Site → In =>
          (∏ v : Site, M (x (τ v)) (σ v)) * ψ σ)).symm
    _ = _ := by
      refine Finset.sum_congr rfl ?_
      intro σ hσ
      rw [hψ]
      congr 1
      exact Fintype.prod_equiv τ
        (fun v : Site => M (x (τ v)) (σ (τ v)))
        (fun v : Site => M (x v) (σ v)) (fun _ => rfl)

/-- An injective common local map reflects invariance under a site
permutation. Its left inverse is derived from injectivity, rather than
supplied as a new hypothesis. This is the common-left-inverse step supporting
arXiv:1804.04964, lines 1891–1894. -/
theorem invariant_of_commonPhysicalProductFamilyMap_invariant
    {In Out : Type*} [Fintype In] [Finite Out]
    (F : Matrix Out In ℂ) (hF : Function.Injective (Matrix.mulVecLin F))
    (τ : Equiv.Perm Site) (R : (Site → In) → ℂ)
    (hψ : ∀ σ,
      dependentPhysicalProductFamilyMap (fun _ : Site => F) R
          (fun v => σ (τ v)) =
        dependentPhysicalProductFamilyMap (fun _ : Site => F) R σ)
    (x : Site → In) :
    R (fun v => x (τ v)) = R x := by
  classical
  let := Fintype.ofFinite Out
  obtain ⟨l, hl⟩ := (Matrix.mulVecLin F).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hF)
  let L : Matrix In Out ℂ := LinearMap.toMatrix' l
  have hLF : L * F = 1 := by
    calc
      L * F = LinearMap.toMatrix' l *
          LinearMap.toMatrix' (Matrix.toLin' F) := by
        rw [LinearMap.toMatrix'_toLin']
      _ = LinearMap.toMatrix' (l ∘ₗ Matrix.toLin' F) :=
        (LinearMap.toMatrix'_comp l (Matrix.toLin' F)).symm
      _ = 1 := by
        rw [Matrix.toLin'_apply', hl, LinearMap.toMatrix'_id]
  have hrec := dependentPhysicalProductFamilyMap_leftInverse
    (fun _ : Site => F) (fun _ : Site => L) (fun _ => hLF) R
  have h := commonPhysicalProductFamilyMap_invariant L τ
    (dependentPhysicalProductFamilyMap (fun _ : Site => F) R) hψ x
  simpa only [hrec] using h

end TNLean.Lattice
