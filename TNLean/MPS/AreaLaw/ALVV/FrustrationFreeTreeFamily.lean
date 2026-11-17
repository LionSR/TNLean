/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.FrustrationFreeImprovingFamily

/-!
# The frustration-free improving family in the coordinates of the merge tree

ALVV, arXiv:1602.08828v2, Theorem `t:unique`, lines 1829–1855, runs the merge tree with the
improving family of Theorem `t:aisff`, lines 1580–1609, for a frustration-free chain with a
unique ground state `Γ` and spectral gap `γ`. The merge tree measures viability of a space on
an interval `J` against the image of `ℂ Γ` under the region-first tensor split of `J` and its
complement. This file restates Theorem `t:aisff` under the hypotheses of Theorem `t:unique` and
in those coordinates.

The spectral gap above the kernel gives the quadratic-form gap used by Theorem `t:aisff`, the
kernel of `H` is the line `ℂ Γ`, and the exterior-first tensor split in which Theorem `t:aisff`
is stated is the region-first split after exchanging the factors.
-/

open scoped InnerProductSpace TensorProduct ComplexOrder MatrixOrder
open Matrix

namespace TNLean.MPS.AreaLaw.ALVV

open TNLean.MPS.AreaLaw TNLean.Lattice

/-- For a positive chain whose kernel is the line spanned by `Γ`, the kernel of the Euclidean
operator of `H` is that line. Auxiliary to ALVV, arXiv:1602.08828v2, Theorem `t:unique`,
lines 1829–1855. -/
theorem ker_toEuclideanCLM_eq_span_singleton {σ : Type*} [Fintype σ] [DecidableEq σ]
    {H : Matrix σ σ ℂ} (Γ : EuclideanSpace ℂ σ) (hΓ : H *ᵥ Γ.ofLp = 0)
    (huniq : ∀ x : EuclideanSpace ℂ σ, H *ᵥ x.ofLp = 0 → x ∈ ℂ ∙ Γ) :
    LinearMap.ker (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) H).toLinearMap = ℂ ∙ Γ := by
  have hzero (x : EuclideanSpace ℂ σ) :
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) H x = 0 ↔ H *ᵥ x.ofLp = 0 := by
    rw [← WithLp.ofLp_eq_zero, Matrix.ofLp_toEuclideanCLM]
  apply le_antisymm
  · intro x hx
    exact huniq x ((hzero x).mp (LinearMap.mem_ker.mp hx))
  · rw [Submodule.span_singleton_le_iff_mem]
    exact LinearMap.mem_ker.mpr ((hzero Γ).mpr hΓ)

/-- **The frustration-free improving family in region coordinates.** Let `H = ∑ hᵢ` be a
nearest-neighbour chain of `L` sites of local dimension `q` with `0 ≤ hᵢ ≤ 1`, let `Γ` satisfy
`H Γ = 0` with every vector of the kernel a multiple of `Γ`, and let every other spectral value
be at least `γ > 0`. Fix an interval `J = [p, r)`. With the universal constant `A ≥ 1` of
Theorem `t:aisff` and `g = min (γ, 1)`, `d = max (q, 2)`, `u = 1 + log d + log (1/g)`,
`ℓ = ⌈A u² / g⌉`, `D = (d ℓ²)^{22ℓ}`, there are `D²` operators `W j` on `J` and `Δ > 0` with
`D¹² Δ ≤ 10⁻⁵`, each of operator Schmidt rank at most `(d² + 4)^{ℓ² + 1}` at every cut of `J`,
such that every subspace of the space of `J` that is `δ`-viable for `ℂ Γ` in the region-first
coordinates of the merge tree, with `δ < 1`, gives a `Δ / (1 - δ)²`-viable span of its images
under the `W j`, in the same coordinates. None of `D`, `Δ` or the rank bound depends on `L`.

ALVV, arXiv:1602.08828v2, Theorem `t:aisff`, lines 1580–1609, under the hypotheses of
Theorem `t:unique`, lines 1829–1855. The scope of Theorem `t:aisff` carries over unchanged;
see `exists_frustrationFree_improving_family`. -/
theorem exists_frustrationFree_improving_family_regionTensorCoordinates :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (L q p r : ℕ), p ≤ r → r ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
        (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
          (interval L i.val (i.val + 2))) →
        (∀ i, 0 ≤ h i) → (∀ i, h i ≤ 1) →
      ∀ γ : ℝ, 0 < γ → ∀ Γ : EuclideanSpace ℂ (Fin L → Fin q),
      let H := ∑ i, h i
      H *ᵥ Γ.ofLp = 0 →
      (∀ x : EuclideanSpace ℂ (Fin L → Fin q), H *ᵥ x.ofLp = 0 → x ∈ ℂ ∙ Γ) →
      (∀ z ∈ spectrum ℝ H, z = 0 ∨ γ ≤ z) →
      let g := min γ 1
      let d := max q 2
      let u : ℝ := 1 + Real.log (d : ℝ) + Real.log (1 / g)
      let ℓ : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D : ℕ := (d * ℓ ^ 2) ^ (22 * ℓ)
      let J := interval L p r
      let G := (ℂ ∙ Γ).map (Entropy.regionTensorCoordinates q J).toLinearEquiv.toLinearMap
      let cut : ℕ → Finset ↥J := fun c ↦
        Finset.univ.filter fun v : ↥J ↦ (v : Fin L) ∈ interval L 0 c
      Real.log (D : ℝ) ≤ 22 * (A + 1) * (6 + 2 * Real.log (A + 1)) / g * u ^ 3 ∧
      Real.log (((d ^ 2 + 4) ^ (ℓ ^ 2 + 1) : ℕ) : ℝ) ≤ 4 * (A + 1) ^ 2 / g ^ 2 * u ^ 5 ∧
      ∃ (W : Fin (D ^ 2) → Matrix (J → Fin q) (J → Fin q) ℂ) (Δ : ℝ),
        0 < Δ ∧ (D : ℝ) ^ 12 * Δ ≤ 1 / 100000 ∧
        (∀ j c, operatorSchmidtRank ((W j).reindex (sheetSplit q (cut c))
          (sheetSplit q (cut c))) ≤ (d ^ 2 + 4) ^ (ℓ ^ 2 + 1)) ∧
        ∀ (S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q))) (δ : ℝ),
          Submodule.IsViable δ S G → δ < 1 →
          Submodule.IsViable (Δ / (1 - δ) ^ 2)
            (⨆ j, S.map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j) :
              EuclideanSpace ℂ (J → Fin q) →ₗ[ℂ] EuclideanSpace ℂ (J → Fin q))) G := by
  obtain ⟨A, hA, hff⟩ := exists_frustrationFree_improving_family
  refine ⟨A, hA, ?_⟩
  intro L q p r hpr hrL h hs h0 h1 γ hγ Γ H hΓ huniq hgap g d u ℓ D J G cut
  have hH : H.IsHermitian :=
    (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
  have hker := ker_toEuclideanCLM_eq_span_singleton Γ hΓ huniq
  have hgapQ : ∀ y ∈ (LinearMap.ker (Matrix.toEuclideanCLM (𝕜 := ℂ)
      (n := Fin L → Fin q) H).toLinearMap)ᗮ,
      γ * ‖y‖ ^ 2 ≤ Complex.re ⟪y, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) H y⟫_ℂ :=
    fun y hy ↦ hH.mul_norm_sq_le_re_inner_of_spectral_gap hgap y fun z hz ↦
      Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_ker.mpr hz) hy
  obtain ⟨hlogD, hlogR, W, Δ, hΔ, hbudget, hrank, himprove⟩ :=
    hff L q p r hpr hrL h hs h0 h1 γ hγ hgapQ
  refine ⟨hlogD, hlogR, W, Δ, hΔ, hbudget, hrank, ?_⟩
  have hcoords := (Entropy.regionTensorCoordinates_eq_exteriorFirst q J).symm
  rw [hker] at himprove
  intro S δ hS hδ
  exact hcoords ▸ himprove S δ (hcoords ▸ hS) hδ

end TNLean.MPS.AreaLaw.ALVV
