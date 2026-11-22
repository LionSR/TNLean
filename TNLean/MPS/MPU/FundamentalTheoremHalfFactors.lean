/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceFactorChoiceGates
import QICLean.Algebra.Combinatorics.FinSumPermutation

/-!
# The fundamental theorem of matrix product unitaries: half factors

Theorem `FundamentalMPU` of arXiv:1703.09188 (lines 624--648) relates the standard forms of
two simple tensors `𝒰`, `𝒱` by unitaries `x`, `y`, `z`. Equation `SFuu` relates the gates,
`u_𝒱 = (x ⊗ y) u_𝒰`. Equation `SFvv` relates the half factors. The half factor of `𝒱` on the
left virtual leg is that of `𝒰` with `z` on the virtual leg and `x†` on the leg of dimension
`ℓ`. The half factor on the right virtual leg is that of `𝒰` with `z†` on the virtual leg and
`y†` on the leg of dimension `r`.

This file states both directions with the half factors themselves.

* Necessity: simple tensors in canonical form II with equal periodic operators at every length
  at least two have the same bond dimension, and unitaries `x`, `y`, `z` with `SFuu` and both
  half-factor relations of `SFvv`. The same `x` and `y` serve both equations, and the factors
  may come from any compact decompositions of the source cuts.
* Converse: two-site standard forms whose gates and half factors are related by `SFuu` and
  `SFvv` are letterwise unitary conjugates, `𝒱₂ = z 𝒰₂ z†`. Hence they generate the same
  operators on every ring of two-site blocks.

**Scope restriction (two-site blocks):** the converse concerns the blocked tensors only. The
standard form of Definition `SF` (lines 619--622) is a standard form of `𝒰₂`, and the
half-factor relations do not determine the original operators at odd lengths. See
`docs/paper-gaps/mpu_standard_form_parity_gap.tex`.

## Main statements

* `MPOTensor.TwoSiteStandardFormData.eq_virtualSandwich_of_half_factor_gauges`
* `MPOTensor.TwoSiteStandardFormData.mpo_eq_of_half_factor_gauges`
* `MPOTensor.IsMPUCanonicalFormII.exists_half_factor_gauges_of_mpo_eq`
-/

open scoped Matrix Kronecker
open Matrix

namespace MPOTensor

/-- **Half factors determine the two-site tensor up to a bond unitary.** Two-site standard forms
whose gates satisfy `u' = (x ⊗ y) u` and whose half factors satisfy
`X₂' = (z ⊗ 1) X₂ x†` and `X₁' = (1 ⊗ conj z) X₁ y†` give letterwise conjugate tensors,
`W' = z W z†`. Here `conj z = (z†)ᵀ` acts on the virtual index of `X₁`, contracted on the right.

Source: arXiv:1703.09188, Theorem `FundamentalMPU`, equations `SFuu` and `SFvv`, lines 624--648,
with the standard form `StandardForm` of lines 603--622. -/
theorem TwoSiteStandardFormData.eq_virtualSandwich_of_half_factor_gauges
    {d D ℓ r : ℕ} {W W' : MPOTensor (d * d) D}
    {u u' : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v v' : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (S' : TwoSiteStandardFormData W' u' v')
    (z : Matrix.unitaryGroup (Fin D) ℂ) (x : Matrix.unitaryGroup (Fin ℓ) ℂ)
    (y : Matrix.unitaryGroup (Fin r) ℂ)
    (hu : u' = ((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u)
    (hX₂ : S'.X₂ = (((z : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *
      S.X₂) * star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ))
    (hX₁ : S'.X₁ = (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
      (star (z : Matrix (Fin D) (Fin D) ℂ)).transpose) * S.X₁) *
        star (y : Matrix (Fin r) (Fin r) ℂ)) :
    W' = virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) W
      (star (z : Matrix (Fin D) (Fin D) ℂ)) := by
  subst hu
  funext i j
  ext α γ
  set p := finProdFinEquiv.symm i
  set q := finProdFinEquiv.symm j
  set Z : Matrix (Fin D) (Fin D) ℂ := (z : Matrix (Fin D) (Fin D) ℂ)
  set a : Fin ℓ → ℂ := fun t ↦
    ((Z ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * S.X₂) (α, p.1) t
  set b : Fin r → ℂ := fun s ↦
    (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (star Z).transpose) * S.X₁) (p.2, γ) s
  have ha : ∀ t, a t = ∑ β : Fin D, Z α β * S.X₂ (β, p.1) t := by
    intro t
    simp only [a, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hb : ∀ s, b s = ∑ δ : Fin D, star Z δ γ * S.X₁ (p.2, δ) s := by
    intro s
    simp only [b, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Matrix.transpose_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte]
  calc W' i j α γ
      = ∑ t, ∑ s, (a ᵥ* star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ)) t *
          (((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u) (t, s) q *
            (b ᵥ* star (y : Matrix (Fin r) (Fin r) ℂ)) s := by
        rw [S'.W_apply, hX₂, hX₁]
        rfl
    _ = ∑ t, ∑ s, a t * u (t, s) q * b s :=
        Matrix.sum_sum_vecMul_star_mul_kronecker_mul a b u x y q
    _ = ∑ t, ∑ s, ∑ δ, ∑ β, Z α β * S.X₂ (β, p.1) t * u (t, s) q *
          (star Z δ γ * S.X₁ (p.2, δ) s) := by
        simp only [ha, hb, Finset.sum_mul, Finset.mul_sum]
    _ = ∑ δ, ∑ β, Z α β * W i j β δ * star Z δ γ := by
        rw [Fintype.sum_last_two_first_four]
        refine Finset.sum_congr rfl fun δ _ ↦ Finset.sum_congr rfl fun β _ ↦ ?_
        rw [S.W_apply, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun s _ ↦ by ring
    _ = virtualSandwich Z W (star Z) i j α γ := by
        simp only [virtualSandwich_apply, Matrix.mul_apply, Finset.sum_mul]

/-- **Converse of the fundamental theorem at block lengths.** Two-site standard forms whose gates
and half factors are related by `SFuu` and `SFvv` generate the same periodic operators on every
ring of two-site blocks.

For `W = 𝒰₂` and `W' = 𝒱₂` this is `U^{(2N)} = V^{(2N)}`, under the module's scope
restriction to two-site blocks.

Source: arXiv:1703.09188, Theorem `FundamentalMPU`, "if" direction, lines 624--648. -/
theorem TwoSiteStandardFormData.mpo_eq_of_half_factor_gauges
    {d D ℓ r : ℕ} {W W' : MPOTensor (d * d) D}
    {u u' : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v v' : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (S' : TwoSiteStandardFormData W' u' v')
    (z : Matrix.unitaryGroup (Fin D) ℂ) (x : Matrix.unitaryGroup (Fin ℓ) ℂ)
    (y : Matrix.unitaryGroup (Fin r) ℂ)
    (hu : u' = ((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u)
    (hX₂ : S'.X₂ = (((z : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *
      S.X₂) * star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ))
    (hX₁ : S'.X₁ = (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
      (star (z : Matrix (Fin D) (Fin D) ℂ)).transpose) * S.X₁) *
        star (y : Matrix (Fin r) (Fin r) ℂ))
    (N : ℕ) :
    mpo W N = mpo W' N := by
  have hW := S.eq_virtualSandwich_of_half_factor_gauges S' z x y hu hX₂ hX₁
  exact mpo_eq_of_unitary_conj rfl z (fun i j ↦ by rw [hW]; rfl) N

/-- **Fundamental theorem of matrix product unitaries, half factors, necessity.** Let `U` and
`V` be simple tensors in canonical form II, of bond dimensions `D₁` and `D₂`, with
`U^{(N)} = V^{(N)}` for every `N ≥ 2`. Build their factors from any compact decompositions of
their source cuts. Then `D₁ = D₂`, and after identifying the rank spaces there are unitaries `z`
on the bond, `x` on the left rank and `y` on the right rank with
`u_V = (x ⊗ y) u_U` (equation `SFuu`) and the half-factor relations
`X₂(V) = (z ⊗ 1) X₂(U) x†`, `X₁(V) = (1 ⊗ conj z) X₁(U) y†` (equation `SFvv`).

The normalizations of canonical form II, `X₁†(1 ⊗ ρ)X₁ = 1` and `X₂†X₂ = 1`, are what make the
half factors unique up to these unitaries. For arbitrary two-site standard-form data the
statement fails: replacing `(X₁, X₂)` by `(c X₁, c⁻¹ X₂)` with `|c| ≠ 1` leaves the tensor and
both gates unchanged, but no unitaries `x`, `y`, `z` relate the two pairs, since multiplication
by unitaries preserves the Frobenius norm of `X₁`.

Source: arXiv:1703.09188, Theorem `FundamentalMPU`, "only if" direction, equations `SFuu` and
`SFvv`, lines 624--648, with the remark that `z` is unitary because both tensors are in canonical
form II, and the factors of lines 479--502. -/
theorem IsMPUCanonicalFormII.exists_half_factor_gauges_of_mpo_eq
    {d D₁ D₂ : ℕ} {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    (hU : IsMPUCanonicalFormII U) (hSU : IsMPUSimple U)
    (hV : IsMPUCanonicalFormII V) (hSV : IsMPUSimple V)
    (hEq : ∀ N : ℕ, 1 < N → mpo U N = mpo V N)
    (S₁ : SourceCutSVD (sourceCutM₁ U) r[U]) (S₂ : SourceCutSVD (sourceCutM₂ U) ℓ[U])
    (T₁ : SourceCutSVD (sourceCutM₁ V) r[V]) (T₂ : SourceCutSVD (sourceCutM₂ V) ℓ[V]) :
    ∃ (h : D₁ = D₂) (z : Matrix.unitaryGroup (Fin D₁) ℂ)
      (er : Fin r[U] ≃ Fin r[V]) (el : Fin ℓ[U] ≃ Fin ℓ[V])
      (x : Matrix.unitaryGroup (Fin ℓ[V]) ℂ) (y : Matrix.unitaryGroup (Fin r[V]) ℂ),
      SourceFactors.sourceU V (sourceFactorsOf T₁ T₂ hV.ρ hV.ρ_posDef) =
          ((x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ⊗ₖ (y : Matrix (Fin r[V]) (Fin r[V]) ℂ)) *
            Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _)
              (SourceFactors.sourceU U (sourceFactorsOf S₁ S₂ hU.ρ hU.ρ_posDef)) ∧
        (sourceFactorsOf T₁ T₂ hV.ρ hV.ρ_posDef).X₂ =
          Matrix.reindex (Equiv.prodCongr (finCongr h) (Equiv.refl _)) el
            (((z : Matrix (Fin D₁) (Fin D₁) ℂ) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *
              (sourceFactorsOf S₁ S₂ hU.ρ hU.ρ_posDef).X₂) *
            star (x : Matrix (Fin ℓ[V]) (Fin ℓ[V]) ℂ) ∧
        (sourceFactorsOf T₁ T₂ hV.ρ hV.ρ_posDef).X₁ =
          Matrix.reindex (Equiv.prodCongr (Equiv.refl _) (finCongr h)) er
            (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
              (star (z : Matrix (Fin D₁) (Fin D₁) ℂ)).transpose) *
              (sourceFactorsOf S₁ S₂ hU.ρ hU.ρ_posDef).X₁) *
            star (y : Matrix (Fin r[V]) (Fin r[V]) ℂ) := by
  obtain ⟨hdim, -⟩ := (hU.mpo_eq_iff_exists_unitary_conj hV).mp hEq
  subst hdim
  obtain ⟨z, rfl⟩ := hU.eq_virtualSandwich_of_mpo_eq hV hEq
  obtain ⟨W₁, W₂, hX₁, hY₁, hX₂, hY₂⟩ :=
    hU.exists_selected_source_factor_unitary_gauges_sourceFactorsOf hSU z hV hSV S₁ S₂ T₁ T₂
  refine ⟨rfl, z, (finCongr (source_rank_virtual_unitary_sandwich U z).1).symm,
    (finCongr (source_rank_virtual_unitary_sandwich U z).2).symm, star W₂, star W₁, ?_, ?_, ?_⟩
  · simpa only [Unitary.coe_star] using
      SourceFactors.sourceU_eq_of_factor_gauges _ _ z _ _ _ _ hY₁ hY₂
  · simp only [Unitary.coe_star, star_star, finCongr_refl]
    exact hX₂
  · simp only [Unitary.coe_star, star_star, finCongr_refl]
    exact hX₁

end MPOTensor
