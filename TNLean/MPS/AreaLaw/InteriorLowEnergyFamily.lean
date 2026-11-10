/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyFilterParameters
import TNLean.MPS.AreaLaw.OriginalLowEnergyFamily

/-!
# Interior low-energy families at the source buffer scale

At fixed low-density bandwidth, one constant precedes the chain length,
local dimension, buffer coefficient, target bandwidth and Hamiltonian.
The actual physical family has a strict dimension-contraction tradeoff
and an explicit logarithmic count. Its action on original spectral windows
retains both losses from the physical spectral comparisons.

**Scope restriction (interior geometry and capped width):** The statement
requires the stated five-region geometry and length at least two. It keeps
`g = min (mu/(3*log L)) 1` in the exact count estimate. No short or boundary
region, low-density bootstrap or sampled-tree conclusion is asserted.
The clipped filter error and original-window viability error are distinct.
See `docs/paper-gaps/alvv16_low_energy_family_buffers.tex`.
-/

open Matrix
open scoped BigOperators TensorProduct InnerProductSpace Matrix.Norms.L2Operator
  ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- A single constant at fixed density bandwidth constructs the actual
interior physical improving family at the source low-energy buffer scale.
The exact capped-width count and strict clipped-filter tradeoff precede
all viable subspaces. The original-window comparison losses remain explicit.
ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041;
Assumption (LD), lines 279–286, fixes the density bandwidth. -/
theorem exists_interior_low_energy_original_filter_family
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ Aconst : ℝ, 1 ≤ Aconst ∧ 21 ≤ Aconst ∧
      ∀ (L q : ℕ) (mu eta : ℝ), 2 ≤ L → 2 ≤ q → 0 < mu →
      2 * mu / Real.log (L : ℝ) ≤ eta → eta ≤ etaLD →
      let w := mu / (3 * Real.log (L : ℝ))
      let g := min w 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈Aconst * u ^ 2 / g⌉₊
      ∀ (a b : ℕ), a + 2 * ell ≤ b → b + 2 * ell ≤ L - 1 →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2)))
      (_h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1),
      let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
      let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
        ∑ i ∈ Finset.univ.filter
          (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
      let Cross : Finset (Fin (L - 1)) := Finset.univ.filter
        (fun i ↦ i.val + 1 ∈
          ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
      let Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ Cross, h i
      let K : Finset (Fin 5) := {0, 2, 4}
      let B : ℝ → (Fin 5 → ℝ) → Finset (Fin 5) →
          Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun t e T ↦
        (∑ j, ((if j ∈ T then
          cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) -
            (e j : ℂ) • 1)) + Y
      ∃ (t : ℝ) (e : Fin 5 → ℝ) (E0 : ℝ) (x z : (Fin L → Fin q) → ℂ)
        (hO : (B t e ∅).IsHermitian),
        t = 21 + eta + 8 * Real.log
          ((288 * Real.exp (11 / 8)) / min 1 ((1 / 200 : ℝ) * w ^ 2 / (2 * (6 + eta)))) ∧
        21 ≤ t ∧ 19 + eta ≤ t ∧
        star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
        (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
        B t e ∅ = (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1 ∧
        star z ⬝ᵥ z = 1 ∧ B t e ∅ *ᵥ z = (E0 : ℂ) • z ∧
        (B t e ∅ - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧
        ‖B t e K‖ ≤ 3 * t + 4 * (ell : ℝ) ∧
        let J := interval L (a + ell) (b + ell + 1)
        let beta := fun _ : Fin L ↦ Fin q
        let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
        let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
        let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
          (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
        let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
          (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
          (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
        let D := (q * ell ^ 2) ^ (18 * ell + 2 * (ell ^ 2 / ell))
        let Delta := (2 * Real.exp (-2 * ((ell ^ 2 : ℕ) : ℝ) *
          Real.sqrt (w / (3 * t + 4 * (ell : ℝ) - (E0 + eta - 2 * w))))) ^ 2
        0 < Delta ∧
        Real.log (D : ℝ) ≤
          22 * (Aconst + 1) * (6 + 2 * Real.log (Aconst + 1)) / g * u ^ 3 ∧
        (D : ℝ) ^ 12 * Delta < 1 / 100000 ∧
        ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ), N ≤ D ^ 2 ∧
          ∀ (S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q))) (delta : ℝ),
            0 ≤ delta → 2 * (delta + (1 / 200 : ℝ)) < 1 →
            Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) delta S
              ((Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues
                (E0 + eta)).map Tm.toLinearEquiv.toLinearMap) →
            let grow := ⨆ j : Fin N, S.map
              (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j)).toLinearMap
            Module.finrank ℂ grow ≤ N * Module.finrank ℂ S ∧
              Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q))
                (2 * (Delta / (1 - 2 * (delta + (1 / 200 : ℝ))) ^ 2 + (1 / 200 : ℝ))) grow
                ((Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues
                  (E0 + eta - 3 * w)).map Tm.toLinearEquiv.toLinearMap) := by
  obtain ⟨Aconst, hA, hA21, hscalar⟩ := Real.exists_low_energy_scalar_parameters etaLD hLD
  refine ⟨Aconst, hA, hA21, ?_⟩
  intro L q mu eta hL hq hmu hetaLower hetaUpper w g u ell a b hab hbL h hs h0 h1
    k A Cross Y K B
  have hlogL : 0 < Real.log (L : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < L by omega))
  have hw : 0 < w := div_pos hmu (by positivity)
  have hbuffer : 3 * w < eta := by
    have heq : 6 * w = 2 * mu / Real.log (L : ℝ) := by
      dsimp only [w]
      field_simp
      ring
    linarith only [heq, hetaLower, hw]
  have hg : 0 < g := lt_min hw zero_lt_one
  have hg1 : g ≤ 1 := min_le_right _ _
  have hu1 : 1 ≤ u := by
    have hlogq : 0 ≤ Real.log (q : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
    have hb : 0 ≤ Real.log (1 / g) := Real.log_nonneg ((one_le_div hg).mpr hg1)
    dsimp only [u]
    linarith only [hlogq, hb]
  have hellA : Aconst ≤ (ell : ℝ) := by
    have hA0 : 0 ≤ Aconst := zero_le_one.trans hA
    have hu2 : 1 ≤ u ^ 2 := one_le_pow₀ hu1
    have hratio : 1 ≤ u ^ 2 / g := (one_le_div hg).mpr (hg1.trans hu2)
    calc
      Aconst = Aconst * 1 := (mul_one Aconst).symm
      _ ≤ Aconst * (u ^ 2 / g) := mul_le_mul_of_nonneg_left hratio hA0
      _ = Aconst * u ^ 2 / g := (mul_div_assoc _ _ _).symm
      _ ≤ (ell : ℝ) := Nat.le_ceil _
  have hell : 1 ≤ ell := by
    have hlarge : (21 : ℝ) ≤ (ell : ℝ) := hA21.trans hellA
    have : 21 ≤ ell := by exact_mod_cast hlarge
    omega
  obtain ⟨t, e, E0, x, z, hO, htformula, ht, hcut, hxunit, hx, hlo,
    hcenter, hzunit, hz, hE0low, hE0, hE04, hnorm, hfamily⟩ :=
    exists_five_region_original_low_energy_filter_family L q a b ell eta w (1 / 200)
      hbuffer hw (by norm_num) hq hell hab hbL h hs h0 h1
  change (B t e ∅).IsHermitian at hO
  refine ⟨t, e, E0, x, z, hO, htformula, ht, hcut, hxunit, hx, hlo,
    hcenter, hzunit, hz, hE0low, hE0, hE04, hnorm, ?_⟩
  intro J beta tau U Phi Tm D Delta
  obtain ⟨_hell, _hR, _hRup, hDelta, hlogD, htrade⟩ :=
    hscalar q eta w E0 t hq hw hbuffer hetaUpper htformula hcut hE0 hE04
  exact ⟨hDelta, hlogD, htrade, hfamily⟩

end TNLean.MPS.AreaLaw
