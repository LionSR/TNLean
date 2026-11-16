/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.FixedBandwidthLowEnergyFamily
import QICLean.Analysis.ShiftedLowEnergyCoordinates

/-!
# One original spectral normalization for changing truncation scales

The regional ground-energy shifts in the physical filter construction may
change with the window length. Every original target is identified here
with the canonical low-energy space of the raw Hamiltonian, based at its
actual minimum eigenvalue. Thus the original spectral targets do not depend
on the selected regional shifts or clipping scale. The same physical family,
actual polynomial and tensor decomposition are retained.

This supports ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`, lines
1027–1041, and Proposition `prop:albootstrap-ld`, lines 1112–1128.
The minimum is derived from the constructed normalized ground vector and
positive-semidefinite lower bound. No gap or simple-spectrum assumption is
made.

**Scope restriction (interior windows):** The fixed-bandwidth and interior
five-region scope is unchanged. The buffer `6*w ≤ eta` is explicit;
see `docs/paper-gaps/alvv16_low_energy_family_scope.tex`. Extension to a
fixed arbitrary physical interval as the scale grows remains separate.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

set_option maxHeartbeats 800000 in
-- The retained tensor decompositions involve dependent finite configuration types.
/-- The actual physical low-energy family in one canonical raw-Hamiltonian
normalization. The constant precedes the physical data; the middle family
precedes every cutoff and viable subspace. All original spectral targets
use the raw Hamiltonian's canonical eigenbasis and minimum, independently
of the regional shifts and clipping scale. The literal polynomial and tensor
decomposition from the fixed-bandwidth construction are retained.
ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041, and
Proposition `prop:albootstrap-ld`, lines 1112–1128. -/
theorem exists_fixed_bandwidth_five_region_canonical_low_energy_family
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ C : ℝ, 100 ≤ C ∧ 19 + etaLD ≤ C ∧
      ∀ (L q m a b : ℕ) (w : ℝ) (hq : 2 ≤ q), q ≤ m → 0 < w →
      let g := min w 1
      let u := 1 + Real.log (m : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
      let D := (m * ell ^ 2) ^ (22 * ell)
      a + 2 * ell ≤ b → b + 2 * ell ≤ L - 1 →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2))) →
      ∀ (h0 : ∀ i, 0 ≤ h i), (∀ i, h i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := ∑ i, h i
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      21 ≤ ell ∧
      Real.log (D : ℝ) ≤ 22 * (C + 1) * (6 + 2 * Real.log (C + 1)) / g * u ^ 3 ∧
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
    ∃ (e : Fin 5 → ℝ) (E0 : ℝ) (x z : (Fin L → Fin q) → ℂ)
      (hO : (B (ell : ℝ) e ∅).IsHermitian) (hC : (B (ell : ℝ) e K).IsHermitian),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      B (ell : ℝ) e ∅ = (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1 ∧
      star z ⬝ᵥ z = 1 ∧ B (ell : ℝ) e ∅ *ᵥ z = (E0 : ℂ) • z ∧
      (B (ell : ℝ) e ∅ - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧
      minEigenvalue hRaw = E0 + ∑ j, e j ∧
      (∀ c : ℝ,
        Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + c) =
          Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues
            (minEigenvalue hRaw + c)) ∧
      ‖B (ell : ℝ) e K‖ ≤ 7 * (ell : ℝ) ∧
      let J := interval L (a + ell) (b + ell + 1)
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
        (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
      ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ), N ≤ D ^ 2 ∧
        ∀ eta : ℝ, 6 * w ≤ eta → eta ≤ etaLD →
      let lower := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - 2 * w)
      let higher := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues
        (E0 + eta - w)
      let Delta := (2 * Real.exp (-2 * ((ell ^ 2 : ℕ) : ℝ) *
        Real.sqrt (w / (7 * (ell : ℝ) - (E0 + eta - 2 * w))))) ^ 2
      lower ≤ higher ∧
      Submodule.IsCloseTo (1 / 200)
        (Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues
          (minEigenvalue hRaw + eta)) higher ∧
      Submodule.IsCloseTo (1 / 200) lower
        (Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues
          (minEigenvalue hRaw + eta - 3 * w)) ∧
      (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
        ∃ p : Polynomial ℝ, p.natDegree = ell ^ 2 ∧ p.eval (E0 + eta - 2 * w) = 1 ∧
          ∃ M : Fin N → Matrix (↥(Jᶜ) → Fin q) (↥(Jᶜ) → Fin q) ℂ,
            Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
                Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
                  (Polynomial.aeval (B (ell : ℝ) e K) (p.map (algebraMap ℝ ℂ))) ∘L
                Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
              ∑ j, TensorProduct.mapL
                (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j))
                (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ↥(Jᶜ) → Fin q) (M j)) ∧
            ∀ (S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q))) (delta : ℝ),
              Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) delta S
                (higher.map Tm.toLinearEquiv.toLinearMap) → delta < 1 →
              let grow := ⨆ j : Fin N, S.map
                (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W j)).toLinearMap
              Module.finrank ℂ grow ≤ N * Module.finrank ℂ S ∧
                Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q))
                  (Delta / (1 - delta) ^ 2) grow (lower.map Tm.toLinearEquiv.toLinearMap) := by
  obtain ⟨C, hC, hCeta, hfamily⟩ :=
    exists_fixed_bandwidth_five_region_low_energy_family etaLD hLD
  refine ⟨C, hC, hCeta, ?_⟩
  intro L q m a b w hq hqm hw g u ell D hab hbL h hs h0 h1 config H hRaw
  let : Nonempty (Fin L → Fin q) := config
  obtain ⟨hell, hlogD, hdata⟩ :=
    hfamily L q m a b w hq hqm hw hab hbL h hs h0 h1
  refine ⟨hell, hlogD, ?_⟩
  intro k A Cross Y K B
  obtain ⟨e, E0, x, z, hO, hClip, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0, hE04, hnorm, htargets⟩ := hdata
  obtain ⟨hminimum, hidentity⟩ :=
    hRaw.spectralSpanLE_centered_ground_of_eq hO (∑ j, e j) E0 z
      hcenter hzunit hz hE0low
  refine ⟨e, E0, x, z, hO, hClip, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0, hE04, hminimum, hidentity, hnorm, ?_⟩
  intro J beta tau U Phi Tm
  obtain ⟨N, W, hN, hfilters⟩ := htargets
  refine ⟨N, W, hN, ?_⟩
  intro eta hbuffer hetaLD lower higher Delta
  obtain ⟨hnest, hupperClose, hlowerClose, htrade, p, hpdegree, hp0, M, hM, himprove⟩ :=
    hfilters eta hbuffer hetaLD
  have hidentityLower :
      Submodule.spectralSpanLE hO.eigenvectorBasis hO.eigenvalues (E0 + eta - 3 * w) =
        Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues
          (minEigenvalue hRaw + eta - 3 * w) := by
    simpa only [add_sub_assoc] using hidentity (eta - 3 * w)
  refine ⟨hnest, ?_, ?_, htrade, p, hpdegree, hp0, M, hM, himprove⟩
  · simpa only [hidentity eta] using hupperClose
  · simpa only [hidentityLower] using hlowerClose

end TNLean.MPS.AreaLaw
