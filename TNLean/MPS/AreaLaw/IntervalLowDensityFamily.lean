/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LongIntervalLowDensityFamily
import TNLean.MPS.AreaLaw.ShortRegionViableFamily
import QICLean.Analysis.ViableSubspaceOrder

/-!
# Low-energy improving families on every prescribed interval

A single fixed-bandwidth scale treats every physical interval, including
short intervals and intervals meeting the chain endpoints. Long intervals
use the same global clipped polynomial and its exact regional factors;
short intervals use actual configuration matrix units. Both cases retain
the same count envelope and suppression budget. All original targets use
the raw Hamiltonian's canonical energy normalization.

This is the physical improving-family construction supporting ALVV,
arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041, with the fixed
bandwidth of Assumption (LD), lines 281–284. No spectral gap or supplied
operator, residual, rank or probability premise is imposed. The subsequent
strict low-density dimension argument is separate.

**Scope restriction (nontrivial local dimension):** The statement retains
`q ≥ 2`. The scalar local space is a separate elementary case;
see `docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

set_option maxHeartbeats 800000 in
-- The long and short cases share dependent physical configuration coordinates.
/-- An actual improving family on every prescribed interval, for all buffered
cutoffs within a fixed bandwidth. The constant precedes every physical datum;
the same family is chosen before every cutoff and viable subspace. Inward
cuts and short-region matrix units discharge all geometric alternatives.
Both cases use the same count and suppression envelope and the same original
canonical Hamiltonian targets. ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, lines 1027–1041. -/
theorem exists_fixed_bandwidth_interval_low_energy_family
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ C : ℝ, 100 ≤ C ∧ 19 + etaLD ≤ C ∧
      ∀ (L q m p r : ℕ) (w : ℝ) (hq : 2 ≤ q), q ≤ m → p ≤ r → r ≤ L → 0 < w →
      let g := min w 1
      let u := 1 + Real.log (m : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
      let D := (m * ell ^ 2) ^ (22 * ell)
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
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
        (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
      let EM := EuclideanSpace ℂ (J → Fin q)
      let EE := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)
      ∃ A : Fin (D ^ 2) → EM →L[ℂ] EM,
        ∀ eta : ℝ, 6 * w ≤ eta → eta ≤ etaLD →
        ∃ (Tlo Thi : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (Delta : ℝ),
          Tlo ≤ Thi ∧
          Submodule.IsCloseTo (1 / 200)
            (Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues
              (minEigenvalue hRaw + eta)) Thi ∧
          Submodule.IsCloseTo (1 / 200) Tlo
            (Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues
              (minEigenvalue hRaw + eta - 3 * w)) ∧
          0 < Delta ∧ (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
          ∀ (S : Submodule ℂ EM) (delta : ℝ),
            Submodule.IsViable (F := EE) delta S (Thi.map Tm.toLinearEquiv.toLinearMap) →
            delta < 1 →
            let grow := ⨆ i : Fin (D ^ 2), S.map (A i).toLinearMap
            Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
              Submodule.IsViable (F := EE) (Delta / (1 - delta) ^ 2)
                grow (Tlo.map Tm.toLinearEquiv.toLinearMap) := by
  classical
  obtain ⟨C, hC, hCeta, hlong⟩ :=
    exists_fixed_bandwidth_long_interval_low_energy_family etaLD hLD
  refine ⟨C, hC, hCeta, ?_⟩
  intro L q m p r w hq hqm hpr hrL hw g u ell D h hs h0 h1 config H hRaw
  let : Nonempty (Fin L → Fin q) := config
  obtain ⟨hell, hlogD, hfamily⟩ := hlong L q m p r w hq hqm hpr hrL hw h hs h0 h1
  refine ⟨hell, hlogD, ?_⟩
  intro J beta tau U Phi Tm EM EE
  by_cases hshort : r - p ≤ 4 * ell
  · have hJ : J.card ≤ 4 * ell := (card_interval_le (L := L) p r).trans hshort
    obtain ⟨A, Delta, hDelta, htrade, himprove⟩ :=
      exists_short_actual_region_improving_family_of_count_base (F := EE)
        L q m ell J hq hqm ((by decide : 1 ≤ 21).trans hell) hJ
    refine ⟨A, ?_⟩
    intro eta _hbuffer _hetaLD
    let Gup := Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues
      (minEigenvalue hRaw + eta)
    let Glow := Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues
      (minEigenvalue hRaw + eta - 3 * w)
    have hle : Glow ≤ Gup := Submodule.span_mono
      (Set.image_mono (fun _ hi ↦ hi.trans
        (show minEigenvalue hRaw + eta - 3 * w ≤ minEigenvalue hRaw + eta by
          linarith only [hw])))
    have hGG : Submodule.IsCloseTo (1 / 200) Gup Gup :=
      Submodule.isCloseTo_of_le (by norm_num) le_rfl
    have hGL : Submodule.IsCloseTo (1 / 200) Gup Glow :=
      Submodule.isCloseTo_of_le (by norm_num) hle
    refine ⟨Gup, Gup, Delta, le_rfl, hGG, hGL, hDelta, htrade, ?_⟩
    intro S delta hS hdelta
    refine ⟨?_, himprove (Gup.map Tm.toLinearEquiv.toLinearMap) S delta hS hdelta⟩
    simpa only [Fintype.card_fin] using
      Submodule.finrank_iSup_map_le_card_mul S (fun i ↦ (A i).toLinearMap)
  · exact hfamily (Nat.lt_of_not_ge hshort)

end TNLean.MPS.AreaLaw
