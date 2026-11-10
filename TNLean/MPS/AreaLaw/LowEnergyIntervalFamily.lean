/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyRegionalFamily
import TNLean.MPS.AreaLaw.LowEnergySourceScale
import TNLean.MPS.AreaLaw.ShortRegionViableFamily

/-!
# Low-energy improving families on prescribed intervals

Inward effective cuts and the actual regional polynomial family treat long
intervals, including intervals at either endpoint. Configuration matrix
units treat short intervals. The family is chosen before all viable
subspaces; the improving-target tradeoff and original-window comparison
losses remain separate. These results support ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, lines 1027–1041.

The finite-length statement uses `L ≥ 2` and local dimension `q ≥ 2`.
The low-density bootstrap, sampled-tree construction and efficient central
tensor representation are separate.

**Scope restriction (finite chain and local dimension):** The source-scale
substitution is stated for `L ≥ 2` and `q ≥ 2`, at a fixed positive upper
bandwidth. The explicit capped count and both original-window comparison
losses are retained; see `docs/paper-gaps/alvv16_low_energy_family_buffers.tex`.

**Local fix (closed cutoffs and filter sign):** All spectral cutoffs are
closed. The long-interval branch uses absolute-value Chebyshev estimates,
without asserting positivity of the unsquared polynomial. See
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf and
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_filter_positivity.pdf.
-/

open Matrix
open scoped BigOperators TensorProduct InnerProductSpace Matrix.Norms.L2Operator
  ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- The existing configuration matrix units improve between any nested target
pair on a short region, with a strict positive tradeoff. Auxiliary to ALVV,
arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041. -/
private theorem exists_strict_short_low_energy_pair_family
    (L q m ell : ℕ) (J : Finset (Fin L)) (hq : 2 ≤ q) (hqm : q ≤ m) (hell : 1 ≤ ell)
    (hJ : J.card ≤ 4 * ell)
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] :
    let E := EuclideanSpace ℂ (J → Fin q)
    let D := (m * ell ^ 2) ^ (22 * ell)
    ∃ (A : Fin (D ^ 2) → E →L[ℂ] E) (Delta : ℝ),
      0 < Delta ∧ (D : ℝ) ^ 12 * Delta < 1 / 100000 ∧
      ∀ (Thi Tlo : Submodule ℂ (E ⊗[ℂ] F)), Tlo ≤ Thi →
      ∀ (S : Submodule ℂ E) (delta : ℝ),
      Submodule.IsViable delta S Thi → delta < 1 →
      let grow := ⨆ j, S.map (A j).toLinearMap
      Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
        Submodule.IsViable (Delta / (1 - delta) ^ 2) grow Tlo := by
  classical
  intro E D
  have hm : 2 ≤ m := hq.trans hqm
  obtain ⟨A, hA⟩ := exists_short_actual_region_spanning_family_of_count_base (F := F)
    L q m ell J hq hqm hell hJ
  have hD : 0 < (D : ℝ) := by
    have hnat : 0 < D := by dsimp only [D]; positivity
    exact_mod_cast hnat
  let Delta := 1 / (200000 * (D : ℝ) ^ 12)
  have hDelta : 0 < Delta := by dsimp only [Delta]; positivity
  have hbudget : (D : ℝ) ^ 12 * Delta < 1 / 100000 := by
    have heq : (D : ℝ) ^ 12 * Delta = 1 / 200000 := by
      dsimp only [Delta]
      field_simp
    rw [heq]
    norm_num
  refine ⟨A, Delta, hDelta, hbudget, ?_⟩
  intro Thi Tlo hsub S delta hS hdelta grow
  constructor
  · refine (Submodule.finrank_iSup_le_sum _).trans ?_
    calc
      _ ≤ ∑ _j : Fin (D ^ 2), Module.finrank ℂ S :=
        Finset.sum_le_sum fun j _ ↦ Submodule.finrank_map_le (A j).toLinearMap S
      _ = D ^ 2 * Module.finrank ℂ S := by simp
  · by_cases hThi : Thi = ⊥
    · have hTlo : Tlo = ⊥ := le_bot_iff.mp (hsub.trans_eq hThi)
      simp [hTlo, Submodule.IsViable, Submodule.IsCloseTo]
    · obtain ⟨htop, _hzero⟩ := hA delta S Thi hS hdelta hThi
      change Submodule.IsViable (Delta / (1 - delta) ^ 2)
        (⨆ j, S.map (A j).toLinearMap) Tlo
      rw [htop]
      exact Submodule.isViable_top _ (div_nonneg hDelta.le (sq_nonneg _)) Tlo


/-- An actual low-energy improving family exists on every prescribed chain
interval. The count base `m ≥ q` is chosen before the physical degree and
filter; the original local dimension and Hamiltonian are unchanged. One
constant at fixed density bandwidth precedes the chain, count base and
Hamiltonian. Suppression is derived for the same degree and count, rather
than inferred by enlarging a native tradeoff. The cap is absorbed in the
explicit source-scale count, and the strict tradeoff concerns the improving
target pair. ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041.
The length convention is `L ≥ 2`; efficient central tensor representations,
the low-density bootstrap and sampled tree are separate. -/
theorem exists_physical_low_energy_interval_family_of_count_base
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ Aconst : ℝ, 1 ≤ Aconst ∧ 21 ≤ Aconst ∧ 100 ≤ Aconst ∧
      ∀ (L q m : ℕ) (mu eta : ℝ), 2 ≤ L → 2 ≤ q → q ≤ m → 0 < mu →
      2 * mu / Real.log (L : ℝ) ≤ eta → eta ≤ etaLD →
      let w := mu / (3 * Real.log (L : ℝ))
      let g := min w 1
      let u := 1 + Real.log (m : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈Aconst * u ^ 2 / g⌉₊
      let D := (m * ell ^ 2) ^ (22 * ell)
      let Kcount := 22 * (Aconst + 1) * (6 + 2 * Real.log (Aconst + 1))
      21 ≤ ell ∧
      Real.log (D : ℝ) ≤ 3 * Kcount * max 1 (etaLD / 6) *
        (Real.log (L : ℝ) / mu) *
        (1 + Real.log (m : ℝ) + max (Real.log (3 * Real.log (L : ℝ) / mu)) 0) ^ 3 ∧
      ∀ (p r : ℕ), p ≤ r → r ≤ L →
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
        (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (h i) (interval L i.val (i.val + 2)))
        (_h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1),
      let H := ∑ i, h i
      ∃ (s E0 : ℝ) (C : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (hC : C.IsHermitian) (z : (Fin L → Fin q) → ℂ),
        C = H - (s : ℂ) • 1 ∧ star z ⬝ᵥ z = 1 ∧ C *ᵥ z = (E0 : ℂ) • z ∧
        (C - (E0 : ℂ) • 1).PosSemidef ∧
        let Gup := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues (E0 + eta)
        let Glo := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues (E0 + eta - 3 * w)
        ∃ (Tlo Thi : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (Delta : ℝ)
          (F : Fin (D ^ 2) → EuclideanSpace ℂ (J → Fin q) →L[ℂ]
            EuclideanSpace ℂ (J → Fin q)),
          Tlo ≤ Thi ∧ Submodule.IsCloseTo (1 / 200) Gup Thi ∧
          Submodule.IsCloseTo (1 / 200) Tlo Glo ∧
          0 < Delta ∧ (D : ℝ) ^ 12 * Delta < 1 / 100000 ∧
          ∀ (S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q))) (delta : ℝ),
            Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) delta S
              (Thi.map Tm.toLinearEquiv.toLinearMap) → delta < 1 →
            let grow := ⨆ j, S.map (F j).toLinearMap
            Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
              Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q))
                (Delta / (1 - delta) ^ 2) grow (Tlo.map Tm.toLinearEquiv.toLinearMap)
 := by
  obtain ⟨Aconst, hA, hA21, hA100, hcounts, hscalar⟩ :=
    Real.exists_low_energy_joint_scalar_parameters_above etaLD 100 hLD
  refine ⟨Aconst, hA, hA21, hA100, ?_⟩
  intro L q m mu eta hL hq hqm hmu hetaLower hetaUpper w g u ell D Kcount
  have hlogL : 0 < Real.log (L : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < L by omega))
  have hw : 0 < w := div_pos hmu (by positivity)
  have hband : 6 * w ≤ eta := by
    have heq : 6 * w = 2 * mu / Real.log (L : ℝ) := by
      dsimp only [w]
      field_simp
      ring
    exact heq.trans_le hetaLower
  have hbuffer : 3 * w < eta := by linarith only [hband, hw]
  have hg : 0 < g := lt_min hw zero_lt_one
  have hg1 : g ≤ 1 := min_le_right _ _
  obtain ⟨hell, hlogD⟩ := hcounts m g (hq.trans hqm) hg hg1
  change 21 ≤ ell at hell
  have hK : 0 ≤ Kcount := by
    have hlogA : 0 ≤ Real.log (Aconst + 1) := Real.log_nonneg (by linarith only [hA])
    dsimp only [Kcount]
    positivity
  refine ⟨hell, Real.low_energy_count_le_source_scale L m mu etaLD Kcount (D : ℝ)
    hL (by omega) hmu hK (hband.trans hetaUpper) hlogD, ?_⟩
  intro p r hpr hrL J beta tau U Phi Tm h hs h0 h1 H
  have hell1 : 1 ≤ ell := by omega
  classical
  by_cases hshort : r - p ≤ 4 * ell
  · let : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, by omega⟩⟩
    have hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    obtain ⟨E0, z, hz, hzunit, hE0low⟩ := hH.exists_unit_eigenvector_le
    refine ⟨0, E0, H, hH, z, by simp, hzunit, hz, hE0low, ?_⟩
    intro Gup Glo
    obtain ⟨F, Delta, hDelta, hbudget, hpair⟩ :=
      exists_strict_short_low_energy_pair_family
        (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) L q m ell J hq hqm hell1
          ((card_interval_le (L := L) p r).trans hshort)
    have hsub : Glo ≤ Gup := Submodule.span_mono
      (Set.image_mono (fun j hj ↦ hj.trans
        (show E0 + eta - 3 * w ≤ E0 + eta by linarith only [hw])))
    have hrefl (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) :
        Submodule.IsCloseTo (1 / 200 : ℝ) T T := by
      apply Submodule.isCloseTo_iff.mpr
      intro v hv
      rw [T.starProjection_eq_self_iff.mpr hv]
      nlinarith only [sq_nonneg ‖v‖]
    refine ⟨Glo, Gup, Delta, F, hsub, hrefl Gup, hrefl Glo, hDelta, hbudget, ?_⟩
    intro S delta hS hdelta
    exact hpair _ _ (Submodule.map_mono hsub) S delta hS hdelta
  · let a := max p ell - ell
    let b := min r (L - ell) - ell - 1
    obtain ⟨_haEnd, _hbEnd, hab, hbL, _hpp, _hpq, _hqq, _hlen,
      _hleft, _hright, _htotal, hsub, hcollar⟩ :=
      inward_effective_cuts L ell p r hell1 hpr hrL (Nat.lt_of_not_ge hshort)
    obtain ⟨t, e, E0, z, hO, hC, htformula, _ht, hcut, hcenter,
      hzunit, hz, hE0low, hE0, hE04, hnorm, hfamily⟩ :=
      exists_five_region_low_energy_family_on_larger_region L q a b ell J
        eta w (1 / 200) hbuffer hw (by norm_num) hq hell1 hab hbL hsub hcollar h hs h0 h1
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let Areg : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
    let Cross : Finset (Fin (L - 1)) := Finset.univ.filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y := ∑ i ∈ Cross, h i
    let K : Finset (Fin 5) := {0, 2, 4}
    let B : Finset (Fin 5) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun T ↦
      (∑ j, ((if j ∈ T then cfc (fun r : ℝ ↦ min r (e j + t)) (Areg j)
        else Areg j) - (e j : ℂ) • 1)) + Y
    change (B ∅).IsHermitian at hO
    change (B K).IsHermitian at hC
    refine ⟨∑ j, e j, E0, B ∅, hO, z, hcenter, hzunit, hz, hE0low, ?_⟩
    intro Gup Glo
    obtain ⟨hsubT, hupper, hlower, N, W, hN, himprove⟩ := hfamily
    have hcount : ((q * ell ^ 2) ^ (22 * ell)) ^ 2 ≤ D ^ 2 :=
      Nat.pow_le_pow_left
        (Nat.pow_le_pow_left (Nat.mul_le_mul_right (ell ^ 2) hqm) (22 * ell)) 2
    have hNenv : N ≤ D ^ 2 := hN.trans hcount
    let Tlo := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues (E0 + eta - 2 * w)
    let Thi := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues (E0 + eta - w)
    let Delta := (2 * Real.exp (-2 * ((ell ^ 2 : ℕ) : ℝ) *
      Real.sqrt (w / (3 * t + 4 * (ell : ℝ) - (E0 + eta - 2 * w))))) ^ 2
    obtain ⟨_hell, _hR, _hRup, hDelta, _hlogD, htrade⟩ :=
      hscalar m eta w E0 t (hq.trans hqm) hw hbuffer hetaUpper htformula hcut hE0 hE04
    let CW := fun i : Fin N ↦ Matrix.toEuclideanCLM (𝕜 := ℂ)
      (n := J → Fin q) (W i)
    obtain ⟨_f, F, _hF, _hzero, hgrow⟩ :=
      Submodule.exists_clm_family_extension_of_card_le
        (by simpa only [Fintype.card_fin] using hNenv) CW
    refine ⟨Tlo, Thi, Delta, F, hsubT, hupper, hlower, hDelta, htrade, ?_⟩
    intro S delta hS hdelta grow
    obtain ⟨hdim, hviable⟩ := himprove S delta hS hdelta
    rw [show grow = ⨆ i : Fin N, S.map (CW i).toLinearMap from hgrow S]
    exact ⟨hdim.trans (Nat.mul_le_mul_right (Module.finrank ℂ S) hNenv), hviable⟩

/-- The equal-count-base specialization retains the native physical family.
ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041. -/
theorem exists_physical_low_energy_interval_family
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ Aconst : ℝ, 1 ≤ Aconst ∧ 21 ≤ Aconst ∧
      ∀ (L q : ℕ) (mu eta : ℝ), 2 ≤ L → 2 ≤ q → 0 < mu →
      2 * mu / Real.log (L : ℝ) ≤ eta → eta ≤ etaLD →
      let w := mu / (3 * Real.log (L : ℝ))
      let g := min w 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈Aconst * u ^ 2 / g⌉₊
      let D := (q * ell ^ 2) ^ (22 * ell)
      let Kcount := 22 * (Aconst + 1) * (6 + 2 * Real.log (Aconst + 1))
      21 ≤ ell ∧
      Real.log (D : ℝ) ≤ 3 * Kcount * max 1 (etaLD / 6) *
        (Real.log (L : ℝ) / mu) *
        (1 + Real.log (q : ℝ) + max (Real.log (3 * Real.log (L : ℝ) / mu)) 0) ^ 3 ∧
      ∀ (p r : ℕ), p ≤ r → r ≤ L →
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
        (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (h i) (interval L i.val (i.val + 2)))
        (_h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1),
      let H := ∑ i, h i
      ∃ (s E0 : ℝ) (C : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (hC : C.IsHermitian) (z : (Fin L → Fin q) → ℂ),
        C = H - (s : ℂ) • 1 ∧ star z ⬝ᵥ z = 1 ∧ C *ᵥ z = (E0 : ℂ) • z ∧
        (C - (E0 : ℂ) • 1).PosSemidef ∧
        let Gup := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues (E0 + eta)
        let Glo := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues (E0 + eta - 3 * w)
        ∃ (Tlo Thi : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (Delta : ℝ)
          (F : Fin (D ^ 2) → EuclideanSpace ℂ (J → Fin q) →L[ℂ]
            EuclideanSpace ℂ (J → Fin q)),
          Tlo ≤ Thi ∧ Submodule.IsCloseTo (1 / 200) Gup Thi ∧
          Submodule.IsCloseTo (1 / 200) Tlo Glo ∧
          0 < Delta ∧ (D : ℝ) ^ 12 * Delta < 1 / 100000 ∧
          ∀ (S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q))) (delta : ℝ),
            Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) delta S
              (Thi.map Tm.toLinearEquiv.toLinearMap) → delta < 1 →
            let grow := ⨆ j, S.map (F j).toLinearMap
            Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
              Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q))
                (Delta / (1 - delta) ^ 2) grow (Tlo.map Tm.toLinearEquiv.toLinearMap)
 := by
  obtain ⟨Aconst, hA, hA21, _hA100, hall⟩ :=
    exists_physical_low_energy_interval_family_of_count_base etaLD hLD
  refine ⟨Aconst, hA, hA21, ?_⟩
  intro L q mu eta hL hq hmu hetaLower hetaUpper
  exact hall L q q mu eta hL hq le_rfl hmu hetaLower hetaUpper

/-- The same prescribed-interval family also improves viability between
the original spectral windows. Both physical comparison losses remain
explicit. ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041,
and Lemma `l:close`, lines 484–489. The improving-target tradeoff is not
identified with the final original-window viability error. -/
theorem exists_physical_original_low_energy_interval_family
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ Aconst : ℝ, 1 ≤ Aconst ∧ 21 ≤ Aconst ∧
      ∀ (L q : ℕ) (mu eta : ℝ), 2 ≤ L → 2 ≤ q → 0 < mu →
      2 * mu / Real.log (L : ℝ) ≤ eta → eta ≤ etaLD →
      let w := mu / (3 * Real.log (L : ℝ))
      let g := min w 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈Aconst * u ^ 2 / g⌉₊
      let D := (q * ell ^ 2) ^ (22 * ell)
      let Kcount := 22 * (Aconst + 1) * (6 + 2 * Real.log (Aconst + 1))
      21 ≤ ell ∧
      Real.log (D : ℝ) ≤ 3 * Kcount * max 1 (etaLD / 6) *
        (Real.log (L : ℝ) / mu) *
        (1 + Real.log (q : ℝ) + max (Real.log (3 * Real.log (L : ℝ) / mu)) 0) ^ 3 ∧
      ∀ (p r : ℕ), p ≤ r → r ≤ L →
      let J := interval L p r
      let beta := fun _ : Fin L ↦ Fin q
      let tau := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
      let Phi := ((EuclideanSpace.basisFun (FiniteProduct.Configuration beta Jᶜ) ℂ).tensorProduct
        (EuclideanSpace.basisFun (FiniteProduct.Configuration beta J) ℂ)).repr
      let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta Jᶜ))
        (EuclideanSpace ℂ (FiniteProduct.Configuration beta J)))
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (h i) (interval L i.val (i.val + 2)))
        (_h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1),
      let H := ∑ i, h i
      ∃ (s E0 : ℝ) (C : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (hC : C.IsHermitian) (z : (Fin L → Fin q) → ℂ),
        C = H - (s : ℂ) • 1 ∧ star z ⬝ᵥ z = 1 ∧ C *ᵥ z = (E0 : ℂ) • z ∧
        (C - (E0 : ℂ) • 1).PosSemidef ∧
        let Gup := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues (E0 + eta)
        let Glo := Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues (E0 + eta - 3 * w)
        ∃ (Tlo Thi : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (Delta : ℝ)
          (F : Fin (D ^ 2) → EuclideanSpace ℂ (J → Fin q) →L[ℂ]
            EuclideanSpace ℂ (J → Fin q)),
          Tlo ≤ Thi ∧ Submodule.IsCloseTo (1 / 200) Gup Thi ∧
          Submodule.IsCloseTo (1 / 200) Tlo Glo ∧
          0 < Delta ∧ (D : ℝ) ^ 12 * Delta < 1 / 100000 ∧
          (∀ (S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q))) (delta : ℝ),
            Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) delta S
              (Thi.map Tm.toLinearEquiv.toLinearMap) → delta < 1 →
            let grow := ⨆ j, S.map (F j).toLinearMap
            Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
              Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q))
                (Delta / (1 - delta) ^ 2) grow (Tlo.map Tm.toLinearEquiv.toLinearMap)) ∧
          ∀ (S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q))) (delta : ℝ),
            0 ≤ delta → 2 * (delta + 1 / 200) < 1 →
            Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) delta S
              (Gup.map Tm.toLinearEquiv.toLinearMap) →
            let grow := ⨆ j, S.map (F j).toLinearMap
            Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
              Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q))
                (2 * (Delta / (1 - 2 * (delta + 1 / 200)) ^ 2 + 1 / 200)) grow
                (Glo.map Tm.toLinearEquiv.toLinearMap)
 := by
  obtain ⟨Aconst, hA, hA21, hall⟩ := exists_physical_low_energy_interval_family etaLD hLD
  refine ⟨Aconst, hA, hA21, ?_⟩
  intro L q mu eta hL hq hmu hetaLower hetaUpper w g u ell D Kcount
  obtain ⟨hell, hlogD, hinterval⟩ := hall L q mu eta hL hq hmu hetaLower hetaUpper
  refine ⟨hell, hlogD, ?_⟩
  intro p r hpr hrL J beta tau U Phi Tm h hs h0 h1 H
  obtain ⟨s, E0, C, hC, z, hshift, hzunit, hz, hground, hfamily⟩ :=
    hinterval p r hpr hrL h hs h0 h1
  refine ⟨s, E0, C, hC, z, hshift, hzunit, hz, hground, ?_⟩
  intro Gup Glo
  obtain ⟨Tlo, Thi, Delta, F, hsub, hupper, hlower, hDelta, hbudget, hclip⟩ := hfamily
  refine ⟨Tlo, Thi, Delta, F, hsub, hupper, hlower, hDelta, hbudget, hclip, ?_⟩
  intro S delta hdelta hstartBudget hS grow
  have hstart : Submodule.IsViable (F := EuclideanSpace ℂ (↥(Jᶜ) → Fin q))
      (2 * (delta + 1 / 200)) S (Thi.map Tm.toLinearEquiv.toLinearMap) :=
    Submodule.IsCloseTo.trans hS ((Submodule.isCloseTo_map_iff Tm).mpr hupper) hdelta
  obtain ⟨hdim, hraw⟩ := hclip S (2 * (delta + 1 / 200)) hstart hstartBudget
  exact ⟨hdim, Submodule.IsCloseTo.trans hraw
    ((Submodule.isCloseTo_map_iff Tm).mpr hlower)
    (div_nonneg hDelta.le (sq_nonneg _))⟩

end TNLean.MPS.AreaLaw
