/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.LowDensity.PhysicalLDTreeNode

/-!
# Refining the root of the low-density merge tree to any accuracy

A space on the whole chain that is `3/200`-close to the window `G(η)` is
refined to any accuracy `δ`. On the whole chain one applies the words of
length `a = clog₂ ⌈32/δ⌉` of the low-density family at the index
`i = clog₁₆ ⌈1/δ⌉`, whose comparison loss is at most `δ/200`. The image is
then trimmed collectively against a matrix product space that is
`δ/48`-close in both directions to the window `G(η - 3w)`. The output is
`δ`-close to `G(η - 3w)`, is spanned by recorded vectors of controlled
Schmidt rank, and consists of matrix product states. On a chain of at most
`4 * ell` sites the whole local space is taken.

This is the `δ`-viability conclusion of ALVV, arXiv:1602.08828v2,
Theorem `t:alg2`, lines 1869–1878, as the analogue of the conclusion of
Theorem `t:alg1`, lines 1779–1781, with the repeated filter of lines
1777–1817 and the families of Theorem `t:aisgapless`, lines 1027–1041.

**Scope restriction (refinement without energy output):** One more level
of the window is used, so the output approximates `G(η - 3w)`. No energy
estimate, number of output states, final Ritz extraction, success
probability or running time is asserted; the energy-output clause of
lines 1869–1878 is not verified against the source. The trim follows the
modified tree with one collective trim. See
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
-/

open ManyBody (interval)

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- The weighted trimming term at the threshold `δ / (16 D √(L+1))` is at
most `δ / 4` at every cut count up to `L + 1`. Supporting ALVV,
arXiv:1602.08828v2, `lem:trimming`, lines 660–697. -/
private theorem refinement_trimming_budget {L cuts D : ℕ} {delta : ℝ} (hdelta : 0 < delta)
    (hcuts : cuts ≤ L + 1) (hD : 1 ≤ D) :
    let xi := delta / (16 * (D : ℝ) * Real.sqrt ((L : ℝ) + 1))
    0 < xi ∧ xi ≤ 1 / 16 * delta ∧
      4 * xi * Real.sqrt ((cuts : ℝ) * (D : ℝ) ^ 2) ≤ delta / 4 := by
  intro xi
  have hD0 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hroot1 : 1 ≤ Real.sqrt ((L : ℝ) + 1) := Real.one_le_sqrt.mpr
    (by linarith only [(Nat.cast_nonneg L : (0 : ℝ) ≤ (L : ℝ))])
  have hden : 0 < 16 * (D : ℝ) * Real.sqrt ((L : ℝ) + 1) := by positivity
  have hxi : 0 < xi := by dsimp only [xi]; positivity
  have hprod : 1 ≤ (D : ℝ) * Real.sqrt ((L : ℝ) + 1) := one_le_mul_of_one_le_of_one_le hD0 hroot1
  refine ⟨hxi, ?_, ?_⟩
  · dsimp only [xi]
    rw [div_le_iff₀ hden]
    nlinarith only [hprod, hdelta]
  · have hcutsR : (cuts : ℝ) ≤ (L : ℝ) + 1 := by exact_mod_cast hcuts
    have hroot : Real.sqrt ((cuts : ℝ) * (D : ℝ) ^ 2) ≤
        (D : ℝ) * Real.sqrt ((L : ℝ) + 1) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity), mul_comm]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcutsR) (by positivity)
    calc
      4 * xi * Real.sqrt ((cuts : ℝ) * (D : ℝ) ^ 2) ≤
          4 * xi * ((D : ℝ) * Real.sqrt ((L : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = delta / 4 := by
        dsimp only [xi]
        field_simp
        ring

set_option maxHeartbeats 1600000 in
-- The refinement combines the dependent coordinates of the whole-chain family,
-- the word image, the reference and the trim.
/-- A whole-chain space that is `3/200`-close to the original window `G(η)`,
with `6w ≤ η ≤ etaLD`, is refined for every `0 < δ ≤ 1` to a space `R` that
is `δ`-close to `G(η - 3w)`. Either the chain has at most `4 * ell` sites
and `R` is the whole local space, or `R` is the collective trim at the
threshold `xi` of the image of the given space under the words of length
`a` of a family of at most `D ^ 2` operators. The output is spanned by at
most `M` recorded vectors with `xi ^ 2 * SR ≤ M` at every cut, and each of its
vectors is a matrix product state. The reference factor `B` has the
logarithmic bound of the low-energy basis theorem. ALVV,
arXiv:1602.08828v2, Theorem `t:alg2`, lines 1869–1878, in the
`δ`-viability form of Theorem `t:alg1`, lines 1779–1781. -/
theorem exists_physical_ld_root_refinement (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ C K : ℝ, 100 ≤ C ∧ 19 + etaLD ≤ C ∧ 0 < K ∧
      ∀ (L q m : ℕ) (w : ℝ) (hq : 2 ≤ q), q ≤ m → 0 < w →
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ (h0 : ∀ i, 0 ≤ Φ.term i), (∀ i, Φ.term i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := Φ.hamiltonian
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let G := fun eta : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + eta)
      ∀ eta : ℝ, 6 * w ≤ eta → eta ≤ etaLD →
      ∀ (count : ℕ) (S0 : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))),
      Submodule.IsCloseTo (3 / 200 : ℝ) (nativeFullIntervalSpace L q S0) (G eta) →
      Module.finrank ℂ S0 ≤ count →
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let i := Nat.clog 16 ⌈1 / delta⌉₊
      let mi := m * 2 ^ i
      let g := min w 1
      let u := 1 + Real.log (mi : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
      let D := (mi * ell ^ 2) ^ (22 * ell)
      let a := Nat.clog 2 ⌈32 / delta⌉₊
      let v := etaLD - (eta - 3 * w)
      let rInner := Module.finrank ℂ (G (eta - 3 * w))
      let rOuter := Module.finrank ℂ (G etaLD)
      let gRef := min (min v (etaLD / 2) / 6) 1
      let uRef := 1 + Real.log (q : ℝ) + Real.log (1 / gRef)
      let aRef := 16 + Real.log (1 / gRef) +
        Real.log (1024 * ((L : ℝ) + 1) * ((rInner : ℝ) + 1) / (delta / 48))
      ∃ B : ℕ, 1 ≤ B ∧ Real.log (B : ℝ) ≤
        K * (uRef ^ 3 / gRef + (1 / gRef) ^ (1 / 4 : ℝ) * aRef ^ (3 / 4 : ℝ) * uRef) *
          (1 + Real.log aRef) ∧
      let Dref := rInner * rOuter * B
      let xi := delta / (16 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
      let M := max (q ^ (4 * ell)) (D ^ (2 * a) * count)
      ∃ R : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q)),
        ((L ≤ 4 * ell ∧ R = ⊤) ∨
          ∃ (N : ℕ) (F : Fin N → EuclideanSpace ℂ (interval L 0 L → Fin q) →L[ℂ]
              EuclideanSpace ℂ (interval L 0 L → Fin q)),
            N ≤ D ^ 2 ∧
            R = intervalTrimSubspace L q 0 L xi (fun k ↦
              (stdOrthonormalBasis ℂ ↥(⨆ x : Fin a → Fin N,
                S0.map ((List.ofFn (fun j ↦ F (x j))).prod :
                  EuclideanSpace ℂ (interval L 0 L → Fin q) →ₗ[ℂ]
                    EuclideanSpace ℂ (interval L 0 L → Fin q)) :
                  Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) k :
                EuclideanSpace ℂ (interval L 0 L → Fin q)))) ∧
        Submodule.IsCloseTo delta (nativeFullIntervalSpace L q R) (G (eta - 3 * w)) ∧
        IsIntervalSpanWithRankBound L q 0 L M xi R ∧
        ∀ x ∈ R, IsOpenMPS L q
          (M * ⌈256 * (Dref : ℝ) ^ 2 * ((L : ℝ) + 1) * M / delta ^ 2⌉₊)
          (fullIntervalRead L q x) := by
  classical
  obtain ⟨C, hC, hCeta, hlong⟩ :=
    exists_fixed_bandwidth_long_interval_dyadic_low_energy_word_family etaLD hLD
  obtain ⟨K, hK, hbasis⟩ :=
    exists_fixed_bandwidth_low_energy_orthonormal_mps_basis etaLD hLD
  refine ⟨C, K, hC, hCeta, hK, ?_⟩
  intro L q m w hq hqm hw Φ h0 h1 config H hRaw G eta hbuffer hetaLD count S0 hS0 hdim0
    delta hdelta hdelta1 i mi g u ell D a v rInner rOuter gRef uRef aRef
  let : Nonempty (Fin L → Fin q) := config
  have hGmono {x y : ℝ} (hxy : x ≤ y) : G x ≤ G y :=
    Submodule.spectralSpanLE_mono_cutoff hRaw.eigenvectorBasis hRaw.eigenvalues
      (by linarith only [hxy])
  have hGne {x : ℝ} (hx : 0 ≤ x) : G x ≠ ⊥ := by
    obtain ⟨j, hj⟩ := minEigenvalue_achieved hRaw
    apply hRaw.spectralSpanLE_ne_bot_of_mem_spectrum
    · simpa only [hj] using hRaw.eigenvalues_mem_spectrum_real j
    · linarith only [hx]
  -- The reference matrix product space for the lower window.
  have hv : 0 < v := by dsimp only [v]; linarith only [hetaLD, hw]
  obtain ⟨B, hB, hlogB, _phi, _hphi, hrest⟩ :=
    hbasis L q v (by omega) hv Φ h0 h1 (delta / 48) (by positivity) (by linarith only [hdelta1])
  obtain ⟨_hinj, _hdim, _hdimle, _hspan, hVG0, hGV0, _hGV', hMPS0, _⟩ := hrest
  obtain ⟨Uref, hVG, hGV, hMPS⟩ : ∃ Uref : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
      Submodule.IsCloseTo (delta / 48) Uref (G (etaLD - v)) ∧
      Submodule.IsCloseTo (delta / 48) (G (etaLD - v)) Uref ∧
      ∀ x ∈ Uref, IsOpenMPS L q
        (Module.finrank ℂ (G (etaLD - v)) * rOuter * B) (fun y ↦ x y) :=
    ⟨_, hVG0, hGV0, hMPS0⟩
  clear hVG0 hGV0 hMPS0 _hGV' _hinj _hdim _hdimle _hspan _hphi
  have hveq : etaLD - v = eta - 3 * w := by dsimp only [v]; ring
  rw [hveq] at hlogB hVG hGV hMPS
  refine ⟨B, hB, hlogB, ?_⟩
  intro Dref xi M
  have hrInner : 1 ≤ rInner :=
    Submodule.one_le_finrank_iff.mpr (hGne (by linarith only [hbuffer, hw]))
  have hrOuter : 1 ≤ rOuter := Submodule.one_le_finrank_iff.mpr (hGne hLD.le)
  have hDref : 1 ≤ Dref := by
    dsimp only [Dref]
    have := Nat.mul_le_mul (Nat.mul_le_mul hrInner hrOuter) hB
    simpa only [one_mul] using this
  obtain ⟨hxi, hxi16, hbudget0⟩ := refinement_trimming_budget (L := L) (cuts := 0)
    hdelta (by omega) hDref
  have hxi1 : xi ≤ 1 := hxi16.trans (by linarith only [hdelta1])
  -- The matrix product bound follows from the recorded generators.
  have hMPSofSpan : ∀ R : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q)),
      IsIntervalSpanWithRankBound L q 0 L M xi R →
      ∀ x ∈ R, IsOpenMPS L q
        (M * ⌈256 * (Dref : ℝ) ^ 2 * ((L : ℝ) + 1) * M / delta ^ 2⌉₊)
        (fullIntervalRead L q x) := by
    intro R hR x hx
    obtain ⟨n, hn, vectors, hspan, hranks⟩ := hR
    have hxi2 : xi ^ 2 = delta ^ 2 / (256 * (Dref : ℝ) ^ 2 * ((L : ℝ) + 1)) := by
      dsimp only [xi]
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      ring
    have hrank (k : Fin n) (j : ℕ) (hj : j < L - 1) :
        Matrix.schmidtRank (WithLp.ofLp
          (ManyBody.cutVector (intervalTrimCut L 0 L j) (vectors k))) ≤
          ⌈256 * (Dref : ℝ) ^ 2 * ((L : ℝ) + 1) * M / delta ^ 2⌉₊ := by
      have hbound := hranks j hj k
      rw [hxi2] at hbound
      have hc : (0 : ℝ) < 256 * (Dref : ℝ) ^ 2 * ((L : ℝ) + 1) := by positivity
      have hreal : (Matrix.schmidtRank (WithLp.ofLp
          (ManyBody.cutVector (intervalTrimCut L 0 L j) (vectors k))) : ℝ) ≤
          256 * (Dref : ℝ) ^ 2 * ((L : ℝ) + 1) * M / delta ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        have hmul := mul_le_mul_of_nonneg_left hbound hc.le
        calc
          _ = (256 * (Dref : ℝ) ^ 2 * ((L : ℝ) + 1)) *
              (delta ^ 2 / (256 * (Dref : ℝ) ^ 2 * ((L : ℝ) + 1)) *
                (Matrix.schmidtRank (WithLp.ofLp
                  (ManyBody.cutVector (intervalTrimCut L 0 L j) (vectors k))) : ℝ)) := by
            field_simp
          _ ≤ _ := hmul
      exact_mod_cast hreal.trans (Nat.le_ceil _)
    have hmem : x ∈ Submodule.span ℂ (Set.range vectors) := by
      rw [← hspan]
      exact hx
    exact (isOpenMPS_fullIntervalRead_of_mem_span vectors hrank hmem).mono
      (Nat.mul_le_mul_right _ hn)
  by_cases hshort : L ≤ 4 * ell
  · -- A short chain: the whole local space.
    have hleaf : q ^ (4 * ell) ≤ M := le_max_left _ _
    obtain ⟨_htopdim, htop⟩ := interval_top_dimension_and_rank_bounds (L := L) (p := 0)
      (r := L) (by omega) hxi.le hxi1 hleaf (by omega)
    refine ⟨⊤, Or.inl ⟨hshort, rfl⟩, ?_, htop, hMPSofSpan ⊤ htop⟩
    exact (isViable_fullInterval_iff_isCloseTo _ _).mp
      (Submodule.isViable_top _ hdelta.le _)
  · -- A long chain: the word image of the given space, trimmed.
    have hlongL : 4 * ell < L - 0 := by omega
    obtain ⟨_hell, _hlogD, hfamily⟩ :=
      hlong L q m 0 L i w hq hqm (Nat.zero_le L) le_rfl hw Φ h0 h1
    obtain ⟨N, F, hN, hwords⟩ := hfamily hlongL
    obtain ⟨Tlo, Thi, Delta, _hnest, hupper, hlower, hDelta, htrade, himprove⟩ :=
      hwords eta hbuffer hetaLD
    let RC := Entropy.regionTensorCoordinates q (interval L 0 L)
    -- The comparison loss at the chosen index.
    have hnu : (1 / 200 : ℝ) / 2 ^ (4 * i) ≤ delta / 200 := by
      have hpow : ⌈1 / delta⌉₊ ≤ 16 ^ i := Nat.le_pow_clog (by norm_num) _
      have hpowR : 1 / delta ≤ (2 : ℝ) ^ (4 * i) := by
        have h1 : (1 / delta : ℝ) ≤ (⌈1 / delta⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : ((⌈1 / delta⌉₊ : ℕ) : ℝ) ≤ ((16 ^ i : ℕ) : ℝ) := by exact_mod_cast hpow
        have h3 : ((16 ^ i : ℕ) : ℝ) = (2 : ℝ) ^ (4 * i) := by
          rw [pow_mul]
          norm_num
        linarith only [h1, h2, h3]
      have hpos : (0 : ℝ) < 2 ^ (4 * i) := by positivity
      rw [div_le_iff₀ hpos]
      have := (div_le_iff₀ hdelta).mp hpowR
      nlinarith only [this, hdelta]
    have hnu0 : (0 : ℝ) ≤ (1 / 200 : ℝ) / 2 ^ (4 * i) := by positivity
    -- The given space is viable for the upper target of the family.
    have hS0v : Submodule.IsViable (3 / 200 : ℝ) S0 ((G eta).map RC.toLinearEquiv.toLinearMap) :=
      (isViable_fullInterval_iff_isCloseTo S0 (G eta)).mpr hS0
    have hhi : Submodule.IsViable (1 / 25 : ℝ) S0 (Thi.map RC.toLinearEquiv.toLinearMap) := by
      apply (Submodule.IsCloseTo.trans hS0v ((Submodule.isCloseTo_map_iff RC).mpr hupper)
        (by norm_num)).of_le
      linarith only [hnu, hdelta1]
    have hhi' := hhi
    dsimp only [RC] at hhi'
    rw [Entropy.regionTensorCoordinates_eq_exteriorFirst] at hhi'
    obtain ⟨hgrowdim, hgrow0⟩ := himprove a S0 (1 / 25) hhi' (by norm_num)
    let grow : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q)) :=
      ⨆ x : Fin a → Fin N, S0.map ((List.ofFn (fun j ↦ F (x j))).prod :
        EuclideanSpace ℂ (interval L 0 L → Fin q) →ₗ[ℂ]
          EuclideanSpace ℂ (interval L 0 L → Fin q))
    have hgrow : Submodule.IsViable (Delta ^ a / (1 - 1 / 25) ^ 2) grow
        (Tlo.map RC.toLinearEquiv.toLinearMap) := by
      dsimp only [RC]
      rw [Entropy.regionTensorCoordinates_eq_exteriorFirst]
      exact hgrow0
    -- Suppression by the words.
    have hDelta12 : Delta ≤ 1 / 2 := by
      have hD1 : (1 : ℝ) ≤ (D : ℝ) ^ 12 := by
        have hbase : 1 ≤ mi * ell ^ 2 := Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by norm_num)))
            (pow_ne_zero 2 (Nat.one_le_iff_ne_zero.mp ((by decide : 1 ≤ 21).trans _hell))))
        exact one_le_pow₀ (by exact_mod_cast Nat.one_le_pow _ _ hbase)
      nlinarith only [hD1, hDelta, htrade]
    have hsuppress : Delta ^ a ≤ delta / 32 := by
      have hpow : ⌈32 / delta⌉₊ ≤ 2 ^ a := Nat.le_pow_clog (by norm_num) _
      have hpowR : 32 / delta ≤ (2 : ℝ) ^ a := by
        have h1 : (32 / delta : ℝ) ≤ (⌈32 / delta⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : ((⌈32 / delta⌉₊ : ℕ) : ℝ) ≤ ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast hpow
        have h3 : ((2 ^ a : ℕ) : ℝ) = (2 : ℝ) ^ a := by norm_num
        linarith only [h1, h2, h3]
      calc
        Delta ^ a ≤ (1 / 2 : ℝ) ^ a := pow_le_pow_left₀ hDelta.le hDelta12 a
        _ = 1 / (2 : ℝ) ^ a := by rw [_root_.one_div_pow]
        _ ≤ delta / 32 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          have := (div_le_iff₀ hdelta).mp hpowR
          linarith only [this]
    have hlo : Submodule.IsViable (delta / 8) grow
        ((G (eta - 3 * w)).map RC.toLinearEquiv.toLinearMap) := by
      have hlower' : Submodule.IsCloseTo ((1 / 200 : ℝ) / 2 ^ (4 * i)) Tlo (G (eta - 3 * w)) := by
        simpa only [G, add_sub_assoc] using hlower
      apply (Submodule.IsCloseTo.trans hgrow ((Submodule.isCloseTo_map_iff RC).mpr hlower')
        (by positivity)).of_le
      have hfrac : Delta ^ a / (1 - 1 / 25 : ℝ) ^ 2 ≤ delta / 25 := by
        rw [div_le_iff₀ (by norm_num)]
        nlinarith only [hsuppress, hdelta]
      linarith only [hfrac, hnu, hdelta]
    -- The trim against the reference.
    obtain ⟨_, _, hbudget⟩ := refinement_trimming_budget (L := L) (cuts := L - 0 - 1)
      hdelta (by omega) hDref
    have htrim := isViable_intervalTrimSubspace_of_reference hDref
      (by positivity : (0 : ℝ) ≤ delta / 48) (by positivity : (0 : ℝ) ≤ delta / 8) hxi hGV hVG
      (fun x hx ↦ by simpa only [Dref, Nat.mul_assoc] using hMPS x hx)
      (stdOrthonormalBasis ℂ grow) hlo
    let R := intervalTrimSubspace L q 0 L xi (fun k ↦
      (stdOrthonormalBasis ℂ grow k : EuclideanSpace ℂ (interval L 0 L → Fin q)))
    have hRviable : Submodule.IsViable delta R
        ((G (eta - 3 * w)).map RC.toLinearEquiv.toLinearMap) := by
      apply htrim.of_le
      linarith only [hbudget, hdelta]
    have hgrowM : Module.finrank ℂ grow ≤ M := by
      calc
        Module.finrank ℂ grow ≤ N ^ a * Module.finrank ℂ S0 := hgrowdim
        _ ≤ (D ^ 2) ^ a * count := Nat.mul_le_mul (Nat.pow_le_pow_left hN a) hdim0
        _ = D ^ (2 * a) * count := by rw [← pow_mul]
        _ ≤ M := le_max_right _ _
    have hRspan : IsIntervalSpanWithRankBound L q 0 L M xi R :=
      isIntervalSpanWithRankBound_intervalTrimSubspace hxi (stdOrthonormalBasis ℂ grow)
        hgrowM
    exact ⟨R, Or.inr ⟨N, F, hN, rfl⟩,
      (isViable_fullInterval_iff_isCloseTo _ _).mp hRviable, hRspan, hMPSofSpan R hRspan⟩

set_option maxHeartbeats 800000 in
-- The composition keeps the dependent coordinates of the tree and the refinement.
/-- The root of the low-density sampled tree, at the failure parameter `1/2`,
refines for every `0 < δ ≤ 1` to a space on the whole chain that is `δ`-close
to the window `etaLD - 3w · clog₂ L - 3w` and consists of matrix product states
of the displayed bond dimension, provided `3w (clog₂ L + 2) ≤ etaLD`. The count
`count` is the node bound of the tree, and the reference factor `B` has the
logarithmic bound of the low-energy basis theorem. ALVV, arXiv:1602.08828v2,
Theorem `t:alg2`, lines 1869–1878, in the `δ`-viability form of Theorem
`t:alg1`, lines 1779–1781. -/
theorem exists_physical_ld_tree_refined_approximation (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ Ct C K : ℝ, 100 ≤ Ct ∧ 100 ≤ C ∧ 0 < K ∧
      ∀ (L q m : ℕ) (w : ℝ) (hq : 2 ≤ q), q ≤ m → 0 < w →
      ∀ (Φ : ManyBody.BondInteraction L q),
      ∀ (h0 : ∀ i, 0 ≤ Φ.term i), (∀ i, Φ.term i ≤ 1) →
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩⟩
      let H := Φ.hamiltonian
      let hRaw : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let G := fun eta : ℝ ↦ Submodule.spectralSpanLE
        hRaw.eigenvectorBasis hRaw.eigenvalues (minEigenvalue hRaw + eta)
      let rG := Module.finrank ℂ (G etaLD)
      let gt := min w 1
      let ut := 1 + Real.log ((4 * m : ℕ) : ℝ) + Real.log (1 / gt)
      let ellt : ℕ := ⌈Ct * ut ^ 2 / gt⌉₊
      let Dt : ℕ := ((4 * m) * ellt ^ 2) ^ (22 * ellt)
      let At := 1 + Real.log (rG : ℝ) + Real.log (Dt : ℝ) + Real.log (1 / (1 / 2 : ℝ))
      let st : ℕ := Nat.ceil (4096 * (rG : ℝ) * At)
      let count : ℕ := Dt ^ 6 * st ^ 3
      let eta := etaLD - 3 * w * Nat.clog 2 L
      3 * w * ((Nat.clog 2 L : ℝ) + 2) ≤ etaLD →
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let i := Nat.clog 16 ⌈1 / delta⌉₊
      let mi := m * 2 ^ i
      let g := min w 1
      let u := 1 + Real.log (mi : ℝ) + Real.log (1 / g)
      let ell : ℕ := ⌈C * u ^ 2 / g⌉₊
      let D := (mi * ell ^ 2) ^ (22 * ell)
      let a := Nat.clog 2 ⌈32 / delta⌉₊
      let v := etaLD - (eta - 3 * w)
      let rInner := Module.finrank ℂ (G (eta - 3 * w))
      let gRef := min (min v (etaLD / 2) / 6) 1
      let uRef := 1 + Real.log (q : ℝ) + Real.log (1 / gRef)
      let aRef := 16 + Real.log (1 / gRef) +
        Real.log (1024 * ((L : ℝ) + 1) * ((rInner : ℝ) + 1) / (delta / 48))
      ∃ B : ℕ, 1 ≤ B ∧ Real.log (B : ℝ) ≤
        K * (uRef ^ 3 / gRef + (1 / gRef) ^ (1 / 4 : ℝ) * aRef ^ (3 / 4 : ℝ) * uRef) *
          (1 + Real.log aRef) ∧
      let Dref := rInner * rG * B
      let M := max (q ^ (4 * ell)) (D ^ (2 * a) * count)
      ∃ R : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q)),
        Submodule.IsCloseTo delta (nativeFullIntervalSpace L q R) (G (eta - 3 * w)) ∧
        ∀ x ∈ R, IsOpenMPS L q
          (M * ⌈256 * (Dref : ℝ) ^ 2 * ((L : ℝ) + 1) * M / delta ^ 2⌉₊)
          (fullIntervalRead L q x) := by
  classical
  obtain ⟨Ct, hCt, _hCteta, htree⟩ := exists_physical_ld_sampled_interval_tree etaLD hLD
  obtain ⟨C, K, hC, _hCeta, hK, hrefine⟩ := exists_physical_ld_root_refinement etaLD hLD
  refine ⟨Ct, C, K, hCt, hC, hK, ?_⟩
  intro L q m w hq hqm hw Φ h0 h1 config H hRaw G rG gt ut ellt Dt At st count eta hdeep
    delta hdelta hdelta1
  let : Nonempty (Fin L → Fin q) := config
  obtain ⟨_hell, _hlogD, _N, _F, _hN, hspaces⟩ := htree L q m w hq hqm hw Φ h0 h1
  have hK0 : (0 : ℝ) ≤ Nat.clog 2 L := Nat.cast_nonneg _
  obtain ⟨_Dref, _hDref, hbeta⟩ := hspaces (by nlinarith only [hdeep, hw, hK0])
  obtain ⟨_hs, _operation, _hliteral, hnodes, hroot, _hMPS⟩ :=
    hbeta (1 / 2) (by norm_num) (by norm_num)
  have hdim := (hnodes 0 L (Nat.zero_le L) le_rfl).2.1
  obtain ⟨B, hB, hlogB, R, _hdesc, hclose, _hspan, hMPS⟩ :=
    hrefine L q m w hq hqm hw Φ h0 h1 eta
      (by dsimp only [eta]; nlinarith only [hdeep, hw, hK0])
      (by dsimp only [eta]; nlinarith only [hw, hK0])
      count _ hroot hdim delta hdelta hdelta1
  exact ⟨B, hB, hlogB, R, hclose, hMPS⟩

end TNLean.MPS.AreaLaw
