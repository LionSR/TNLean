/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.FiveRegionSoftResiduals
import TNLean.MPS.AreaLaw.SelectedRegionalSoftMPO
import QICLean.Analysis.GroundShiftSpectralComparison

/-!
# Spectral comparisons and an MPO for the same physical soft Hamiltonian

The original interactions construct all regional ground data, the actual estimated-center
soft Hamiltonian and its low-energy residuals. Its normalized ground vector derives the
energy shift and both buffered low-space comparisons. A separate approximation of exactly
that same matrix gives actual Hermitian tensors on the nonempty physical chain.

These corrected auxiliaries support ALVV, arXiv:1602.08828v2, `t:aisefficient`,
lines 1373–1392. The interaction-label cluster bound, independent scale at least three times
order, explicit tensor bond and spectral window count remain visible. No polynomial GEN
or running-time claim is made; see `docs/paper-gaps/alvv16_cluster_approximation.tex` and
`docs/paper-gaps/alvv16_soft_regional_residuals.tex`.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- The actual simultaneous estimated-center soft Hamiltonian has both physical residuals,
a derived ground-energy shift, both directed buffered spectral comparisons and an actual
Hermitian MPO approximation. Regional and soft ground data precede all comparison parameters
and the requested MPO accuracy. The represented chain has N+1 sites. Corrected auxiliary to
ALVV, arXiv:1602.08828v2, `t:aisefficient`, lines 1373–1392; no efficient-GEN conclusion. -/
theorem exists_five_region_soft_representation {N q k1 k2 k3 k4 : ℕ}
    (hq : 0 < q) (h12 : k1 ≤ k2) (h23 : k2 ≤ k3)
    (h34 : k3 ≤ k4) (h4L : k4 ≤ N + 1)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) (interval (N + 1) i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, k1, k2, k3, k4, N + 1]
    let I := fun j : Fin 5 ↦ Finset.univ.filter
      (fun i : Fin N ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A := fun j : Fin 5 ↦ ∑ i ∈ I j, h i
    let J := Finset.univ.filter
      (fun i : Fin N ↦ i.val + 1 ∈ ({k1, k2, k3, k4} : Finset ℕ))
    let Y := ∑ i ∈ J, h i
    J.card ≤ 4 ∧ ∃ (e : Fin 5 → ℝ) (x z : (Fin (N + 1) → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      let H := (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1
      star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E : ℂ) • z ∧
      (H - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ (J.card : ℝ) ∧
      H.IsHermitian ∧
      ∃ (bH : OrthonormalBasis (Fin (N + 1) → Fin q) ℂ (EuclideanSpace ℂ (Fin (N + 1) → Fin q)))
        (aH : (Fin (N + 1) → Fin q) → ℝ),
        (∀ v, toEuclideanCLM (n := Fin (N + 1) → Fin q) (𝕜 := ℂ) H (bH v) =
          (aH v : ℂ) • bH v) ∧ ∀ (S : Finset (Fin 5)) (p : Fin 5 → ℝ) (t : ℝ) (m : ℕ),
        (∀ j ∈ S, e j - 10 ≤ p j) → (∀ j ∈ S, p j ≤ e j) → 0 < t → 2 ≤ m →
        let B := ∑ j, ((if j ∈ S then (p j : ℂ) • 1 +
          cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1) else A j) - (e j : ℂ) • 1)
        let D := 10 * (S.card : ℝ)
        let G := B + Y
        ∃ (mu : ℝ) (w : (Fin (N + 1) → Fin q) → ℂ), G.IsHermitian ∧
          (B + (D : ℂ) • 1).PosSemidef ∧ G ≤ H ∧ star w ⬝ᵥ w = 1 ∧
          G *ᵥ w = (mu : ℂ) • w ∧ (G - (mu : ℂ) • 1).PosSemidef ∧
          -D ≤ mu ∧ mu ≤ E ∧ mu ≤ (J.card : ℝ) ∧
          ∃ (bG : OrthonormalBasis (Fin (N + 1) → Fin q) ℂ (EuclideanSpace ℂ (Fin (N + 1) → Fin q)))
            (aG : (Fin (N + 1) → Fin q) → ℝ),
            (∀ v, toEuclideanCLM (n := Fin (N + 1) → Fin q) (𝕜 := ℂ) G (bG v) =
              (aG v : ℂ) • bG v) ∧
          (∀ eta T : ℝ, 0 ≤ eta → eta + 3 * (J.card : ℝ) + 12 ≤ T →
            ‖(toEuclideanCLM (n := Fin (N + 1) → Fin q) (𝕜 := ℂ) (H - G)).domRestrict
              (Submodule.spectralSpanLE bH aH (E + eta))‖ ≤
              (S.card : ℝ) * ((8 * (J.card : ℝ)) *
                Real.exp (-(T - eta - 3 * (J.card : ℝ) - 12) / 8) +
                (t / (m : ℝ)) * (T / t) ^ m)) ∧
          (∀ eta T : ℝ, 0 ≤ eta →
            let U := 2 * (eta + D + 3 * (J.card : ℝ) + 2)
            U ≤ t → U ≤ T →
            ‖(toEuclideanCLM (n := Fin (N + 1) → Fin q) (𝕜 := ℂ) (H - G)).domRestrict
              (Submodule.spectralSpanLE bG aG (mu + eta))‖ ≤
              (S.card : ℝ) * ((8 * (J.card : ℝ)) * Real.exp (-(T - U) / 8) +
                (t / (m : ℝ)) * (T / t) ^ m)) ∧
          (∀ eta T hwin wbuf : ℝ, 0 ≤ eta → 0 < hwin → 0 < wbuf →
            let U := 2 * (eta + D + 3 * (J.card : ℝ) + 2)
            U ≤ t → U ≤ T → eta + 3 * (J.card : ℝ) + 12 ≤ T →
            let rhoH := (S.card : ℝ) * ((8 * (J.card : ℝ)) *
              Real.exp (-(T - eta - 3 * (J.card : ℝ) - 12) / 8) +
              (t / (m : ℝ)) * (T / t) ^ m)
            let rhoG := (S.card : ℝ) * ((8 * (J.card : ℝ)) * Real.exp (-(T - U) / 8) +
              (t / (m : ℝ)) * (T / t) ^ m)
            let count := ⌈(eta + hwin) / (2 * hwin)⌉₊
            0 ≤ E - mu ∧ E - mu ≤ rhoG ∧
              Submodule.IsCloseTo ((count : ℝ) * (rhoH + hwin) ^ 2 / (wbuf + hwin) ^ 2)
                (Submodule.spectralSpanLE bG aG (mu + eta + rhoG + wbuf))
                (Submodule.spectralSpanLE bH aH (E + eta)) ∧
              Submodule.IsCloseTo ((count : ℝ) * (rhoG + hwin) ^ 2 / (wbuf + hwin) ^ 2)
                (Submodule.spectralSpanLE bH aH (E + eta + wbuf))
                (Submodule.spectralSpanLE bG aG (mu + eta))) ∧
          (∀ xi : ℝ, 0 < xi → 3 * (m : ℝ) ≤ t →
            let delta := xi / (max 1 S.card : ℕ)
            let W := t * (2 : ℝ) ^ (m + 1)
            let b := 2 * (Real.exp (1 / 3 : ℝ) - 1)
            let r := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
              Real.log (Real.log (1 + delta / W))) / (-Real.log b)⌉₊
            let D0 := 1 + N * q ^ 2
            let bond := D0 + ((D0 + (r ^ 2 * q ^ r) * (m + 1)) * 2) * S.card
            ∃ tensors : Fin (N + 1) → MPOTensor q bond,
              (MPOTensor.traceChainOperator tensors 1).IsHermitian ∧
              ‖G - MPOTensor.traceChainOperator tensors 1‖ ≤ xi) := by
  intro k I A J Y
  obtain ⟨hJ, e, x, z, E, hx, hxe, he, hz, hHz, hE, hE0, hEC,
      hH, bH, aH, hEigH, hfamily⟩ :=
    exists_five_region_soft_residuals hq h12 h23 h34 h4L h hs h0 h1
  let H := (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1
  refine ⟨hJ, e, x, z, E, hx, hxe, he, hz, hHz, hE, hE0, hEC, hH, bH, aH, hEigH, ?_⟩
  intro S p t m hpl hpu ht hm B D G
  obtain ⟨mu, w, hG, hBpos, hGH, hw, hGw, hGlow, hmuD, hmuE, hmuC,
      bG, aG, hEigG, hforward, hreverse⟩ := hfamily S p t m hpl hpu ht hm
  refine ⟨mu, w, hG, hBpos, hGH, hw, hGw, hGlow, hmuD, hmuE, hmuC,
    bG, aG, hEigG, hforward, hreverse, ?_, ?_⟩
  · intro eta T hwin wbuf heta hhwin hwbuf U hscale hT hTorig rhoH rhoG count
    let v : EuclideanSpace ℂ (Fin (N + 1) → Fin q) :=
      (EuclideanSpace.equiv (Fin (N + 1) → Fin q) ℂ).symm w
    have hvnorm : ‖v‖ = 1 := by
      have hsquare := re_star_dotProduct_self_eq_norm_sq w
      rw [hw] at hsquare
      change (1 : ℝ) = ‖v‖ ^ 2 at hsquare
      nlinarith only [hsquare, norm_nonneg v]
    have hvEigen : toEuclideanCLM (n := Fin (N + 1) → Fin q) (𝕜 := ℂ) G v =
        (mu : ℂ) • v := by
      change (EuclideanSpace.equiv (Fin (N + 1) → Fin q) ℂ).symm (G *ᵥ w) = _
      have hGw' : G *ᵥ w = (mu : ℂ) • w := hGw
      rw [hGw', map_smul]
    exact ground_shift_and_isCloseTo_pair_of_restricted_residuals H G
      E mu eta rhoH rhoG hwin wbuf hE hGlow bH bG aH aG hEigH hEigG
      v hvnorm hvEigen hmuE heta hhwin hwbuf
      (hforward eta T heta hTorig) (hreverse eta T heta hscale hT)
  · intro xi hxi hscale delta W b r D0 bond
    let F := fun j : Fin 5 ↦ (p j : ℂ) • 1 +
      cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1)
    let Braw := ∑ j, (A j - (e j : ℂ) • 1)
    obtain ⟨_hk, _hR, _hsA, _hA, _hY, _hYC, _hJ, hsumraw⟩ :=
      five_region_original_bond_data (N + 1) q k1 k2 k3 k4 h12 h23 h34 h4L h hs h0 h1
    change (∑ i, h i) = (∑ j, A j) + Y at hsumraw
    have hcenter : H = Braw + Y := by
      dsimp only [H, Braw]
      rw [hsumraw, Finset.sum_sub_distrib]
      push_cast
      rw [Finset.sum_smul]
      abel
    have hdiff : Braw - B = ∑ j ∈ S, (A j - F j) :=
      sum_centered_sub_partially_replaced_eq A F (fun j ↦ (e j : ℂ) • 1) S
    have hGsum : G = H + ∑ j ∈ S, (F j - A j) := by
      calc
        _ = (Braw + Y) - (Braw - B) := by dsimp only [G]; abel
        _ = H - ∑ j ∈ S, (A j - F j) := by rw [← hcenter, hdiff]
        _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]; abel
    have hsites (i : Fin N) :
        interval (N + 1) i.val (i.val + 2) ⊆ {i.castSucc, i.succ} := by
      intro j hj
      have hj' := mem_interval.mp hj
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hji : j.val = i.val
      · left
        exact Fin.ext hji
      · right
        apply Fin.ext
        change j.val = i.val + 1
        omega
    have hs' (i : Fin N) : Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
        (h i) {i.castSucc, i.succ} := (hs i).mono (hsites i)
    have hherm (i : Fin N) : (h i).IsHermitian := (h0 i).posSemidef.isHermitian
    have hnorm (i : Fin N) : ‖h i‖ ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg (h i) (h0 i)).mpr (h1 i)
    have hlo (j : Fin 5) (hj : j ∈ S) : (p j : ℂ) • 1 ≤ ∑ i ∈ I j, h i := by
      have hpe : (p j : ℝ) • (1 : Matrix (Fin (N + 1) → Fin q)
          (Fin (N + 1) → Fin q) ℂ) ≤ (e j : ℝ) • 1 :=
        smul_le_smul_of_nonneg_right (hpu j hj) zero_le_one
      have heA : (e j : ℝ) • (1 : Matrix (Fin (N + 1) → Fin q)
          (Fin (N + 1) → Fin q) ℂ) ≤ A j := by
        have heAj : (A j - (e j : ℂ) • 1).PosSemidef := he j
        have heA' : (e j : ℂ) • (1 : Matrix (Fin (N + 1) → Fin q)
            (Fin (N + 1) → Fin q) ℂ) ≤ A j := Matrix.le_iff.mpr heAj
        simpa only [Complex.coe_smul] using heA'
      simpa only [Complex.coe_smul] using hpe.trans heA
    obtain ⟨tensors, _hM, hMT, herr⟩ :=
      exists_selected_regional_softTruncations_hermitian_mpo_of_accuracy
        (by omega : 1 ≤ q) (by omega : 0 < m) h hs' hherm hnorm I p S
        t xi (-∑ j, e j) hlo hscale hxi
    have hmatrix : (∑ i, h i) + (((-∑ j, e j) : ℝ) : ℂ) • 1 +
        ∑ j ∈ S, (F j - A j) = G := by
      rw [hGsum]
      dsimp only [H]
      rw [Complex.ofReal_neg, neg_smul]
      abel
    rw [hmatrix] at herr
    exact ⟨tensors, hMT, herr⟩

end TNLean.MPS.AreaLaw.ALVV
