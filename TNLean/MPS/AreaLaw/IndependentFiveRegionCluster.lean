/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.EuclideanEigenvectorBasis
import QICLean.Analysis.GroundEnergyBounds
import QICLean.Analysis.LowEnergyCluster
import QICLean.Analysis.LowEnergyPerturbation
import TNLean.Algebra.ExpMulSubMonotone
import TNLean.MPS.AreaLaw.IndependentFiveRegionResidual

/-!
# The physical low cluster with independent clipping and window scales

An independent real clipping threshold gives a full low spectral cluster
of the same dimension as the original physical ground space. The actual
original regional minima, centered energy and clipped Hamiltonian are
constructed from positive nearest-neighbour contractions. The only
additional quantitative premise is the displayed scalar tail bound.

The original full ground space may be degenerate. Its gap is positive
and at most one in this auxiliary; later physical applications may use
the capped gap. This supports ALVV, arXiv:1602.08828v2,
`c:goodagsphardtrunc`, lines 979–1005, and `t:ais`, lines 1010–1024.

**Local fix (closed spectral cutoffs):** The cluster retains the full
original ground space with the closed-cutoff convention documented at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- An actual three-bulk clipping at an independent real threshold has an
accuracy-scaled low cluster. The
regional minima, clipped operator, spectral basis and restricted residuals
are derived from the original nearest-neighbour terms. Only the displayed
scalar tail condition is assumed in this intermediate lemma; the universal
accuracy parameter choice discharges it in the long-middle theorem.
Auxiliary to ALVV, arXiv:1602.08828v2, Corollary 4.6 (`c:goodagsphardtrunc`)
and the approximation conclusion of Theorem 4.9 (`thm:al-dg`).
No simple-ground-space assumption is made. -/
theorem exists_five_region_independent_scaled_low_cluster
    (L q a b ell : ℕ) (t : ℝ) (hq : 0 < q) (hell : 1 ≤ ell) (ht : 21 ≤ t)
    (hab : a + 2 * ell ≤ b + 1) (hbL : b + 2 * ell ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (mu g xi tau : ℝ) (hg : 0 < g) (hg1 : g ≤ 1)
    (htau : 0 < tau) (htau1 : tau ≤ 1)
    (htail : (288 * Real.exp (11 / 8)) *
      Real.exp (-(t - g) / 8) ≤ xi)
    (hxi : xi ≤ tau * g / 1000000) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    mu ∈ spectrum ℝ H →
    (∀ r ∈ spectrum ℝ H, r = mu ∨ mu + g ≤ r) →
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
    let J : Finset (Fin (L - 1)) := Finset.univ.filter
      (fun i ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
    let Y := ∑ i ∈ J, h i
    ∃ (e : Fin 5 → ℝ) (E0 : ℝ),
      let S := ∑ j, e j
      let K : Finset (Fin 5) := {0, 2, 4}
      let B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
        (∑ j, ((if j ∈ K then
          cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) -
            (e j : ℂ) • 1)) + Y
      let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (∃ x : (Fin L → Fin q) → ℂ, star x ⬝ᵥ x = 1 ∧
        (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
        ∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      E0 + S = mu ∧ 0 ≤ E0 ∧ E0 ≤ 4 ∧ ‖B‖ ≤ 3 * t + 4 * (ell : ℝ) ∧
      ∃ (v : OrthonormalBasis (Fin L → Fin q) ℂ
          (EuclideanSpace ℂ (Fin L → Fin q))) (lam : (Fin L → Fin q) → ℝ),
        (∀ j, ι B (v j) = (lam j : ℂ) • v j) ∧
        let T := Submodule.spectralSpanLE v lam (E0 + g / 10)
        T = Submodule.spectralSpanLE v lam (E0 + 9 * g / 10) ∧
        (∀ tau : ℝ, E0 + g / 20 ≤ tau → tau ≤ E0 + 19 * g / 20 →
          Submodule.spectralSpanLE v lam tau = T) ∧
        Module.finrank ℂ T = Module.finrank ℂ G ∧
        Submodule.IsCloseTo (tau / 200 : ℝ) T G ∧
        Submodule.IsCloseTo (tau / 200 : ℝ) G T ∧
        ∀ j, lam j ≤ E0 + g / 10 ∨ E0 + 9 * g / 10 ≤ lam j := by
  intro H hH G hmu hgap k A J Y
  have : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
  obtain ⟨e, E0, x, z, hxunit, hx, hlo, hcenter, hzunit, hz, hE0low,
    hE0ge, hE0le, hnorm, hres⟩ :=
    exists_five_region_independent_truncation_residual L q a b ell t hq hell
      (by linarith only [ht]) hab hbL
      h hs h0 h1
  let S : ℝ := ∑ j, e j
  let K : Finset (Fin 5) := {0, 2, 4}
  let Bcur : Finset (Fin 5) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun T ↦
    (∑ j, ((if j ∈ T then cfc (fun r : ℝ ↦ min r (e j + t))
      (A j) else A j) - (e j : ℂ) • 1)) + Y
  let B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Bcur K
  let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
  have hcenter' : Bcur ∅ = H - (S : ℂ) • 1 := hcenter
  have hzeigen : (H - (S : ℂ) • 1) *ᵥ z = (E0 : ℂ) • z := by
    rw [← hcenter']
    exact hz
  have hlow : ((H - (S : ℂ) • 1) - (E0 : ℂ) • 1).PosSemidef := by
    rw [← hcenter']
    exact hE0low
  obtain ⟨hmuE, hOldEigen, hOldGap⟩ := hH.original_basis_centered_gap_data
    mu g S E0 hmu hgap hg z hzunit hzeigen hlow
  let b0 := hH.eigenvectorBasis
  let a0 : (Fin L → Fin q) → ℝ := fun j ↦ hH.eigenvalues j - S
  have h0Eigen (j : Fin L → Fin q) :
      ι (Bcur ∅) (b0 j) = (a0 j : ℂ) • b0 j := by
    rw [hcenter']
    exact hOldEigen j
  have hA (j : Fin 5) : (A j).IsHermitian := by
    have hAj : 0 ≤ A j := Finset.sum_nonneg fun i _ ↦ h0 i
    exact (IsSelfAdjoint.of_nonneg hAj).isHermitian
  have he (j : Fin 5) : (e j : ℂ) •
      (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ A j :=
    Matrix.le_iff.mpr (hlo j)
  obtain ⟨hXpos, _hXzero⟩ :=
    Matrix.centered_partially_clipped_sum_posSemidef_and_mulVec_eq_zero
      A e t K hA he x hx (by linarith only [ht])
  have hYnonneg : 0 ≤ Y := Finset.sum_nonneg fun i _ ↦ h0 i
  have hBpos : B.PosSemidef := hXpos.add (Matrix.nonneg_iff_posSemidef.mp hYnonneg)
  have hB : B.IsHermitian := hBpos.isHermitian
  let v := hB.eigenvectorBasis
  let lam := hB.eigenvalues
  have hBEigen (j : Fin L → Fin q) : ι B (v j) = (lam j : ℂ) • v j := by
    exact hB.toEuclideanCLM_eigenvectorBasis j
  have hC : 0 ≤ (288 : ℝ) * Real.exp (11 / 8) :=
    mul_nonneg (by norm_num) (Real.exp_nonneg _)
  have hxi0 : 0 ≤ xi :=
    (mul_nonneg hC (Real.exp_nonneg _)).trans htail
  have htailEta (eta : ℝ) (heta : eta ≤ g) :
      (288 * Real.exp (11 / 8)) * Real.exp (-(t - eta) / 8) ≤ xi := by
    have hexp := Real.exp_mul_sub_le_exp_mul_sub
      (v := (1 / 8 : ℝ)) (x := eta) (T := g) (c := t / 8)
      (by norm_num) heta
    have harg (r : ℝ) : -(t - r) / 8 =
        (1 / 8 : ℝ) * r - t / 8 := by ring
    rw [← harg eta, ← harg g] at hexp
    exact (mul_le_mul_of_nonneg_left hexp hC).trans htail
  have hsmall (Tcur : Finset (Fin 5)) (eta : ℝ) (heta0 : 0 ≤ eta) (heta : eta ≤ g)
      (w : OrthonormalBasis (Fin L → Fin q) ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
      (d : (Fin L → Fin q) → ℝ)
      (hEigen : ∀ j, ι (Bcur Tcur) (w j) = (d j : ℂ) • w j) :
      ‖(ι (Bcur ∅) - ι B).domRestrict
        (Submodule.spectralSpanLE w d (E0 + eta))‖ ≤ xi := by
    have hr := (hres Tcur eta heta0 (by linarith only [heta, hg1, ht]) w d hEigen).trans
      (htailEta eta heta)
    simpa only [map_sub] using hr
  have hres0 := hsmall ∅ (g / 40) (by linarith) (by linarith) b0 a0 h0Eigen
  have hresK := hsmall K (19 * g / 20) (by linarith) (by linarith) v lam hBEigen
  obtain ⟨_hUV, hdim, hUG, hGU, hwindow, hNewGap⟩ :=
    Submodule.low_spectral_cluster_of_scaled_restricted_residuals
      (ι (Bcur ∅)) (ι B) b0 v a0 lam h0Eigen hBEigen E0 g xi tau hg htau htau1 hxi0 hxi
      hOldGap hres0 hresK
  let G0 := Submodule.spectralSpanLE b0 a0 E0
  have hG : G0 = G := by
    ext w
    change w ∈ Submodule.spectralSpanLE b0 a0 E0 ↔
      w ∈ Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    simp only [Submodule.mem_spectralSpanLE_iff]
    constructor
    · intro hw j hj
      apply hw j
      change E0 < hH.eigenvalues j - S
      linarith
    · intro hw j hj
      apply hw j
      change E0 < hH.eigenvalues j - S at hj
      linarith
  let U := Submodule.spectralSpanLE v lam (E0 + g / 20)
  let Tlow := Submodule.spectralSpanLE v lam (E0 + g / 10)
  have hTU : Tlow = U :=
    (hwindow (E0 + g / 10) (by linarith) (by linarith)).1
  have hupper : Submodule.spectralSpanLE v lam (E0 + 9 * g / 10) = U :=
    (hwindow (E0 + 9 * g / 10) (by linarith) (by linarith)).1
  refine ⟨e, E0, ⟨x, hxunit, hx, hlo⟩, hmuE.symm, hE0ge, hE0le, hnorm,
    v, lam, hBEigen, hTU.trans hupper.symm, ?_, ?_, ?_, ?_, hNewGap⟩
  · intro tau htaulo htauhi
    exact (hwindow tau htaulo htauhi).1.trans hTU.symm
  · change Module.finrank ℂ Tlow = Module.finrank ℂ G
    rw [hTU, ← hG]
    exact hdim
  · change Submodule.IsCloseTo (tau / 200 : ℝ) Tlow G
    rw [hTU, ← hG]
    exact hUG
  · change Submodule.IsCloseTo (tau / 200 : ℝ) G Tlow
    rw [hTU, ← hG]
    exact hGU

end TNLean.MPS.AreaLaw
