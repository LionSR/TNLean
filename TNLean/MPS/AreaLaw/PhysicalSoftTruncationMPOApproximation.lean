/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalScaledSoftTruncationCloseness
import TNLean.MPS.AreaLaw.SoftTruncatedHamiltonianMPO

/-!
# Physical spectral windows and an actual soft-truncation MPO at one parameter choice

The order is chosen before every physical Hamiltonian. The actual soft replacement has both
proved spectral-window comparisons and constructed operator tensors at any requested norm
accuracy, with a logarithmic cluster order. Supporting the corrected moment and label routes to
ALVV, arXiv:1602.08828v2, `lem:exp-approx` and `lem:exp-approx-eff`, lines 1195–1268.

**Local fix (parameters and corrected estimates):** scale is three times order. The proof uses
the corrected exponential-moment residual and interaction-label cluster estimate. Neither
false printed estimate nor a computational running time is asserted; see
`docs/paper-gaps/alvv16_soft_truncation_energy_estimate.tex` and
`docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- One physical soft Hamiltonian has the two directed spectral comparisons and an actual
operator-chain approximation at every norm accuracy. The regional and ground data, order and
cluster budget are constructed; no heat, residual, closeness or MPO family is supplied.
Supporting the corrected ALVV route, arXiv:1602.08828v2, `lem:exp-approx` and
`lem:exp-approx-eff`, lines 1195–1268. -/
theorem exists_interval_physical_soft_closeness_and_mpo
    (eta w delta : ℝ) (heta : 0 < eta) (hw : 0 < w) (hdelta : 0 < delta) :
    let rho := min 1 (min (w / 2) (delta * w ^ 2 / (2 * (eta + 2))))
    ∃ m : ℕ, m = ⌈12 + (2 / 3 : ℝ) * eta + (16 / 3 : ℝ) * Real.log (80 / rho)⌉₊ ∧ 0 < m ∧
      ∀ (N q p v : ℕ) (hq : 0 < q) (_hpr : p ≤ v) (_hrL : v ≤ (N + 1))
        (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ),
        (∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
          (h i) (interval (N + 1) i.val (i.val + 2))) →
        (∀ i, 0 ≤ h i) → (∀ i, h i ≤ 1) →
        let : Nonempty (Fin (N + 1) → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
        let k : Fin 6 → ℕ := ![0, p, v, v, v, (N + 1)]
        let A : Fin 5 → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ := fun j ↦
          ∑ i ∈ Finset.univ.filter
            (fun i : Fin N ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
        ∃ (e : Fin 5 → ℝ) (E0 : ℝ) (x : (Fin (N + 1) → Fin q) → ℂ),
          let H := ∑ i, h i
          let Hc := H - (((∑ j, e j) : ℝ) : ℂ) • 1
          ∃ hHc : Hc.IsHermitian,
            star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
            (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
            E0 = minEigenvalue hHc ∧ 0 ≤ E0 ∧ E0 ≤ 2 ∧
            ∀ eps : ℝ, e 1 - 10 ≤ eps → eps ≤ e 1 →
              let Hsoft := H - A 1 + (eps : ℂ) • 1 +
                cfc (Real.softTruncation (3 * (m : ℝ)) m) (A 1 - (eps : ℂ) • 1)
              let Hsc := Hsoft - (((∑ j, e j) : ℝ) : ℂ) • 1
              ∃ (Es : ℝ) (hHsc : Hsc.IsHermitian),
                Es = minEigenvalue hHsc ∧ Hsoft ≤ H ∧
                0 ≤ E0 - Es ∧ E0 - Es ≤ rho ∧
                Submodule.IsCloseTo delta
                  (Submodule.spectralSpanLE hHsc.eigenvectorBasis hHsc.eigenvalues
                    (Es + eta + w))
                  (Submodule.spectralSpanLE hHc.eigenvectorBasis hHc.eigenvalues
                    (E0 + eta)) ∧
                Submodule.IsCloseTo delta
                  (Submodule.spectralSpanLE hHc.eigenvectorBasis hHc.eigenvalues
                    (E0 + eta + w))
                  (Submodule.spectralSpanLE hHsc.eigenvectorBasis hHsc.eigenvalues
                    (Es + eta)) ∧
                ∀ (xi : ℝ), 0 < xi →
                  let W := 3 * (m : ℝ) * (2 : ℝ) ^ (m + 1)
                  let b := 2 * (Real.exp (1 / 3 : ℝ) - 1)
                  let ell := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
                    Real.log (Real.log (1 + xi / W))) / (-Real.log b)⌉₊
                  ∃ T : Fin (N + 1) → MPOTensor q
                      ((1 + N * q ^ 2) + (ell ^ 2 * q ^ ell) * (m + 1)),
                    ‖Hsoft - MPOTensor.traceChainOperator T 1‖ ≤ xi := by
  intro rho
  obtain ⟨m, hmformula, hm, hphysical⟩ :=
    exists_interval_physical_scaled_soft_low_energy_closeness eta w delta heta hw hdelta
  refine ⟨m, hmformula, hm, ?_⟩
  intro N q p v hq hpv hvL h hs h0 h1 _inst k A
  obtain ⟨e, E0, x, hO, hxunit, hx, he, hEcan, hE0, hE2, hclose⟩ :=
    hphysical (N + 1) q p v hq hpv hvL h hs h0 h1
  refine ⟨e, E0, x, hO, hxunit, hx, he, hEcan, hE0, hE2, ?_⟩
  intro eps hepslo hepshi Hsoft Hsc
  obtain ⟨Es, hS, hEscan, hsoftH, hshift0, hshift, hforward, hreverse⟩ :=
    hclose eps hepslo hepshi
  refine ⟨Es, hS, hEscan, hsoftH, hshift0, hshift, hforward, hreverse, ?_⟩
  intro xi hxi W b ell
  classical
  let I : Finset (Fin N) := Finset.univ.filter
    (fun i ↦ p ≤ i.val ∧ i.val + 1 < v)
  have hI : (∑ i ∈ I, h i) = A 1 := by rfl
  have hpair (i : Fin N) : interval (N + 1) i.val (i.val + 2) =
      ({i.castSucc, i.succ} : Finset (Fin (N + 1))) := by
    ext z
    simp only [mem_interval, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff,
      Fin.val_castSucc, Fin.val_succ]
    omega
  have hs' (i : Fin N) : Entropy.IsSupportedOn (h i) {i.castSucc, i.succ} := by
    simpa only [hpair] using hs i
  have hh (i : Fin N) : (h i).IsHermitian := (IsSelfAdjoint.of_nonneg (h0 i)).isHermitian
  have hn (i : Fin N) : ‖h i‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (h0 i)).mpr (h1 i)
  have heps : (eps : ℂ) • (1 : Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ) ≤ A 1 := by
    have heA : (A 1 - (e 1 : ℂ) • 1).PosSemidef := he 1
    have hmin : (e 1 : ℂ) • 1 ≤ A 1 := Matrix.le_iff.mpr heA
    have hlower : eps • (1 : Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ) ≤
        (e 1 : ℝ) • 1 :=
      smul_le_smul_of_nonneg_right hepshi zero_le_one
    have hlowerC : (eps : ℂ) • (1 : Matrix (Fin (N + 1) → Fin q)
        (Fin (N + 1) → Fin q) ℂ) ≤ (e 1 : ℂ) • 1 := by
      simpa only [Complex.coe_smul] using hlower
    exact hlowerC.trans hmin
  obtain ⟨T, hT⟩ := exists_softTruncatedHamiltonian_mpo_of_accuracy hq hm h hs' hh hn I eps xi
    (by simpa only [hI] using heps) hxi
  refine ⟨T, ?_⟩
  simpa only [hI] using hT

end TNLean.MPS.AreaLaw
