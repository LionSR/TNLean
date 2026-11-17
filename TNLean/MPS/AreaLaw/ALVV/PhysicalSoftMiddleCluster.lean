/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.FiveRegionSoftUniformClusters
import TNLean.MPS.AreaLaw.ALVV.SoftGeneratedMiddleApproximation
import QICLean.Analysis.SoftClusterParameters

/-!
# A native soft middle approximation with its actual spectral cluster

The soft order, scale and residual cutoff are selected before the chain.
One tuple of actual regional minima is then retained for every admissible
estimated center. The middle soft term has native operator tensors at an
explicit precision, and replacing this term produces an actual invariant
low spectral cluster of the original full ground-space dimension.

This is an existence auxiliary to ALVV, arXiv:1602.08828v2,
`prop:Cheby-AGSP-eff` and `t:aisefficient`, lines 1309–1333 and 1373–1420.
**Local fix (cluster approximation and residuals):** The construction uses
interaction-label cluster estimates and the corrected physical soft
residuals; see `docs/paper-gaps/alvv16_cluster_approximation.tex` and
`docs/paper-gaps/alvv16_soft_regional_residuals.tex`.
**Scope restriction (natural intervals and center dependence):** The interval
has two full collars and the operator tensors are chosen after the centers.
No center-independent family, adaptive measurability or running time is
asserted; see `docs/paper-gaps/alvv16_soft_regional_residuals.tex`.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- On the natural five-region geometry, actual native tensors approximate
the same middle soft term and give a Hermitian matrix with its own closed
low cluster. The scalar parameters precede the chain, the regional minima
precede every estimated center, and the tensors precede every original
ground spectral value. Auxiliary to ALVV, arXiv:1602.08828v2,
`prop:Cheby-AGSP-eff` and `t:aisefficient`, lines 1309–1333 and 1373–1420. -/
theorem exists_physical_soft_middle_cluster {g tau : ℝ}
    (hg : 0 < g) (htau : 0 < tau) (htau1 : tau ≤ 1) :
    ∃ (m : ℕ) (t T : ℝ), 2 ≤ m ∧ t = 3 * (m : ℝ) ∧
      156 + 2 * g ≤ t ∧ 156 + 2 * g ≤ T ∧ g / 40 + 24 ≤ T ∧
      3 * (32 * Real.exp (-(T - g / 40 - 24) / 8) +
        (t / m) * (T / t) ^ m) ≤ tau * g / 1000000 ∧
      3 * (32 * Real.exp (-(T - 156 - 2 * g) / 8) +
        (t / m) * (T / t) ^ m) ≤ tau * g / 1000000 ∧
    ∀ (N q ell a b : ℕ) (_hq : 2 ≤ q) (_hell : 1 ≤ ell)
      (_hab : a + 2 * ell ≤ b) (_hb : b + 2 * ell ≤ N),
      let M := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
      let xi := min 1 (tau * g ^ 2 / (20000 * (M + g + 8)))
      let W := t * (2 : ℝ) ^ (m + 1)
      let clusterBase := 2 * (Real.exp (1 / 3 : ℝ) - 1)
      let order := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
        Real.log (Real.log (1 + xi / W))) / (-Real.log clusterBase)⌉₊
      let bond := ((1 + N * q ^ 2) + (order ^ 2 * q ^ order) * (m + 1)) * 2
      ∀ (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
        (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
          (h i) (interval (N + 1) i.val (i.val + 2)))
        (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1),
      let cuts : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, N + 1]
      let I := fun j : Fin 5 ↦ Finset.univ.filter
        (fun i : Fin N ↦ cuts j.castSucc ≤ i.val ∧ i.val + 1 < cuts j.succ)
      let A := fun j : Fin 5 ↦ ∑ i ∈ I j, h i
      let crossings := Finset.univ.filter
        (fun i : Fin N ↦ i.val + 1 ∈
          ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
      let Y := ∑ i ∈ crossings, h i
      ∃ (e : Fin 5 → ℝ) (x : (Fin (N + 1) → Fin q) → ℂ) (E : ℝ),
        star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
        (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧ 0 ≤ E ∧ E ≤ 4 ∧
        ∀ (p : Fin 5 → ℝ),
          (∀ j ∈ ({0, 2, 4} : Finset (Fin 5)), e j - 10 ≤ p j) →
          (∀ j ∈ ({0, 2, 4} : Finset (Fin 5)), p j ≤ e j) →
          let F := fun j : Fin 5 ↦ (p j : ℂ) • 1 +
            cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1)
          let G := (∑ j, ((if j ∈ ({0, 2, 4} : Finset (Fin 5)) then F j else A j) -
            (e j : ℂ) • 1)) + Y
          G.IsHermitian ∧ ‖G‖ ≤ M ∧ 0 < xi ∧ xi ≤ 1 ∧ (p 2 : ℂ) • 1 ≤ A 2 ∧
          let hq0 : 0 < q := by omega
          let sigma0 : Fin (N + 1) → Fin q := fun _ ↦ ⟨0, hq0⟩
          let insert := insertInterval (L := (b + 1) - (a + 2 * ell))
            (a + 2 * ell) sigma0
          let eJ := intervalShiftOrderIso
            (by omega : a + 2 * ell ≤ b + 1) (by omega : b + 1 ≤ N + 1)
          ∃ (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q bond)
            (C0 : Matrix (Fin bond) (Fin bond) ℂ),
            let Z := MPOTensor.traceChainOperator Acore C0
            let Zphys := QuantumCircuit.embedOp
              (Subtype.val : interval (N + 1) (a + 2 * ell) (b + 1) → Fin (N + 1))
              (QuantumCircuit.embedOp eJ Z)
            let Ghat := G - F 2 + Zphys
            ∃ hGhat : Ghat.IsHermitian,
              Z.IsHermitian ∧ Zphys.IsHermitian ∧
              F 2 = QuantumCircuit.embedOp
                (Subtype.val : interval (N + 1) (a + 2 * ell) (b + 1) → Fin (N + 1))
                (QuantumCircuit.embedOp eJ ((F 2).submatrix insert insert)) ∧
              ‖(F 2).submatrix insert insert - Z‖ ≤ xi ∧ ‖F 2 - Zphys‖ ≤ xi ∧
              Ghat = G - F 2 + Zphys ∧ ‖G - Ghat‖ ≤ xi ∧ ‖Ghat‖ ≤ M + xi ∧
              let Hraw := ∑ i, h i
              let hRaw : Hraw.IsHermitian :=
                (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
              ∀ mu0 : ℝ, mu0 ∈ spectrum ℝ Hraw →
                (∀ z ∈ spectrum ℝ Hraw, z = mu0 ∨ mu0 + g ≤ z) →
                E + ∑ j, e j = mu0 ∧
                let original := Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues mu0
                let target := Submodule.spectralSpanLE hGhat.eigenvectorBasis hGhat.eigenvalues
                  (E + g / 4)
                target = Submodule.spectralSpanLE hGhat.eigenvectorBasis hGhat.eigenvalues
                    (E + 3 * g / 4) ∧
                  Module.finrank ℂ target = Module.finrank ℂ original ∧
                  Submodule.IsCloseTo (3 * tau / 200) target original ∧
                  Submodule.IsCloseTo (3 * tau / 200) original target := by
  obtain ⟨m, t, T, hm, ht, hscale, hT, hTsmall, hO, hR⟩ :=
    Real.exists_soft_cluster_parameters hg htau
  refine ⟨m, t, T, hm, ht, hscale, hT, hTsmall, hO, hR, ?_⟩
  intro N q ell a b hq hell hab hb M xi W clusterBase order bond
    h hs h0 h1 cuts I A crossings Y
  obtain ⟨hcross, e, x, E, hx, hxe, he, hE0, hEC, hfamily⟩ :=
    exists_five_region_soft_uniform_clusters
      (L := N + 1) (q := q) (ell := ell)
      (k1 := a + 1) (k2 := a + 2 * ell) (k3 := b + 1) (k4 := b + 2 * ell)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) h hs h0 h1
  refine ⟨e, x, E, hx, hxe, he, hE0, hEC.trans (by exact_mod_cast hcross), ?_⟩
  intro p hpl hpu F G
  obtain ⟨hG, hnorm, hcomparison⟩ :=
    hfamily p t m hpl hpu (by linarith only [hscale, hg]) hm
  change G.IsHermitian at hG
  change ‖G‖ ≤ M at hnorm
  obtain ⟨hxi, hxi1, _hLo, _hHi⟩ := soft_cluster_actual_window_losses
    (norm_nonneg G) hnorm hE0 (hEC.trans (by exact_mod_cast hcross)) hg htau
  have hp2 : (p 2 : ℂ) • 1 ≤ A 2 :=
    (show (p 2 : ℂ) • (1 : Matrix (Fin (N + 1) → Fin q)
        (Fin (N + 1) → Fin q) ℂ) ≤ (e 2 : ℂ) • 1 from by
      simpa only [Complex.coe_smul] using
        smul_le_smul_of_nonneg_right (hpu 2 (by decide))
          (zero_le_one : (0 : Matrix (Fin (N + 1) → Fin q)
            (Fin (N + 1) → Fin q) ℂ) ≤ 1)).trans (Matrix.le_iff.mpr (he 2))
  refine ⟨hG, hnorm, hxi, hxi1, hp2, ?_⟩
  intro hq0 sigma0 insert eJ
  obtain ⟨Acore, C0, hZ, hZphys, hRecon, hNative, hPlaced⟩ :=
    exists_native_soft_middle_mpo_approximation
      (N := N) (q := q) (l := a + 2 * ell) (r := b + 1) (m := m)
      hq0 (by omega) (by omega) (by omega) h hs h0 h1
      (p 2) t xi hp2 ht.ge hxi
  refine ⟨Acore, C0, ?_⟩
  intro Z Zphys Ghat
  have hF2 : (F 2).IsHermitian :=
    (isHermitian_one.smul (by simp [isSelfAdjoint_iff])).add
      (cfc_predicate (Real.softTruncation t m) (A 2 - (p 2 : ℂ) • 1))
  have hGhat : Ghat.IsHermitian := (hG.sub hF2).add hZphys
  have hDifference : G - Ghat = F 2 - Zphys := by
    dsimp only [Ghat]
    abel
  change ‖F 2 - Zphys‖ ≤ xi at hPlaced
  have hError : ‖G - Ghat‖ ≤ xi := by
    simpa only [hDifference] using hPlaced
  have hNorm : ‖Ghat‖ ≤ M + xi :=
    (norm_le_norm_add_norm_sub G Ghat).trans (add_le_add hnorm hError)
  refine ⟨hGhat, hZ, hZphys, hRecon, hNative, hPlaced, rfl, hError, hNorm, ?_⟩
  intro Hraw hRaw mu0 hmu0 hgap
  obtain ⟨_hxi, _hxi1, hshift, happrox⟩ :=
    hcomparison mu0 g tau T T hmu0 hg htau htau1 hgap
      hTsmall hscale hT hO hR
  exact ⟨hshift, happrox Ghat hGhat hError⟩

end TNLean.MPS.AreaLaw.ALVV
