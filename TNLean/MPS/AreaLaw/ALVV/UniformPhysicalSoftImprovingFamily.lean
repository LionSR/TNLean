/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TwoWindowSum
import TNLean.MPS.AreaLaw.ALVV.FiveRegionSoftUniformClusters
import TNLean.MPS.AreaLaw.ALVV.UniformSoftMiddleMPO
import TNLean.MPS.AreaLaw.CommonClosingPolynomialFamily
import QICLean.Analysis.ChebyshevWordPower

/-!
# An actual soft improving family before all estimated centers

One construction of the original regional minima determines a common native
core and polynomial closing matrices. Their common left family precedes every
estimated center. The same represented approximant supplies its own derived
spectral target and actual Chebyshev filter, including every ordered power.

This is a corrected auxiliary to ALVV, arXiv:1602.08828v2,
`prop:Cheby-AGSP-eff` and `t:aisefficient`, lines 1309–1333 and 1373–1420.
**Scope restriction (numerical budgets and geometry):** the statement uses
explicit scalar residual budgets and the natural two-window geometry. It does
not assert the printed fourth-order choice, an adaptive sampling algorithm or
a running-time estimate. The corrected cluster selector and soft residuals
remain those in `docs/paper-gaps/alvv16_cluster_approximation.tex` and
`docs/paper-gaps/alvv16_soft_regional_residuals.tex`.

The filter has minimum gain one on its low cluster; positivity or identity
on the whole low band is not asserted. The closed spectral convention and
unsquared filter are documented at:
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_filter_positivity.pdf
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker TensorProduct Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw.ALVV

/-- Additive identity for replacing three bulks and then the middle one.
Auxiliary to ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333. -/
private theorem actual_three_bulk_replacement_sum {M : Type*} [AddCommGroup M]
    (L a b ell : ℕ) (hell : 1 ≤ ell) (hab : a + 2 * ell ≤ b)
    (hb : b + 2 * ell ≤ L - 1) (h : Fin (L - 1) → M)
    (F shifts : Fin 5 → M) (Z U : M) :
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let A : Fin 5 → M := fun j ↦ ∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
    let Y := ∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ i.val + 1 ∈
        ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ)), h i
    let WL : Fin (2 * ell) → M := fun r ↦ h ⟨a + r.val, by omega⟩
    let WR : Fin (2 * ell) → M := fun r ↦ h ⟨b + r.val, by omega⟩
    let PL := F 0 - ∑ j, shifts j + U
    let G := (∑ j, ((if j ∈ ({0, 2, 4} : Finset (Fin 5)) then F j else A j) -
      shifts j)) + Y
    (∑ i, Sum.elim (Sum.elim WL WR) ![PL, Z, F 4] i) = G - F 2 + U + Z := by
  classical
  intro k A Y WL WR PL G
  have htotal : (∑ i, h i) = (∑ j, A j) + Y := by
    have hh := Finset.sum_five_internal_regions_add_crossings
      (A := M) (L := L) (k1 := a + 1) (k2 := a + 2 * ell)
      (k3 := b + 1) (k4 := b + 2 * ell)
      (by omega) (by omega) (by omega) h
    rw [Fin.sum_univ_five]
    change (∑ i, h i) =
      (∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ 0 ≤ i.val ∧ i.val + 1 < a + 1), h i) +
      (∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ a + 1 ≤ i.val ∧ i.val + 1 < a + 2 * ell), h i) +
      (∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ a + 2 * ell ≤ i.val ∧ i.val + 1 < b + 1), h i) +
      (∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ b + 1 ≤ i.val ∧ i.val + 1 < b + 2 * ell), h i) +
      (∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ b + 2 * ell ≤ i.val ∧ i.val + 1 < L), h i) +
      (∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ i.val + 1 ∈
          ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ)), h i)
    exact hh
  have hwin : (∑ i, h i) = A 0 + (∑ r, WL r) + A 2 + (∑ r, WR r) + A 4 :=
    Fin.sum_univ_eq_actual_two_window_alphabet L a b ell hab hb h
  have hbulk : (∑ r, WL r) + (∑ r, WR r) = A 1 + A 3 + Y := by
    apply add_left_cancel (a := A 0 + A 2 + A 4)
    calc
      _ = A 0 + (∑ r, WL r) + A 2 + (∑ r, WR r) + A 4 := by abel
      _ = (∑ j, A j) + Y := hwin.symm.trans htotal
      _ = _ := by rw [Fin.sum_univ_five]; abel
  have hG : G = F 0 + A 1 + F 2 + A 3 + F 4 - (∑ j, shifts j) + Y := by
    simp only [G, Finset.sum_sub_distrib, Fin.sum_univ_five]
    simp
  simp only [Fintype.sum_sumElim, Fin.sum_univ_three]
  change ((∑ r, WL r) + (∑ r, WR r)) + (PL + Z + F 4) = G - F 2 + U + Z
  rw [hbulk, hG]
  dsimp only [PL]
  abel


open Classical in
/-- The original interactions determine one common polynomial matrix family
before every admissible soft center, together with the approximant's own
closed low cluster. Auxiliary to ALVV, arXiv:1602.08828v2,
`prop:Cheby-AGSP-eff` and `t:aisefficient`, lines 1311–1420. -/
private theorem exists_uniform_physical_soft_polynomial_family
    (q ell m k : ℕ) (g tau t T0 T1 : ℝ)
    (hq : 2 ≤ q) (hell : 1 ≤ ell) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hg : 0 < g) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hscale : 3 * (m : ℝ) ≤ t)
    (hT0 : g / 40 + 24 ≤ T0) (htfloor : 156 + 2 * g ≤ t)
    (hT1 : 156 + 2 * g ≤ T1)
    (hO : 3 * (32 * Real.exp (-(T0 - g / 40 - 24) / 8) +
      (t / m) * (T0 / t) ^ m) ≤ tau * g / 1000000)
    (hR : 3 * (32 * Real.exp (-(T1 - 156 - 2 * g) / 8) +
      (t / m) * (T1 / t) ^ m) ≤ tau * g / 1000000)
    (N a b : ℕ) (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ N)
      (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
      (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
        (h i) (interval (N + 1) i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
  (by
    exact (show Prop from
    let Msoft := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
    let xi := min 1 (tau * g ^ 2 / (20000 * (Msoft + g + 8)))
    let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
    let Sbulk : Finset (Fin 5) := {0, 2, 4}
      let cuts : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, N + 1]
      let A : Fin 5 → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
        fun j ↦ ∑ i ∈ Finset.univ.filter
        (fun i : Fin N ↦ cuts j.castSucc ≤ i.val ∧ i.val + 1 < cuts j.succ), h i
      let crossings := Finset.univ.filter
        (fun i : Fin N ↦ i.val + 1 ∈
          ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
      let Y := ∑ i ∈ crossings, h i
      let Ksites := interval (N + 1) (a + 2 * ell) (b + 1)
      let eK := intervalShiftOrderIso
        (hab.trans (Nat.le_succ b))
        (Nat.succ_le_succ ((Nat.le_add_right b (2 * ell)).trans hb))
      let J := interval (N + 1) (a + ell) (b + ell + 1)
      let eJ := intervalShiftOrderIso
        ((Nat.add_le_add_right ((Nat.le_add_right a (2 * ell)).trans hab) ell).trans
          (Nat.le_succ (b + ell)))
        (Nat.succ_le_succ ((Nat.add_le_add_left
          (Nat.le_mul_of_pos_left ell (by decide : 0 < 2)) b).trans hb))
      let beta := fun _ : Fin (N + 1) ↦ Fin q
      let midConfig := FiniteProduct.Configuration beta J
      let extConfig := FiniteProduct.Configuration beta Jᶜ
      let split := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
      let heatWeight := t * (2 : ℝ) ^ (m + 1)
      let clusterBase := 2 * (Real.exp (1 / 3 : ℝ) - 1)
      let order := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
        Real.log (Real.log (1 + xi / heatWeight))) / (-Real.log clusterBase)⌉₊
      let bond := ((order ^ 2 * q ^ order) * 2) * (m + 1)
      ∃ (e : Fin 5 → ℝ) (x : (Fin (N + 1) → Fin q) → ℂ) (E : ℝ),
        star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
        (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧ 0 ≤ E ∧ E ≤ 4 ∧
        ∃ (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q bond)
          (C : Fin (m + 1) → Matrix (Fin bond) (Fin bond) ℂ),
          let Z := fun z : ℂ ↦ MPOTensor.traceChainOperator Acore
            (∑ j : Fin (m + 1), z ^ j.val • C j)
          let Zphys := fun z : ℂ ↦ QuantumCircuit.embedOp
            (Subtype.val : Ksites → Fin (N + 1)) (QuantumCircuit.embedOp eK (Z z))
          ∃ (n : ℕ) (W : Fin n → Matrix (midConfig)
              (midConfig) ℂ),
            n ≤ D ∧
            (∀ i, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
              ((max 1 bond) ^ (2 * k)) (fun w ↦ W i
                (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
                (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2))) ∧
            ∀ (p : Fin 5 → ℝ)
              (hp0 : ∀ j : Fin 5, j ∈ Sbulk → e j - 10 ≤ p j)
              (hp1 : ∀ j : Fin 5, j ∈ Sbulk → p j ≤ e j),
              let z := Real.exp ((p 2 - e 2) / t)
              let Fraw : Fin 5 → Matrix (Fin (N + 1) → Fin q)
                  (Fin (N + 1) → Fin q) ℂ := fun j ↦ (p j : ℂ) • 1 +
                cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1)
              let G : Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
                (∑ j, ((if j ∈ Sbulk then Fraw j else A j) -
                (e j : ℂ) • 1)) + Y
              let Ghat : Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
                G - Fraw 2 + (p 2 : ℂ) • 1 + Zphys (z : ℂ)
              ∃ hGhat : Ghat.IsHermitian,
                ‖cfc (Real.softTruncation t m) (A 2 - (p 2 : ℂ) • 1) - Zphys (z : ℂ)‖ ≤ xi ∧
                ‖G - Ghat‖ ≤ xi ∧ ‖Ghat‖ ≤ Msoft + xi ∧
                let Hraw := ∑ i, h i
                let hRaw : Hraw.IsHermitian :=
                  (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
                ∀ mu0 : ℝ, mu0 ∈ spectrum ℝ Hraw →
                  (∀ y ∈ spectrum ℝ Hraw, y = mu0 ∨ mu0 + g ≤ y) →
                  let original := Submodule.spectralSpanLE
                    hRaw.eigenvectorBasis hRaw.eigenvalues mu0
                  let target := Submodule.spectralSpanLE hGhat.eigenvectorBasis hGhat.eigenvalues
                    (E + g / 4)
                  E + ∑ j, e j = mu0 ∧
                  target = Submodule.spectralSpanLE hGhat.eigenvectorBasis hGhat.eigenvalues
                    (E + 3 * g / 4) ∧
                  Module.finrank ℂ target = Module.finrank ℂ original ∧
                  Submodule.IsCloseTo (3 * tau / 200) target original ∧
                  Submodule.IsCloseTo (3 * tau / 200) original target ∧
                  ∀ Q : Polynomial ℂ, Q.natDegree ≤ k →
                    ∃ M : Fin n → Matrix extConfig extConfig ℂ,
                      Polynomial.aeval Ghat Q =
                        (∑ i, M i ⊗ₖ W i).submatrix split split)) := by
  classical
  intro resultType
  unfold resultType
  intro Msoft xi D Sbulk cuts A crossings Y Ksites eK J eJ
    beta midConfig extConfig split heatWeight clusterBase order bond
  have ht : 0 < t := lt_of_lt_of_le (by positivity : 0 < 3 * (m : ℝ)) hscale
  have hMsoft : 0 ≤ Msoft := by
    have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
    dsimp only [Msoft]
    positivity
  have hxi : 0 < xi := lt_min (by norm_num) (by positivity)
  have hdata := exists_five_region_soft_uniform_clusters
    (L := N + 1) (q := q) (ell := ell)
    (k1 := a + 1) (k2 := a + 2 * ell) (k3 := b + 1) (k4 := b + 2 * ell)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) h hs h0 h1
  obtain ⟨hcross, e, x, E, hx, hxe, he, hE0, hEC, hfamily⟩ := hdata
  have hlo : (e 2 : ℂ) • 1 ≤ ∑ i ∈ Finset.univ.filter
      (fun i : Fin N ↦ a + 2 * ell ≤ i.val ∧ i.val + 1 < b + 1), h i := by
    exact Matrix.le_iff.mpr (he 2)
  obtain ⟨Acore, C, hZherm, hZerror⟩ := exists_uniform_native_soft_middle_mpo
    (N := N) (q := q) (l := a + 2 * ell) (r := b + 1) (m := m)
    (by omega) (by omega) (by omega) (by omega) h hs h0 h1 (e 2) t xi hlo hscale hxi
  let WL : Fin (2 * ell) → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
    fun r ↦ h ⟨a + r.val, by omega⟩
  let WR : Fin (2 * ell) → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
    fun r ↦ h ⟨b + r.val, by omega⟩
  have hWL (r : Fin (2 * ell)) : Entropy.IsSupportedOn (WL r)
      (interval (N + 1) (a + r.val) (a + r.val + 2)) := hs _
  have hWR (r : Fin (2 * ell)) : Entropy.IsSupportedOn (WR r)
      (interval (N + 1) (b + r.val) (b + r.val + 2)) := hs _
  obtain ⟨n, W, hn, hWbond, hWpoly⟩ :=
    exists_common_physical_polynomial_closing_family_fin
      (L := N + 1) (q := q) (ell := ell) (a := a) (b := b) (B := bond) (k := k)
      WL WR hWL hWR hab (by simpa using hb) hell hq hk Acore C
  have hnD : n ≤ D := by
    convert hn using 1
    dsimp only [D]
    rw [← pow_mul]
    congr 2
    omega
  have hE4 : E ≤ 4 := hEC.trans (by exact_mod_cast hcross)
  refine ⟨e, x, E, hx, hxe, he, hE0, hE4, Acore, C, ?_⟩
  intro Z Zphys
  refine ⟨n, W, hnD, hWbond, ?_⟩
  intro p hpl hpu z Fraw G Ghat
  obtain ⟨hG, hGnorm, hcomparison⟩ := hfamily p t m hpl hpu ht hm
  change G.IsHermitian at hG
  change ‖G‖ ≤ Msoft at hGnorm
  have hp2upper : p 2 ≤ e 2 :=
    hpu 2 (by exact (by decide : (2 : Fin 5) ∈ ({0, 2, 4} : Finset (Fin 5))))
  have hZpoint := hZerror (p 2) hp2upper
  obtain ⟨hz0, hz1, hNativeError, hPlacedError⟩ := hZpoint
  change ‖cfc (Real.softTruncation t m) (A 2 - (p 2 : ℂ) • 1) - Zphys (z : ℂ)‖ ≤ xi
    at hPlacedError
  have hp2 : ((p 2 : ℂ) • (1 : Matrix (Fin (N + 1) → Fin q)
      (Fin (N + 1) → Fin q) ℂ)).IsHermitian :=
    isHermitian_one.smul (by simp [isSelfAdjoint_iff])
  have hF2 : (Fraw 2).IsHermitian := hp2.add
    (cfc_predicate (Real.softTruncation t m) (A 2 - (p 2 : ℂ) • 1))
  have hGhat : Ghat.IsHermitian := ((hG.sub hF2).add hp2).add (hZherm z).2
  have hError : ‖G - Ghat‖ ≤ xi := by
    convert hPlacedError using 1
    congr 1
    dsimp only [Ghat, Fraw]
    abel
  have hNorm : ‖Ghat‖ ≤ Msoft + xi :=
    (norm_le_norm_add_norm_sub G Ghat).trans (add_le_add hGnorm hError)
  refine ⟨hGhat, hPlacedError, hError, hNorm, ?_⟩
  intro Hraw hRaw mu0 hmu0 hgap original target
  have hAtMu := hcomparison mu0
  have hAtScales := hAtMu g tau T0 T1
  have hFixed := hAtScales hmu0 hg htau htau1 hgap hT0 htfloor hT1 hO hR
  obtain ⟨hxiActual, hxi1, hshift, happrox⟩ := hFixed
  change ∀ (Bhat : Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
      (hBhat : Bhat.IsHermitian), ‖G - Bhat‖ ≤ xi →
      let V := Submodule.spectralSpanLE hBhat.eigenvectorBasis hBhat.eigenvalues (E + g / 4)
      V = Submodule.spectralSpanLE hBhat.eigenvectorBasis hBhat.eigenvalues (E + 3 * g / 4) ∧
        Module.finrank ℂ V = Module.finrank ℂ original ∧
        Submodule.IsCloseTo (3 * tau / 200) V original ∧
        Submodule.IsCloseTo (3 * tau / 200) original V at happrox
  obtain ⟨hclosed, hdim, htargetOriginal, horiginalTarget⟩ := happrox Ghat hGhat hError
  refine ⟨hshift, hclosed, hdim, htargetOriginal, horiginalTarget, ?_⟩
  let PL := Fraw 0 - ∑ j, (e j : ℂ) • (1 : Matrix (Fin (N + 1) → Fin q)
    (Fin (N + 1) → Fin q) ℂ) + (p 2 : ℂ) • 1
  have hFsupport (j : Fin 5) : Entropy.IsSupportedOn (Fraw j)
      (interval (N + 1) (cuts j.castSucc) (cuts j.succ)) := by
    let V := QuantumCircuit.supportedOperators q
      (interval (N + 1) (cuts j.castSucc) (cuts j.succ) : Set (Fin (N + 1)))
    have hAmem : A j ∈ V := QuantumCircuit.mem_supportedOperators_of_isSupportedOn
      (isSupportedOn_sum_internal_bonds (N + 1) q (cuts j.castSucc) (cuts j.succ) h hs)
    apply QuantumCircuit.isSupportedOn_of_mem_supportedOperators
    exact V.add_mem (V.smul_mem _ (QuantumCircuit.one_mem_supportedOperators _))
      (QuantumCircuit.cfc_mem_supportedOperators _
        (V.sub_mem hAmem (V.smul_mem _ (QuantumCircuit.one_mem_supportedOperators _))))
  have hPL : Entropy.IsSupportedOn PL (interval (N + 1) 0 (a + 1)) := by
    let V := QuantumCircuit.supportedOperators q
      (interval (N + 1) 0 (a + 1) : Set (Fin (N + 1)))
    have hFmem : Fraw 0 ∈ V := QuantumCircuit.mem_supportedOperators_of_isSupportedOn
      (hFsupport 0)
    apply QuantumCircuit.isSupportedOn_of_mem_supportedOperators
    exact V.add_mem (V.sub_mem hFmem (V.sum_mem fun j _ ↦
      V.smul_mem _ (QuantumCircuit.one_mem_supportedOperators _)))
      (V.smul_mem _ (QuantumCircuit.one_mem_supportedOperators _))
  have hPR : Entropy.IsSupportedOn (Fraw 4) (interval (N + 1) (b + 2 * ell) (N + 1)) :=
    hFsupport 4
  have hAlphabet : (∑ i, Sum.elim (Sum.elim WL WR) ![PL, Zphys (z : ℂ), Fraw 4] i) = Ghat :=
    actual_three_bulk_replacement_sum (N + 1) a b ell hell hab (by simpa using hb) h
      Fraw (fun j ↦ (e j : ℂ) • 1) (Zphys (z : ℂ)) ((p 2 : ℂ) • 1)
  intro Q hQ
  obtain ⟨M, hMatrix, _hTensor⟩ := hWpoly (z : ℂ) PL (Fraw 4) hPL hPR Q hQ
  refine ⟨M, ?_⟩
  have hEval := congrArg (fun B : Matrix (Fin (N + 1) → Fin q)
      (Fin (N + 1) → Fin q) ℂ ↦ Polynomial.aeval B Q) hAlphabet.symm
  exact hEval.trans hMatrix

private theorem contraction_upper_mono {g eta0 upper k : ℝ}
    (hg : 0 < g) (heta : 0 ≤ eta0) (hupper : eta0 < upper) (hk : 0 ≤ k) :
    (2 * Real.exp (-2 * k * Real.sqrt ((g / 2) / (upper - eta0)))) ^ 2 ≤
      (2 * Real.exp (-2 * k * Real.sqrt ((g / 2) / upper))) ^ 2 := by
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonpos_left _ (by linarith only [hk] : -2 * k ≤ 0)
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_left (by positivity : 0 ≤ g / 2)
    (sub_pos.mpr hupper) (sub_le_self upper heta)

/-- A common polynomial matrix decomposition supplies a Chebyshev family with
uniform contraction on a closed cluster of bounded lower endpoint. -/
private theorem exists_uniformly_contracting_tensor_word_family
    {sigma mu nu : Type*} [Fintype sigma] [DecidableEq sigma]
    [Fintype mu] [Fintype nu] [DecidableEq nu] {n k : ℕ}
    (split : sigma ≃ mu × nu) (B : Matrix sigma sigma ℂ) (hB : B.IsHermitian)
    (W : Fin n → Matrix nu nu ℂ)
    (hpoly : ∀ Q : Polynomial ℂ, Q.natDegree ≤ k →
      ∃ M : Fin n → Matrix mu mu ℂ,
        Polynomial.aeval B Q = (∑ i, M i ⊗ₖ W i).submatrix split split)
    (D : ℕ) (hn : n ≤ D) (E g M : ℝ) (hg : 0 < g)
    (hE0 : 0 ≤ E) (hE4 : E ≤ 4) (hNorm : ‖B‖ ≤ M)
    (hclosed : Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues (E + g / 4) =
      Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues (E + 3 * g / 4)) :
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ split
    let Phi := ((EuclideanSpace.basisFun mu ℂ).tensorProduct
      (EuclideanSpace.basisFun nu ℂ)).repr
    let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
      (EuclideanSpace ℂ mu) (EuclideanSpace ℂ nu))
    let A := fun i : Fin n ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := nu) (W i)
    let target := Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues (E + g / 4)
    let Tc := target.map Tm.toLinearEquiv.toLinearMap
    let Delta := (2 * Real.exp (-2 * (k : ℝ) * Real.sqrt ((g / 2) / (M + 4 + g)))) ^ 2
    ∃ (K : (EuclideanSpace ℂ nu ⊗[ℂ] EuclideanSpace ℂ mu) →L[ℂ]
        (EuclideanSpace ℂ nu ⊗[ℂ] EuclideanSpace ℂ mu))
      (Rop : Fin n → EuclideanSpace ℂ mu →L[ℂ] EuclideanSpace ℂ mu),
      K = ∑ i, TensorProduct.mapL (A i) (Rop i) ∧
      (∀ v ∈ Tc, K v ∈ Tc) ∧ (∀ v ∈ Tcᗮ, K v ∈ Tcᗮ) ∧
      (∀ v ∈ Tc, ‖v‖ ≤ ‖K v‖) ∧
      (∀ v ∈ Tcᗮ, ‖K v‖ ^ 2 ≤ Delta * ‖v‖ ^ 2) ∧
      ∀ (r : ℕ) (S : Submodule ℂ (EuclideanSpace ℂ nu)) (delta : ℝ),
        Submodule.IsViable delta S Tc → delta < 1 →
        let grow := ⨆ w : Fin r → Fin n,
          S.map ((List.ofFn (fun j ↦ A (w j))).prod : _ →ₗ[ℂ] _)
        Module.finrank ℂ grow ≤ D ^ r * Module.finrank ℂ S ∧
          Submodule.IsViable (Delta ^ r / (1 - delta) ^ 2) grow Tc := by
  classical
  intro U Phi Tm A target Tc Delta
  have hTensorDecomp (Q : Polynomial ℂ) (hQ : Q.natDegree ≤ k) :
      ∃ M : Fin n → Matrix mu mu ℂ,
        Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          Matrix.toEuclideanCLM (𝕜 := ℂ) (n := sigma) (Polynomial.aeval B Q) ∘L
          Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
            ∑ i, TensorProduct.mapL (A i)
              (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := mu) (M i)) := by
    obtain ⟨M, hM⟩ := hpoly Q hQ
    exact ⟨M, Matrix.toEuclideanCLM_middleFirst_conjugation_of_kronecker_sum
      split M W (Polynomial.aeval B Q) hM⟩
  have hsep : E + g / 4 < E + 3 * g / 4 := by linarith only [hg]
  have hupper : E + 3 * g / 4 ≤ M + 4 + g := by
    have hnonneg := (norm_nonneg B).trans hNorm
    linarith only [hE4, hnonneg, hg]
  obtain ⟨K, Rop, hdec, hKT, hKTo, hlow, hhigh, hwords⟩ :=
    Matrix.exists_chebyshev_tensor_family_of_actual_cluster B hB
      hB.eigenvectorBasis hB.eigenvalues hB.toEuclideanCLM_eigenvectorBasis
      W Tm hTensorDecomp D hn (E + g / 4) (E + 3 * g / 4) (M + 4 + g)
      hsep hupper hclosed (hNorm.trans (by linarith only [hg]))
  have hDelta := contraction_upper_mono (k := (k : ℝ)) hg
    (by linarith only [hE0, hg] : 0 ≤ E + g / 4) (hsep.trans_le hupper)
    (Nat.cast_nonneg k)
  have hgap : E + 3 * g / 4 - (E + g / 4) = g / 2 := by ring
  have hDeltaBound :
      (2 * Real.exp (-2 * (k : ℝ) * Real.sqrt
        ((E + 3 * g / 4 - (E + g / 4)) / (M + 4 + g - (E + g / 4))))) ^ 2 ≤ Delta := by
    simpa only [hgap] using hDelta
  refine ⟨K, Rop, hdec, hKT, hKTo, hlow, ?_, ?_⟩
  · intro v hv
    exact (hhigh v hv).trans (mul_le_mul_of_nonneg_right hDeltaBound (sq_nonneg ‖v‖))
  · intro r S delta hS hdelta grow
    obtain ⟨hdim, hviable⟩ := hwords r S delta hS hdelta
    refine ⟨hdim, hviable.of_le ?_⟩
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (sq_nonneg _) hDeltaBound r) (sq_nonneg (1 - delta))

open Classical in
/-- The original interactions construct one common physical improving family
before every admissible soft center. Each center gives the same native core
with a different closing matrix and its own derived invariant low cluster.
All ordered word families use these same left operators. Auxiliary to ALVV,
arXiv:1602.08828v2, `prop:Cheby-AGSP-eff` and `t:aisefficient`,
lines 1311–1420. -/
theorem exists_uniform_physical_soft_improving_family
    (q ell m k : ℕ) (g tau t T0 T1 : ℝ)
    (hq : 2 ≤ q) (hell : 1 ≤ ell) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hg : 0 < g) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hscale : 3 * (m : ℝ) ≤ t)
    (hT0 : g / 40 + 24 ≤ T0) (htfloor : 156 + 2 * g ≤ t)
    (hT1 : 156 + 2 * g ≤ T1)
    (hO : 3 * (32 * Real.exp (-(T0 - g / 40 - 24) / 8) +
      (t / m) * (T0 / t) ^ m) ≤ tau * g / 1000000)
    (hR : 3 * (32 * Real.exp (-(T1 - 156 - 2 * g) / 8) +
      (t / m) * (T1 / t) ^ m) ≤ tau * g / 1000000)
    (N a b : ℕ) (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ N)
      (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
      (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
        (h i) (interval (N + 1) i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
  (by
    exact (show Prop from
    let Msoft := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
    let xi := min 1 (tau * g ^ 2 / (20000 * (Msoft + g + 8)))
    let upper := Msoft + xi + 4 + g
    let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
    let Delta := (2 * Real.exp (-2 * (k : ℝ) * Real.sqrt ((g / 2) / upper))) ^ 2
    let Sbulk : Finset (Fin 5) := {0, 2, 4}
      let cuts : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, N + 1]
      let A : Fin 5 → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
        fun j ↦ ∑ i ∈ Finset.univ.filter
        (fun i : Fin N ↦ cuts j.castSucc ≤ i.val ∧ i.val + 1 < cuts j.succ), h i
      let crossings := Finset.univ.filter
        (fun i : Fin N ↦ i.val + 1 ∈
          ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ))
      let Y := ∑ i ∈ crossings, h i
      let Ksites := interval (N + 1) (a + 2 * ell) (b + 1)
      let eK := intervalShiftOrderIso
        (hab.trans (Nat.le_succ b))
        (Nat.succ_le_succ ((Nat.le_add_right b (2 * ell)).trans hb))
      let J := interval (N + 1) (a + ell) (b + ell + 1)
      let eJ := intervalShiftOrderIso
        ((Nat.add_le_add_right ((Nat.le_add_right a (2 * ell)).trans hab) ell).trans
          (Nat.le_succ (b + ell)))
        (Nat.succ_le_succ ((Nat.add_le_add_left
          (Nat.le_mul_of_pos_left ell (by decide : 0 < 2)) b).trans hb))
      let beta := fun _ : Fin (N + 1) ↦ Fin q
      let midConfig := FiniteProduct.Configuration beta J
      let extConfig := FiniteProduct.Configuration beta Jᶜ
      let HM := EuclideanSpace ℂ midConfig
      let HE := EuclideanSpace ℂ extConfig
      let HT := HM ⊗[ℂ] HE
      let split := (FiniteProduct.splitEquiv beta J).trans (Equiv.prodComm _ _)
      let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ split
      let Phi := ((EuclideanSpace.basisFun (extConfig) ℂ).tensorProduct
        (EuclideanSpace.basisFun (midConfig) ℂ)).repr
      let Tcoord := U.trans Phi.symm
      let Tm := Tcoord.trans (TensorProduct.commIsometry ℂ
        (HE)
        (HM))
      let heatWeight := t * (2 : ℝ) ^ (m + 1)
      let clusterBase := 2 * (Real.exp (1 / 3 : ℝ) - 1)
      let order := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
        Real.log (Real.log (1 + xi / heatWeight))) / (-Real.log clusterBase)⌉₊
      let bond := ((order ^ 2 * q ^ order) * 2) * (m + 1)
      ∃ (e : Fin 5 → ℝ) (x : (Fin (N + 1) → Fin q) → ℂ) (E : ℝ),
        star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
        (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧ 0 ≤ E ∧ E ≤ 4 ∧
        ∃ (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q bond)
          (C : Fin (m + 1) → Matrix (Fin bond) (Fin bond) ℂ),
          let Z := fun z : ℂ ↦ MPOTensor.traceChainOperator Acore
            (∑ j : Fin (m + 1), z ^ j.val • C j)
          let Zphys := fun z : ℂ ↦ QuantumCircuit.embedOp
            (Subtype.val : Ksites → Fin (N + 1)) (QuantumCircuit.embedOp eK (Z z))
          ∃ (n : ℕ) (W : Fin n → Matrix (midConfig)
              (midConfig) ℂ),
            let Fops : Fin n → HM →L[ℂ]
                HM := fun i ↦
              Matrix.toEuclideanCLM (𝕜 := ℂ)
              (n := midConfig) (W i)
            n ≤ D ∧
            (∀ i, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
              ((max 1 bond) ^ (2 * k)) (fun w ↦ W i
                (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
                (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2))) ∧
            ∀ (p : Fin 5 → ℝ)
              (hp0 : ∀ j : Fin 5, j ∈ Sbulk → e j - 10 ≤ p j)
              (hp1 : ∀ j : Fin 5, j ∈ Sbulk → p j ≤ e j),
              let z := Real.exp ((p 2 - e 2) / t)
              let Fraw : Fin 5 → Matrix (Fin (N + 1) → Fin q)
                  (Fin (N + 1) → Fin q) ℂ := fun j ↦ (p j : ℂ) • 1 +
                cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1)
              let G : Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
                (∑ j, ((if j ∈ Sbulk then Fraw j else A j) -
                (e j : ℂ) • 1)) + Y
              let Ghat : Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
                G - Fraw 2 + (p 2 : ℂ) • 1 + Zphys (z : ℂ)
              ∃ hGhat : Ghat.IsHermitian,
                ‖cfc (Real.softTruncation t m) (A 2 - (p 2 : ℂ) • 1) - Zphys (z : ℂ)‖ ≤ xi ∧
                ‖G - Ghat‖ ≤ xi ∧ ‖Ghat‖ ≤ Msoft + xi ∧
                let Hraw := ∑ i, h i
                let hRaw : Hraw.IsHermitian :=
                  (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
                ∀ mu0 : ℝ, mu0 ∈ spectrum ℝ Hraw →
                  (∀ y ∈ spectrum ℝ Hraw, y = mu0 ∨ mu0 + g ≤ y) →
                  let original := Submodule.spectralSpanLE
                    hRaw.eigenvectorBasis hRaw.eigenvalues mu0
                  let target := Submodule.spectralSpanLE hGhat.eigenvectorBasis hGhat.eigenvalues
                    (E + g / 4)
                  let Tc := target.map Tm.toLinearEquiv.toLinearMap
                  E + ∑ j, e j = mu0 ∧
                  target = Submodule.spectralSpanLE hGhat.eigenvectorBasis hGhat.eigenvalues
                    (E + 3 * g / 4) ∧
                  Module.finrank ℂ target = Module.finrank ℂ original ∧
                  Submodule.IsCloseTo (3 * tau / 200) target original ∧
                  Submodule.IsCloseTo (3 * tau / 200) original target ∧
                  ∃ (K : HT →L[ℂ] HT) (Rop : Fin n → HE →L[ℂ] HE),
                    K = ∑ i, TensorProduct.mapL (Fops i) (Rop i) ∧
                    (∀ v ∈ Tc, K v ∈ Tc) ∧ (∀ v ∈ Tcᗮ, K v ∈ Tcᗮ) ∧
                    (∀ v ∈ Tc, ‖v‖ ≤ ‖K v‖) ∧
                    (∀ v ∈ Tcᗮ, ‖K v‖ ^ 2 ≤ Delta * ‖v‖ ^ 2) ∧
                    ∀ (r : ℕ) (S : Submodule ℂ HM) (delta : ℝ),
                      Submodule.IsViable delta S Tc → delta < 1 →
                      let grow := ⨆ w : Fin r → Fin n,
                        S.map ((List.ofFn (fun j ↦ Fops (w j))).prod : _ →ₗ[ℂ] _)
                      Module.finrank ℂ grow ≤ D ^ r * Module.finrank ℂ S ∧
                        Submodule.IsViable (Delta ^ r / (1 - delta) ^ 2) grow Tc)) := by
  classical
  intro resultType
  unfold resultType
  intro Msoft xi upper D Delta Sbulk cuts A crossings Y Ksites eK J eJ
    beta midConfig extConfig HM HE HT split U Phi Tcoord Tm heatWeight clusterBase order bond
  obtain ⟨e, x, E, hx, hxe, he, hE0, hE4, Acore, C, n, W, hnD, hWbond, hcenter⟩ :=
    exists_uniform_physical_soft_polynomial_family q ell m k g tau t T0 T1
      hq hell hm hk hg htau htau1 hscale hT0 htfloor hT1 hO hR N a b hab hb h hs h0 h1
  refine ⟨e, x, E, hx, hxe, he, hE0, hE4, Acore, C, ?_⟩
  intro Z Zphys
  refine ⟨n, W, hnD, hWbond, ?_⟩
  intro p hpl hpu z Fraw G Ghat
  obtain ⟨hGhat, hMiddleError, hError, hNorm, hOwn⟩ := hcenter p hpl hpu
  refine ⟨hGhat, hMiddleError, hError, hNorm, ?_⟩
  intro Hraw hRaw mu0 hmu0 hgap original target Tc
  obtain ⟨hshift, hclosed, hdim, htargetOriginal, horiginalTarget, hdecomp⟩ :=
    hOwn mu0 hmu0 hgap
  refine ⟨hshift, hclosed, hdim, htargetOriginal, horiginalTarget, ?_⟩
  have hResult := exists_uniformly_contracting_tensor_word_family
    (sigma := Fin (N + 1) → Fin q) (mu := extConfig) (nu := midConfig)
    split Ghat hGhat W hdecomp D hnD E g (Msoft + xi) hg hE0 hE4 hNorm hclosed
  exact hResult

end TNLean.MPS.AreaLaw.ALVV
