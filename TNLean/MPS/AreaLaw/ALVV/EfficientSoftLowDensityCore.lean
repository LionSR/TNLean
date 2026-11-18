/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.FiveRegionSoftRepresentation
import TNLean.MPS.AreaLaw.ALVV.UniformPhysicalSoftImprovingFamily

/-!
# A soft polynomial family with windowed spectral comparisons

One construction of the original regional minima determines the native soft middle
operator, its polynomial closing matrices and a common family of middle operators with
open matrix product bond. For every admissible estimate of the three bulk energies, the
represented approximant `Ghat` has a polynomial matrix decomposition through this family, and
the exact soft Hamiltonian `G` it approximates has the buffered windowed comparisons with
the original Hamiltonian. No spectral gap is assumed: these are the inputs of the efficient
low-density improving family.

This is a corrected auxiliary to ALVV, arXiv:1602.08828v2, `t:aisgaplessefficient`,
lines 1435–1457, built as the gapped family of `t:aisefficient`, lines 1373–1420.

**Local fix (cluster estimate and soft residuals):** the middle operator uses the corrected
interaction-label cluster estimate and an independent scale `t ≥ 3 m`, and the residuals are
the corrected regional ones. See `docs/paper-gaps/alvv16_cluster_approximation.tex` and
`docs/paper-gaps/alvv16_soft_regional_residuals.tex`.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker TensorProduct Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- The original interactions determine one common polynomial matrix family before every
admissible soft center. For each center, the represented approximant has a polynomial
decomposition through the family, and the exact soft Hamiltonian it approximates has both
buffered windowed comparisons with the original Hamiltonian. No gap is assumed. Auxiliary to
ALVV, arXiv:1602.08828v2, `t:aisgaplessefficient`, lines 1435–1457. -/
theorem exists_soft_low_density_polynomial_core
    (q ell m k : ℕ) (t xi : ℝ)
    (hq : 2 ≤ q) (hell : 1 ≤ ell) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hscale : 3 * (m : ℝ) ≤ t) (hxi : 0 < xi)
    (N a b : ℕ) (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ N)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) (interval (N + 1) i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
  (by
    exact (show Prop from
    let Msoft := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
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
      let H := (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1
      (∃ z : (Fin (N + 1) → Fin q) → ℂ, star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E : ℂ) • z ∧
        (H - (E : ℂ) • 1).PosSemidef) ∧
      ∃ (bH : OrthonormalBasis (Fin (N + 1) → Fin q) ℂ
          (EuclideanSpace ℂ (Fin (N + 1) → Fin q)))
        (aH : (Fin (N + 1) → Fin q) → ℝ),
        (∀ v, toEuclideanCLM (n := Fin (N + 1) → Fin q) (𝕜 := ℂ) H (bH v) =
          (aH v : ℂ) • bH v) ∧
      ∃ (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q bond)
        (C : Fin (m + 1) → Matrix (Fin bond) (Fin bond) ℂ),
        let Z := fun z : ℂ ↦ MPOTensor.traceChainOperator Acore
          (∑ j : Fin (m + 1), z ^ j.val • C j)
        let Zphys := fun z : ℂ ↦ QuantumCircuit.embedOp
          (Subtype.val : Ksites → Fin (N + 1)) (QuantumCircuit.embedOp eK (Z z))
        ∃ (n : ℕ) (W : Fin n → Matrix midConfig midConfig ℂ),
          n ≤ D ∧
          (∀ i, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
            ((max 1 bond) ^ (2 * k)) (fun w ↦ W i
              (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
              (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2))) ∧
          ∀ (p : Fin 5 → ℝ)
            (_hp0 : ∀ j : Fin 5, j ∈ Sbulk → e j - 10 ≤ p j)
            (_hp1 : ∀ j : Fin 5, j ∈ Sbulk → p j ≤ e j),
            let z := Real.exp ((p 2 - e 2) / t)
            let Fraw : Fin 5 → Matrix (Fin (N + 1) → Fin q)
                (Fin (N + 1) → Fin q) ℂ := fun j ↦ (p j : ℂ) • 1 +
              cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1)
            let G : Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
              (∑ j, ((if j ∈ Sbulk then Fraw j else A j) - (e j : ℂ) • 1)) + Y
            let Ghat : Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ :=
              G - Fraw 2 + (p 2 : ℂ) • 1 + Zphys (z : ℂ)
            ∃ (hG : G.IsHermitian) (hGhat : Ghat.IsHermitian),
              ‖G - Ghat‖ ≤ xi ∧ ‖Ghat‖ ≤ Msoft + xi ∧
              (∀ Q : Polynomial ℂ, Q.natDegree ≤ k →
                ∃ M : Fin n → Matrix extConfig extConfig ℂ,
                  Polynomial.aeval Ghat Q = (∑ i, M i ⊗ₖ W i).submatrix split split) ∧
              ∃ mu : ℝ, -30 ≤ mu ∧ mu ≤ E ∧
                ∀ (eta T hwin wbuf : ℝ), 0 ≤ eta → 0 < hwin → 0 < wbuf →
                  let U := 2 * (eta + 30 + 3 * (crossings.card : ℝ) + 2)
                  U ≤ t → U ≤ T → eta + 3 * (crossings.card : ℝ) + 12 ≤ T →
                  let rhoH := 3 * ((8 * (crossings.card : ℝ)) *
                    Real.exp (-(T - eta - 3 * (crossings.card : ℝ) - 12) / 8) +
                    (t / (m : ℝ)) * (T / t) ^ m)
                  let rhoG := 3 * ((8 * (crossings.card : ℝ)) * Real.exp (-(T - U) / 8) +
                    (t / (m : ℝ)) * (T / t) ^ m)
                  let count := ⌈(eta + hwin) / (2 * hwin)⌉₊
                  0 ≤ E - mu ∧ E - mu ≤ rhoG ∧
                    Submodule.IsCloseTo ((count : ℝ) * (rhoH + hwin) ^ 2 / (wbuf + hwin) ^ 2)
                      (Submodule.spectralSpanLE hG.eigenvectorBasis hG.eigenvalues
                        (mu + eta + rhoG + wbuf))
                      (Submodule.spectralSpanLE bH aH (E + eta)) ∧
                    Submodule.IsCloseTo ((count : ℝ) * (rhoG + hwin) ^ 2 / (wbuf + hwin) ^ 2)
                      (Submodule.spectralSpanLE bH aH (E + eta + wbuf))
                      (Submodule.spectralSpanLE hG.eigenvectorBasis hG.eigenvalues
                        (mu + eta)))) := by
  classical
  intro resultType
  unfold resultType
  intro Msoft D Sbulk cuts A crossings Y Ksites eK J eJ
    beta midConfig extConfig split heatWeight clusterBase order bond
  have ht : 0 < t := lt_of_lt_of_le (by positivity : 0 < 3 * (m : ℝ)) hscale
  obtain ⟨hJ, e, x, z0, E, hx, hxe, he, hz0, hHz0, hE, hE0, hEC, _hH, bH, aH, hEigH,
      hfamily⟩ :=
    exists_five_region_soft_representation (N := N) (q := q)
      (k1 := a + 1) (k2 := a + 2 * ell) (k3 := b + 1) (k4 := b + 2 * ell)
      (by omega) (by omega) (by omega) (by omega) (by omega) h hs h0 h1
  have hE4 : E ≤ 4 := hEC.trans (by exact_mod_cast hJ)
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
  refine ⟨e, x, E, hx, hxe, he, hE0, hE4, ⟨z0, hz0, hHz0, hE⟩, bH, aH, hEigH, Acore, C, ?_⟩
  intro Z Zphys
  refine ⟨n, W, hnD, hWbond, ?_⟩
  intro p hpl hpu z Fraw G Ghat
  obtain ⟨mu, w, hG, _hBpos, _hGH, hw, hGw, hGlow, hmuD, hmuE, _hmuC,
      bG, aG, hEigG, _hforward, _hreverse, hwindows, _hmpo⟩ :=
    hfamily Sbulk p t m hpl hpu ht hm
  change G.IsHermitian at hG
  have hGnorm : ‖G‖ ≤ Msoft :=
    norm_five_region_soft_three_bulk_le (L := N + 1) (q := q)
      (k1 := a + 1) (k2 := a + 2 * ell) (k3 := b + 1) (k4 := b + 2 * ell) (ell := ell)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      h hs h0 h1 e x hx hxe he p t m hpl hpu ht (by omega)
  have hp2upper : p 2 ≤ e 2 :=
    hpu 2 (by exact (by decide : (2 : Fin 5) ∈ ({0, 2, 4} : Finset (Fin 5))))
  obtain ⟨_hz0, _hz1, _hNativeError, hPlacedError⟩ := hZerror (p 2) hp2upper
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
  have hSbulk : (Sbulk.card : ℝ) = 3 := by norm_num [Sbulk]
  have hDbulk : 10 * (Sbulk.card : ℝ) = 30 := by rw [hSbulk]; norm_num
  refine ⟨hG, hGhat, hError, hNorm, ?_, mu, by linarith [hmuD, hDbulk], hmuE, ?_⟩
  · let PL := Fraw 0 - ∑ j, (e j : ℂ) • (1 : Matrix (Fin (N + 1) → Fin q)
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
    have hAlphabet :
        (∑ i, Sum.elim (Sum.elim WL WR) ![PL, Zphys (z : ℂ), Fraw 4] i) = Ghat :=
      actual_three_bulk_replacement_sum (N + 1) a b ell hell hab (by simpa using hb) h
        Fraw (fun j ↦ (e j : ℂ) • 1) (Zphys (z : ℂ)) ((p 2 : ℂ) • 1)
    intro Q hQ
    obtain ⟨M, hMatrix, _hTensor⟩ := hWpoly (z : ℂ) PL (Fraw 4) hPL hPR Q hQ
    refine ⟨M, ?_⟩
    have hEval := congrArg (fun B : Matrix (Fin (N + 1) → Fin q)
        (Fin (N + 1) → Fin q) ℂ ↦ Polynomial.aeval B Q) hAlphabet.symm
    exact hEval.trans hMatrix
  · intro eta T hwin wbuf heta hhwin hwbuf U hUt hUT hTorig rhoH rhoG count
    have hG' (c : ℝ) := Submodule.spectralSpanLE_eq_of_eigenbases
      bG hG.eigenvectorBasis aG hG.eigenvalues hEigG hG.toEuclideanCLM_eigenvectorBasis c
    have h30 : (10 : ℝ) * 3 = 30 := by norm_num
    have hwins := hwindows eta T hwin wbuf heta hhwin hwbuf
    simp only [hSbulk, h30] at hwins
    obtain ⟨h1', h2', h3', h4'⟩ := hwins hUt hUT hTorig
    refine ⟨h1', h2', ?_, ?_⟩
    · rw [← hG']
      exact h3'
    · rw [← hG']
      exact h4'

end TNLean.MPS.AreaLaw.ALVV
