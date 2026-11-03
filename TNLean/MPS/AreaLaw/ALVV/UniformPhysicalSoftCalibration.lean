/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.UniformPhysicalSoftImprovingFamily
import QICLean.Analysis.SoftFamilyCalibration
import QICLean.Analysis.GeometricOrderPolynomialBound

/-!
# Calibrated physical soft families and a uniform polynomial bond

The soft scale and order, filter degree and precision precede the chain length. The same
actual physical soft family retains its derived spectral target and all word
powers; its individual tensor bonds have one natural polynomial bound.

This is a corrected auxiliary to ALVV, arXiv:1602.08828v2,
`prop:Cheby-AGSP-eff` and `t:aisefficient`, lines 1311–1420.
**Scope restriction (parameter dependence):** the construction uses the
corrected residual and cluster estimates in
`docs/paper-gaps/alvv16_soft_regional_residuals.tex` and
`docs/paper-gaps/alvv16_cluster_approximation.tex`. It does not identify the
source's fourth-order choice or assert its running time.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker TensorProduct Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw.ALVV

private theorem sampling_budgets_of_soft_profile {D M Delta : ℝ}
    (hD : 2 ≤ D) (hM : 34 ≤ M)
    (hDelta : Delta ≤ 1 / (D ^ 12 * M ^ 10)) :
    let tau := 1 / (D ^ 24 * M ^ 10)
    3 * tau / 200 ≤ (((3 / 100 : ℝ) / D ^ 2) ^ 2) / 100 ∧
      3 * tau / 200 ≤ 1 / 200 ∧ D ^ 12 * Delta ≤ 1 / 100000 := by
  intro tau
  have hD0 : 0 < D := by linarith only [hD]
  have hM1 : 1 ≤ M := by linarith only [hM]
  have hD20 : (10000 : ℝ) ≤ D ^ 20 :=
    (by norm_num : (10000 : ℝ) ≤ 2 ^ 20).trans
      (pow_le_pow_left₀ (by norm_num) hD 20)
  have hM10 : 1 ≤ M ^ 10 := one_le_pow₀ hM1
  have hDen : 10000 * D ^ 4 ≤ D ^ 24 * M ^ 10 := by
    calc
      10000 * D ^ 4 ≤ D ^ 20 * D ^ 4 :=
        mul_le_mul_of_nonneg_right hD20 (by positivity)
      _ ≤ (D ^ 20 * D ^ 4) * M ^ 10 :=
        le_mul_of_one_le_right (by positivity) hM10
      _ = _ := by ring
  have htau : tau ≤ 1 / (10000 * D ^ 4) :=
    one_div_le_one_div_of_le (by positivity) hDen
  refine ⟨?_, ?_, ?_⟩
  · calc
      3 * tau / 200 ≤ 3 * (1 / (10000 * D ^ 4)) / 200 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htau (by norm_num))
          (by norm_num)
      _ ≤ _ := by
        field_simp [hD0.ne']
        nlinarith only [pow_pos hD0 4]
  · have hD4 : 1 ≤ D ^ 4 := one_le_pow₀ (by linarith only [hD])
    have hDen3 : 3 ≤ D ^ 24 * M ^ 10 :=
      (by linarith only [hD4] : (3 : ℝ) ≤ 10000 * D ^ 4).trans hDen
    have htauSmall : tau ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hDen3
    linarith only [htauSmall]
  · have hM10large : (100000 : ℝ) ≤ M ^ 10 :=
      (by norm_num : (100000 : ℝ) ≤ 34 ^ 10).trans
        (pow_le_pow_left₀ (by norm_num) hM 10)
    calc
      D ^ 12 * Delta ≤ D ^ 12 * (1 / (D ^ 12 * M ^ 10)) :=
        mul_le_mul_of_nonneg_left hDelta (by positivity)
      _ = 1 / M ^ 10 := by field_simp [hD0.ne']
      _ ≤ _ := one_div_le_one_div_of_le (by norm_num) hM10large

/-- The corrected soft residuals, sampling losses and tensor-bond polynomial
can be chosen uniformly before the chain length. -/
private theorem exists_uniform_soft_parameters (q : ℕ) (hq : 2 ≤ q)
    (g : ℝ) (hg : 0 < g) :
    ∃ u : ℕ, 2 ≤ u ∧
      let ell := u ^ 8
      let m := u ^ 10
      let t := 3 * (m : ℝ)
      let k := u ^ 16
      let T := (u : ℝ) ^ 9
      let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
      let M := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
      let tau := 1 / ((D : ℝ) ^ 24 * M ^ 10)
      let xi := min 1 (tau * g ^ 2 / (20000 * (M + g + 8)))
      let Delta := (2 * Real.exp (-2 * (k : ℝ) *
        Real.sqrt ((g / 2) / (M + xi + 4 + g)))) ^ 2
      ∃ Cpoly ppoly : ℕ, 1 ≤ Cpoly ∧
        1 ≤ ell ∧ 2 ≤ m ∧ 1 ≤ k ∧
        156 + 2 * g ≤ t ∧ 156 + 2 * g ≤ T ∧ g / 40 + 24 ≤ T ∧
        2 ≤ D ∧ 34 ≤ M ∧ 0 < tau ∧ tau ≤ 1 ∧ 0 < xi ∧ xi ≤ 1 ∧
        3 * (32 * Real.exp (-(T - g / 40 - 24) / 8) +
          (t / m) * (T / t) ^ m) ≤ tau * g / 1000000 ∧
        3 * (32 * Real.exp (-(T - 156 - 2 * g) / 8) +
          (t / m) * (T / t) ^ m) ≤ tau * g / 1000000 ∧
        Delta ≤ 1 / ((D : ℝ) ^ 12 * M ^ 10) ∧
        3 * tau / 200 ≤ (((3 / 100 : ℝ) / (D : ℝ) ^ 2) ^ 2) / 100 ∧
        3 * tau / 200 ≤ 1 / 200 ∧ (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
        ∀ N : ℕ,
          let base := 2 * (Real.exp (1 / 3 : ℝ) - 1)
          let order := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
            Real.log (Real.log (1 + xi / (t * 2 ^ (m + 1))))) / (-Real.log base)⌉₊
          let B := ((order ^ 2 * q ^ order) * 2) * (m + 1)
          (max 1 B) ^ (2 * k) ≤ Cpoly * (N + 1) ^ ppoly := by
  obtain ⟨u, hu, hcal⟩ := Real.exists_soft_family_calibration q hq g hg 24 10 10
  refine ⟨u, hu, ?_⟩
  intro ell m t k T D M tau xi Delta
  obtain ⟨hell, hm, hk, htfloor, hTfloor, hT0, hD1, hM1, htau, htau1,
    hxi, hxi1, hO, hR, hDelta⟩ := hcal
  have hD2 : 2 ≤ D := by
    have hqk : 1 ≤ q * k := one_le_mul_of_one_le_of_one_le (by omega) hk
    have hpow : 1 ≤ (q * k) ^ (36 * ell + 4 * (k / ell)) := one_le_pow₀ hqk
    have hprod := Nat.mul_le_mul_left (m * k + 1) hpow
    have hmk : 2 ≤ m * k := by simpa using Nat.mul_le_mul hm hk
    dsimp only [D]
    omega
  have ht : 0 < t := by dsimp only [t]; positivity
  have hM34 : 34 ≤ M := by
    have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
    have hpart : 0 ≤ 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) := by positivity
    dsimp only [M]
    linarith only [hpart]
  have hSampling := sampling_budgets_of_soft_profile
    (by exact_mod_cast hD2) hM34 hDelta
  have hbase := softHeat_base_bounds
  obtain ⟨Cpoly, ppoly, hCpoly, hGeom⟩ := Real.exists_geometric_order_polynomial_bound
    (2 * (Real.exp (1 / 3 : ℝ) - 1)) (t * 2 ^ (m + 1)) xi hbase.1 hbase.2
    (by positivity) hxi q (by omega) (m + 1) k
  refine ⟨Cpoly, ppoly, hCpoly, hell, hm, hk, htfloor, hTfloor, hT0,
    hD2, hM34, htau, htau1, hxi, hxi1, hO, hR, hDelta,
    hSampling.1, hSampling.2.1, hSampling.2.2, ?_⟩
  intro N base order B
  have hGeomN := hGeom N
  change (2 * (m + 1) * order ^ 2 * q ^ order) ^ (2 * k) ≤
    Cpoly * (N + 1) ^ ppoly at hGeomN
  have horder : 0 < order := Nat.zero_lt_one.trans_le (le_max_left _ _)
  have hq0 : 0 < q := by omega
  have hBpos : 0 < B := by dsimp only [B]; positivity
  have hBform : B = 2 * (m + 1) * order ^ 2 * q ^ order := by
    dsimp only [B]
    ring
  rw [max_eq_right (show 1 ≤ B from hBpos), hBform]
  exact hGeomN

open Classical in
/-- Fixed local dimension and positive gap determine the soft parameters
and a natural polynomial bond ceiling before the chain length. The physical
certificate is unchanged, with the same actual family, represented matrices,
spectral targets and word powers. Corrected auxiliary to ALVV,
arXiv:1602.08828v2, `prop:Cheby-AGSP-eff` and `t:aisefficient`, lines 1311–1420. -/
theorem exists_calibrated_uniform_physical_soft_improving_family
    (q : ℕ) (hq : 2 ≤ q) (g : ℝ) (hg : 0 < g) :
  (by
    exact (show Prop from
    let Family := fun (ell m k : ℕ) (tau t : ℝ) (N a b : ℕ)
      (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ N)
      (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
      (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
        (h i) (interval (N + 1) i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) ↦
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
                        Submodule.IsViable (Delta ^ r / (1 - delta) ^ 2) grow Tc))
    ∃ u : ℕ, 2 ≤ u ∧
      let ell := u ^ 8
      let m := u ^ 10
      let t := 3 * (m : ℝ)
      let k := u ^ 16
      let T := (u : ℝ) ^ 9
      let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
      let Msoft := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
      let tau := 1 / ((D : ℝ) ^ 24 * Msoft ^ 10)
      let xi := min 1 (tau * g ^ 2 / (20000 * (Msoft + g + 8)))
      let upper := Msoft + xi + 4 + g
      let Delta := (2 * Real.exp (-2 * (k : ℝ) * Real.sqrt ((g / 2) / upper))) ^ 2
      ∃ Cpoly ppoly : ℕ, 1 ≤ Cpoly ∧
        156 + 2 * g ≤ t ∧ 156 + 2 * g ≤ T ∧ g / 40 + 24 ≤ T ∧
        3 * (32 * Real.exp (-(T - g / 40 - 24) / 8) +
          (t / m) * (T / t) ^ m) ≤ tau * g / 1000000 ∧
        3 * (32 * Real.exp (-(T - 156 - 2 * g) / 8) +
          (t / m) * (T / t) ^ m) ≤ tau * g / 1000000 ∧
        2 ≤ D ∧ 34 ≤ Msoft ∧ 0 < tau ∧ tau ≤ 1 ∧ 0 < xi ∧ xi ≤ 1 ∧
        Delta ≤ 1 / ((D : ℝ) ^ 12 * Msoft ^ 10) ∧
        3 * tau / 200 ≤ (((3 / 100 : ℝ) / (D : ℝ) ^ 2) ^ 2) / 100 ∧
        3 * tau / 200 ≤ 1 / 200 ∧ (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
        ∀ N : ℕ,
          let base := 2 * (Real.exp (1 / 3 : ℝ) - 1)
          let order := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
            Real.log (Real.log (1 + xi / (t * 2 ^ (m + 1))))) / (-Real.log base)⌉₊
          let B := ((order ^ 2 * q ^ order) * 2) * (m + 1)
          (max 1 B) ^ (2 * k) ≤ Cpoly * (N + 1) ^ ppoly ∧
          ∀ (a b : ℕ) (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ N)
            (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
            (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
              (h i) (interval (N + 1) i.val (i.val + 2)))
            (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1),
            Family ell m k tau t N a b hab hb h hs h0 h1)) := by
  classical
  intro resultType
  unfold resultType
  intro Family
  have hPhysical (ell m k : ℕ) (tau t T : ℝ)
      (hell : 1 ≤ ell) (hm : 2 ≤ m) (hk : 1 ≤ k)
      (htau : 0 < tau) (htau1 : tau ≤ 1) (hscale : 3 * (m : ℝ) ≤ t)
      (hT0 : g / 40 + 24 ≤ T) (htfloor : 156 + 2 * g ≤ t)
      (hTfloor : 156 + 2 * g ≤ T)
      (hO : 3 * (32 * Real.exp (-(T - g / 40 - 24) / 8) +
        (t / m) * (T / t) ^ m) ≤ tau * g / 1000000)
      (hR : 3 * (32 * Real.exp (-(T - 156 - 2 * g) / 8) +
        (t / m) * (T / t) ^ m) ≤ tau * g / 1000000)
      (N a b : ℕ) (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ N)
      (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
      (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
        (h i) (interval (N + 1) i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
      Family ell m k tau t N a b hab hb h hs h0 h1 := by
    exact exists_uniform_physical_soft_improving_family q ell m k g tau t T T
      hq hell hm hk hg htau htau1 hscale hT0 htfloor hTfloor hO hR
      N a b hab hb h hs h0 h1
  obtain ⟨u, hu, hparams⟩ := exists_uniform_soft_parameters q hq g hg
  refine ⟨u, hu, ?_⟩
  intro ell m t k T D Msoft tau xi upper Delta
  obtain ⟨Cpoly, ppoly, hCpoly, hell, hm, hk, htfloor, hTfloor, hT0,
    hD2, hM34, htau, htau1, hxi, hxi1, hO, hR, hDelta,
    hSampling, hCloseSmall, hDeltaSmall, hPoly⟩ := hparams
  refine ⟨Cpoly, ppoly, hCpoly, htfloor, hTfloor, hT0, hO, hR,
    hD2, hM34, htau, htau1, hxi, hxi1,
    hDelta, hSampling, hCloseSmall, hDeltaSmall, ?_⟩
  intro N base order B
  refine ⟨hPoly N, ?_⟩
  intro a b hab hb h hs h0 h1
  exact hPhysical ell m k tau t T hell hm hk htau htau1 (by rfl)
    hT0 htfloor hTfloor hO hR N a b hab hb h hs h0 h1

end TNLean.MPS.AreaLaw.ALVV
