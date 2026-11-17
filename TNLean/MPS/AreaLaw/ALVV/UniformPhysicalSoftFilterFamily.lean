/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.UniformPhysicalSoftImprovingFamily

/-!
# A physical soft filter family without native tensor witnesses

The original physical construction is used once. Its native tensors and
closing matrices remain private witnesses, while its actual approximant,
own spectral target and filter are retained. This auxiliary supports ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1311–1420.

**Scope restriction (numerical budgets and geometry):** this auxiliary retains
explicit scalar residual budgets and the natural two-window geometry. It
asserts neither the printed fourth-order choice nor an adaptive algorithm or
running-time bound. The corrected cluster and residual conventions remain
those in `docs/paper-gaps/alvv16_cluster_approximation.tex` and
`docs/paper-gaps/alvv16_soft_regional_residuals.tex`. The closed spectral
convention and the unsquared filter are documented at:
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_filter_positivity.pdf
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker TensorProduct Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- The same natural physical family, with the native tensor witnesses
hidden and the represented Hermitian approximant retained explicitly.
The original factory is used once. Auxiliary to ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1311–1420. -/
theorem exists_uniform_physical_soft_filter_family
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
    let Msoft := 3 * t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 34
    let xi := min 1 (tau * g ^ 2 / (20000 * (Msoft + g + 8)))
    let upper := Msoft + xi + 4 + g
    let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
    let Delta := (2 * Real.exp (-2 * (k : ℝ) * Real.sqrt ((g / 2) / upper))) ^ 2
    let Sbulk : Finset (Fin 5) := {0, 2, 4}
    let cuts : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, N + 1]
    let A := fun j : Fin 5 ↦ ∑ i ∈ Finset.univ.filter
      (fun i : Fin N ↦ cuts j.castSucc ≤ i.val ∧ i.val + 1 < cuts j.succ), h i
    let Y := ∑ i ∈ Finset.univ.filter (fun i : Fin N ↦ i.val + 1 ∈
      ({a + 1, a + 2 * ell, b + 1, b + 2 * ell} : Finset ℕ)), h i
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
    let split := (FiniteProduct.splitEquiv beta J).trans
      (Equiv.prodComm _ _)
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ split
    let Phi := ((EuclideanSpace.basisFun extConfig ℂ).tensorProduct
      (EuclideanSpace.basisFun midConfig ℂ)).repr
    let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ HE HM)
    let order := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + xi / (t * (2 : ℝ) ^ (m + 1)))))/
        (-Real.log (2 * (Real.exp (1 / 3 : ℝ) - 1)))⌉₊
    let bond := ((order ^ 2 * q ^ order) * 2) * (m + 1)
    let Hraw := ∑ i, h i
    let hRaw : Hraw.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    ∃ (e : Fin 5 → ℝ) (x : (Fin (N + 1) → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧ 0 ≤ E ∧ E ≤ 4 ∧
      ∃ (n : ℕ) (W : Fin n → Matrix midConfig midConfig ℂ),
        let Fops : Fin n → HM →L[ℂ] HM := fun i ↦
          Matrix.toEuclideanCLM (𝕜 := ℂ) (n := midConfig) (W i)
        n ≤ D ∧
        (∀ i, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
          ((max 1 bond) ^ (2 * k))
          (fun w ↦ W i
            (fun v ↦ (finProdFinEquiv.symm (w (eJ.symm v))).1)
            (fun v ↦ (finProdFinEquiv.symm (w (eJ.symm v))).2))) ∧
        ∀ (pc : Fin 5 → ℝ)
          (hp0 : ∀ j : Fin 5, j ∈ Sbulk → e j - 10 ≤ pc j)
          (hp1 : ∀ j : Fin 5, j ∈ Sbulk → pc j ≤ e j),
          let Fraw := fun j : Fin 5 ↦ (pc j : ℂ) • 1 +
            cfc (Real.softTruncation t m) (A j - (pc j : ℂ) • 1)
          let G := (∑ j, ((if j ∈ Sbulk then Fraw j else A j) - (e j : ℂ) • 1)) + Y
          ∃ (Ghat : Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
            (hGhat : Ghat.IsHermitian),
            ‖G - Ghat‖ ≤ xi ∧ ‖Ghat‖ ≤ Msoft + xi ∧
            ∀ mu0 : ℝ, mu0 ∈ spectrum ℝ Hraw →
              (∀ y ∈ spectrum ℝ Hraw, y = mu0 ∨ mu0 + g ≤ y) →
              let original := Submodule.spectralSpanLE hRaw.eigenvectorBasis hRaw.eigenvalues mu0
              let target := Submodule.spectralSpanLE hGhat.eigenvectorBasis hGhat.eigenvalues
                (E + g / 4)
              let Tc := target.map Tm.toLinearEquiv.toLinearMap
              E + ∑ j, e j = mu0 ∧
              target = Submodule.spectralSpanLE hGhat.eigenvectorBasis hGhat.eigenvalues
                (E + 3 * g / 4) ∧
              Module.finrank ℂ target = Module.finrank ℂ original ∧
              Submodule.IsCloseTo (3 * tau / 200) target original ∧
              Submodule.IsCloseTo (3 * tau / 200) original target ∧
              ∃ (K : HM ⊗[ℂ] HE →L[ℂ] HM ⊗[ℂ] HE)
                (Rop : Fin n → HE →L[ℂ] HE),
                K = ∑ i, TensorProduct.mapL (Fops i) (Rop i) ∧
                (∀ v ∈ Tc, K v ∈ Tc) ∧ (∀ v ∈ Tcᗮ, K v ∈ Tcᗮ) ∧
                (∀ v ∈ Tc, ‖v‖ ≤ ‖K v‖) ∧
                (∀ v ∈ Tcᗮ, ‖K v‖ ^ 2 ≤ Delta * ‖v‖ ^ 2) ∧
                ∀ (power : ℕ) (S : Submodule ℂ HM) (delta : ℝ),
                  Submodule.IsViable delta S Tc → delta < 1 →
                  let grow := ⨆ w : Fin power → Fin n,
                    S.map ((List.ofFn (fun j ↦ Fops (w j))).prod : _ →ₗ[ℂ] _)
                  Module.finrank ℂ grow ≤ D ^ power * Module.finrank ℂ S ∧
                    Submodule.IsViable (Delta ^ power / (1 - delta) ^ 2) grow Tc := by
  classical
  intro Msoft xi upper D Delta Sbulk cuts A Y J eJ
    beta midConfig extConfig HM HE split U Phi Tm order bond Hraw hRaw
  obtain ⟨e, x, E, hx, hxe, he, hE0, hE4, Acore, C, n0, W0, hn0, hW0, hcenter0⟩ :=
    exists_uniform_physical_soft_improving_family q ell m k g tau t T0 T1
      hq hell hm hk hg htau htau1 hscale hT0 htfloor hT1 hO hR
      N a b hab hb h hs h0 h1
  refine ⟨e, x, E, hx, hxe, he, hE0, hE4, n0, W0, ?_⟩
  intro Fops
  refine ⟨hn0, hW0, ?_⟩
  intro pc hp0 hp1 Fraw G
  obtain ⟨hGhat, _hMiddleError, hError, hNorm, hOwn0⟩ := hcenter0 pc hp0 hp1
  refine ⟨_, hGhat, hError, hNorm, ?_⟩
  intro mu0 hmu0 hgap original target Tc
  obtain ⟨hshift, hclosed, hdim, hTO, hOT, K0, Rop0,
    hdec0, hKT0, hKTo0, hlow0, hhigh0, hwords0⟩ := hOwn0 mu0 hmu0 hgap
  refine ⟨hshift, ?_⟩
  refine ⟨hclosed, ?_⟩
  refine ⟨hdim, ?_⟩
  refine ⟨hTO, ?_⟩
  refine ⟨hOT, ?_⟩
  refine ⟨K0, Rop0, ?_⟩
  refine ⟨?_, ?_⟩
  · unfold Fops HM HE midConfig extConfig beta J
    exact hdec0
  unfold Fops Tc target Tm Phi U split HM HE midConfig extConfig beta J
    Delta upper xi Msoft D
  exact ⟨hKT0, hKTo0, hlow0, hhigh0, hwords0⟩

end TNLean.MPS.AreaLaw.ALVV
