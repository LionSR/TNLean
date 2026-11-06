/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.UniformPhysicalSoftFilterFamily
import TNLean.MPS.AreaLaw.CommonCollarFilterFamily
import TNLean.MPS.AreaLaw.PrecenterCollarCount
import QICLean.Analysis.MatrixTensorDecomposition

/-!
# One pre-center soft improving family on every long parent interval

The original native construction is used once on the inward core. Its
same matrix family is enlarged once before every estimated center.
The same global filter is then represented on the parent interval;
no viability assertion is transported between different tensor splits.
This is an explicit-budget auxiliary for ALVV, arXiv:1602.08828v2,
Proposition 5.7 and the efficient family, lines 1311–1420.

**Scope restriction (numerical budgets and long intervals):** the statement
retains explicit scalar residual budgets and assumes the prescribed parent
interval has length greater than four window widths. It asserts neither the
printed fourth-order parameter choice nor an adaptive algorithm or running
time. The corrected cluster and residual conventions remain those in
`docs/paper-gaps/alvv16_cluster_approximation.tex` and
`docs/paper-gaps/alvv16_soft_regional_residuals.tex`. The closed spectral
convention and unsquared filter remain those of the natural construction:
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_filter_positivity.pdf
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker TensorProduct Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace TNLean.MPS.AreaLaw.ALVV

/-- Unpack one proved old-filter existence in abstract finite spaces,
pull back that same filter, and retain an opaque final conclusion. The
actual collar conclusion is supplied by the previously proved family
transport; no second filter is chosen. -/
private theorem transport_existing_filter
    {Z X Y ι : Type*} [Fintype Z] [Fintype X] [Fintype Y] [Fintype ι]
    [DecidableEq Z] [DecidableEq Y]
    (split0 : Z ≃ X × Y) (W0 : ι → Matrix Y Y ℂ)
    (T : Submodule ℂ (EuclideanSpace ℂ Z)) (Delta : ℝ)
    (P : (EuclideanSpace ℂ Z →L[ℂ] EuclideanSpace ℂ Z) → Prop)
    (finish : ∀ Kwhole : EuclideanSpace ℂ Z →L[ℂ] EuclideanSpace ℂ Z,
      (∃ M0 : ι → Matrix X X ℂ,
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Z)).symm Kwhole =
          (∑ i, M0 i ⊗ₖ W0 i).submatrix split0 split0) →
      (∀ v ∈ T, Kwhole v ∈ T) → (∀ v ∈ Tᗮ, Kwhole v ∈ Tᗮ) →
      (∀ v ∈ T, ‖v‖ ≤ ‖Kwhole v‖) →
      (∀ v ∈ Tᗮ, ‖Kwhole v‖ ^ 2 ≤ Delta * ‖v‖ ^ 2) → P Kwhole) :
    let U0 := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ split0
    let Phi0 := ((EuclideanSpace.basisFun X ℂ).tensorProduct
      (EuclideanSpace.basisFun Y ℂ)).repr
    let Tm0 := (U0.trans Phi0.symm).trans (TensorProduct.commIsometry ℂ
      (EuclideanSpace ℂ X) (EuclideanSpace ℂ Y))
    let T0 := T.map Tm0.toLinearEquiv.toLinearMap
    (∃ (K0 : EuclideanSpace ℂ Y ⊗[ℂ] EuclideanSpace ℂ X →L[ℂ]
        EuclideanSpace ℂ Y ⊗[ℂ] EuclideanSpace ℂ X)
      (Rop0 : ι → EuclideanSpace ℂ X →L[ℂ] EuclideanSpace ℂ X),
      K0 = ∑ i, TensorProduct.mapL
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Y) (W0 i)) (Rop0 i) ∧
      (∀ v ∈ T0, K0 v ∈ T0) ∧ (∀ v ∈ T0ᗮ, K0 v ∈ T0ᗮ) ∧
      (∀ v ∈ T0, ‖v‖ ≤ ‖K0 v‖) ∧
      (∀ v ∈ T0ᗮ, ‖K0 v‖ ^ 2 ≤ Delta * ‖v‖ ^ 2)) →
      ∃ Kwhole, P Kwhole := by
  let : DecidableEq X := Classical.decEq X
  intro U0 Phi0 Tm0 T0 hOld
  obtain ⟨K0, Rop0, hdec, hKT, hKTo, hlow, hhigh⟩ := hOld
  let Kwhole := Tm0.symm.toContinuousLinearEquiv.conjContinuousAlgEquiv K0
  obtain ⟨hmatrix, hKT', hKTo', hlow', hhigh'⟩ :=
    Matrix.global_filter_of_middleFirst_tensor_decomposition split0 W0 K0 Rop0 T Delta
      hdec hKT hKTo hlow hhigh
  exact ⟨Kwhole, finish Kwhole ⟨_, hmatrix⟩ hKT' hKTo' hlow' hhigh'⟩

open Classical in
/-- The same explicit-budget soft approximation and filter give one
family on a prescribed long parent interval, before every estimated
center. The input nearest-neighbour chain determines all minima, native
cores, targets and decompositions. Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1311–1420; this is not a
short-interval construction, sharp gap-rate or running-time assertion. -/
theorem exists_uniform_long_interval_soft_improving_family
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
    (N p r : ℕ) (hpr : p ≤ r) (hrN : r ≤ N + 1) (hlong : 4 * ell < r - p)
      (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
      (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
        (h i) (interval (N + 1) i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    ∃ (a b : ℕ) (_hab : a + 2 * ell ≤ b) (_hb : b + 2 * ell ≤ N),
      p ≤ a + ell ∧ b + ell + 1 ≤ r ∧
      (interval (N + 1) p r \ interval (N + 1) (a + ell) (b + ell + 1)).card ≤ 2 * ell ∧
      a + 2 * ell - p ≤ 2 * ell ∧ r - (b + 1) ≤ 2 * ell ∧
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
    let J := interval (N + 1) p r
    let eJ := intervalShiftOrderIso hpr hrN
    let midConfig := J → Fin q
    let extConfig := ↥(Jᶜ) → Fin q
    let HM := EuclideanSpace ℂ midConfig
    let HE := EuclideanSpace ℂ extConfig
    let Hfull := EuclideanSpace ℂ (Fin (N + 1) → Fin q)
    let split := (FiniteProduct.splitEquiv (fun _ : Fin (N + 1) ↦ Fin q) J).trans
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
        let Fops := fun i ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := midConfig) (W i)
        n ≤ D ^ 2 ∧
        (∀ i, IsOpenMPS (r - p) (q * q) (max 1 ((max 1 bond) ^ (2 * k)))
          (fun w ↦ W i
            (fun v ↦ (finProdFinEquiv.symm (w (eJ.symm v))).1)
            (fun v ↦ (finProdFinEquiv.symm (w (eJ.symm v))).2))) ∧
        ∀ (pc : Fin 5 → ℝ)
          (_hp0 : ∀ j : Fin 5, j ∈ Sbulk → e j - 10 ≤ pc j)
          (_hp1 : ∀ j : Fin 5, j ∈ Sbulk → pc j ≤ e j),
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
              ∃ (Kwhole : Hfull →L[ℂ] Hfull) (M : Fin n → Matrix extConfig extConfig ℂ),
                let K := Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv Kwhole
                let Rop := fun i ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := extConfig) (M i)
                (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (N + 1) → Fin q)).symm Kwhole =
                  (∑ i, M i ⊗ₖ W i).submatrix split split ∧
                K = ∑ i, TensorProduct.mapL (Fops i) (Rop i) ∧
                (∀ v ∈ Tc, K v ∈ Tc) ∧ (∀ v ∈ Tcᗮ, K v ∈ Tcᗮ) ∧
                (∀ v ∈ Tc, ‖v‖ ≤ ‖K v‖) ∧
                (∀ v ∈ Tcᗮ, ‖K v‖ ^ 2 ≤ Delta * ‖v‖ ^ 2) ∧
                ∀ (power : ℕ) (S : Submodule ℂ HM) (delta : ℝ),
                  Submodule.IsViable delta S Tc → delta < 1 →
                  let grow := ⨆ w : Fin power → Fin n,
                    S.map ((List.ofFn (fun j ↦ Fops (w j))).prod : _ →ₗ[ℂ] _)
                  Module.finrank ℂ grow ≤ n ^ power * Module.finrank ℂ S ∧
                    Submodule.IsViable (Delta ^ power / (1 - delta) ^ 2) grow Tc := by
  classical
  let a := max p ell - ell
  let b := min r (N + 1 - ell) - ell - 1
  obtain ⟨haEnd, hbEnd, hab, hb0, hpc0, _horder, hrd0, _hlen,
    hleft, hright, _htotal, _hsub, hcard⟩ :=
    inward_effective_cuts (N + 1) ell p r hell hpr hrN hlong
  have hb : b + 2 * ell ≤ N := by
    simpa only [Nat.add_sub_cancel] using hb0
  have hpc : p ≤ a + ell := hpc0.trans_eq haEnd.symm
  have hdr : b + ell + 1 ≤ r := hbEnd.trans_le hrd0
  have hleftMid : a + 2 * ell - p ≤ 2 * ell := by omega
  have hrightMid : r - (b + 1) ≤ 2 * ell := by omega
  refine ⟨a, b, hab, hb, hpc, hdr, hcard, hleftMid, hrightMid, ?_⟩
  intro Msoft xi upper D Delta Sbulk cuts A Y J eJ midConfig extConfig HM HE Hfull
    split U Phi Tm order bond Hraw hRaw
  obtain ⟨e, x, E, hx, hxe, he, hE0, hE4, n0, W0, hn0, hW0, hcenter0⟩ :=
    exists_uniform_physical_soft_filter_family q ell m k g tau t T0 T1
      hq hell hm hk hg htau htau1 hscale hT0 htfloor hT1 hO hR
      N a b hab hb h hs h0 h1
  have hq0 : 0 < q := by omega
  have hq1 : 1 ≤ q := by omega
  have hcd0 : a + ell ≤ b + ell + 1 := by omega
  obtain ⟨n, W, hn, hW, hFilter⟩ := exists_common_collar_filter_family
    (L := N + 1) (q := q) (c := a + ell) (d := b + ell + 1)
    (p := p) (r := r) (n0 := n0) (B := (max 1 bond) ^ (2 * k))
    hq0 hpc hcd0 hdr hrN W0 hW0
  have hnD : n ≤ D ^ 2 := by
    rw [hn]
    exact common_collar_count_le_precenter_square q m k ell n0 _
      hq1 hk (hcard.trans (Nat.mul_le_mul_right ell (by decide : 2 ≤ 4))) hn0
  refine ⟨e, x, E, hx, hxe, he, hE0, hE4, n, W, ?_⟩
  intro Fops
  refine ⟨hnD, hW, ?_⟩
  intro pc hp0 hp1 Fraw G
  let point := hcenter0 pc hp0 hp1
  let Ghat := Classical.choose point
  let matrixCertificate := Classical.choose_spec point
  let hGhat := Classical.choose matrixCertificate
  have matrixBounds := Classical.choose_spec matrixCertificate
  have hError := matrixBounds.1
  have hNorm := matrixBounds.2.1
  have hOwn0 := matrixBounds.2.2
  refine ⟨Ghat, hGhat, hError, hNorm, ?_⟩
  intro mu0 hmu0 hgap original target Tc
  have spectral := hOwn0 mu0 hmu0 hgap
  have hshift := spectral.1
  have hclosed := spectral.2.1
  have hdim := spectral.2.2.1
  have hTO := spectral.2.2.2.1
  have hOT := spectral.2.2.2.2.1
  refine ⟨hshift, hclosed, hdim, hTO, hOT, ?_⟩
  let split0 := (FiniteProduct.splitEquiv (fun _ : Fin (N + 1) ↦ Fin q)
    (interval (N + 1) (a + ell) (b + ell + 1))).trans
    (Equiv.prodComm _ _)
  unfold Fops Tc target Tm Phi U split Hfull HM HE midConfig extConfig J
    Delta upper xi Msoft
  have oldFilter := spectral.2.2.2.2.2
  have oldBounds := oldFilter.imp (fun _ h ↦ h.imp (fun _ b ↦
    And.intro b.1 (And.intro b.2.1 (And.intro b.2.2.1
      (And.intro b.2.2.2.1 b.2.2.2.2.1)))))
  refine transport_existing_filter split0 W0 target Delta _ ?_ oldBounds
  intro Kwhole hmatrix hKT hKTo hlow hhigh
  exact hFilter target Delta Kwhole (sq_nonneg _) hmatrix hKT hKTo hlow hhigh

end TNLean.MPS.AreaLaw.ALVV
