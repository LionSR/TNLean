/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.LongIntervalSoftImprovingFamily
import QICLean.Entropy.RegionalViability
import QICLean.Analysis.ViableSubspaceSpectralProjector

/-!
# A common physical soft family in the native regional coordinates

The same physical family is retained before all three energy estimates.
Its actual filter and target are expressed in the canonical regional
coordinates, and its single-step image is the literal sum of the native
operator images. Supporting ALVV, arXiv:1602.08828v2, Lemma l:er and
Proposition 5.7, lines 597–622 and 1311–1420.

**Scope restriction (numerical budgets and long intervals):** the public
theorem `exists_uniform_native_long_interval_soft_improving_family` retains
the explicit residual budgets and the parent length condition of
the physical long-interval construction. No printed fourth-order parameter
choice, adaptive success statement or running-time bound is asserted.
The corrected residual and cluster conventions remain those in
`docs/paper-gaps/alvv16_soft_regional_residuals.tex` and
`docs/paper-gaps/alvv16_cluster_approximation.tex`. The closed spectral
convention and unsquared filter are documented at:
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_filter_positivity.pdf
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker TensorProduct Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw.ALVV

/-- The same global filter has its native tensor decomposition and directly
improves the literal sum of regional images. Only the existing equality of
coordinate isometries is used; the target is not changed. Supporting ALVV,
arXiv:1602.08828v2, Lemma l:er, lines 606–622. -/
private theorem native_filter_image {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (J : Finset V) (n : ℕ)
    (W : Fin n → Matrix (J → Fin q) (J → Fin q) ℂ)
    (M : Fin n → Matrix (↥(Jᶜ) → Fin q) (↥(Jᶜ) → Fin q) ℂ)
    (T : Submodule ℂ (EuclideanSpace ℂ (V → Fin q))) (Delta : ℝ) (hDelta : 0 ≤ Delta)
    (Kwhole : EuclideanSpace ℂ (V → Fin q) →L[ℂ] EuclideanSpace ℂ (V → Fin q)) :
    let HM := EuclideanSpace ℂ (J → Fin q)
    let HE := EuclideanSpace ℂ (↥(Jᶜ) → Fin q)
    let Fops := fun i ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) (W i)
    let Rop := fun i ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ↥(Jᶜ) → Fin q) (M i)
    let split := (FiniteProduct.splitEquiv (fun _ : V ↦ Fin q) J).trans (Equiv.prodComm _ _)
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ split
    let Phi := ((EuclideanSpace.basisFun (↥(Jᶜ) → Fin q) ℂ).tensorProduct
      (EuclideanSpace.basisFun (J → Fin q) ℂ)).repr
    let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ HE HM)
    let K0 := Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv Kwhole
    let T0 := T.map Tm.toLinearEquiv.toLinearMap
    (K0 = ∑ i, TensorProduct.mapL (Fops i) (Rop i) ∧
      (∀ v ∈ T0, K0 v ∈ T0) ∧ (∀ v ∈ T0ᗮ, K0 v ∈ T0ᗮ) ∧
      (∀ v ∈ T0, ‖v‖ ≤ ‖K0 v‖) ∧
      (∀ v ∈ T0ᗮ, ‖K0 v‖ ^ 2 ≤ Delta * ‖v‖ ^ 2)) →
    let coords := Entropy.regionTensorCoordinates q J
    let K := coords.toContinuousLinearEquiv.conjContinuousAlgEquiv Kwhole
    let Tc := T.map coords.toLinearEquiv.toLinearMap
    K = ∑ i, TensorProduct.mapL (Fops i) (Rop i) ∧
      (∀ v ∈ Tc, K v ∈ Tc) ∧ (∀ v ∈ Tcᗮ, K v ∈ Tcᗮ) ∧
      (∀ v ∈ Tc, ‖v‖ ≤ ‖K v‖) ∧
      (∀ v ∈ Tcᗮ, ‖K v‖ ^ 2 ≤ Delta * ‖v‖ ^ 2) ∧
      ∀ (S : Submodule ℂ HM) (delta : ℝ),
        Submodule.IsViable delta S Tc → delta < 1 →
        let image := ⨆ i : Fin n, S.map (Fops i : HM →ₗ[ℂ] HM)
        Module.finrank ℂ image ≤ n * Module.finrank ℂ S ∧
          Submodule.IsViable (Delta / (1 - delta) ^ 2) image Tc := by
  intro HM HE Fops Rop split U Phi Tm K0 T0 hOld coords K Tc
  let Bounds := fun C : EuclideanSpace ℂ (V → Fin q) ≃ₗᵢ[ℂ] HM ⊗[ℂ] HE ↦
    let A := C.toContinuousLinearEquiv.conjContinuousAlgEquiv Kwhole
    let G := T.map C.toLinearEquiv.toLinearMap
    A = ∑ i, TensorProduct.mapL (Fops i) (Rop i) ∧
      (∀ v ∈ G, A v ∈ G) ∧ (∀ v ∈ Gᗮ, A v ∈ Gᗮ) ∧
      (∀ v ∈ G, ‖v‖ ≤ ‖A v‖) ∧
      (∀ v ∈ Gᗮ, ‖A v‖ ^ 2 ≤ Delta * ‖v‖ ^ 2)
  have hcoords : Tm = coords :=
    (Entropy.regionTensorCoordinates_eq_exteriorFirst q J).symm
  have hNative : Bounds coords := Eq.mp (congrArg Bounds hcoords) hOld
  obtain ⟨hdec, hKT, hKTo, hlow, hhigh⟩ := hNative
  refine ⟨hdec, hKT, hKTo, hlow, hhigh, ?_⟩
  intro S delta hS hdelta image
  simpa only [Fintype.card_fin] using
    hS.map_of_tensor_decomposition Fops Rop hdec hdelta hDelta hKT hKTo hlow hhigh

open Classical in
/-- One actual enlarged physical family precedes all bulk-center estimates.
Its same global filter has a tensor decomposition in the exact native
regional coordinates and improves the literal sum of regional images.
The original attained minima, approximant and own target are retained.
Supporting ALVV, arXiv:1602.08828v2, Lemma l:er and Proposition 5.7,
lines 606–622 and 1311–1420. -/
theorem exists_uniform_native_long_interval_soft_improving_family
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
    let Hfull := EuclideanSpace ℂ (Fin (N + 1) → Fin q)
    let split := (FiniteProduct.splitEquiv (fun _ : Fin (N + 1) ↦ Fin q) J).trans
      (Equiv.prodComm _ _)
    let coords := Entropy.regionTensorCoordinates q J
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
              let Tc := target.map coords.toLinearEquiv.toLinearMap
              E + ∑ j, e j = mu0 ∧
              target = Submodule.spectralSpanLE hGhat.eigenvectorBasis hGhat.eigenvalues
                (E + 3 * g / 4) ∧
              Module.finrank ℂ target = Module.finrank ℂ original ∧
              Submodule.IsCloseTo (3 * tau / 200) target original ∧
              Submodule.IsCloseTo (3 * tau / 200) original target ∧
              ∃ (Kwhole : Hfull →L[ℂ] Hfull) (M : Fin n → Matrix extConfig extConfig ℂ),
                let K := coords.toContinuousLinearEquiv.conjContinuousAlgEquiv Kwhole
                let Rop := fun i ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := extConfig) (M i)
                (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (N + 1) → Fin q)).symm Kwhole =
                  (∑ i, M i ⊗ₖ W i).submatrix split split ∧
                K = ∑ i, TensorProduct.mapL (Fops i) (Rop i) ∧
                (∀ v ∈ Tc, K v ∈ Tc) ∧ (∀ v ∈ Tcᗮ, K v ∈ Tcᗮ) ∧
                (∀ v ∈ Tc, ‖v‖ ≤ ‖K v‖) ∧
                (∀ v ∈ Tcᗮ, ‖K v‖ ^ 2 ≤ Delta * ‖v‖ ^ 2) ∧
                ∀ (S : Submodule ℂ HM) (delta : ℝ),
                  Submodule.IsViable delta S Tc → delta < 1 →
                  let image := ⨆ i : Fin n, S.map (Fops i : HM →ₗ[ℂ] HM)
                  Module.finrank ℂ image ≤ n * Module.finrank ℂ S ∧
                    Submodule.IsViable (Delta / (1 - delta) ^ 2) image Tc := by
  obtain ⟨a, b, hab, hb, hpc, hdr, hcard, hleft, hright, hFamily⟩ :=
    exists_uniform_long_interval_soft_improving_family q ell m k g tau t T0 T1
      hq hell hm hk hg htau htau1 hscale hT0 htfloor hT1 hO hR
      N p r hpr hrN hlong h hs h0 h1
  refine ⟨a, b, hab, hb, hpc, hdr, hcard, hleft, hright, ?_⟩
  intro Msoft xi upper D Delta Sbulk cuts A Y J eJ midConfig extConfig HM Hfull
    split coords order bond Hraw hRaw
  obtain ⟨e, x, E, hx, hxe, he, hE0, hE4, n, W, hn, hW, hCenter⟩ := hFamily
  refine ⟨e, x, E, hx, hxe, he, hE0, hE4, n, W, ?_⟩
  intro Fops
  refine ⟨hn, hW, ?_⟩
  intro pc hp0 hp1 Fraw G
  let point := hCenter pc hp0 hp1
  let Ghat := Classical.choose point
  let matrixCertificate := Classical.choose_spec point
  let hGhat := Classical.choose matrixCertificate
  have matrixBounds := Classical.choose_spec matrixCertificate
  refine ⟨Ghat, hGhat, matrixBounds.1, matrixBounds.2.1, ?_⟩
  intro mu0 hmu0 hgap original target Tc
  have spectral := matrixBounds.2.2 mu0 hmu0 hgap
  refine ⟨spectral.1, spectral.2.1, spectral.2.2.1, spectral.2.2.2.1,
    spectral.2.2.2.2.1, ?_⟩
  refine (spectral.2.2.2.2.2).imp ?_
  intro Kwhole hExterior
  refine hExterior.imp ?_
  intro M packet K Rop
  refine ⟨packet.1, ?_⟩
  unfold K Rop Fops Tc target coords HM midConfig extConfig J Delta upper xi Msoft
  have oldBounds := And.intro packet.2.1 (And.intro packet.2.2.1
    (And.intro packet.2.2.2.1 (And.intro packet.2.2.2.2.1 packet.2.2.2.2.2.1)))
  exact native_filter_image q (interval (N + 1) p r) n W M target Delta
    (sq_nonneg _) Kwhole oldBounds

end TNLean.MPS.AreaLaw.ALVV
