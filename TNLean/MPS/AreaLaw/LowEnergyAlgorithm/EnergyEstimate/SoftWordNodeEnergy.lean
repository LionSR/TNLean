/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.EnergyEstimate.SoftWordEnergyEstimate
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.EnergyEstimate.RegionalCentralEnergyEstimate
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.DegenerateGround.PhysicalDGInterleavedTree

/-!
# One-sided energy updates on the same word family

Two child estimates of width 49/16 determine a parent estimate of width
57/8. Exact collar minima then determine an admissible middle center. The
actual compressed minimum of the specified family's one-word child image,
minus three, again has width 49/16. The spaces and operator family remain
fixed throughout the choice of energy estimates.

This is a corrected auxiliary to ALVV, arXiv:1602.08828v2, Figure
`fig:algo1`, line 1631, and its energy argument at line 1807.
**Local fix (one-sided energy update):** The raw compressed eigenvalue is
biased downward by three, and the middle center is obtained using attained
collar minima. The family certificate comes from the hard-clipped
construction, not an identification with literal soft Generate. See
`docs/paper-gaps/alvv16_soft_regional_energy_centering.tex`.
No efficient computation of these choices is asserted.

## Energy updates on the actual interleaved interval tree

The calibrated construction selects its targets, operator families and retained
spaces once. Each long node then admits the corrected one-sided energy update
on its own literal one-word child image. No second operator family or space
tree is selected for the energy calculation.

This is an auxiliary to ALVV, arXiv:1602.08828v2, Figure `fig:algo1`,
line 1631, and its energy argument at line 1807.
**Local fix (same-family one-sided update):** This construction uses the
calibrated hard-clipped family and the corrected raw compressed minimum minus
three. It does not identify that family with literal soft Generate or assert
a running-time bound. See
`docs/paper-gaps/alvv16_soft_regional_energy_centering.tex`.

## A middle soft center from actual child energy estimates

The attained parent and middle minima are retained from the regional soft
construction. Actual collar minima are chosen before the child estimates.
The two child errors of width 49/16 yield a parent-sum error of width 57/8;
subtracting the collar minima and two gives a middle estimate of width ten.
This construction is independent of the family, target and terminal image.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, line 1631,
and the energy-estimation argument at line 1807.
-/

section

open ManyBody (interval)

open Matrix
open scoped BigOperators TensorProduct InnerProductSpace ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

/-- A lower energy estimate with an explicit error width for the actual
original regional Hamiltonian. The minimum is certified by an attained unit
eigenvector and a positive spectral shift. Auxiliary to ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, line 1631. -/
def IsRegionalLowerEnergyEstimate {L q : ℕ}
    (Φ : ManyBody.BondInteraction L q)
    (l r : ℕ) (width p : ℝ) : Prop :=
  let A := ManyBody.BondInteraction.threeRegionHamiltonians l r Φ 1
  ∃ (e : ℝ) (x : (Fin L → Fin q) → ℂ),
    star x ⬝ᵥ x = 1 ∧ A *ᵥ x = (e : ℂ) • x ∧
    (A - (e : ℂ) • 1).PosSemidef ∧ e - width ≤ p ∧ p ≤ e

/-- The energy update is the actual last eigenvalue of the raw soft matrix
compressed to the specified family's literal one-word child image, minus
three. The raw native matrix is a fixed-complement principal slice, before
its minimum is known. Auxiliary to ALVV, arXiv:1602.08828v2, Figure
`fig:algo1`, line 1631; the downward bias is a corrected one-sided update. -/
def IsSoftWordEnergyUpdate {L q N l k u v r : ℕ} (hq : 0 < q)
    (hlk : l ≤ k) (hkr : k ≤ r)
    (Φ : ManyBody.BondInteraction L q)
    (F : Fin N → EuclideanSpace ℂ (interval L l r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L l r → Fin q))
    (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L l k → Fin q)))
    (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q)))
    (center p : ℝ) : Prop :=
  let J := interval L l r
  let P := ManyBody.BondInteraction.threeRegionHamiltonians l r Φ 1
  let M := ManyBody.BondInteraction.threeRegionHamiltonians u v Φ 1
  let R := P - M + (center : ℂ) • 1 +
    cfc (Real.softTruncation 768 12) (M - (center : ℂ) • 1)
  let sigma0 : Fin L → Fin q := fun _ ↦ ⟨0, hq⟩
  let y0 := ((ManyBody.cutEquiv (fun _ ↦ Fin q) J) sigma0).2
  let native := fun x : J → Fin q ↦
    (ManyBody.cutEquiv (fun _ ↦ Fin q) J).symm (x, y0)
  let Kraw := R.submatrix native native
  let W : Submodule ℂ (EuclideanSpace ℂ (J → Fin q)) :=
    adjacentIntervalMerge L q l k r hlk hkr S1 S2
  let V : Submodule ℂ (EuclideanSpace ℂ (J → Fin q)) := ⨆ word : Fin 1 → Fin N,
    W.map ((List.ofFn (fun j ↦ F (word j))).prod : _ →ₗ[ℂ] _)
  Kraw.IsHermitian ∧ ∃ (n : ℕ) (b : OrthonormalBasis (Fin (n + 1)) ℂ V)
    (energy : Fin (n + 1) → ℝ),
    Module.finrank ℂ V = n + 1 ∧
    (∀ j, V.orthogonalCompression
      (toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) Kraw).toLinearMap
        (b j) = (energy j : ℂ) • b j) ∧
    Antitone energy ∧ p = energy (Fin.last n) - 3

/-- A node update uses actual attained collar minima to convert the sum of
its child estimates into the soft middle center. Every returned parent
estimate is the raw compressed minimum on the same word image, biased by
three. Corrected auxiliary to ALVV, arXiv:1602.08828v2, Figure
`fig:algo1`, line 1631. -/
def HasSoftWordNodeEnergyUpdate {L q N l k u v r : ℕ} (hq : 0 < q)
    (hlk : l ≤ k) (hkr : k ≤ r)
    (Φ : ManyBody.BondInteraction L q)
    (F : Fin N → EuclideanSpace ℂ (interval L l r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L l r → Fin q))
    (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L l k → Fin q)))
    (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q))) : Prop :=
∃ (eLeft eRight : ℝ) (xLeft xRight : (Fin L → Fin q) → ℂ),
        star xLeft ⬝ᵥ xLeft = 1 ∧
        ManyBody.BondInteraction.threeRegionHamiltonians l u Φ 1 *ᵥ xLeft = (eLeft : ℂ) • xLeft ∧
        (ManyBody.BondInteraction.threeRegionHamiltonians l u Φ 1 - (eLeft : ℂ) • 1).PosSemidef ∧
        star xRight ⬝ᵥ xRight = 1 ∧
        ManyBody.BondInteraction.threeRegionHamiltonians v r Φ 1 *ᵥ xRight = (eRight : ℂ) • xRight ∧
        (ManyBody.BondInteraction.threeRegionHamiltonians v r Φ 1 - (eRight : ℂ) • 1).PosSemidef ∧
        ∀ p1 p2 : ℝ,
          IsRegionalLowerEnergyEstimate Φ l k (49 / 16) p1 →
          IsRegionalLowerEnergyEstimate Φ k r (49 / 16) p2 →
          IsRegionalLowerEnergyEstimate Φ u v 10
            (p1 + p2 - eLeft - eRight - 2) ∧
          ∃ p : ℝ, IsRegionalLowerEnergyEstimate Φ l r (49 / 16) p ∧
            IsSoftWordEnergyUpdate (u := u) (v := v) hq hlk hkr Φ F S1 S2
              (p1 + p2 - eLeft - eRight - 2) p

/-- Fixed spaces and their own word-family certificate yield a one-sided
node energy update. Child errors of width 49/16 give a parent-sum error at
most 57/8, hence a valid middle center after subtracting the two actual collar
minima and two. The returned update is the actual raw compressed minimum
minus three, not an independently chosen minimum or family. Corrected
auxiliary to ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, line 1631,
and the energy estimate at line 1807. -/
theorem exists_soft_word_node_energy_update
    {L q l u v r ell D s N : ℕ}
    (hq : 0 < q) (hlu : l ≤ u) (huv : u ≤ v) (hvr : v ≤ r) (hrL : r ≤ L)
    (hleft : u - l ≤ 2 * ell) (hright : r - v ≤ 2 * ell)
    (hell : 21 ≤ ell) (hD : 2 ≤ D) (hcount : 50 * ell ^ 2 ≤ D) (hsample : 1 ≤ s)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (F : Fin N → EuclideanSpace ℂ (interval L l r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L l r → Fin q)) :
    let _ : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
    let H := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH)
    let J := interval L l r
    let coords := Entropy.regionTensorCoordinates q J
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let tau := a ^ 2 / 1048576
    let Delta := 1 / (200000 * (D : ℝ) ^ 12)
    let loss := Delta / (1 - (1 / 4 : ℝ)) ^ 2
    Module.finrank ℂ T = Module.finrank ℂ G → Submodule.IsCloseTo tau G T →
    (∀ S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q)),
      Submodule.IsViable (1 / 4 : ℝ) S (T.map coords.toLinearEquiv.toLinearMap) →
      let grow : Submodule ℂ (EuclideanSpace ℂ (J → Fin q)) := ⨆ w : Fin 1 → Fin N,
        S.map ((List.ofFn (fun j ↦ F (w j))).prod : _ →ₗ[ℂ] _)
      Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
        Submodule.IsViable loss grow (T.map coords.toLinearEquiv.toLinearMap)) →
    ∀ (k : ℕ) (hlk : l ≤ k) (hkr : k ≤ r)
      (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L l k → Fin q)))
      (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q))),
      Submodule.IsViable (3 / 200 : ℝ) S1
        (G.map (Entropy.regionTensorCoordinates q
          (interval L l k)).toLinearEquiv.toLinearMap) →
      Submodule.IsViable (3 / 200 : ℝ) S2
        (G.map (Entropy.regionTensorCoordinates q
          (interval L k r)).toLinearEquiv.toLinearMap) →
      HasSoftWordNodeEnergyUpdate (u := u) (v := v) hq hlk hkr Φ F S1 S2 := by
  classical
  intro config H hH G J coords a tau Delta loss hdimT hGT hword
    k hlk hkr S1 S2 hS1 hS2
  let : Nonempty (Fin L → Fin q) := config
  obtain ⟨hrho0, hrho, eP, eM, xP, xM, hxP, hPxP, hPmin,
    hxM, hMxM, hMmin, hsoft⟩ :=
    exists_native_soft_word_compressed_energy_estimate hq hlu huv hvr hrL
      hleft hright hell hD hcount hsample Φ h0 h1 T F hdimT hGT hword
  obtain ⟨eLeft, eMiddle, eRight, eParent, xLeft, xMiddle, xRight, xParent,
    hxLeft, hLeft, hLeftMin, hxMiddle, hMiddle, hMiddleMin,
    hxRight, hRight, hRightMin, hxParent, hParent, hParentMin,
    _hThreeLower, _hThreeUpper, hcenter⟩ :=
    exists_regional_central_energy_estimate hq hlu huv hvr hrL Φ h0 h1
  have heP : eP = eParent := groundEnergy_eq_of_normalized_eigenvectors
    (ManyBody.BondInteraction.threeRegionHamiltonians l r Φ 1) eP eParent xP xParent
    hPxP hxP hParent hxParent hPmin hParentMin
  have heM : eM = eMiddle := groundEnergy_eq_of_normalized_eigenvectors
    (ManyBody.BondInteraction.threeRegionHamiltonians u v Φ 1) eM eMiddle xM xMiddle
    hMxM hxM hMiddle hxMiddle hMmin hMiddleMin
  obtain ⟨eA, eB, eMerge, x, z, hx, hAx, hBx, hAmin, hBmin,
    hz, hMerge, hMergeMin, hMergeLower, hMergeUpper, _⟩ :=
    exists_adjacent_interval_energy_merge hq hlk hkr hrL Φ h0 h1
  have heMerge : eMerge = eParent := groundEnergy_eq_of_normalized_eigenvectors
    (ManyBody.BondInteraction.threeRegionHamiltonians l r Φ 1) eMerge eParent z xParent
    hMerge hz hParent hxParent hMergeMin hParentMin
  refine ⟨eLeft, eRight, xLeft, xRight, hxLeft, hLeft, hLeftMin,
    hxRight, hRight, hRightMin, ?_⟩
  intro p1 p2 hp1 hp2
  obtain ⟨e1, y1, hy1, hAy1, hA1min, hp1l, hp1u⟩ := hp1
  obtain ⟨e2, y2, hy2, hBy2, hB2min, hp2l, hp2u⟩ := hp2
  have he1 : e1 = eA := groundEnergy_eq_of_normalized_eigenvectors
    (ManyBody.BondInteraction.threeRegionHamiltonians l k Φ 1) e1 eA y1 x hAy1 hy1 hAx hx hA1min hAmin
  have he2 : e2 = eB := groundEnergy_eq_of_normalized_eigenvectors
    (ManyBody.BondInteraction.threeRegionHamiltonians k r Φ 1) e2 eB y2 x hBy2 hy2 hBx hx hB2min hBmin
  have hsumLower : eParent - 8 ≤ p1 + p2 := by
    linarith only [hMergeUpper, heMerge, he1, he2, hp1l, hp2l]
  have hsumUpper : p1 + p2 ≤ eParent := by
    linarith only [hMergeLower, heMerge, he1, he2, hp1u, hp2u]
  obtain ⟨hcenterLower, hcenterUpper⟩ := hcenter (p1 + p2) hsumLower hsumUpper
  rw [← heM] at hcenterLower hcenterUpper
  obtain ⟨hKraw, eSoft, w, _hLift, _hw, _hRw, _hKlower, _heSoft, _hshift, hcompressed⟩ :=
    hsoft (p1 + p2 - eLeft - eRight - 2) hcenterLower hcenterUpper
  obtain ⟨_hdim, n, b, energy, hdim, heigen, hanti, _hlower, _hupper,
    hplower, hpupper⟩ := hcompressed k hlk hkr S1 S2 hS1 hS2
  refine ⟨⟨eM, xM, hxM, hMxM, hMmin, hcenterLower, hcenterUpper⟩,
    energy (Fin.last n) - 3, ?_, ?_⟩
  · refine ⟨eP, xP, hxP, hPxP, hPmin, ?_, hpupper⟩
    linarith only [hplower, hrho]
  · exact ⟨hKraw, n, b, energy, hdim, heigen, hanti, rfl⟩

end TNLean.MPS.AreaLaw.ALVV

end

section

open ManyBody (interval)

open Matrix
open scoped BigOperators TensorProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The actual interleaved tree retains its original spaces, targets and
families while acquiring the one-sided node energy callback. At every long
node, all child estimates of width 49/16 yield an actual raw compression
update of the same width. Corrected auxiliary to ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, line 1631, and line 1807. -/
theorem exists_physical_dg_interleaved_tree_with_energy_updates :
    ∃ Ctail C Kref : ℝ, 21 ≤ Ctail ∧ 21 ≤ C ∧ 0 < Kref ∧ ∀ (L q : ℕ),
    ∀ (Φ : ManyBody.BondInteraction L q)
      (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu nu gamma : ℝ),
    0 < gamma →
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let rG := Module.finrank ℂ G
    let g := min gamma 1
    let m := max q 50
    let w := 1 + Real.log (rG : ℝ) + 2 * Real.log ((L : ℝ) + 1)
    let v := 1 + Real.log (m : ℝ) + Real.log (1 / g) + Real.log (1 + w)
    let ell := Nat.ceil (C * (v ^ 6 / g + Real.sqrt w * v ^ 3 / Real.sqrt g))
    let D := (m * ell ^ 2) ^ (22 * ell)
    let s := Nat.ceil (4096 * (rG : ℝ) * (Real.log (D : ℝ) + w))
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let tau := a ^ 2 / 1048576
    let epsilon := 200 * tau
    let t := Ctail * (1 + Real.log (1 / g) + Real.log (1 / tau))
    let Delta := (1 / 200000 : ℝ) / (D : ℝ) ^ 12
    21 ≤ ell ∧ 2 ≤ D ∧ 1 ≤ s ∧ 0 < a ∧ a ≤ 1 / 100 ∧
      0 < epsilon ∧ epsilon ≤ 1 ∧ 21 ≤ t ∧
      (288 * Real.exp (11 / 8)) * Real.exp (-(t - g) / 8) ≤ epsilon * g / 1000000 ∧
      (D : ℝ) ^ 12 * Delta < 1 / 100000 ∧
    let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
    let bref := 16 + Real.log (1 / g) + Real.log (32 * (rG : ℝ) * ((L : ℝ) + 1) / tau)
    ∃ B : ℕ, 1 ≤ B ∧
      Real.log (B : ℝ) ≤
        Kref * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bref ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log bref) ∧
    ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
      Module.finrank ℂ U = rG ∧
      (∀ z ∈ U, IsOpenMPS L q (rG ^ 2 * B) (fun x ↦ z x)) ∧
    let Dref := rG ^ 2 * B
    let xiMax := a / (256 * (Dref : ℝ) * Real.sqrt ((L : ℝ) + 1))
    0 < xiMax ∧
    let width := 4 * ell
    ∃ hwidth : 1 ≤ width, ∃ hq : 0 < q,
    ∃ (T : LongIntervalIndex L width →
        Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
      (N : LongIntervalIndex L width → ℕ)
      (F : ∀ J : LongIntervalIndex L width,
        Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
      (∀ J, N J ≤ D ^ 2) ∧
      (∀ J, Module.finrank ℂ (T J) = rG ∧
        Submodule.IsCloseTo tau (T J) G ∧ Submodule.IsCloseTo tau G (T J) ∧
        Submodule.IsCloseTo (4 * tau) (T J) U ∧
        Submodule.IsCloseTo (4 * tau) U (T J) ∧
        (∀ (power : ℕ)
          (S : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))) (delta : ℝ),
          Submodule.IsViable delta S
            ((T J).map (Entropy.regionTensorCoordinates q
              (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) → delta < 1 →
          let grow := ⨆ w : Fin power → Fin (N J),
            S.map ((List.ofFn (fun j ↦ F J (w j))).prod : _ →ₗ[ℂ] _)
          Module.finrank ℂ grow ≤ (D ^ 2) ^ power * Module.finrank ℂ S ∧
            Submodule.IsViable (Delta ^ power / (1 - delta) ^ 2) grow
              ((T J).map (Entropy.regionTensorCoordinates q
                (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap))) ∧
      ∀ xi : ℝ, 0 < xi → xi ≤ xiMax →
      ∃ operation : IntervalMergeOperation L q,
        (∀ (p r : ℕ), p ≤ r → r ≤ L →
          let S := balancedIntervalSpace operation width hwidth p r
          Submodule.IsViable (3 / 200 : ℝ) S
            (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) ∧
          Module.finrank ℂ S ≤ D ^ 6 * s ^ 3 ∧
          IsIntervalSpanWithRankBound L q p r (D ^ 6 * s ^ 3) xi S) ∧
        (∀ (J : LongIntervalIndex L width) (k : ℕ)
          (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2),
          let S1 := balancedIntervalSpace operation width hwidth J.val.1 k
          let S2 := balancedIntervalSpace operation width hwidth k J.val.2
          ∃ U : Matrix.unitaryGroup
            (Fin (Module.finrank ℂ (adjacentIntervalMerge L q
              J.val.1 k J.val.2 hpk hkr S1 S2))) ℂ,
            operation J.val.1 k J.val.2 hpk hkr S1 S2 =
              sampledIntervalInterleavedTrim L q J.val.1 J.val.2 D s (F J) xi
                (adjacentIntervalMerge L q J.val.1 k J.val.2 hpk hkr S1 S2) U) ∧
        ∀ (J : LongIntervalIndex L width) (k : ℕ)
          (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2),
          let S1 := balancedIntervalSpace operation width hwidth J.val.1 k
          let S2 := balancedIntervalSpace operation width hwidth k J.val.2
          ALVV.HasSoftWordNodeEnergyUpdate
            (u := J.val.1 + ell) (v := J.val.2 - ell) hq hpk hkr Φ (F J) S1 S2 := by
  classical
  obtain ⟨Ctail, C, Kref, hCtail, hC, hKref, hfactory⟩ :=
    exists_physical_dg_interleaved_interval_tree_with_word_powers
  refine ⟨Ctail, C, Kref, hCtail, hC, hKref, ?_⟩
  intro L q Φ h0 h1 mu nu gamma hgamma H hH hmu hnu hmunu hgap
    G rG g m w v ell D s a tau epsilon t Delta
  obtain ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff,
    B, hB, hlogB, Uref, hdimU, hUMPS, hxiMax, hwidth, T, N, F,
    hN, htargets, htrees⟩ :=
    hfactory L q Φ h0 h1 mu nu gamma hgamma hmu hnu hmunu hgap
  change 21 ≤ ell at hell
  refine ⟨hell, hD, hs, ha, haSmall, hepsilon, hepsilon1, ht, htail, htradeoff, ?_⟩
  intro u bref
  refine ⟨B, hB, hlogB, Uref, hdimU, hUMPS, ?_⟩
  intro Dref xiMax
  refine ⟨hxiMax, ?_⟩
  intro width
  have hq : 0 < q := lt_of_lt_of_le (by decide : 0 < 2)
    (hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu))
  let : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
  obtain ⟨j, hj⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hmu
  have hminle : minEigenvalue hH ≤ mu := by
    simpa only [hj] using minEigenvalue_le hH j
  obtain ⟨i, hi⟩ := minEigenvalue_achieved hH
  have hmin : minEigenvalue hH = mu := by
    rcases hgap _ (hH.eigenvalues_mem_spectrum_real i) with heq | hle
    · exact hi.symm.trans heq
    · rw [hi] at hle
      linarith only [hminle, hle, hgamma]
  have hcount : 50 * ell ^ 2 ≤ D := by
    have hbase : 1 ≤ m * ell ^ 2 := by
      have hm : 50 ≤ m := Nat.le_max_right q 50
      have he : 1 ≤ ell ^ 2 := Nat.one_le_pow 2 ell (by omega)
      nlinarith only [hm, he]
    have hpow : m * ell ^ 2 ≤ D := le_self_pow hbase (by omega : 22 * ell ≠ 0)
    exact (Nat.mul_le_mul_right (ell ^ 2) (Nat.le_max_right q 50)).trans hpow
  refine ⟨hwidth, hq, T, N, F, hN, htargets, ?_⟩
  intro xi hxi hxiMax
  obtain ⟨operation, hspaces, hnodes⟩ := htrees xi hxi hxiMax
  refine ⟨operation, hspaces, hnodes, ?_⟩
  intro J k hpk hkr S1 S2
  have hlong : 4 * ell < J.val.2 - J.val.1 := J.property.2.2
  have hlu : J.val.1 ≤ J.val.1 + ell := by omega
  have huv : J.val.1 + ell ≤ J.val.2 - ell := by omega
  have hvr : J.val.2 - ell ≤ J.val.2 := Nat.sub_le _ _
  have hleft : J.val.1 + ell - J.val.1 ≤ 2 * ell := by omega
  have hright : J.val.2 - (J.val.2 - ell) ≤ 2 * ell := by omega
  obtain ⟨hdimT, _hTG, hGT, _hTU, _hUT, hwords⟩ := htargets J
  have hdimRaw : Module.finrank ℂ (T J) = Module.finrank ℂ
      (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu) := hdimT
  have hdimCanonical : Module.finrank ℂ (T J) = Module.finrank ℂ
      (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH)) :=
    Eq.mpr (congrArg (fun c ↦ Module.finrank ℂ (T J) = Module.finrank ℂ
      (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues c)) hmin) hdimRaw
  have hGTRaw : Submodule.IsCloseTo tau
      (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu) (T J) := hGT
  have hGTCanonical : Submodule.IsCloseTo tau
      (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH))
      (T J) := Eq.mpr (congrArg (fun c ↦ Submodule.IsCloseTo tau
        (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues c) (T J)) hmin) hGTRaw
  have hone (S : Submodule ℂ (EuclideanSpace ℂ
      (interval L J.val.1 J.val.2 → Fin q)))
      (hS : Submodule.IsViable (1 / 4 : ℝ) S ((T J).map
        (Entropy.regionTensorCoordinates q
          (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap)) :
      let grow := ⨆ word : Fin 1 → Fin (N J),
        S.map ((List.ofFn (fun j ↦ F J (word j))).prod : _ →ₗ[ℂ] _)
      Module.finrank ℂ grow ≤ D ^ 2 * Module.finrank ℂ S ∧
        Submodule.IsViable ((1 / (200000 * (D : ℝ) ^ 12)) / (1 - (1 / 4 : ℝ)) ^ 2)
          grow ((T J).map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) := by
    simpa only [pow_one, Delta, div_div] using hwords 1 S (1 / 4) hS (by norm_num)
  have hS1Raw : Submodule.IsViable (3 / 200 : ℝ) S1
      ((Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu).map
        (Entropy.regionTensorCoordinates q (interval L J.val.1 k)).toLinearEquiv.toLinearMap) :=
    (hspaces J.val.1 k hpk (hkr.trans J.property.2.1)).1
  have hS2Raw : Submodule.IsViable (3 / 200 : ℝ) S2
      ((Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu).map
        (Entropy.regionTensorCoordinates q (interval L k J.val.2)).toLinearEquiv.toLinearMap) :=
    (hspaces k J.val.2 hkr J.property.2.1).1
  have hS1Canonical := Eq.mpr (congrArg (fun c ↦
    Submodule.IsViable (3 / 200 : ℝ) S1
    ((Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues c).map
      (Entropy.regionTensorCoordinates q (interval L J.val.1 k)).toLinearEquiv.toLinearMap)) hmin)
    hS1Raw
  have hS2Canonical := Eq.mpr (congrArg (fun c ↦
    Submodule.IsViable (3 / 200 : ℝ) S2
    ((Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues c).map
      (Entropy.regionTensorCoordinates q (interval L k J.val.2)).toLinearEquiv.toLinearMap)) hmin)
    hS2Raw
  exact ALVV.exists_soft_word_node_energy_update hq hlu huv hvr J.property.2.1
    hleft hright hell hD hcount hs Φ h0 h1 (T J) (F J)
    hdimCanonical hGTCanonical hone k hpk hkr S1 S2 hS1Canonical hS2Canonical

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw.ALVV

/-- The same attained parent and middle minima admit actual collar minima
whose child-dependent middle center is one-sided and has error at most ten.
The exact parent-sum width is 57/8. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, line 1631 and line 1807. -/
theorem exists_regional_middle_center_of_child_estimates {L q l u v r : ℕ}
    (hq : 0 < q) (hlu : l ≤ u) (huv : u ≤ v) (hvr : v ≤ r) (hrL : r ≤ L)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (eP eM : ℝ) (xP xM : (Fin L → Fin q) → ℂ)
    (hxP : star xP ⬝ᵥ xP = 1)
    (hPxP : ManyBody.BondInteraction.threeRegionHamiltonians l r Φ 1 *ᵥ xP = (eP : ℂ) • xP)
    (hPmin : (ManyBody.BondInteraction.threeRegionHamiltonians l r Φ 1 - (eP : ℂ) • 1).PosSemidef)
    (hxM : star xM ⬝ᵥ xM = 1)
    (hMxM : ManyBody.BondInteraction.threeRegionHamiltonians u v Φ 1 *ᵥ xM = (eM : ℂ) • xM)
    (hMmin : (ManyBody.BondInteraction.threeRegionHamiltonians u v Φ 1 - (eM : ℂ) • 1).PosSemidef) :
    ∃ (eLeft eRight : ℝ) (xLeft xRight : (Fin L → Fin q) → ℂ),
      star xLeft ⬝ᵥ xLeft = 1 ∧
      ManyBody.BondInteraction.threeRegionHamiltonians l u Φ 1 *ᵥ xLeft = (eLeft : ℂ) • xLeft ∧
      (ManyBody.BondInteraction.threeRegionHamiltonians l u Φ 1 - (eLeft : ℂ) • 1).PosSemidef ∧
      star xRight ⬝ᵥ xRight = 1 ∧
      ManyBody.BondInteraction.threeRegionHamiltonians v r Φ 1 *ᵥ xRight = (eRight : ℂ) • xRight ∧
      (ManyBody.BondInteraction.threeRegionHamiltonians v r Φ 1 - (eRight : ℂ) • 1).PosSemidef ∧
      ∀ (k : ℕ), l ≤ k → k ≤ r → ∀ p1 p2 : ℝ,
        IsRegionalLowerEnergyEstimate Φ l k (49 / 16) p1 →
        IsRegionalLowerEnergyEstimate Φ k r (49 / 16) p2 →
        let center := p1 + p2 - eLeft - eRight - 2
        eM - 10 ≤ center ∧ center ≤ eM ∧
          IsRegionalLowerEnergyEstimate Φ u v 10 center ∧
          IsRegionalLowerEnergyEstimate Φ l r (57 / 8) (p1 + p2) := by
  classical
  obtain ⟨eLeft, eMiddle, eRight, eParent, xLeft, xMiddle, xRight, xParent,
    hxLeft, hLeft, hLeftMin, hxMiddle, hMiddle, hMiddleMin,
    hxRight, hRight, hRightMin, hxParent, hParent, hParentMin,
    _hThreeLower, _hThreeUpper, hcenter⟩ :=
    exists_regional_central_energy_estimate hq hlu huv hvr hrL Φ h0 h1
  have heP : eP = eParent := groundEnergy_eq_of_normalized_eigenvectors
    (ManyBody.BondInteraction.threeRegionHamiltonians l r Φ 1) eP eParent xP xParent
    hPxP hxP hParent hxParent hPmin hParentMin
  have heM : eM = eMiddle := groundEnergy_eq_of_normalized_eigenvectors
    (ManyBody.BondInteraction.threeRegionHamiltonians u v Φ 1) eM eMiddle xM xMiddle
    hMxM hxM hMiddle hxMiddle hMmin hMiddleMin
  refine ⟨eLeft, eRight, xLeft, xRight, hxLeft, hLeft, hLeftMin,
    hxRight, hRight, hRightMin, ?_⟩
  intro k hlk hkr p1 p2 hp1 hp2 center
  obtain ⟨eA, eB, eMerge, x, z, hx, hAx, hBx, hAmin, hBmin,
    hz, hMerge, hMergeMin, hMergeLower, hMergeUpper, _⟩ :=
    exists_adjacent_interval_energy_merge hq hlk hkr hrL Φ h0 h1
  have heMerge : eMerge = eParent := groundEnergy_eq_of_normalized_eigenvectors
    (ManyBody.BondInteraction.threeRegionHamiltonians l r Φ 1) eMerge eParent z xParent
    hMerge hz hParent hxParent hMergeMin hParentMin
  obtain ⟨e1, y1, hy1, hAy1, hA1min, hp1l, hp1u⟩ := hp1
  obtain ⟨e2, y2, hy2, hBy2, hB2min, hp2l, hp2u⟩ := hp2
  have he1 : e1 = eA := groundEnergy_eq_of_normalized_eigenvectors
    (ManyBody.BondInteraction.threeRegionHamiltonians l k Φ 1) e1 eA y1 x hAy1 hy1 hAx hx hA1min hAmin
  have he2 : e2 = eB := groundEnergy_eq_of_normalized_eigenvectors
    (ManyBody.BondInteraction.threeRegionHamiltonians k r Φ 1) e2 eB y2 x hBy2 hy2 hBx hx hB2min hBmin
  have hsumLower : eParent - 57 / 8 ≤ p1 + p2 := by
    linarith only [hMergeUpper, heMerge, he1, he2, hp1l, hp2l]
  have hsumUpper : p1 + p2 ≤ eParent := by
    linarith only [hMergeLower, heMerge, he1, he2, hp1u, hp2u]
  obtain ⟨hcenterLower, hcenterUpper⟩ := hcenter (p1 + p2)
    (by linarith only [hsumLower]) hsumUpper
  rw [← heM] at hcenterLower hcenterUpper
  refine ⟨hcenterLower, hcenterUpper,
    ⟨eM, xM, hxM, hMxM, hMmin, hcenterLower, hcenterUpper⟩,
    eP, xP, hxP, hPxP, hPmin, ?_, ?_⟩
  · linarith only [hsumLower, heP]
  · linarith only [hsumUpper, heP]

end TNLean.MPS.AreaLaw.ALVV

end
