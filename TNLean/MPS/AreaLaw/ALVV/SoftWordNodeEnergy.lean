/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.SoftWordEnergyEstimate
import TNLean.MPS.AreaLaw.RegionalCentralEnergyEstimate

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
-/

open Matrix
open scoped BigOperators TensorProduct InnerProductSpace ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

/-- A lower energy estimate with an explicit error width for the actual
original regional Hamiltonian. The minimum is certified by an attained unit
eigenvector and a positive spectral shift. Auxiliary to ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, line 1631. -/
def IsRegionalLowerEnergyEstimate {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (l r : ℕ) (width p : ℝ) : Prop :=
  let A := aklvRegionalHamiltonians l r h 1
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
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (F : Fin N → EuclideanSpace ℂ (interval L l r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L l r → Fin q))
    (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L l k → Fin q)))
    (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q)))
    (center p : ℝ) : Prop :=
  let J := interval L l r
  let P := aklvRegionalHamiltonians l r h 1
  let M := aklvRegionalHamiltonians u v h 1
  let R := P - M + (center : ℂ) • 1 +
    cfc (Real.softTruncation 768 12) (M - (center : ℂ) • 1)
  let sigma0 : Fin L → Fin q := fun _ ↦ ⟨0, hq⟩
  let y0 := ((Entropy.cutEquiv (fun _ : Fin L ↦ q) J) sigma0).2
  let native := fun x : J → Fin q ↦
    (Entropy.cutEquiv (fun _ : Fin L ↦ q) J).symm (x, y0)
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
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (F : Fin N → EuclideanSpace ℂ (interval L l r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L l r → Fin q))
    (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L l k → Fin q)))
    (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k r → Fin q))) : Prop :=
∃ (eLeft eRight : ℝ) (xLeft xRight : (Fin L → Fin q) → ℂ),
        star xLeft ⬝ᵥ xLeft = 1 ∧
        aklvRegionalHamiltonians l u h 1 *ᵥ xLeft = (eLeft : ℂ) • xLeft ∧
        (aklvRegionalHamiltonians l u h 1 - (eLeft : ℂ) • 1).PosSemidef ∧
        star xRight ⬝ᵥ xRight = 1 ∧
        aklvRegionalHamiltonians v r h 1 *ᵥ xRight = (eRight : ℂ) • xRight ∧
        (aklvRegionalHamiltonians v r h 1 - (eRight : ℂ) • 1).PosSemidef ∧
        ∀ p1 p2 : ℝ,
          IsRegionalLowerEnergyEstimate h l k (49 / 16) p1 →
          IsRegionalLowerEnergyEstimate h k r (49 / 16) p2 →
          IsRegionalLowerEnergyEstimate h u v 10
            (p1 + p2 - eLeft - eRight - 2) ∧
          ∃ p : ℝ, IsRegionalLowerEnergyEstimate h l r (49 / 16) p ∧
            IsSoftWordEnergyUpdate (u := u) (v := v) hq hlk hkr h F S1 S2
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
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (F : Fin N → EuclideanSpace ℂ (interval L l r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L l r → Fin q)) :
    let _ : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
    let H := ∑ i, h i
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
      HasSoftWordNodeEnergyUpdate (u := u) (v := v) hq hlk hkr h F S1 S2 := by
  classical
  intro config H hH G J coords a tau Delta loss hdimT hGT hword
    k hlk hkr S1 S2 hS1 hS2
  let : Nonempty (Fin L → Fin q) := config
  obtain ⟨hrho0, hrho, eP, eM, xP, xM, hxP, hPxP, hPmin,
    hxM, hMxM, hMmin, hsoft⟩ :=
    exists_native_soft_word_compressed_energy_estimate hq hlu huv hvr hrL
      hleft hright hell hD hcount hsample h hs h0 h1 T F hdimT hGT hword
  obtain ⟨eLeft, eMiddle, eRight, eParent, xLeft, xMiddle, xRight, xParent,
    hxLeft, hLeft, hLeftMin, hxMiddle, hMiddle, hMiddleMin,
    hxRight, hRight, hRightMin, hxParent, hParent, hParentMin,
    _hThreeLower, _hThreeUpper, hcenter⟩ :=
    exists_regional_central_energy_estimate hq hlu huv hvr hrL h hs h0 h1
  have heP : eP = eParent := groundEnergy_eq_of_normalized_eigenvectors
    (aklvRegionalHamiltonians l r h 1) eP eParent xP xParent
    hPxP hxP hParent hxParent hPmin hParentMin
  have heM : eM = eMiddle := groundEnergy_eq_of_normalized_eigenvectors
    (aklvRegionalHamiltonians u v h 1) eM eMiddle xM xMiddle
    hMxM hxM hMiddle hxMiddle hMmin hMiddleMin
  obtain ⟨eA, eB, eMerge, x, z, hx, hAx, hBx, hAmin, hBmin,
    hz, hMerge, hMergeMin, hMergeLower, hMergeUpper, _⟩ :=
    exists_adjacent_interval_energy_merge hq hlk hkr hrL h hs h0 h1
  have heMerge : eMerge = eParent := groundEnergy_eq_of_normalized_eigenvectors
    (aklvRegionalHamiltonians l r h 1) eMerge eParent z xParent
    hMerge hz hParent hxParent hMergeMin hParentMin
  refine ⟨eLeft, eRight, xLeft, xRight, hxLeft, hLeft, hLeftMin,
    hxRight, hRight, hRightMin, ?_⟩
  intro p1 p2 hp1 hp2
  obtain ⟨e1, y1, hy1, hAy1, hA1min, hp1l, hp1u⟩ := hp1
  obtain ⟨e2, y2, hy2, hBy2, hB2min, hp2l, hp2u⟩ := hp2
  have he1 : e1 = eA := groundEnergy_eq_of_normalized_eigenvectors
    (aklvRegionalHamiltonians l k h 1) e1 eA y1 x hAy1 hy1 hAx hx hA1min hAmin
  have he2 : e2 = eB := groundEnergy_eq_of_normalized_eigenvectors
    (aklvRegionalHamiltonians k r h 1) e2 eB y2 x hBy2 hy2 hBx hx hB2min hBmin
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
