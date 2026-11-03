/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.SoftParentStructure
import TNLean.MPS.AreaLaw.RegionalGroundEnergy
import TNLean.Circuit.SupportedFunctionalCalculus
import QICLean.Entropy.PositiveLocalLift

/-!
# Regional coordinates and energy of the central soft replacement

The actual central replacement and its unmodified collars give a
positive centered native operator with an explicit norm bound. Its
actual attained minimum is compared with the original parent minimum
by the proved reverse residual. The resulting energy estimate concerns
the entire original ground space. The generated soft spectral target
and its separate untrimmed energy candidate remain subsequent steps.
These are corrected auxiliaries to ALVV, arXiv:1602.08828v2,
Figure `fig:generate`, lines 1348–1392, and Figure `fig:algo1`, line 1631.

**Scope restriction (regional energy auxiliary):** The center is one-sided,
the norm bound is for the centered operator, and the energy bound concerns
the original ground space. Transfer to the generated soft spectral target
and the recursive energy estimate remain separate. See
`docs/paper-gaps/alvv16_soft_regional_energy_centering.tex`.
-/

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

/-- Original bonds construct a native positive centered soft
operator, its true attained energy and a norm bound independent of the
parent volume apart from the explicit collar lengths. The native matrix
is chosen before every auxiliary tail cutoff. The energy comparison is
on the original full ground space; no soft-target energy or generation
algorithm is assumed or concluded. Auxiliary to ALVV,
arXiv:1602.08828v2, Figure `fig:generate`, lines 1348–1392,
and Figure `fig:algo1`, line 1631. -/
theorem exists_native_soft_parent_energy_bound {L q l u v r ell : ℕ}
    (hq : 0 < q) (hlu : l ≤ u) (huv : u ≤ v) (hvr : v ≤ r) (hrL : r ≤ L)
    (hleft : u - l ≤ 2 * ell) (hright : r - v ≤ 2 * ell)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let _ : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
    let H := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH)
    let J := interval L l r
    let P := ∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ l ≤ i.val ∧ i.val + 1 < r), h i
    let M := ∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ u ≤ i.val ∧ i.val + 1 < v), h i
    ∃ (eP eM : ℝ) (xP xM : (Fin L → Fin q) → ℂ),
      star xP ⬝ᵥ xP = 1 ∧ P *ᵥ xP = (eP : ℂ) • xP ∧
      (P - (eP : ℂ) • 1).PosSemidef ∧
      star xM ⬝ᵥ xM = 1 ∧ M *ᵥ xM = (eM : ℂ) • xM ∧
      (M - (eM : ℂ) • 1).PosSemidef ∧
      ∀ (p t : ℝ) (m : ℕ), eM - 10 ≤ p → p ≤ eM → 0 < t → 2 ≤ m →
        let R := P - M + (p : ℂ) • 1 + cfc (Real.softTruncation t m) (M - (p : ℂ) • 1)
        let budget := t * (1 + Real.log (m : ℝ)) + 4 * (ell : ℝ) + 14
        ∃ (eSoft : ℝ) (K : Matrix (J → Fin q) (J → Fin q) ℂ)
          (w : (Fin L → Fin q) → ℂ),
          K.PosSemidef ∧ ‖K‖ ≤ budget ∧
          R = Entropy.localLift (n := fun _ : Fin L ↦ q) J K + (eSoft : ℂ) • 1 ∧
          star w ⬝ᵥ w = 1 ∧ R *ᵥ w = (eSoft : ℂ) • w ∧
          (R - (eSoft : ℂ) • 1).PosSemidef ∧ ‖R - (eSoft : ℂ) • 1‖ ≤ budget ∧
          ∀ T : ℝ, 48 ≤ t → 48 ≤ T →
            let rho := 32 * Real.exp (-(T - 48) / 8) + (t / (m : ℝ)) * (T / t) ^ m
            eSoft ≤ eP ∧ eP - eSoft ≤ rho ∧
              ∀ g ∈ G,
                (inner ℂ (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
                  (Entropy.localLift (n := fun _ : Fin L ↦ q) J K) g) g).re ≤
                    (2 + rho) * ‖g‖ ^ 2 := by
  classical
  intro config H hH G J P M
  let : Nonempty (Fin L → Fin q) := config
  let hp := intervalBondRestriction l r h
  let k : Fin 6 → ℕ := ![0, l, u, v, r, L]
  let I := fun j : Fin 5 ↦ Finset.univ.filter
    (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
  let A := fun j : Fin 5 ↦ ∑ i ∈ I j, hp i
  obtain ⟨e, x, z, E, hx, hxe, he, _he0, hz, hHz, hE, _hE0, _hE4, hfamily⟩ :=
    exists_soft_parent_structure hq hlu huv hvr hrL hleft hright h hs h0 h1
  have hAM : A 2 = M := sum_internal_intervalBondRestriction_eq hlu hvr h
  let s := ∑ j, e j
  let eP := E + s
  have hPz : P *ᵥ z = (eP : ℂ) • z := by
    have hh := hHz
    change (P - (s : ℂ) • 1) *ᵥ z = (E : ℂ) • z at hh
    rw [sub_mulVec, smul_mulVec, one_mulVec] at hh
    dsimp only [eP]
    rw [Complex.ofReal_add, add_smul]
    exact sub_eq_iff_eq_add.mp hh
  have hPmin : (P - (eP : ℂ) • 1).PosSemidef := by
    convert hE using 1
    dsimp only [eP]
    rw [Complex.ofReal_add, add_smul]
    abel
  obtain ⟨e0, x0, hx0, hPx0, hP0, _hPnorm, hGenergy, _hprojection⟩ :=
    exists_regional_ground_energy_bound hq (hlu.trans (huv.trans hvr)) hrL h hs h0 h1
  have heP : e0 = eP := groundEnergy_eq_of_normalized_eigenvectors P e0 eP x0 z
    hPx0 hx0 hPz hz hP0 hPmin
  have hMxe : M *ᵥ x = (e 2 : ℂ) • x := by rw [← hAM]; exact hxe 2
  have hMmin : (M - (e 2 : ℂ) • 1).PosSemidef := by rw [← hAM]; exact he 2
  refine ⟨eP, e 2, z, x, hz, hPz, hPmin, hx, hMxe, hMmin, ?_⟩
  intro p t m hpl hpu ht hm R budget
  obtain ⟨mu, w, _hB, _hBplus, hBC, hw, hBw, hBlow, _hmu10, hmuE, hnorm, hshift⟩ :=
    hfamily p t m hpl hpu ht hm
  let B := P - M + (p : ℂ) • 1 + cfc (Real.softTruncation t m) (M - (p : ℂ) • 1) -
    (s : ℂ) • 1
  let Bmid := P - A 2 + (p : ℂ) • 1 +
    cfc (Real.softTruncation t m) (A 2 - (p : ℂ) • 1) - (s : ℂ) • 1
  have hBform : Bmid = B := by dsimp only [Bmid, B]; rw [hAM]
  change (Bmid - (mu : ℂ) • 1).PosSemidef at hBlow
  rw [hBform] at hBlow
  change ‖Bmid - (mu : ℂ) • 1‖ ≤ budget at hnorm
  rw [hBform] at hnorm
  change Bmid *ᵥ w = (mu : ℂ) • w at hBw
  rw [hBform] at hBw
  change Bmid ≤ P - (s : ℂ) • 1 at hBC
  rw [hBform] at hBC
  let eSoft := mu + s
  let Csoft := B - (mu : ℂ) • 1
  have hCraw : Csoft = R - (eSoft : ℂ) • 1 := by
    dsimp only [Csoft, B, R, eSoft]
    rw [Complex.ofReal_add, add_smul]
    abel
  have hPs : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) P J :=
    isSupportedOn_sum_internal_bonds L q l r h hs
  have hMs : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) M J := by
    apply (isSupportedOn_sum_internal_bonds L q u v h hs).mono
    intro i hi
    simp only [J, mem_interval] at hi ⊢
    omega
  let V := QuantumCircuit.supportedOperators q (J : Set (Fin L))
  have hPV : P ∈ V := QuantumCircuit.mem_supportedOperators_of_isSupportedOn hPs
  have hMV : M ∈ V := QuantumCircuit.mem_supportedOperators_of_isSupportedOn hMs
  have hIV : (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ∈ V :=
    QuantumCircuit.one_mem_supportedOperators (J : Set (Fin L))
  have hXV : M - (p : ℂ) • 1 ∈ V := V.sub_mem hMV (V.smul_mem _ hIV)
  have hFV : cfc (Real.softTruncation t m) (M - (p : ℂ) • 1) ∈ V :=
    QuantumCircuit.cfc_mem_supportedOperators _ hXV
  have hCV : Csoft ∈ V :=
    V.sub_mem (V.sub_mem (V.add_mem (V.add_mem (V.sub_mem hPV hMV)
      (V.smul_mem _ hIV)) hFV) (V.smul_mem _ hIV)) (V.smul_mem _ hIV)
  have hCs := QuantumCircuit.isSupportedOn_of_mem_supportedOperators hCV
  obtain ⟨K, hK, hKnorm, hLift⟩ := hCs.exists_posSemidef_localLift_norm_le hBlow budget hnorm
  have hRnative : R = Entropy.localLift (n := fun _ : Fin L ↦ q) J K + (eSoft : ℂ) • 1 := by
    rw [← hLift, hCraw]
    abel
  have hRw : R *ᵥ w = (eSoft : ℂ) • w := by
    change (R - (s : ℂ) • 1) *ᵥ w = (mu : ℂ) • w at hBw
    rw [sub_mulVec, smul_mulVec, one_mulVec] at hBw
    dsimp only [eSoft]
    rw [Complex.ofReal_add, add_smul]
    exact sub_eq_iff_eq_add.mp hBw
  refine ⟨eSoft, K, w, hK, hKnorm, hRnative, hw, hRw, ?_, ?_, ?_⟩
  · exact hCraw ▸ hBlow
  · exact hCraw ▸ hnorm
  · intro T ht48 hT48 rho
    obtain ⟨_hmuLower, hmuUpper⟩ := hshift T ht48 hT48
    have hrho : E - mu ≤ rho := hmuUpper
    have hSoftle : eSoft ≤ eP := by
      dsimp only [eSoft, eP]
      exact _root_.add_le_add hmuE (le_refl s)
    have hDiff : eP - eSoft = E - mu := by dsimp only [eP, eSoft]; ring
    refine ⟨hSoftle, ?_, ?_⟩
    · rw [hDiff]
      exact hrho
    · intro g hg
      have horder : Csoft ≤ (P - (eP : ℂ) • 1) + ((E - mu : ℝ) : ℂ) • 1 := by
        calc
          Csoft ≤ (P - (s : ℂ) • 1) - (mu : ℂ) • 1 := sub_le_sub_right hBC _
          _ = _ := by
            dsimp only [eP]
            rw [Complex.ofReal_add, Complex.ofReal_sub, add_smul, sub_smul]
            abel
      have hform := (le_iff.mp horder).isPositive_toEuclideanCLM.re_inner_nonneg_left g
      simp only [map_sub, map_add, map_smul, map_one, _root_.sub_apply, _root_.add_apply,
        _root_.smul_apply, one_apply_eq_self, inner_sub_left, inner_add_left,
        inner_smul_left, RCLike.re_to_complex, Complex.conj_ofReal,
        Complex.re_ofReal_mul] at hform
      have hself : (inner ℂ g g).re = ‖g‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) g
      rw [hself] at hform
      have horiginal : (inner ℂ (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
          (P - (eP : ℂ) • 1) g) g).re ≤ 2 * ‖g‖ ^ 2 := by
        rw [← heP]
        exact hGenergy g hg
      simp only [map_sub, map_smul, map_one, _root_.sub_apply, _root_.smul_apply,
        one_apply_eq_self, inner_sub_left, inner_smul_left, Complex.conj_ofReal,
        Complex.sub_re, Complex.re_ofReal_mul] at horiginal
      rw [hself] at horiginal
      rw [← hLift]
      nlinarith only [hform, horiginal,
        mul_le_mul_of_nonneg_right hrho (sq_nonneg ‖g‖)]

end TNLean.MPS.AreaLaw.ALVV
