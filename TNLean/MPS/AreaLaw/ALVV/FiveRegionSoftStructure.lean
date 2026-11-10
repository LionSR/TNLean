/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.FiveRegionHamiltonian
import TNLean.Lattice.DisjointRegionalGround
import QICLean.Analysis.SoftTruncationCommutingFamily

/-!
# The actual simultaneous soft replacement of five consecutive regions

The original local interactions determine all regional minimum energies and a single
commuting interior, even when several regions are softened simultaneously. The correction
is ten times the number of replaced regions. The original and softened ground energies
are constructed, rather than supplied. This is an auxiliary construction for ALVV,
arXiv:1602.08828v2, `def:soft-trunc` and `t:aisefficient`, lines 1178–1185 and 1373–1392.
It supplies neither a residual estimate nor the complete efficient-filter theorem.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- Actual five-region geometry supplies the ground-energy caps, common commuting
interior and high-projection floor for every simultaneous estimated-center replacement.
The regional minima precede every choice of replaced regions, estimates, scale and order.
Auxiliary to ALVV, arXiv:1602.08828v2, `def:soft-trunc` and `t:aisefficient`,
lines 1178–1185 and 1373–1392; no spectral gap is assumed. -/
theorem exists_five_region_soft_structure {L q k1 k2 k3 k4 : ℕ}
    (hq : 0 < q) (h12 : k1 ≤ k2) (h23 : k2 ≤ k3)
    (h34 : k3 ≤ k4) (h4L : k4 ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, k1, k2, k3, k4, L]
    let I := fun j : Fin 5 ↦ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A := fun j : Fin 5 ↦ ∑ i ∈ I j, h i
    let J := Finset.univ.filter
      (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({k1, k2, k3, k4} : Finset ℕ))
    let Y := ∑ i ∈ J, h i
    J.card ≤ 4 ∧ ∃ (e : Fin 5 → ℝ) (x z : (Fin L → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
      let Braw := ∑ j, (A j - (e j : ℂ) • 1)
      let H := (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1
      H = Braw + Y ∧ Braw.PosSemidef ∧ star z ⬝ᵥ z = 1 ∧
      H *ᵥ z = (E : ℂ) • z ∧ (H - (E : ℂ) • 1).PosSemidef ∧
      0 ≤ E ∧ E ≤ (J.card : ℝ) ∧
      H.IsHermitian ∧ ∀ (S : Finset (Fin 5)) (p : Fin 5 → ℝ) (t : ℝ) (m : ℕ),
        (∀ j ∈ S, e j - 10 ≤ p j) → (∀ j ∈ S, p j ≤ e j) → 0 < t → 1 ≤ m →
        let B := ∑ j, ((if j ∈ S then (p j : ℂ) • 1 +
          cfc (Real.softTruncation t m) (A j - (p j : ℂ) • 1) else A j) - (e j : ℂ) • 1)
        let D := 10 * (S.card : ℝ)
        let G := B + Y
        ∃ (mu : ℝ) (w : (Fin L → Fin q) → ℂ), G.IsHermitian ∧
          (B + (D : ℂ) • 1).PosSemidef ∧ G ≤ H ∧ star w ⬝ᵥ w = 1 ∧
          G *ᵥ w = (mu : ℂ) • w ∧ (G - (mu : ℂ) • 1).PosSemidef ∧
          -D ≤ mu ∧ mu ≤ E ∧ mu ≤ (J.card : ℝ) ∧
          (∀ j, Commute B (A j)) ∧
          ∀ j ∈ S, ∀ U : ℝ, 0 ≤ U →
            (U - (t / (m : ℝ)) * (U / t) ^ m) • spectralProjectionGE (A j) (p j + U) ≤
              B + (D : ℂ) • 1 := by
  intro k I A J Y
  let R := fun j : Fin 5 ↦ interval L (k j.castSucc) (k j.succ)
  obtain ⟨hk, hR, hsA, hA, hY, hYC, hJ, hsum⟩ :=
    five_region_original_bond_data L q k1 k2 k3 k4 h12 h23 h34 h4L h hs h0 h1
  obtain ⟨e, x, hx, hxe, he, hclip⟩ :=
    Matrix.exists_disjoint_regional_clipping_structure hq R A (fun j ↦ (I j).card)
      hR hsA (fun j ↦ (hA j).1) (fun j ↦ (hA j).2) Y J.card hY hYC
  obtain ⟨hBraw, _hx0, _hc0, _ho0, _hcap0, _hnorm0,
      E, z, hz, hHz, hE, hE0, hEC⟩ := hclip 0 le_rfl ∅
  let Braw := ∑ j, (A j - (e j : ℂ) • 1)
  let H := (∑ i, h i) - (((∑ j, e j) : ℝ) : ℂ) • 1
  have hHY : H = Braw + Y := by
    dsimp only [H, Braw]
    rw [hsum, Finset.sum_sub_distrib]
    push_cast
    rw [Finset.sum_smul]
    abel
  have hBraw' : Braw.PosSemidef := by simpa only [Finset.notMem_empty, ite_false] using hBraw
  have hHz' : H *ᵥ z = (E : ℂ) • z := by
    rw [hHY]
    simpa only [Finset.notMem_empty, ite_false] using hHz
  have hE' : (H - (E : ℂ) • 1).PosSemidef := by
    rw [hHY]
    simpa only [Finset.notMem_empty, ite_false] using hE
  have hHpos : H.PosSemidef := by
    rw [hHY]
    exact hBraw'.add hY
  let hH := hHpos.isHermitian
  refine ⟨hJ, e, x, z, E, hx, hxe, he, hHY, hBraw', hz, hHz', hE', hE0, hEC, hH, ?_⟩
  intro S p t m hpl hpu ht hm B D G
  have hcomm : Pairwise fun i j : Fin 5 ↦ Commute (A i) (A j) :=
    pairwise_commute_sum_internal_consecutive_regions k hk h hs
  obtain ⟨hBpos, hBle, hBA, hproj⟩ := softTruncation_commuting_family_bounds A e p S
    (fun j ↦ (hA j).1.isHermitian) (fun j ↦ le_iff.mpr (he j)) hpl hpu hcomm t m ht hm
  change (B + (D : ℂ) • 1).PosSemidef at hBpos
  have hGshift : (G + (D : ℂ) • 1).PosSemidef := by
    convert hBpos.add hY using 1
    dsimp only [G]
    abel
  have hGH : G ≤ H := by
    rw [hHY]
    exact _root_.add_le_add hBle (le_refl Y)
  have hG : G.IsHermitian := by
    have hD : IsSelfAdjoint (D : ℂ) := by simp [IsSelfAdjoint]
    have hp := hGshift.isHermitian.sub (isHermitian_one.smul hD)
    convert hp using 1
    abel
  have : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
  obtain ⟨mu, w, hGw, hw, hGlow⟩ := hG.exists_unit_eigenvector_le
  have hmuD : -D ≤ mu := by
    have hv : (G + (D : ℂ) • 1) *ᵥ w = ((mu + D : ℝ) : ℂ) • w := by
      rw [add_mulVec, smul_mulVec, one_mulVec, hGw, Complex.ofReal_add, add_smul]
    have hp := hGshift.nonneg_of_normalized_eigenvector (mu + D) w hv hw
    linarith only [hp]
  have hmuE : mu ≤ E := by
    have hp : (H - (mu : ℂ) • 1).PosSemidef := by
      convert hGlow.add (le_iff.mp hGH) using 1
      abel
    have hv : (H - (mu : ℂ) • 1) *ᵥ z = ((E - mu : ℝ) : ℂ) • z := by
      rw [sub_mulVec, smul_mulVec, one_mulVec, hHz', Complex.ofReal_sub, sub_smul]
    exact sub_nonneg.mp (hp.nonneg_of_normalized_eigenvector (E - mu) z hv hz)
  exact ⟨mu, w, hG, hBpos, hGH, hw, hGw, hGlow, hmuD, hmuE, hmuE.trans hEC, hBA, hproj⟩

end TNLean.MPS.AreaLaw.ALVV
