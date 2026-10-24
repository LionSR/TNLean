/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AreaLaw
import TNLean.MPS.AreaLaw.InformationReset
import TNLean.MPS.AreaLaw.IntervalNeighborhoodEntropy
import QICLean.Entropy.ConditionalTwoFamilies

/-!
# Information at logarithmic separation

The interval area law bounds the mutual information of an enlarged finite
interval union with its exterior by a uniform constant. Information reset
then gives polynomially small mutual information at logarithmic separation.
The constants precede the chain, Hamiltonian, state and regions. Empty and
overlapping interval components are permitted.

**Scope restriction (contiguous chains):** The sites are `Fin L`; the broader
finite-domain reading is recorded in
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

Source: TNLean one-dimensional note, Lemma `lem:logsep`,
`part2a_mps_information.tex`, lines 472–488.
-/

namespace TNLean.MPS.AreaLaw

/-- A union of at most `k₀` intervals has polynomially small mutual information
with every region at logarithmic separation. Source: TNLean note,
Lemma `lem:logsep`, `part2a_mps_information.tex:472–488`. -/
theorem ChainHamiltonian.mutualInformation_le_of_logarithmic_separation
    (q : ℕ) (hq : 1 ≤ q) (R : ℕ) (J Δ : ℝ) (hΔ : 0 < Δ)
    (p : ℝ) (hp : 0 < p) (k₀ : ℕ) (hk₀ : 1 ≤ k₀) :
    ∃ (Dp : ℝ) (L₀ : ℕ), 0 < Dp ∧ 1 ≤ L₀ ∧
      ∀ (L : ℕ), L₀ ≤ L →
      ∀ (h : ChainHamiltonian L q R J)
        (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (E₀ : ℝ),
        Matrix.IsGappedGroundState h.operator E₀ Ω Δ →
        ∀ T E : Finset (Fin L),
          (∃ (n : ℕ) (a z : Fin n → ℕ), n ≤ k₀ ∧
            T = Finset.univ.biUnion (fun i ↦ interval L (a i) (z i))) →
          (∀ x ∈ T, ∀ y ∈ E,
            Dp * Real.log (L : ℝ) ≤ (Nat.dist x.val y.val : ℝ)) →
          FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω T E ≤
            (L : ℝ) ^ (-p) := by
  classical
  let c := max 0 (chainIntervalEntropyBound q R J Δ)
  have hc : 0 ≤ c := le_max_left _ _
  let b := 4 * (k₀ : ℝ) * c
  have hk₀r : 0 ≤ (k₀ : ℝ) := by exact_mod_cast (Nat.zero_le 1).trans hk₀
  have hb : 0 ≤ b := mul_nonneg (mul_nonneg (by norm_num) hk₀r) hc
  obtain ⟨Cp, Lreset, hCp, hLreset, hreset⟩ :=
    ChainHamiltonian.information_reset q hq R J Δ hΔ p hp
  refine ⟨3 * Cp * (2 + b) + 3, max Lreset ⌈Real.exp 1⌉₊,
    by positivity, hLreset.trans (le_max_left _ _), ?_⟩
  intro L hL h Ω E₀ hgs T E hT hdist
  have hLn : 1 ≤ L := hLreset.trans ((le_max_left _ _).trans hL)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hLn
  have hLexp : Real.exp 1 ≤ (L : ℝ) :=
    (Nat.le_ceil (Real.exp 1)).trans (by exact_mod_cast (le_max_right _ _).trans hL)
  have hlog : 1 ≤ Real.log (L : ℝ) :=
    (Real.le_log_iff_exp_le (zero_lt_one.trans_le hL1)).mpr hLexp
  let w := Cp * (1 + b + Real.log (L : ℝ))
  have hw : 0 < w := mul_pos hCp (by linarith)
  have hsep : 3 * w + 3 ≤ (3 * Cp * (2 + b) + 3) * Real.log (L : ℝ) := by
    dsimp only [w]
    nlinarith only [mul_nonneg (show 0 ≤ 3 * Cp * (1 + b) + 3 by positivity)
      (sub_nonneg.mpr hlog)]
  let N := fun (ρ : ℝ) (S : Finset (Fin L)) ↦
    chainNeighborhood S ρ
  let D := N (w + 1) T
  let C := (N (2 * w + 2) T)ᶜ
  have hDC : Disjoint D C := by
    apply Finset.disjoint_left.mpr
    intro y hyD hyC
    obtain ⟨x, hx, hxy⟩ := (Finset.mem_filter.mp hyD).2
    exact (Finset.mem_compl.mp hyC)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ y, x, hx, by linarith only [hxy, hw]⟩)
  have hTD : T ⊆ D := by
    intro x hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ x, x, hx, by simpa using (show 0 ≤ w + 1 by linarith only [hw])⟩
  have hEC : E ⊆ C := by
    intro y hy
    apply Finset.mem_compl.mpr
    intro hyN
    obtain ⟨x, hx, hxy⟩ := (Finset.mem_filter.mp hyN).2
    linarith only [hdist x hx y hy, hsep, hxy, hw]
  have hmarginT : ∀ x ∈ T, ∀ y : Fin L, y ∉ D →
      w < (Nat.dist x.val y.val : ℝ) := by
    intro x hx y hy
    by_contra hnot
    exact hy (Finset.mem_filter.mpr
      ⟨Finset.mem_univ y, x, hx, by linarith only [not_lt.mp hnot]⟩)
  have hmarginE : ∀ e ∈ E, ∀ y : Fin L, y ∉ C →
      w < (Nat.dist e.val y.val : ℝ) := by
    intro e he y hy
    have hyN : y ∈ N (2 * w + 2) T := by
      simpa only [C, Finset.mem_compl, not_not] using hy
    obtain ⟨x, hx, hxy⟩ := (Finset.mem_filter.mp hyN).2
    have htri : (Nat.dist x.val e.val : ℝ) ≤
        (Nat.dist x.val y.val : ℝ) + (Nat.dist e.val y.val : ℝ) := by
      exact_mod_cast (Nat.dist.triangle_inequality x.val y.val e.val).trans_eq
        (congrArg (Nat.dist x.val y.val + ·) (Nat.dist_comm y.val e.val))
    linarith only [htri, hxy, hsep, hdist x hx e he]
  have hJ : 0 ≤ J := h.norm_bound_nonneg ⟨0, hLn⟩
  have hI : ∀ a z : ℕ,
      Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L a z) Ω ≤ c :=
    fun a z ↦ (regionEntropy_interval_le hq hJ hΔ h hgs a z).trans (le_max_right _ _)
  have hD : Entropy.regionEntropy (n := fun _ : Fin L ↦ q) D Ω ≤ (k₀ : ℝ) * c := by
    obtain ⟨n, a, z, hn, hT⟩ := hT
    have hbound := regionEntropy_chainNeighborhood_biUnion_intervals_le hgs.1 hI
      (Finset.univ : Finset (Fin n)) a z (w + 1) (by linarith only [hw])
    dsimp only at hbound
    change Entropy.regionEntropy (n := fun _ : Fin L ↦ q)
      (N (w + 1) (Finset.univ.biUnion (fun i ↦ interval L (a i) (z i)))) Ω ≤
        ((Finset.univ : Finset (Fin n)).card : ℝ) * c at hbound
    rw [← hT, Finset.card_univ, Fintype.card_fin] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hc)
  have hMI : FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω D C ≤ b := by
    have hbound := FiniteProduct.mutualInformation_le_two_entropy
      (fun _ : Fin L ↦ Fin q) Ω hgs.1 D C hDC
    rw [← Entropy.regionEntropy_eq_entropy] at hbound
    dsimp only [b]
    nlinarith only [hbound, hD, mul_nonneg hk₀r hc]
  exact hreset L ((le_max_left _ _).trans hL) h Ω E₀ hgs
    D C T E hDC hTD hEC b hMI hmarginT hmarginE

end TNLean.MPS.AreaLaw
