/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DomainInformationReset
import TNLean.MPS.AreaLaw.DomainIntervalNeighborhoodEntropy
import QICLean.Entropy.ConditionalTwoFamilies

/-!
# Information at logarithmic separation in a finite integer domain

Separation is measured in the original integer positions. Intrinsic graph
neighborhoods provide the two outer regions used in information reset; their
entropy is bounded by the interval area law. The constants are uniform over
the domain, Hamiltonian, global ground state and the chosen regions.

Extension of the chain lemma in the TNLean one-dimensional note, `lem:logsep`,
`part2a_mps_information.tex`, lines 472–488, in the finite-domain setting of
`part0_preamble.tex`, lines 191–215.
-/

open QuantumCircuit

namespace TNLean.MPS.AreaLaw

/-- A finite intrinsic distance bounds the physical integer separation.
This auxiliary estimate makes no assertion across disconnected components.
Source: TNLean note, `part0_preamble.tex`, lines 191–199. -/
private theorem abs_sitePos_sub_le_of_edist_le
    {Λ : Finset ℤ} (x y : Fin Λ.card) (m : ℕ)
    (hxy : (domainGraph Λ).edist x y ≤ (m : ℕ∞)) :
    |(sitePos Λ x : ℝ) - (sitePos Λ y : ℝ)| ≤ (m : ℝ) := by
  obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top
    (ne_top_of_le_ne_top (by simp) hxy)
  have hlen : w.length ≤ m := by exact_mod_cast (hw.le.trans hxy)
  have hh := sitePos_sub_val_of_walk w
  have h1 : sitePos Λ x - sitePos Λ y ≤ (m : ℤ) := by omega
  have h2 : sitePos Λ y - sitePos Λ x ≤ (m : ℤ) := by omega
  apply abs_sub_le_iff.mpr
  constructor <;> exact_mod_cast (by assumption)

/-- A union of at most k₀ relative intervals has polynomially small mutual
information with a region separated in the original physical integer positions.
This extends the chain lemma in the TNLean note, Lemma lem:logsep,
part2a_mps_information.tex, lines 472–488,
in the finite-domain setting of part0_preamble.tex, lines 191–215. -/
theorem DomainHamiltonian.mutualInformation_le_of_logarithmic_separation
    (q : ℕ) (hq : 1 ≤ q) (R : ℕ) (J Δ : ℝ) (hΔ : 0 < Δ)
    (p : ℝ) (hp : 0 < p) (k₀ : ℕ) (hk₀ : 1 ≤ k₀) :
    ∃ (Dp : ℝ) (L₀ : ℕ), 0 < Dp ∧ 1 ≤ L₀ ∧
      ∀ (Λ : Finset ℤ), L₀ ≤ Λ.card →
      ∀ (h : DomainHamiltonian Λ q R J)
        (Ω : EuclideanSpace ℂ (Fin Λ.card → Fin q)) (E₀ : ℝ),
        Matrix.IsGappedGroundState h.operator E₀ Ω Δ →
        ∀ T E : Finset (Fin Λ.card),
          (∃ (n : ℕ) (a z : Fin n → ℕ), n ≤ k₀ ∧
            T = Finset.univ.biUnion (fun i ↦ interval Λ.card (a i) (z i))) →
          (∀ x ∈ T, ∀ y ∈ E,
            Dp * Real.log (Λ.card : ℝ) ≤
              |(sitePos Λ x : ℝ) - (sitePos Λ y : ℝ)|) →
          FiniteProduct.mutualInformation (fun _ : Fin Λ.card ↦ Fin q) Ω T E ≤
            (Λ.card : ℝ) ^ (-p) := by
  classical
  let c := max 0 (chainIntervalEntropyBound q R J Δ)
  have hc : 0 ≤ c := le_max_left _ _
  let b := 4 * (k₀ : ℝ) * c
  have hk₀r : 0 ≤ (k₀ : ℝ) := by exact_mod_cast (Nat.zero_le 1).trans hk₀
  have hb : 0 ≤ b := mul_nonneg (mul_nonneg (by norm_num) hk₀r) hc
  obtain ⟨Cp, Lreset, hCp, hLreset, hreset⟩ :=
    DomainHamiltonian.information_reset q hq R J Δ hΔ p hp
  refine ⟨3 * Cp * (2 + b) + 4, max Lreset ⌈Real.exp 1⌉₊,
    by positivity, hLreset.trans (le_max_left _ _), ?_⟩
  intro Λ hL h Ω E₀ hgs T E hT hdist
  have hLn : 1 ≤ Λ.card := hLreset.trans ((le_max_left _ _).trans hL)
  have hL1 : (1 : ℝ) ≤ Λ.card := by exact_mod_cast hLn
  have hLexp : Real.exp 1 ≤ (Λ.card : ℝ) :=
    (Nat.le_ceil (Real.exp 1)).trans (by exact_mod_cast (le_max_right _ _).trans hL)
  have hlog : 1 ≤ Real.log (Λ.card : ℝ) :=
    (Real.le_log_iff_exp_le (zero_lt_one.trans_le hL1)).mpr hLexp
  let w := Cp * (1 + b + Real.log (Λ.card : ℝ))
  have hw : 0 < w := mul_pos hCp (by linarith)
  have hsep : 3 * w + 4 ≤ (3 * Cp * (2 + b) + 4) * Real.log (Λ.card : ℝ) := by
    dsimp only [w]
    nlinarith only [mul_nonneg (show 0 ≤ 3 * Cp * (1 + b) + 4 by positivity)
      (sub_nonneg.mpr hlog)]
  let n := ⌈w + 1⌉₊
  have hnlo : w + 1 ≤ (n : ℝ) := Nat.le_ceil _
  have hnhi : (n : ℝ) < w + 2 := by
    simpa only [add_assoc, one_add_one_eq_two] using Nat.ceil_lt_add_one (by linarith : 0 ≤ w + 1)
  let N := fun (j : ℕ) (S : Finset (Fin Λ.card)) ↦
    S.biUnion (fun x ↦ graphBall (domainGraph Λ) x j)
  let D := N n T
  let C := (N (2 * n) T)ᶜ
  have hDC : Disjoint D C := by
    apply Finset.disjoint_left.mpr
    intro y hyD hyC
    obtain ⟨x, hx, hxy⟩ := Finset.mem_biUnion.mp hyD
    exact (Finset.mem_compl.mp hyC) (Finset.mem_biUnion.mpr
      ⟨x, hx, mem_graphBall.mpr ((mem_graphBall.mp hxy).trans
        (by exact_mod_cast (show n ≤ 2 * n by omega)))⟩)
  have hTD : T ⊆ D := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨x, hx, mem_graphBall.mpr (by simp)⟩
  have hEC : E ⊆ C := by
    intro y hy
    apply Finset.mem_compl.mpr
    intro hyN
    obtain ⟨x, hx, hxy⟩ := Finset.mem_biUnion.mp hyN
    have hcoord := abs_sitePos_sub_le_of_edist_le x y (2 * n) (mem_graphBall.mp hxy)
    push_cast at hcoord
    linarith only [hcoord, hdist x hx y hy, hsep, hnhi, hw]
  have hmarginT : ∀ x ∈ T, ∀ y : Fin Λ.card, y ∉ D → ∀ d : ℕ,
      (domainGraph Λ).edist x y = (d : ℕ∞) → w < (d : ℝ) := by
    intro x hx y hy d hd
    by_contra hnot
    have hdn : d ≤ n := by exact_mod_cast (show (d : ℝ) ≤ n by linarith only [not_lt.mp hnot, hnlo])
    exact hy (Finset.mem_biUnion.mpr ⟨x, hx, mem_graphBall.mpr (hd ▸ (by exact_mod_cast hdn))⟩)
  have hmarginE : ∀ e ∈ E, ∀ y : Fin Λ.card, y ∉ C → ∀ d : ℕ,
      (domainGraph Λ).edist e y = (d : ℕ∞) → w < (d : ℝ) := by
    intro e he y hy d hd
    have hyN : y ∈ N (2 * n) T := by simpa only [C, Finset.mem_compl, not_not] using hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_biUnion.mp hyN
    have htri : (domainGraph Λ).edist x e ≤ ((2 * n + d : ℕ) : ℕ∞) := by
      calc
        _ ≤ (domainGraph Λ).edist x y + (domainGraph Λ).edist y e := (domainGraph Λ).edist_triangle
        _ ≤ ((2 * n : ℕ) : ℕ∞) + (d : ℕ∞) := add_le_add (mem_graphBall.mp hxy)
          (by rw [SimpleGraph.edist_comm, hd])
        _ = _ := by simp only [Nat.cast_add]
    have hcoord := abs_sitePos_sub_le_of_edist_le x e (2 * n + d) htri
    push_cast at hcoord
    linarith only [hcoord, hdist x hx e he, hsep, hnhi]
  have hJ : 0 ≤ J := h.norm_bound_nonneg ⟨0, hLn⟩
  have hD : Entropy.regionEntropy (n := fun _ : Fin Λ.card ↦ q) D Ω ≤ (k₀ : ℝ) * c := by
    obtain ⟨n₀, a, z, hn₀, hT⟩ := hT
    have hbound := h.regionEntropy_neighborhood_biUnion_intervals_le hq hJ hΔ hgs
      (Finset.univ : Finset (Fin n₀)) a z n
    rw [← hT, Finset.card_univ, Fintype.card_fin] at hbound
    exact hbound.trans ((mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hn₀) hc))
  have hMI : FiniteProduct.mutualInformation (fun _ : Fin Λ.card ↦ Fin q) Ω D C ≤ b := by
    have hbound := FiniteProduct.mutualInformation_le_two_entropy
      (fun _ : Fin Λ.card ↦ Fin q) Ω hgs.1 D C hDC
    rw [← Entropy.regionEntropy_eq_entropy] at hbound
    dsimp only [b]
    nlinarith only [hbound, hD, mul_nonneg hk₀r hc]
  exact hreset Λ ((le_max_left _ _).trans hL) h Ω E₀ hgs
    D C T E hDC hTD hEC b hMI hmarginT hmarginE

end TNLean.MPS.AreaLaw
