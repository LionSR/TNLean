/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.TranslationSupercellDecay
import TNLean.Lattice.TranslationSupercellSpacing

/-!
# Low-energy commutators of a translation-invariant lattice

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1603–1641), shows that for a translationally invariant system on a `d`-dimensional
lattice whose ground-state momenta have bounded denominators, the low-energy commutator
`[P M_i P, P M_j P]` of the filtered terms is exponentially small in the linear size of the
system. The argument has three steps, each formalized separately:

* the commutator is unchanged when `j` is translated by a supercell
  (`groundCompression_commutator_eq_of_mem_supercell`), and the supercell is the subgroup fixing
  the ground space (`mem_supercell_iff`);
* some supercell translation carries `j` to a distance of order the linear size `n` from `i`
  (`exists_mem_supercell_lt_edist_add`);
* the low-energy commutator decays in the separation (eq. `blecm`,
  `norm_groundCompression_commutator_le_of_supercell_separation`).

## Main results

* `TNLean.Lattice.norm_groundCompression_commutator_le_of_momenta`: for terms indexed by the
  sites, covariant under an abelian group of translations, with momenta of denominator `N`, the
  low-energy commutator at `i` and `j` obeys the bound of eq. `blecm` at every separation `l`
  with `2R + l + N ≤ n / 2`. Taking `l = n / 2 - N - 2R` makes it exponentially small in `n`.
-/

open Matrix GaussianFilter QuantumCircuit
open scoped Matrix.Norms.L2Operator

namespace TNLean.Lattice

/-- Conjugation by a site permutation preserves the operator norm. -/
theorem norm_sitePermMatrix_mul_mul_conjTranspose {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : Type*} [Group Γ] [MulAction Γ V] (d : ℕ) (g : Γ)
    (A : Matrix (V → Fin d) (V → Fin d) ℂ) :
    ‖sitePermMatrix d g * A * (sitePermMatrix d g)ᴴ‖ = ‖A‖ := by
  let U : unitary (Matrix (V → Fin d) (V → Fin d) ℂ) :=
    ⟨sitePermMatrix d g, sitePermMatrix_mem_unitaryGroup d g⟩
  calc ‖sitePermMatrix d g * A * (sitePermMatrix d g)ᴴ‖
      = ‖(U : Matrix _ _ ℂ) * A * ((star U : unitary _) : Matrix _ _ ℂ)‖ := by
        rfl
    _ = ‖A‖ := by rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The low-energy commutator of a translation-invariant lattice is exponentially small in its
linear size.** Let the terms `h_k` be indexed by the sites, with `h_k` acting on a set `X_k ∋ k`
of diameter at most `R` in the lattice graph `G`, as in eq. `blecm`. Let an abelian group `Γ` of
translations act on the sites with `h_{g•k} = P_g h_k P_g†` (Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 862 and 1603–1613), and let every eigenvalue of
`H = ∑_k h_k` equal `E₀` or be at least `E₀ + ΔE`. Suppose the momenta have denominator `N`:
`χ(g)^N = 1` for every character with a nonzero momentum sector (lines 1620–1625). Let `π` be the
cell coordinate along one lattice direction, with `n` cells, such that edges join cells at most
one apart, and let `e` translate by one cell in that direction. Then for every `l` with
`2R + l + N ≤ n / 2`, the low-energy commutator of the filtered terms at `i` and `j` obeys the
bound of eq. `blecm` at separation `l` with the norms of `h_i` and `h_j`. This is the
conclusion of lines 1634–1641. -/
theorem norm_groundCompression_commutator_le_of_momenta [NeZero d]
    (G : SimpleGraph ι) (X : ι → Finset ι) (hX : ∀ k, k ∈ X k)
    (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ k, (h k).IsHermitian)
    (hSupport : ∀ k, h k ∈ supportedOperators d (X k : Set ι))
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ X k, ∀ z ∈ X k, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ k, (X k).card ≤ vR)
    (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ X j), ‖h j‖ ≤ b₀)
    {Γ : Type*} [CommGroup Γ] [MulAction Γ ι]
    (hcov : ∀ (g : Γ) k, h (g • k) = sitePermMatrix d g * h k * (sitePermMatrix d g)ᴴ)
    (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {r q ΔE : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) (hΔE : 0 < ΔE) (hH : (∑ k, h k).IsHermitian)
    {E₀ : ℝ} (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k)
    {N : ℕ} (hN : 0 < N)
    (hden : ∀ χ : Γ →* ℂ, momentumSector Γ d (∑ k, h k) E₀ χ ≠ ⊥ → ∀ g, χ g ^ N = 1)
    {n : ℕ} [NeZero n] (π : ι → Fin n)
    (hπ : ∀ u v, G.Adj u v → SimpleGraph.ringNorm (π v - π u) ≤ 1)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1)
    (i j : ι) (l : ℕ) (hl : 2 * R + l + N ≤ n / 2) {T : ℝ} (hT : 0 ≤ T) :
    ‖groundCompression (∑ k, h k) E₀ (gaussianFilteredTerm r ΔE (∑ k, h k) (h i)) *
          groundCompression (∑ k, h k) E₀ (gaussianFilteredTerm r ΔE (∑ k, h k) (h j)) -
        groundCompression (∑ k, h k) E₀ (gaussianFilteredTerm r ΔE (∑ k, h k) (h j)) *
          groundCompression (∑ k, h k) E₀ (gaussianFilteredTerm r ΔE (∑ k, h k) (h i))‖ ≤
      2 * ‖h j‖ *
          ((2 + 4 * |b₀| * Real.exp (2 * R)) * ((X i).card : ℝ) ^ 2 * ‖h i‖ * Kg *
              (2 ^ kg * kg.factorial * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) *
              Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * T - l / 2) +
            2 * ‖h i‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q))) +
        2 * ‖h i‖ * ‖h j‖ * Real.exp (-q / 2) := by
  have hInv := isSiteInvariant_sum_of_covariant d h hcov
  obtain ⟨g, hg, hdist⟩ := exists_mem_supercell_lt_edist_add hN hden G π hπ e he i j
  have hsep : Disjoint (((X i).biUnion fun x => graphBall G x l : Finset ι) : Set ι)
      (X (g • j) : Set ι) := by
    refine Set.disjoint_left.mpr fun z hz hz' ↦ ?_
    obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hz)
    have h1 := hDiam i i (hX i) x hx
    have h2 := mem_graphBall.mp hzx
    have h3 := hDiam (g • j) z (Finset.mem_coe.mp hz') (g • j) (hX _)
    have hle : G.edist i (g • j) ≤ ((2 * R + l : ℕ) : ℕ∞) :=
      calc G.edist i (g • j) ≤ G.edist i x + G.edist x z + G.edist z (g • j) :=
            SimpleGraph.edist_triangle.trans (by gcongr; exact SimpleGraph.edist_triangle)
        _ ≤ R + l + R := add_le_add (add_le_add h1 h2) h3
        _ = ((2 * R + l : ℕ) : ℕ∞) := by push_cast; ring
    have hlt : ((n / 2 : ℕ) : ℕ∞) < ((2 * R + l + N : ℕ) : ℕ∞) := by
      calc ((n / 2 : ℕ) : ℕ∞) < G.edist i (g • j) + N := hdist
        _ ≤ ((2 * R + l : ℕ) : ℕ∞) + N := by gcongr
        _ = ((2 * R + l + N : ℕ) : ℕ∞) := by push_cast; ring
    have := ENat.natCast_lt_natCast.mp hlt
    omega
  have hmain := norm_groundCompression_commutator_le_of_supercell_separation G X id hX h hHerm
    hSupport R hDiam vR hCard b₀ hBudget hcov Kg kg hGrowth hr hq hΔE hH hgap
    (supercell Γ d (∑ k, h k) E₀)
    (fun g hg v hv ↦ sitePermMatrix_mulVec_eq_of_mem_supercell hInv hg v hv) hg i j l hsep hT
  rwa [hcov, norm_sitePermMatrix_mul_mul_conjTranspose] at hmain

end TNLean.Lattice
