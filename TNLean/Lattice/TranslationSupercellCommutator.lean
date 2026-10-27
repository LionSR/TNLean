/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyCommutatorSum
import TNLean.Lattice.TranslationSupercellDecay
import TNLean.Lattice.TranslationSupercellSpacing

/-!
# Low-energy commutators of a translation-invariant lattice

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1603–1641), shows that for a translationally invariant system on a `d`-dimensional
lattice whose ground-state momenta have bounded denominators, the low-energy commutator
`[P M_i P, P M_j P]` is exponentially small in the linear size of the system. There `M_i` is
the truncated filtered term of eq. `mid` (lines 285–307). The argument has three steps, each
formalized separately, for the filtered terms `H_tilde_i`:

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
  This is the statement for the filtered terms `H_tilde_i`.
* `TNLean.Lattice.norm_groundCompression_commutator_le_of_norm_sub_le`: the commutator moves by
  at most `2 ε_i ‖h_j‖ + 2 ‖h_i‖ ε_j` when the filtered terms are replaced by operators within
  `ε_i`, `ε_j` of them.
* `TNLean.Lattice.norm_groundCompression_commutator_truncated_le_of_momenta`: the same bound,
  up to the truncation errors of eq. `apb`, for the truncated terms `M_i` of eq. `mid`.

For the source's truncated terms `M_i` themselves, eq. `blecm` applies to the `M_i` directly
(lines 1555–1601), which `TranslationSupercellTruncated.lean` uses to prove the exponential
smallness in `n` with no truncation error.
-/

open Matrix GaussianFilter QuantumCircuit
open scoped Matrix.Norms.L2Operator

namespace TNLean.Lattice

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
conclusion of lines 1634–1641 for the filtered terms `H_tilde_i`; for the source's truncated `M_i`,
up to the errors of eq. `apb`, see `norm_groundCompression_commutator_truncated_le_of_momenta`. -/
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
    {n : ℕ} [NeZero n] (π : ι → ZMod n)
    (hπ : ∀ u v, G.Adj u v → (π v - π u).valMinAbs.natAbs ≤ 1)
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
  obtain ⟨g, hg, hdist⟩ : ∃ g ∈ supercell Γ d (∑ k, h k) E₀,
      ((n / 2 : ℕ) : ℕ∞) < G.edist i (g • j) + N := by
    simpa only [Nat.cast_one, one_mul] using
      exists_mem_supercell_lt_edist_add hN hden G (R := 1) Nat.zero_lt_one π hπ e he i j
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
  rwa [hcov, Matrix.norm_sitePermMatrix_mul_mul_conjTranspose] at hmain


/-- **Truncated terms near filtered terms.** If the low-energy commutator of the filtered terms
`H_tilde_i`, `H_tilde_j` is at most `B`, and the operators `M_i`, `M_j` are within `ε_i`, `ε_j`
of them with `‖M_j‖ ≤ ‖h_j‖`, then `‖[P M_i P, P M_j P]‖ ≤ B + 2 ε_i ‖h_j‖ + 2 ‖h_i‖ ε_j`. -/
theorem norm_groundCompression_commutator_le_of_norm_sub_le [NeZero d]
    {H : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hH : H.IsHermitian) (E₀ r ΔE : ℝ) (hr : 0 ≤ r)
    {hi hj Mi Mj : Matrix (ι → Fin d) (ι → Fin d) ℂ} {B εi εj : ℝ}
    (hB : ‖groundCompression H E₀ (gaussianFilteredTerm r ΔE H hi) *
          groundCompression H E₀ (gaussianFilteredTerm r ΔE H hj) -
        groundCompression H E₀ (gaussianFilteredTerm r ΔE H hj) *
          groundCompression H E₀ (gaussianFilteredTerm r ΔE H hi)‖ ≤ B)
    (hεi : ‖gaussianFilteredTerm r ΔE H hi - Mi‖ ≤ εi)
    (hεj : ‖gaussianFilteredTerm r ΔE H hj - Mj‖ ≤ εj) (hMj : ‖Mj‖ ≤ ‖hj‖) :
    ‖groundCompression H E₀ Mi * groundCompression H E₀ Mj -
        groundCompression H E₀ Mj * groundCompression H E₀ Mi‖ ≤
      B + 2 * εi * ‖hj‖ + 2 * ‖hi‖ * εj := by
  have hsub (W W' : Matrix (ι → Fin d) (ι → Fin d) ℂ) :
      groundCompression H E₀ W - groundCompression H E₀ W' = groundCompression H E₀ (W - W') := by
    unfold groundCompression
    rw [map_sub, mul_sub, sub_mul]
  set A := groundCompression H E₀ (gaussianFilteredTerm r ΔE H hi)
  set Bc := groundCompression H E₀ (gaussianFilteredTerm r ΔE H hj)
  set A' := groundCompression H E₀ Mi
  set B' := groundCompression H E₀ Mj
  have key : A' * B' - B' * A' =
      (A * Bc - Bc * A) + ((A' - A) * B' - B' * (A' - A)) + (A * (B' - Bc) - (B' - Bc) * A) := by
    simp only [sub_mul, mul_sub]
    abel
  rw [key]
  have e1 : ‖(A' - A) * B' - B' * (A' - A)‖ ≤ 2 * εi * ‖hj‖ := by
    have hc := norm_groundCompression_commutator_le_two_mul H E₀
      (Mi - gaussianFilteredTerm r ΔE H hi) Mj
    rw [← hsub] at hc
    have hε : ‖Mi - gaussianFilteredTerm r ΔE H hi‖ ≤ εi := by rw [norm_sub_rev]; exact hεi
    have h1 := mul_le_mul hε hMj (norm_nonneg _) ((norm_nonneg _).trans hε)
    change ‖(A' - A) * B' - B' * (A' - A)‖ ≤ _ at hc
    nlinarith
  have e2 : ‖A * (B' - Bc) - (B' - Bc) * A‖ ≤ 2 * ‖hi‖ * εj := by
    have hc := norm_groundCompression_commutator_le_two_mul H E₀ hi
      (Mj - gaussianFilteredTerm r ΔE H hj)
    have hAeq : A = groundCompression H E₀ hi := by
      simp only [A, groundCompression_gaussianFilteredTerm hr hH]
    rw [← hsub, ← hAeq] at hc
    have hε : ‖Mj - gaussianFilteredTerm r ΔE H hj‖ ≤ εj := by rw [norm_sub_rev]; exact hεj
    have h1 := mul_le_mul (le_refl ‖hi‖) hε (norm_nonneg _) (norm_nonneg _)
    change ‖A * (B' - Bc) - (B' - Bc) * A‖ ≤ _ at hc
    nlinarith
  have h3 := norm_add₃_le (a := A * Bc - Bc * A) (b := (A' - A) * B' - B' * (A' - A))
    (c := A * (B' - Bc) - (B' - Bc) * A)
  linarith

/-- **The low-energy commutator of Hastings' truncated terms.** In the setting of
`norm_groundCompression_commutator_le_of_momenta`, let `M_k` be the filter of `h_k` under the
truncated Hamiltonian `∑_{k' ∈ s_k} h_{k'}`, the operator of eq. `mid` (Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 285–307), and let `ε_i`, `ε_j` bound
`‖H_tilde_i - M_i‖`, `‖H_tilde_j - M_j‖`, as eq. `apb` does
(`norm_gaussianFilteredTerm_sub_truncated_le`). Then `‖[P M_i P, P M_j P]‖` is at most the bound of
`norm_groundCompression_commutator_le_of_momenta` plus `2 ε_i ‖h_j‖ + 2 ‖h_i‖ ε_j`. The errors
`ε` of eq. `apb` do not decrease with `n`; for the exponential smallness in `n` of the `M_i`
see `norm_groundCompression_truncatedTerm_commutator_le_of_momenta`. -/
theorem norm_groundCompression_commutator_truncated_le_of_momenta [NeZero d]
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
    {n : ℕ} [NeZero n] (π : ι → ZMod n)
    (hπ : ∀ u v, G.Adj u v → (π v - π u).valMinAbs.natAbs ≤ 1)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1)
    (i j : ι) (l : ℕ) (hl : 2 * R + l + N ≤ n / 2) {T : ℝ} (hT : 0 ≤ T)
    (s : ι → Finset ι) {εi εj : ℝ}
    (hεi : ‖gaussianFilteredTerm r ΔE (∑ k, h k) (h i) -
      gaussianFilteredTerm r ΔE (∑ k ∈ s i, h k) (h i)‖ ≤ εi)
    (hεj : ‖gaussianFilteredTerm r ΔE (∑ k, h k) (h j) -
      gaussianFilteredTerm r ΔE (∑ k ∈ s j, h k) (h j)‖ ≤ εj) :
    ‖groundCompression (∑ k, h k) E₀ (gaussianFilteredTerm r ΔE (∑ k ∈ s i, h k) (h i)) *
          groundCompression (∑ k, h k) E₀ (gaussianFilteredTerm r ΔE (∑ k ∈ s j, h k) (h j)) -
        groundCompression (∑ k, h k) E₀ (gaussianFilteredTerm r ΔE (∑ k ∈ s j, h k) (h j)) *
          groundCompression (∑ k, h k) E₀ (gaussianFilteredTerm r ΔE (∑ k ∈ s i, h k) (h i))‖ ≤
      (2 * ‖h j‖ *
          ((2 + 4 * |b₀| * Real.exp (2 * R)) * ((X i).card : ℝ) ^ 2 * ‖h i‖ * Kg *
              (2 ^ kg * kg.factorial * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) *
              Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * T - l / 2) +
            2 * ‖h i‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q))) +
        2 * ‖h i‖ * ‖h j‖ * Real.exp (-q / 2))
        + 2 * εi * ‖h j‖ + 2 * ‖h i‖ * εj :=
  norm_groundCompression_commutator_le_of_norm_sub_le hH E₀ r ΔE hr
    (norm_groundCompression_commutator_le_of_momenta G X hX h hHerm hSupport R hDiam vR hCard b₀
      hBudget hcov Kg kg hGrowth hr hq hΔE hH hgap hN hden π hπ e he i j l hl hT) hεi hεj
    (norm_gaussianFilteredTerm_le _ _ (Matrix.isHermitian_sum _ fun k _ ↦ hHerm k) _)

end TNLean.Lattice
