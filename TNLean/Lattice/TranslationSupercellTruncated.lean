/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GaussianFilteredTruncation
import TNLean.Lattice.TranslationSupercellCommutator

/-!
# Low-energy commutators of the truncated terms of a translation-invariant lattice

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3, `proj3new.tex`),
uses the truncated terms `M_i` of eq. `mid` (lines 285–307): the Gaussian filter of `h_i` under
the truncated Hamiltonian `H_{s_i} = ∑_{k ∈ s_i} h_k` of the terms near `i`. Each `M_i` acts on a
bounded set `K_i` of sites near `i`. Eq. `blecm` bounds the low-energy commutator of two such
operators directly in the separation of their supports, by filtering `M_i` a second time
(lines 1555–1601). For a translation-invariant lattice with momenta of bounded denominator, a
supercell translation carries `j` to a distance of order the linear size `n` from `i`, so the
low-energy commutator of the `M_i` is exponentially small in `n` (lines 1603–1641).

The truncations are taken covariant, `s_{g•k} = g • s_k`, as the terms are: then
`M_{g•k} = P_g M_k P_g†` (`truncatedTerm_smul`).

## Main results

* `TNLean.Lattice.truncatedTerm_smul`: covariance of the truncated terms.
* `TNLean.Lattice.norm_groundCompression_truncatedTerm_commutator_le_of_momenta`: the
  low-energy commutator of the truncated terms at `i` and `j` obeys the bound of eq. `blecm` at
  every separation `l` with `2R' + l + N ≤ n / 2`, where `R'` bounds the diameters of the
  supports `K_k`. Taking `l = n / 2 - N - 2R'` makes it exponentially small in `n`.
-/

open Matrix GaussianFilter QuantumCircuit
open scoped Matrix.Norms.L2Operator

namespace TNLean.Lattice

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The truncated term** `M_k`: the Gaussian filter of `h_k` under the truncated Hamiltonian
`∑_{k' ∈ s_k} h_{k'}`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `mid`
(lines 285–307). -/
noncomputable def truncatedTerm (r ΔE : ℝ) (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (s : ι → Finset ι) (k : ι) : Matrix (ι → Fin d) (ι → Fin d) ℂ :=
  gaussianFilteredTerm r ΔE (∑ k' ∈ s k, h k') (h k)

/-- **Covariance of the truncated terms.** If the terms are covariant,
`h_{g•k} = P_g h_k P_g†`, and so are the truncations, `s_{g•k} = g • s_k`, then
`M_{g•k} = P_g M_k P_g†`. -/
theorem truncatedTerm_smul {Γ : Type*} [Group Γ] [MulAction Γ ι] (r ΔE : ℝ)
    {h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ} (hHerm : ∀ k, (h k).IsHermitian)
    (hcov : ∀ (g : Γ) k, h (g • k) = sitePermMatrix d g * h k * (sitePermMatrix d g)ᴴ)
    {s : ι → Finset ι} (hs : ∀ (g : Γ) k, s (g • k) = (s k).map (MulAction.toPerm g).toEmbedding)
    (g : Γ) (k : ι) :
    truncatedTerm r ΔE h s (g • k) =
      sitePermMatrix d g * truncatedTerm r ΔE h s k * (sitePermMatrix d g)ᴴ := by
  have hsum : ∑ k' ∈ s (g • k), h k' =
      sitePermMatrix d g * (∑ k' ∈ s k, h k') * (sitePermMatrix d g)ᴴ := by
    rw [hs, Finset.sum_map, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k' _ ↦ hcov g k'
  rw [truncatedTerm, hsum, hcov, gaussianFilteredTerm_conj r ΔE
    (sitePermMatrix_mem_unitaryGroup d g) (Matrix.isHermitian_sum _ fun k' _ ↦ hHerm k'),
    truncatedTerm]

/-- **The low-energy commutator of the truncated terms is exponentially small in the linear
size.** Let the terms `h_k` be indexed by the sites, with `h_k` acting on `X_k ∋ k` of diameter at
most `R`, covariant under an abelian group `Γ` of translations, and let every eigenvalue of
`H = ∑_k h_k` equal `E₀` or be at least `E₀ + ΔE`. Let the momenta have denominator `N`, and let
`π`, `e` be a cell coordinate with `n` cells and the unit translation along it. Let the
truncations `s_k` be covariant, with the terms of `s_k` and `h_k` itself acting on a set
`K_k ∋ k` of diameter at most `R'`. Then for every `l` with `2R' + l + N ≤ n / 2`, the low-energy
commutator of the truncated terms `M_i`, `M_j` of eq. `mid` obeys the bound of eq. `blecm` at
separation `l`. This is the conclusion of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1603–1641, for the source's `M_i`, with eq. `blecm` (lines 1555–1601) applied to the
`M_i` themselves. -/
theorem norm_groundCompression_truncatedTerm_commutator_le_of_momenta [NeZero d]
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
    {r q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE) (hH : (∑ k, h k).IsHermitian)
    {E₀ : ℝ} (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k)
    {N : ℕ} (hN : 0 < N)
    (hden : ∀ χ : Γ →* ℂ, momentumSector Γ d (∑ k, h k) E₀ χ ≠ ⊥ → ∀ g, χ g ^ N = 1)
    {n : ℕ} [NeZero n] (π : ι → ZMod n)
    (hπ : ∀ u v, G.Adj u v → (π v - π u).valMinAbs.natAbs ≤ 1)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1)
    (s : ι → Finset ι)
    (hs : ∀ (g : Γ) k, s (g • k) = (s k).map (MulAction.toPerm g).toEmbedding)
    (K : ι → Finset ι) (hsK : ∀ k, ∀ k' ∈ s k, X k' ⊆ K k) (hXK : ∀ k, X k ⊆ K k)
    (R' : ℕ) (hKdiam : ∀ k, ∀ x ∈ K k, ∀ z ∈ K k, G.edist x z ≤ R')
    (i j : ι) (l : ℕ) (hl : 2 * R' + l + N ≤ n / 2) {T : ℝ} (hT : 0 ≤ T) :
    ‖groundCompression (∑ k, h k) E₀ (truncatedTerm r ΔE h s i) *
          groundCompression (∑ k, h k) E₀ (truncatedTerm r ΔE h s j) -
        groundCompression (∑ k, h k) E₀ (truncatedTerm r ΔE h s j) *
          groundCompression (∑ k, h k) E₀ (truncatedTerm r ΔE h s i)‖ ≤
      2 * ‖truncatedTerm r ΔE h s j‖ *
          ((2 + 4 * |b₀| * Real.exp (2 * R)) * ((K i).card : ℝ) ^ 2 *
              ‖truncatedTerm r ΔE h s i‖ * Kg *
              (2 ^ kg * kg.factorial * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) *
              Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * T - l / 2) +
            2 * ‖truncatedTerm r ΔE h s i‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q))) +
        2 * ‖truncatedTerm r ΔE h s i‖ * ‖truncatedTerm r ΔE h s j‖ * Real.exp (-q / 2) := by
  set M := truncatedTerm r ΔE h s
  have hInv := isSiteInvariant_sum_of_covariant d h hcov
  have hkK (k : ι) : k ∈ K k := hXK k (hX k)
  have hMsupp (k : ι) : M k ∈ supportedOperators d (K k : Set ι) :=
    gaussianFilteredTerm_mem_supportedOperators r ΔE
      (Submodule.sum_mem _ fun k' hk' ↦
        supportedOperators_mono (by exact_mod_cast hsK k k' hk') (hSupport k'))
      (supportedOperators_mono (by exact_mod_cast hXK k) (hSupport k))
  obtain ⟨g, hg, hdist⟩ := exists_mem_supercell_lt_edist_add hN hden G π hπ e he i j
  have hsep : Disjoint (((K i).biUnion fun x => graphBall G x l : Finset ι) : Set ι)
      (K (g • j) : Set ι) := by
    refine Set.disjoint_left.mpr fun z hz hz' ↦ ?_
    obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hz)
    have h1 := hKdiam i i (hkK i) x hx
    have h2 := mem_graphBall.mp hzx
    have h3 := hKdiam (g • j) z (Finset.mem_coe.mp hz') (g • j) (hkK _)
    have hle : G.edist i (g • j) ≤ ((2 * R' + l : ℕ) : ℕ∞) :=
      calc G.edist i (g • j) ≤ G.edist i x + G.edist x z + G.edist z (g • j) :=
            SimpleGraph.edist_triangle.trans (by gcongr; exact SimpleGraph.edist_triangle)
        _ ≤ R' + l + R' := add_le_add (add_le_add h1 h2) h3
        _ = ((2 * R' + l : ℕ) : ℕ∞) := by push_cast; ring
    have hlt : ((n / 2 : ℕ) : ℕ∞) < ((2 * R' + l + N : ℕ) : ℕ∞) := by
      calc ((n / 2 : ℕ) : ℕ∞) < G.edist i (g • j) + N := hdist
        _ ≤ ((2 * R' + l : ℕ) : ℕ∞) + N := by gcongr
        _ = ((2 * R' + l + N : ℕ) : ℕ∞) := by push_cast; ring
    have := ENat.natCast_lt_natCast.mp hlt
    omega
  have hMg : M (g • j) = sitePermMatrix d g * M j * (sitePermMatrix d g)ᴴ :=
    truncatedTerm_smul r ΔE hHerm hcov hs g j
  have hcomp : groundCompression (∑ k, h k) E₀ (M (g • j)) =
      groundCompression (∑ k, h k) E₀ (M j) := by
    rw [hMg]
    exact groundCompression_sitePermMatrix_conj (supercell Γ d (∑ k, h k) E₀)
      (fun g hg v hv ↦ sitePermMatrix_mulVec_eq_of_mem_supercell hInv hg v hv) hg _
  have hmain := norm_groundCompression_commutator_le_graphNeighborhood G X id hX h hHerm
    hSupport R hDiam vR hCard b₀ hBudget Kg kg hGrowth hq hΔE hH hgap (K i) (hMsupp i) l _ hsep
    (hMsupp (g • j)) hT
  rwa [hcomp, hMg, norm_sitePermMatrix_mul_mul_conjTranspose] at hmain

end TNLean.Lattice
