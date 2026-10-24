/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.TranslationSupercell

/-!
# Decay of low-energy commutators across supercell translations

Let a group `G` act on the sites of a finite graph and on the index set of the local terms
`h_k`, covariantly: `h_{g•k} = P_g h_k P_g†`. Let `S` be a subgroup whose site permutations
leave every ground vector of `H = ∑_k h_k` unchanged. Hastings, *Solving gapped Hamiltonians
locally* (arXiv:cond-mat/0508554v3, `References/cond-mat_0508554/proj3new.tex`, lines
1634–1641) concludes the translation-invariant case as follows: the low-energy commutator
`[P M_i P, P M_j P]` equals `[P M_i P, P M_{g•j} P]` for every `g ∈ S`, and choosing `g` that
places `g • j` far from `i` makes it small in that distance, since the low-energy commutator
decays in the separation (eq. `blecm`).

## Main results

* `TNLean.Lattice.norm_groundCompression_commutator_le_of_supercell_separation`: if `g ∈ S`
  and the support of `h_{g•j}` is disjoint from the sites within graph distance `l` of the
  support of `h_i`, then `‖[P M_i P, P M_j P]‖` is at most the bound of eq. `blecm` at
  separation `l`, with the norm of `h_{g•j}`.

When every `l`-neighbourhood of a support can be avoided by some `g ∈ S` with `l` of order the
linear size of the system, this bound is exponentially small in that size, which is the
source's conclusion; that geometric choice is left to the application.

**Scope restriction (supercell):** the source assumes that the momenta of the ground states are
rational multiples of `2π` whose denominators do not depend on the system size (lines
1620–1625), and derives from this a supercell whose translations leave every ground state
unchanged (lines 1626–1630). The theorem here instead assumes such a subgroup `S` directly.
Documented in `docs/paper-gaps/hastings05_translation_supercell.tex`.
-/

open Matrix GaussianFilter QuantumCircuit
open scoped Matrix.Norms.L2Operator

namespace TNLean.Lattice

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι) (ha : ∀ k, a k ∈ X k)
  (h : κ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ k, (h k).IsHermitian)
  (hSupport : ∀ k, h k ∈ supportedOperators d (X k : Set ι))
  (R : ℕ) (hDiam : ∀ k, ∀ x ∈ X k, ∀ z ∈ X k, G.edist x z ≤ R)
  (vR : ℕ) (hCard : ∀ k, (X k).card ≤ vR)
  (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ X j), ‖h j‖ ≤ b₀)

include ha hHerm hSupport hDiam hCard hBudget

/-- **The low-energy commutator is small when a supercell translate is far away.** Let the
terms be covariant under the action of `Γ`, `h_{g•k} = P_g h_k P_g†` (Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, line 862), let every eigenvalue of `H = ∑_k h_k`
equal `E₀` or be at least `E₀ + ΔE`, and let `S ≤ Γ` leave every ground vector unchanged
(lines 1626–1628). If `g ∈ S` and the support of `h_{g•j}` is disjoint from the sites within
graph distance `l` of the support of `h_i`, then the low-energy commutator of the filtered terms
`M_k` at `i` and `j` obeys the bound of eq. `blecm` at separation `l`, for all `q ≥ 0` and
`T ≥ 0`. This is the step of lines 1634–1641. -/
theorem norm_groundCompression_commutator_le_of_supercell_separation [NeZero d]
    {Γ : Type*} [Group Γ] [MulAction Γ ι] [MulAction Γ κ]
    (hcov : ∀ (g : Γ) k, h (g • k) = sitePermMatrix d g * h k * (sitePermMatrix d g)ᴴ)
    (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {r q ΔE : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) (hΔE : 0 < ΔE) (hH : (∑ k, h k).IsHermitian)
    {E₀ : ℝ} (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k)
    (S : Subgroup Γ)
    (hS : ∀ g ∈ S, ∀ v ∈ groundEigenspace (∑ k, h k) E₀,
      sitePermMatrix d g *ᵥ WithLp.ofLp v = WithLp.ofLp v)
    {g : Γ} (hg : g ∈ S) (i j : κ) (l : ℕ)
    (hsep : Disjoint (((X i).biUnion fun x => graphBall G x l : Finset ι) : Set ι)
      (X (g • j) : Set ι))
    {T : ℝ} (hT : 0 ≤ T) :
    ‖groundCompression (∑ k, h k) E₀ (gaussianFilteredTerm r ΔE (∑ k, h k) (h i)) *
          groundCompression (∑ k, h k) E₀ (gaussianFilteredTerm r ΔE (∑ k, h k) (h j)) -
        groundCompression (∑ k, h k) E₀ (gaussianFilteredTerm r ΔE (∑ k, h k) (h j)) *
          groundCompression (∑ k, h k) E₀ (gaussianFilteredTerm r ΔE (∑ k, h k) (h i))‖ ≤
      2 * ‖h (g • j)‖ *
          ((2 + 4 * |b₀| * Real.exp (2 * R)) * ((X i).card : ℝ) ^ 2 * ‖h i‖ * Kg *
              (2 ^ kg * kg.factorial * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) *
              Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * T - l / 2) +
            2 * ‖h i‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q))) +
        2 * ‖h i‖ * ‖h (g • j)‖ * Real.exp (-q / 2) := by
  have hj : groundCompression (∑ k, h k) E₀ (h (g • j)) =
      groundCompression (∑ k, h k) E₀ (h j) := by
    rw [hcov]
    exact groundCompression_sitePermMatrix_conj S hS hg _
  rw [groundCompression_gaussianFilteredTerm hr hH, groundCompression_gaussianFilteredTerm hr hH,
    ← hj]
  exact norm_groundCompression_commutator_le_graphNeighborhood G X a ha h hHerm hSupport R hDiam
    vR hCard b₀ hBudget Kg kg hGrowth hq hΔE hH hgap (X i) (hSupport i) l _ hsep
    (hSupport (g • j)) hT

end TNLean.Lattice
