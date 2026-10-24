/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.LinearAlgebra.Matrix.Permutation
import TNLean.Algebra.PermutationMatrixUnitary
import TNLean.Circuit.SitePermutationSupport
import TNLean.Lattice.GaussianFilteredTerm

/-!
# Site permutations and invariant Hamiltonians on a finite system

A group `G` acting on a finite set of sites `V` acts on the configurations `V → Fin q`, and so by
permutation matrices `P_g` on the state space. The translations of a periodic lattice and the
automorphisms of a finite graph are such actions. An operator is invariant under the action when
it commutes with every `P_g`.

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1603–1642) shows that for a translationally
invariant system the low-energy commutators of the filtered terms are exponentially small in
the linear size of the system. The argument uses three facts proved here: the Hamiltonian is
invariant when its terms are translates of one another (line 862: "a translationally invariant
Hamiltonian, `H = ∑_i H_i`, with all the `H_i` equal"); the filtered term of a translate is the
translate of the filtered term (lines 1613–1618); and translations preserve the distance on the
lattice, so that translating one of two operators changes their separation as it changes the
positions (lines 1634–1639).

## Main definitions

* `Matrix.sitePermMatrix`: the permutation of the configurations of finitely many sites induced by
  a group element acting on the sites.
* `Matrix.IsSiteInvariant`: an operator commuting with every site permutation.

## Main results

* `Matrix.sitePermMatrix_mul`, `Matrix.sitePermMatrix_mem_unitaryGroup`: `g ↦ P_g` is a unitary
  representation.
* `Matrix.sitePermMatrix_mul_mul_conjTranspose_mem_supportedOperators`: `P_g A P_g†` acts on
  `g • S` when `A` acts on `S`.
* `Matrix.isSiteInvariant_sum_of_covariant`: the sum of covariant terms is invariant;
  `Matrix.isSiteInvariant_sum_conj` is the sum of the translates of one term.
* `Matrix.gaussianFilteredTerm_sitePermMatrix_conj`: for invariant `H`, filtering commutes with
  translation.
* `Matrix.edist_smul_of_adj_iff`: an action by graph automorphisms preserves distances;
  `Matrix.cycleGraph_adj_smul`: the rotations of a ring are such an action.
-/

open Matrix GaussianFilter
open scoped Matrix.Norms.L2Operator

namespace Matrix

section SitePermutation

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Type*} [Group G] [MulAction G V]

attribute [local instance] arrowAction

/-- The unitary that moves a configuration of the sites `V` along `g`:
`(P_g ψ)(x) = ψ(x ∘ g)`, as the image of `g` under the action `(g • x)(v) = x(g⁻¹ • v)` on
configurations and the permutation-matrix homomorphism. -/
noncomputable def sitePermMatrix (q : ℕ) (g : G) : Matrix (V → Fin q) (V → Fin q) ℂ :=
  permMatrixHom (MulAction.toPermHom G (V → Fin q) g)

theorem sitePermMatrix_mul (q : ℕ) (g h : G) :
    sitePermMatrix (V := V) q (g * h) = sitePermMatrix q g * sitePermMatrix q h := by
  simp only [sitePermMatrix, map_mul]

theorem sitePermMatrix_mem_unitaryGroup (q : ℕ) (g : G) :
    sitePermMatrix (V := V) q g ∈ unitaryGroup (V → Fin q) ℂ :=
  Equiv.Perm.permMatrix_mem_unitaryGroup _

/-- Conjugating by `P_g` moves both configurations of a matrix by `g⁻¹`:
`(P_g A P_g†)(x, y) = A(x ∘ g, y ∘ g)`, where `x ∘ g` is `v ↦ x (g • v)`. -/
theorem sitePermMatrix_mul_mul_conjTranspose (q : ℕ) (g : G)
    (A : Matrix (V → Fin q) (V → Fin q) ℂ) :
    sitePermMatrix q g * A * (sitePermMatrix q g)ᴴ =
      A.submatrix (fun x v ↦ x (g • v)) (fun x v ↦ x (g • v)) := by
  ext x y
  simp only [sitePermMatrix, permMatrixHom_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, conjTranspose_permMatrix, PEquiv.mul_toMatrix_toPEquiv,
    submatrix_apply, id_eq]
  congr 1 <;> funext v
  · change x ((g⁻¹)⁻¹ • v) = x (g • v)
    rw [inv_inv]
  · change y ((g⁻¹)⁻¹ • v) = y (g • v)
    rw [inv_inv]

/-- `P_g A P_g†` acts on `g • S` when `A` acts on `S`. -/
theorem sitePermMatrix_mul_mul_conjTranspose_mem_supportedOperators (q : ℕ) (g : G)
    {S : Set V} {A : Matrix (V → Fin q) (V → Fin q) ℂ}
    (hA : A ∈ QuantumCircuit.supportedOperators q S) :
    sitePermMatrix q g * A * (sitePermMatrix q g)ᴴ ∈
      QuantumCircuit.supportedOperators q ((g • ·) '' S) := by
  rw [sitePermMatrix_mul_mul_conjTranspose]
  exact QuantumCircuit.supportedOperators_submatrix_siteEquiv (MulAction.toPerm g) hA

/-- An operator `H` on the configurations of the sites `V` is **invariant under the site action**
of `G` when it commutes with every site permutation `P_g`.

For the translations of a lattice this is the translation invariance of Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1603–1613 ("a translationally invariant,
`d`-dimensional, system on a lattice"; "the Hamiltonian is invariant under translation"). -/
def IsSiteInvariant (G : Type*) [Group G] [MulAction G V] (q : ℕ)
    (H : Matrix (V → Fin q) (V → Fin q) ℂ) : Prop :=
  ∀ g : G, Commute (sitePermMatrix q g) H

/-- An operator with `P_g H P_g† = H` for every `g` is invariant under the site action. -/
theorem isSiteInvariant_of_conj {q : ℕ} {H : Matrix (V → Fin q) (V → Fin q) ℂ}
    (h : ∀ g : G, sitePermMatrix q g * H * (sitePermMatrix q g)ᴴ = H) :
    IsSiteInvariant G q H := fun g ↦ by
  have hu : (sitePermMatrix (V := V) q g)ᴴ * sitePermMatrix q g = 1 := by
    simpa [star_eq_conjTranspose] using
      (mem_unitaryGroup_iff').mp (sitePermMatrix_mem_unitaryGroup (V := V) q g)
  calc sitePermMatrix q g * H
      = sitePermMatrix q g * H * ((sitePermMatrix q g)ᴴ * sitePermMatrix q g) := by
        rw [hu, Matrix.mul_one]
    _ = H * sitePermMatrix q g := by rw [← Matrix.mul_assoc, h g]

/-- **The sum of covariant terms is invariant.** Let `G` act on the sites and on an index set
`κ`, and let the terms satisfy `h (g • k) = P_g h(k) P_g†`: the term at the translate of `k`
is the translate of the term at `k`. Then `∑_k h(k)` is invariant under the site action.

For the translations of a lattice and terms indexed by the sites, this is the source's
reading of a translationally invariant Hamiltonian `H = ∑_i H_i`, whose terms are translates
of one another: Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 862–863 and
1603–1613. -/
theorem isSiteInvariant_sum_of_covariant {κ : Type*} [Fintype κ] [MulAction G κ] (q : ℕ)
    (h : κ → Matrix (V → Fin q) (V → Fin q) ℂ)
    (hcov : ∀ (g : G) k, h (g • k) = sitePermMatrix q g * h k * (sitePermMatrix q g)ᴴ) :
    IsSiteInvariant G q (∑ k, h k) :=
  isSiteInvariant_of_conj fun g ↦ by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Fintype.sum_equiv (MulAction.toPerm g) _ _ fun k ↦ (hcov g k).symm

/-- The sum of the translates `∑_g P_g H₀ P_g†` of one term is invariant under the site
action. -/
theorem isSiteInvariant_sum_conj [Fintype G] (q : ℕ) (H₀ : Matrix (V → Fin q) (V → Fin q) ℂ) :
    IsSiteInvariant G q (∑ g : G, sitePermMatrix q g * H₀ * (sitePermMatrix q g)ᴴ) :=
  isSiteInvariant_sum_of_covariant q _ fun g k ↦ by
    simp only [smul_eq_mul, sitePermMatrix_mul, conjTranspose_mul, Matrix.mul_assoc]

/-- Conjugating `H` and `W` by the same unitary conjugates the Gaussian-filtered operator. -/
theorem gaussianFilteredTerm_conj {n : Type*} [Fintype n] [DecidableEq n] (r ΔE : ℝ)
    {U H : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) (hH : H.IsHermitian) (W : Matrix n n ℂ) :
    TNLean.Lattice.gaussianFilteredTerm r ΔE (U * H * Uᴴ) (U * W * Uᴴ) =
      U * TNLean.Lattice.gaussianFilteredTerm r ΔE H W * Uᴴ := by
  have hUU : U * Uᴴ = 1 := by simpa [star_eq_conjTranspose] using (mem_unitaryGroup_iff).mp hU
  have hUU' : Uᴴ * U = 1 := by simpa [star_eq_conjTranspose] using (mem_unitaryGroup_iff').mp hU
  have hpath (t : ℝ) : hermitianUnitaryPath (U * H * Uᴴ) t = U * hermitianUnitaryPath H t * Uᴴ := by
    have hinv : Uᴴ = U⁻¹ := (inv_eq_right_inv hUU).symm
    rw [hinv, hermitianUnitaryPath, hermitianUnitaryPath,
      ← exp_conj U _ ((isUnit_iff_isUnit_det U).mpr (isUnit_det_of_right_inverse hUU))]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  have hint (t : ℝ) : hermitianUnitaryPath (U * H * Uᴴ) t * (U * W * Uᴴ) *
      hermitianUnitaryPath (U * H * Uᴴ) (-t) =
        U * (hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t)) * Uᴴ := by
    rw [hpath, hpath]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hUU', Matrix.one_mul]
  simp only [TNLean.Lattice.gaussianFilteredTerm, gaussianIntertwiner, hint]
  exact (ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ) U Uᴴ).integral_comp_comm
    (integrable_intertwinerIntegrand _ hH hH W)

/-- **Covariance of the filtered terms.** If `H` is invariant under the site action, the
filtered operator of the translate `P_g W P_g†` is the translate of the filtered operator of
`W`. With covariant terms `H_{g•i} = P_g H_i P_g†` this gives the relation
`M_{g•i} = P_g M_i P_g†` that Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1613–1618, uses for translationally invariant systems. -/
theorem gaussianFilteredTerm_sitePermMatrix_conj {q : ℕ} (r ΔE : ℝ)
    {H : Matrix (V → Fin q) (V → Fin q) ℂ} (hInv : IsSiteInvariant G q H) (hH : H.IsHermitian)
    (g : G) (W : Matrix (V → Fin q) (V → Fin q) ℂ) :
    TNLean.Lattice.gaussianFilteredTerm r ΔE H
        (sitePermMatrix q g * W * (sitePermMatrix q g)ᴴ) =
      sitePermMatrix q g * TNLean.Lattice.gaussianFilteredTerm r ΔE H W *
        (sitePermMatrix q g)ᴴ := by
  have hu := sitePermMatrix_mem_unitaryGroup (V := V) q g
  have hconj : sitePermMatrix q g * H * (sitePermMatrix q g)ᴴ = H := by
    rw [(hInv g).eq, Matrix.mul_assoc]
    simpa [star_eq_conjTranspose] using
      congrArg (H * ·) ((mem_unitaryGroup_iff).mp hu)
  conv_lhs => rw [← hconj]
  exact gaussianFilteredTerm_conj r ΔE hu hH W

omit [Fintype V] [DecidableEq V] in
/-- **Site actions by graph automorphisms preserve distances.** If every `g` preserves
adjacency of the graph `Γ` on the sites, then `d(g • x, g • y) = d(x, y)`. For the
translations of a lattice this is the source's setting of a translationally invariant system
on a lattice: Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1603–1612. -/
theorem edist_smul_of_adj_iff (Γ : SimpleGraph V)
    (hΓ : ∀ (g : G) (x y : V), Γ.Adj (g • x) (g • y) ↔ Γ.Adj x y) (g : G) (x y : V) :
    Γ.edist (g • x) (g • y) = Γ.edist x y := by
  have hle : ∀ (g : G) (x y : V), Γ.edist (g • x) (g • y) ≤ Γ.edist x y := by
    intro g x y
    rcases eq_or_ne (Γ.edist x y) ⊤ with h | h
    · simp [h]
    · obtain ⟨w, hw⟩ := Γ.exists_walk_of_edist_ne_top h
      let φ : Γ →g Γ := ⟨(g • ·), (hΓ g _ _).mpr⟩
      rw [← hw]
      exact (Γ.edist_le (w.map φ)).trans_eq (by simp)
  refine le_antisymm (hle g x y) ?_
  simpa only [inv_smul_smul] using hle g⁻¹ (g • x) (g • y)

end SitePermutation

/-- The rotations of a ring of `n` sites, `x ↦ a + x`, are automorphisms of the cycle graph. -/
theorem cycleGraph_adj_smul {n : ℕ} [NeZero n] (a : Multiplicative (Fin n)) (x y : Fin n) :
    (SimpleGraph.cycleGraph n).Adj (a • x) (a • y) ↔ (SimpleGraph.cycleGraph n).Adj x y := by
  change (SimpleGraph.cycleGraph n).Adj (a.toAdd + x) (a.toAdd + y) ↔ _
  simp only [SimpleGraph.cycleGraph_adj', add_sub_add_left_eq_sub]

end Matrix
