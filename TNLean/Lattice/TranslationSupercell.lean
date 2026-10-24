/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.SiteSymmetry

/-!
# Low-energy commutators under a supercell of translations

Let a group `G` act on the sites of a finite system, let `H` be invariant under the induced
site permutations `P_g`, and let `P` be the orthogonal projection onto the ground eigenspace of
`H`. Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1603–1642) argues that for a translationally
invariant lattice the low-energy commutators `[P M_i P, P M_j P]` of the filtered terms are
exponentially small in the linear size of the system. The step is this: if translation by `g`
leaves every ground state unchanged, then `P M_{g•j} P = P M_j P`, so
`[P M_i P, P M_j P] = [P M_i P, P M_{g•j} P]`, and the decay of the low-energy commutator in the
distance applies at the distance from `i` to `g • j` (lines 1634–1641). This file proves the
step and the transfer of any bound.

## Main results

* `Matrix.sitePermMatrix_inv`: `P_{g⁻¹} = P_g†`.
* `Submodule.starProjection_mul_conj_mul_starProjection`: if `U†` fixes a closed subspace
  pointwise, compressing `U W U†` onto it gives the compression of `W`.
* `TNLean.Lattice.starProjection_mul_sitePermMatrix_conj_mul_starProjection`: the same for the
  site permutations of a subgroup that fixes every ground vector.
* `TNLean.Lattice.groundCompression_commutator_eq_of_mem_supercell`: for covariant terms, the
  low-energy commutator of the filtered terms at `i` and `j` equals the one at `i` and `g • j`.
* `TNLean.Lattice.norm_groundCompression_commutator_le_of_mem_supercell`: so a bound `B i j` on
  the low-energy commutators also gives `B i (g • j)` for every `g` in the subgroup.

**Scope restriction (supercell):** the source assumes that the momenta of the ground states are
rational multiples of `2π` whose denominators do not depend on the system size (lines
1620–1625), and derives from this a supercell whose translations leave every ground state
unchanged (lines 1626–1630). The three results in `TNLean.Lattice` above instead assume
directly a subgroup `S` of the symmetry group with this property. Documented in `docs/paper-gaps/hastings05_translation_supercell.tex`.
-/

open Matrix GaussianFilter
open scoped InnerProductSpace

section Projection

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- **Compression of a conjugate by an operator fixing the subspace.** If the adjoint `U†`
leaves every vector of `K` unchanged, then `P (U W U†) P = P W P`, where `P` is the orthogonal
projection onto `K`: indeed `U† P = P`, and so `P U = P` on taking adjoints. -/
theorem Submodule.starProjection_mul_conj_mul_starProjection {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] {U : E →L[𝕜] E} (hU : ∀ v ∈ K, U.adjoint v = v)
    (W : E →L[𝕜] E) :
    K.starProjection * (U * W * U.adjoint) * K.starProjection =
      K.starProjection * W * K.starProjection := by
  have hP : U.adjoint * K.starProjection = K.starProjection := by
    ext1 x
    exact hU _ (K.starProjection_apply_mem x)
  have hP' : K.starProjection * U = K.starProjection := by
    have hsa : K.starProjection.adjoint = K.starProjection :=
      (isSelfAdjoint_starProjection K).adjoint_eq
    have h := congrArg star hP
    simpa only [star_mul, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint,
      hsa] using h
  calc K.starProjection * (U * W * U.adjoint) * K.starProjection
      = K.starProjection * U * W * (U.adjoint * K.starProjection) := by simp only [mul_assoc]
    _ = K.starProjection * W * K.starProjection := by rw [hP', hP]

end Projection

namespace TNLean.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Type*} [Group G] [MulAction G V]

/-- The site permutation of `g⁻¹` is the adjoint of that of `g`. -/
theorem _root_.Matrix.sitePermMatrix_inv (q : ℕ) (g : G) :
    sitePermMatrix (V := V) q g⁻¹ = (sitePermMatrix q g)ᴴ := by
  have hu : sitePermMatrix (V := V) q g * (sitePermMatrix q g)ᴴ = 1 := by
    simpa [star_eq_conjTranspose] using
      (mem_unitaryGroup_iff).mp (sitePermMatrix_mem_unitaryGroup (V := V) q g)
  have hinv : sitePermMatrix (V := V) q g⁻¹ * sitePermMatrix q g = 1 := by
    rw [← sitePermMatrix_mul, inv_mul_cancel, sitePermMatrix, map_one, map_one]
  calc sitePermMatrix q g⁻¹
      = sitePermMatrix q g⁻¹ * (sitePermMatrix q g * (sitePermMatrix q g)ᴴ) := by
        rw [hu, Matrix.mul_one]
    _ = (sitePermMatrix q g)ᴴ := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]

variable {q : ℕ} {H : Matrix (V → Fin q) (V → Fin q) ℂ} {E₀ : ℝ}

/-- `𝒞 W` is the compression `P W P` of `W` to the ground eigenspace of `H` at energy `E₀`, as
an operator on the Euclidean space; `P` is the orthogonal projection onto that eigenspace. -/
local notation "𝒞 " W:max => Submodule.starProjection (groundEigenspace H E₀) *
  toEuclideanCLM (n := V → Fin q) (𝕜 := ℂ) W * Submodule.starProjection (groundEigenspace H E₀)

/-- **The low-energy compression is unchanged by a supercell translation.** Let `S` be a
subgroup whose site permutations leave every ground vector of `H` unchanged: the source's
supercell, "such that all of the `n` ground states are unchanged by translation by a
supercell" (Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1626–1628). Then for
`g ∈ S` the compression of `P_g W P_g†` to the ground space equals that of `W`. -/
theorem starProjection_mul_sitePermMatrix_conj_mul_starProjection (S : Subgroup G)
    (hS : ∀ g ∈ S, ∀ v ∈ groundEigenspace H E₀,
      sitePermMatrix q g *ᵥ WithLp.ofLp v = WithLp.ofLp v)
    {g : G} (hg : g ∈ S) (W : Matrix (V → Fin q) (V → Fin q) ℂ) :
    𝒞 (sitePermMatrix q g * W * (sitePermMatrix q g)ᴴ) = 𝒞 W := by
  have hstar : toEuclideanCLM (n := V → Fin q) (𝕜 := ℂ) (sitePermMatrix q g)ᴴ =
      (toEuclideanCLM (n := V → Fin q) (𝕜 := ℂ) (sitePermMatrix q g)).adjoint := by
    rw [← star_eq_conjTranspose, map_star, ContinuousLinearMap.star_eq_adjoint]
  rw [map_mul, map_mul, hstar]
  refine Submodule.starProjection_mul_conj_mul_starProjection (fun v hv ↦ ?_) _
  rw [← hstar, ← sitePermMatrix_inv]
  calc toEuclideanCLM (n := V → Fin q) (𝕜 := ℂ) (sitePermMatrix q g⁻¹) v
      = WithLp.toLp 2 (sitePermMatrix q g⁻¹ *ᵥ WithLp.ofLp v) := toEuclideanCLM_toLp _ _
    _ = v := by rw [hS g⁻¹ (S.inv_mem hg) v hv]

variable {κ : Type*} [MulAction G κ] {h : κ → Matrix (V → Fin q) (V → Fin q) ℂ}

/-- **Low-energy commutators across a supercell translation.** Let the terms be covariant,
`h_{g•k} = P_g h_k P_g†` (Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, line 862, the
terms of a translationally invariant Hamiltonian are translates of one another), let `H` be
invariant and Hermitian, and let `M_k` be the filtered terms. For `g` in a subgroup `S` that
leaves every ground vector unchanged (lines 1626–1628),
`[P M_i P, P M_j P] = [P M_i P, P M_{g•j} P]`. This is the identity used at lines 1634–1637:
the commutator "equal[s] `[M_{x₁,y₁}, M_{x₂+x',y₂}]` where `x'` translates `x₂` by some number
of supercells". -/
theorem groundCompression_commutator_eq_of_mem_supercell (r ΔE : ℝ)
    (hInv : IsSiteInvariant G q H) (hH : H.IsHermitian)
    (hcov : ∀ (g : G) k, h (g • k) = sitePermMatrix q g * h k * (sitePermMatrix q g)ᴴ)
    (S : Subgroup G)
    (hS : ∀ g ∈ S, ∀ v ∈ groundEigenspace H E₀,
      sitePermMatrix q g *ᵥ WithLp.ofLp v = WithLp.ofLp v)
    {g : G} (hg : g ∈ S) (i j : κ) :
    𝒞 (gaussianFilteredTerm r ΔE H (h i)) * 𝒞 (gaussianFilteredTerm r ΔE H (h (g • j))) -
        𝒞 (gaussianFilteredTerm r ΔE H (h (g • j))) * 𝒞 (gaussianFilteredTerm r ΔE H (h i)) =
      𝒞 (gaussianFilteredTerm r ΔE H (h i)) * 𝒞 (gaussianFilteredTerm r ΔE H (h j)) -
        𝒞 (gaussianFilteredTerm r ΔE H (h j)) * 𝒞 (gaussianFilteredTerm r ΔE H (h i)) := by
  have hj : 𝒞 (gaussianFilteredTerm r ΔE H (h (g • j))) =
      𝒞 (gaussianFilteredTerm r ΔE H (h j)) := by
    simp only [hcov, gaussianFilteredTerm_sitePermMatrix_conj r ΔE hInv hH]
    exact starProjection_mul_sitePermMatrix_conj_mul_starProjection S hS hg _
  rw [hj]

/-- **Transfer of a commutator bound across supercell translations.** If `B i j` bounds the
low-energy commutator of the filtered terms at `i` and `j` for all `i` and `j`, then so does
`B i (g • j)` for every `g` in a subgroup `S` that leaves every ground vector unchanged. With
`B` the bound that decays in the distance from `i` to `j`, choosing `g` that moves `j` far from
`i` makes the commutator small in that larger distance: Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1634–1641. -/
theorem norm_groundCompression_commutator_le_of_mem_supercell (r ΔE : ℝ)
    (hInv : IsSiteInvariant G q H) (hH : H.IsHermitian)
    (hcov : ∀ (g : G) k, h (g • k) = sitePermMatrix q g * h k * (sitePermMatrix q g)ᴴ)
    (S : Subgroup G)
    (hS : ∀ g ∈ S, ∀ v ∈ groundEigenspace H E₀,
      sitePermMatrix q g *ᵥ WithLp.ofLp v = WithLp.ofLp v)
    (B : κ → κ → ℝ)
    (hB : ∀ i j,
      ‖𝒞 (gaussianFilteredTerm r ΔE H (h i)) * 𝒞 (gaussianFilteredTerm r ΔE H (h j)) -
        𝒞 (gaussianFilteredTerm r ΔE H (h j)) * 𝒞 (gaussianFilteredTerm r ΔE H (h i))‖ ≤ B i j)
    {g : G} (hg : g ∈ S) (i j : κ) :
    ‖𝒞 (gaussianFilteredTerm r ΔE H (h i)) * 𝒞 (gaussianFilteredTerm r ΔE H (h j)) -
        𝒞 (gaussianFilteredTerm r ΔE H (h j)) * 𝒞 (gaussianFilteredTerm r ΔE H (h i))‖ ≤
      B i (g • j) := by
  have := hB i (g • j)
  rwa [groundCompression_commutator_eq_of_mem_supercell r ΔE hInv hH hcov S hS hg i j] at this

end TNLean.Lattice
