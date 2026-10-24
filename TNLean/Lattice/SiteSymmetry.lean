/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Permutation
import TNLean.Algebra.PermutationMatrixUnitary

/-!
# Site permutations of a finite system

A group `G` acting on a finite set of sites `V` acts on the configurations `V → Fin q`, and so by
permutation matrices `P_g` on the state space. The translations of a periodic lattice and the
automorphisms of a finite graph are such actions.

## Main definitions

* `Matrix.sitePermMatrix`: the permutation of the configurations of finitely many sites induced by
  a group element acting on the sites.

## Main results

* `Matrix.sitePermMatrix_mul`, `Matrix.sitePermMatrix_mem_unitaryGroup`: `g ↦ P_g` is a unitary
  representation.
* `Matrix.commute_sitePermMatrix_sum`: every `P_h` commutes with the sum of the translates
  `∑_g P_g H₀ P_g†`.
-/

open Matrix

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

/-- Every site permutation commutes with the sum of the translates `∑_g P_g H₀ P_g†`. -/
theorem commute_sitePermMatrix_sum [Fintype G] (q : ℕ) (H₀ : Matrix (V → Fin q) (V → Fin q) ℂ)
    (h : G) :
    Commute (sitePermMatrix (V := V) q h)
      (∑ g : G, sitePermMatrix q g * H₀ * (sitePermMatrix q g)ᴴ) := by
  have hu : (sitePermMatrix (V := V) q h)ᴴ * sitePermMatrix q h = 1 := by
    simpa [star_eq_conjTranspose] using
      (mem_unitaryGroup_iff').mp (sitePermMatrix_mem_unitaryGroup (V := V) q h)
  have hconj : sitePermMatrix (V := V) q h *
      (∑ g : G, sitePermMatrix q g * H₀ * (sitePermMatrix q g)ᴴ) * (sitePermMatrix q h)ᴴ =
        ∑ g : G, sitePermMatrix q g * H₀ * (sitePermMatrix q g)ᴴ := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g ↦ ?_
    simp only [Equiv.coe_mulLeft, sitePermMatrix_mul, conjTranspose_mul, Matrix.mul_assoc]
  calc sitePermMatrix q h * (∑ g : G, sitePermMatrix q g * H₀ * (sitePermMatrix q g)ᴴ)
      = sitePermMatrix q h * (∑ g : G, sitePermMatrix q g * H₀ * (sitePermMatrix q g)ᴴ) *
          ((sitePermMatrix q h)ᴴ * sitePermMatrix q h) := by rw [hu, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hconj]

end SitePermutation

end Matrix
