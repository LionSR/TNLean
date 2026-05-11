import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Separation.Basic

/-!
# Gram-matrix convergence implies eventual linear independence

This file proves eventual linear-independence criteria from convergence of
Gram matrices. The generalized theorem
`eventually_linearIndependent_of_gram_tendsto_nondegenerate` handles
convergence to any matrix with nonzero determinant (e.g. a diagonal matrix
with positive entries). The special case of convergence to the identity is
`eventually_linearIndependent_of_gram_tendsto_id`.

Both are used in the MPDO papers arXiv:1606.00608 and arXiv:1708.00029.
-/

open scoped BigOperators InnerProductSpace
open Filter

namespace MPSTensor

/--
**Generalized Gram-matrix criterion**: eventual linear independence from
Gram-matrix convergence to any matrix with nonzero determinant.

If the Gram matrix entries converge `⟪v i N, v j N⟫_ℂ → L i j` as `N → ∞`
and `L.det ≠ 0`, then for `N` large enough the Gram matrix is invertible and
the vectors `{v i N}` are linearly independent.
-/
theorem eventually_linearIndependent_of_gram_tendsto_nondegenerate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (v : ι → ℕ → V) (L : Matrix ι ι ℂ) (hL : L.det ≠ 0)
    (h : ∀ i j, Tendsto (fun N => ⟪v i N, v j N⟫_ℂ) atTop (nhds (L i j))) :
    ∀ᶠ N in atTop, LinearIndependent ℂ (fun i => v i N) := by
  let G : ℕ → Matrix ι ι ℂ := fun N i j => ⟪v i N, v j N⟫_ℂ
  have hG : Tendsto G atTop (nhds L) := by
    refine tendsto_pi_nhds.2 fun i ↦ ?_
    refine tendsto_pi_nhds.2 fun j ↦ ?_
    exact h i j
  have hdet : Tendsto (fun N => (G N).det) atTop (nhds L.det) :=
    ((continuous_id.matrix_det).tendsto L).comp hG
  have hdet_ne : ∀ᶠ N in atTop, (G N).det ≠ 0 := hdet.eventually_ne hL
  exact hdet_ne.mono fun N hN => by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hmul : (G N).mulVec c = 0 := by
      ext j
      have key : (G N).mulVec c j = ⟪v j N, ∑ i : ι, c i • v i N⟫_ℂ := by
        simp only [Matrix.mulVec.eq_1, dotProduct, inner_sum, inner_smul_right]
        apply Finset.sum_congr rfl; intro i _; ring
      simp only [key, hc, inner_zero_right, Pi.zero_apply]
    have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hN hmul
    intro i; exact congr_fun hc0 i

/--
**Lem1 (MPDO 1606.00608 / 1708.00029)**: eventual linear independence from
Gram-matrix convergence to the identity.

Special case of `eventually_linearIndependent_of_gram_tendsto_nondegenerate`
where the limit matrix is the identity. For a finite family of vectors
`v i N` in a complex inner product space, if `⟪v i N, v j N⟫_ℂ → δ_{ij}`,
then for `N` large enough the vectors are linearly independent.
-/
theorem eventually_linearIndependent_of_gram_tendsto_id
    {ι : Type*} [Finite ι] [DecidableEq ι]
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (v : ι → ℕ → V)
    (h : ∀ i j, Tendsto (fun N => ⟪v i N, v j N⟫_ℂ) atTop
             (nhds (if i = j then (1 : ℂ) else 0))) :
    ∀ᶠ N in atTop, LinearIndependent ℂ (fun i => v i N) := by
  cases nonempty_fintype ι
  exact eventually_linearIndependent_of_gram_tendsto_nondegenerate v 1
    (by simp) (fun i j => by simpa [Matrix.one_apply] using h i j)

end MPSTensor
