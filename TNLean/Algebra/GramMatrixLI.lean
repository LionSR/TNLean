import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Separation.Basic

/-!
# Gram-matrix convergence implies eventual linear independence

This file proves an eventual linear-independence criterion from convergence of
Gram matrices to the identity. The main theorem
`eventually_linearIndependent_of_gram_tendsto_id` packages the finite-dimensional
argument used in the MPDO papers arXiv:1606.00608 and arXiv:1708.00029.
-/

open scoped BigOperators InnerProductSpace
open Filter

namespace MPSTensor

/--
**Lem1 (MPDO 1606.00608 / 1708.00029)**: eventual linear independence from
Gram-matrix convergence.

For a finite family of vectors `v i N` in a complex inner product space,
if the Gram matrix entries converge `⟪v i N, v j N⟫_ℂ → δ_{ij}` as `N → ∞`,
then the Gram matrices converge to the identity. Hence for `N` large enough the Gram matrix is
invertible, and the vectors `{v i N}` are linearly independent.
-/
theorem eventually_linearIndependent_of_gram_tendsto_id
    {ι : Type} [Finite ι] [DecidableEq ι]
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (v : ι → ℕ → V)
    (h : ∀ i j, Tendsto (fun N => ⟪v i N, v j N⟫_ℂ) atTop
             (nhds (if i = j then (1 : ℂ) else 0))) :
    ∀ᶠ N in atTop, LinearIndependent ℂ (fun i => v i N) := by
  cases nonempty_fintype ι
  -- Define the Gram matrix G(N)_{ij} = ⟪v_i(N), v_j(N)⟫
  let G : ℕ → Matrix ι ι ℂ := fun N i j => ⟪v i N, v j N⟫_ℂ
  -- Step 1: G(N) → 1 (identity matrix) as N → ∞
  have hG : Tendsto G atTop (nhds (1 : Matrix ι ι ℂ)) := by
    rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_pi_nhds]
    intro j
    simp only [Matrix.one_apply]
    exact h i j
  -- Step 2: det(G(N)) → det(1) = 1 by continuity of det
  have hdet : Tendsto (fun N => (G N).det) atTop (nhds (1 : ℂ)) := by
    have hcont : Continuous (fun M : Matrix ι ι ℂ => M.det) := continuous_id.matrix_det
    have h1 := (hcont.tendsto (1 : Matrix ι ι ℂ)).comp hG
    rwa [Function.comp_def, Matrix.det_one] at h1
  -- Step 3: Eventually det(G(N)) ≠ 0
  have hdet_ne : ∀ᶠ N in atTop, (G N).det ≠ 0 :=
    hdet.eventually_ne one_ne_zero
  -- Step 4: det ≠ 0 implies linear independence
  exact hdet_ne.mono fun N hN => by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    -- From ∑ c_i • v_i(N) = 0, derive (G N) * c = 0 via inner products
    have hmul : (G N).mulVec c = 0 := by
      ext j
      -- Show (G N).mulVec c j = ⟪v j N, ∑ c_i • v_i(N)⟫ = ⟪v j N, 0⟫ = 0
      have key : (G N).mulVec c j = ⟪v j N, ∑ i : ι, c i • v i N⟫_ℂ := by
        simp only [Matrix.mulVec.eq_1, dotProduct, inner_sum, inner_smul_right]
        apply Finset.sum_congr rfl
        intro i _
        ring
      simp only [key, hc, inner_zero_right, Pi.zero_apply]
    -- det(G N) ≠ 0 and G N * c = 0 imply c = 0
    have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hN hmul
    intro i
    exact congr_fun hc0 i

end MPSTensor
