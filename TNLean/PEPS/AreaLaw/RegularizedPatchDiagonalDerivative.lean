import TNLean.PEPS.AreaLaw.RegularizedPatchCoordinate
import TNLean.PEPS.AreaLaw.RegularizedPatchMarginal
import QICLean.Entropy.FilterStationarity
import QICLean.Analysis.OperatorMean.MatrixPowers
import QICLean.Analysis.DensitySimplex
import QICLean.Entropy.FilterClipping
import QICLean.Analysis.LiebOperatorIntegral

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/


/-!
# Trace pairing for an insertion in the ordered regularized product

The larger-index filters can be removed from the expectation when each of them
commutes with its marginal of the same normalized final output. This gives the
exact complex pairing with an arbitrary matrix inserted at one occurrence.
The input vector and the real weights are arbitrary. The identity also covers
a zero output.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, proof of Proposition 4.1, `03-patches.tex`, lines 123–154,
  `eq:patch-trace-stripping`, and lines 170–178, `eq:patch-simplex-derivative`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, Fintype (Out v)]
variable {m : ℕ} (regions : Fin m → Finset V)

open Classical in
/-- The pairing of the actual ordered output with an arbitrary local insertion
is its squared norm times the canonical marginal trace of the insertion followed
by the inverse local filter. Nesting and the larger-index commutations remove
the outer conjugations. A positive identity shift makes every local filter
invertible, including when the defining positive semidefinite matrix is singular.

Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 123–154,
`eq:patch-trace-stripping`, and lines 170–178, `eq:patch-simplex-derivative`.
The identity holds for arbitrary input vectors and real weights. -/
theorem inner_regularizedPatchInsertion_eq_trace_of_outer_commute
    (hnested : Monotone regions) (a : Fin m → ℝ) {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (x : ∀ k, Matrix ((v : regions k) → Out v.1) ((v : regions k) → Out v.1) ℂ)
    (hx : ∀ k, (x k).PosSemidef) (j : Fin m)
    (houter : ∀ k : Fin m, j < k →
      Commute ((x k + b • 1) ^ (-(a k) / 2))
        (normalizedRegularizedPatchMarginal regions a b Ω x (regions k)))
    (H : Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ) :
    inner ℂ (regularizedPatchOutput regions a b Ω x)
        (regularizedPatchInsertion regions a b Ω x j H) =
      (regularizedPatchObjective regions a b Ω x : ℂ) ^ 2 *
        Matrix.trace (normalizedRegularizedPatchMarginal regions a b Ω x (regions j) *
          (H * ((x j + b • 1) ^ (-(a j) / 2))⁻¹)) := by
  classical
  let ell := (List.finRange m).reverse
  have hj : j ∈ ell := by simp [ell]
  have hp : ell.idxOf j < ell.length := List.idxOf_lt_length_of_mem hj
  have hnodup : ell.Nodup := List.nodup_reverse.mpr (List.nodup_finRange m)
  let L := regularizedPatchFilter regions a b x
  have hins (K : Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ) :
      regularizedPatchInsertion regions a b Ω x j K = WithLp.toLp 2
        ((((ell.take (ell.idxOf j)).map L).prod *
          dependentRegionOperatorLift (regions j) K *
          ((ell.drop (ell.idxOf j + 1)).map L).prod) *ᵥ Ω) := by
    rw [regularizedPatchInsertion_apply, List.ofFn_eq_map, ← List.map_reverse,
      hnodup.map_update, ite_eq_left hj, List.prod_set]
    simp only [L, List.length_map, ite_eq_left hp, ← List.map_take, ← List.map_drop]
  have hdesc : ell.Pairwise (fun k l ↦ l < k) :=
    List.pairwise_reverse.mpr (List.pairwise_lt_finRange m)
  have hgreater (k : Fin m) (hk : k ∈ ell.take (ell.idxOf j)) : j < k :=
    hdesc.rel_of_mem_take_of_mem_drop hk (by simp [List.drop_eq_getElem_cons hp])
  let e (v : V) := Fintype.equivFin (Out v)
  let F : Fin m → Entropy.RegionFilter (fun v ↦ Fintype.card (Out v)) := fun k ↦
    ⟨regions k, Matrix.reindexAlgEquiv ℂ ℂ (dependentRegionFinEquiv e (regions k))
      ((x k + b • 1) ^ (-(a k) / 2))⟩
  have hdet (k : Fin m) : IsUnit (F k).2.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      ((((hx k).add_smul_one_posDef hb).rpow (-(a k) / 2)).isUnit.map
        (Matrix.reindexAlgEquiv ℂ ℂ (dependentRegionFinEquiv e (regions k))))
  let φ := dependentGlobalFinIsometry e (normalizedRegularizedPatchOutput regions a b Ω x)
  have hc (k : Fin m) (hjk : j < k) :
      (F k).2 * Entropy.regionState (regions k) φ =
        Entropy.regionState (regions k) φ * (F k).2 := by
    simpa only [F, φ, Matrix.coe_reindexAlgEquiv,
      reindex_normalizedRegularizedPatchMarginal] using
      ((houter k hjk).map
        (Matrix.reindexAlgEquiv ℂ ℂ (dependentRegionFinEquiv e (regions k)))).eq
  have hchain_aux : ∀ t : List (Fin m), t.Pairwise (fun k l ↦ l < k) →
      (∀ k ∈ t, j < k) → Entropy.IsDescendingChain φ (t.map F) :=
    List.rec (fun _ _ ↦ True.intro) fun k t ih ht hg ↦
      ⟨hdet k, hc k (hg k List.mem_cons_self),
        fun q hq ↦ (List.mem_map.mp hq).elim fun l hl ↦
          hl.2 ▸ hnested (le_of_lt ((List.pairwise_cons.mp ht).1 l hl.1)),
        ih (List.pairwise_cons.mp ht).2 (fun l hl ↦ hg l (List.mem_cons_of_mem k hl))⟩
  have hchain := hchain_aux (ell.take (ell.idxOf j)) hdesc.take hgreater
  have hU (M : Matrix ((v : (Finset.univ : Finset V)) → Out v.1)
      ((v : (Finset.univ : Finset V)) → Out v.1) ℂ)
      (ξ : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1)) :
      dependentGlobalFinIsometry e (WithLp.toLp 2 (M *ᵥ ξ)) =
        Matrix.toEuclideanLin
          (Matrix.reindexAlgEquiv ℂ ℂ (dependentGlobalFinEquiv e) M)
          (dependentGlobalFinIsometry e ξ) := by
    ext σ
    change (M *ᵥ ξ) ((dependentGlobalFinEquiv e).symm σ) =
      (M.submatrix (dependentGlobalFinEquiv e).symm (dependentGlobalFinEquiv e).symm *ᵥ
        (fun τ ↦ ξ ((dependentGlobalFinEquiv e).symm τ))) σ
    simpa only [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply] using
      (congrFun (Matrix.submatrix_mulVec_equiv M
        (fun τ ↦ ξ ((dependentGlobalFinEquiv e).symm τ))
        (dependentGlobalFinEquiv e).symm (dependentGlobalFinEquiv e).symm) σ).symm
  have hprod (t : List (Fin m)) :
      Matrix.reindexAlgEquiv ℂ ℂ (dependentGlobalFinEquiv e) ((t.map L).prod) =
        Entropy.liftProd (t.map F) := by
    simpa only [Entropy.liftProd, List.map_map, Function.comp_def, L,
      regularizedPatchFilter, Matrix.coe_reindexAlgEquiv,
      reindex_dependentRegionOperatorLift, F] using
      map_list_prod (Matrix.reindexAlgEquiv ℂ ℂ (dependentGlobalFinEquiv e)) (t.map L)
  have hinsU (K : Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ) :
      dependentGlobalFinIsometry e (regularizedPatchInsertion regions a b Ω x j K) =
        Matrix.toEuclideanLin
          (Entropy.liftProd ((ell.take (ell.idxOf j)).map F) *
            Entropy.localLift (regions j)
              (Matrix.reindexAlgEquiv ℂ ℂ (dependentRegionFinEquiv e (regions j)) K) *
            Entropy.liftProd ((ell.drop (ell.idxOf j + 1)).map F))
          (dependentGlobalFinIsometry e Ω) := by
    rw [hins, hU, map_mul (Matrix.reindexAlgEquiv ℂ ℂ (dependentGlobalFinEquiv e)),
      map_mul (Matrix.reindexAlgEquiv ℂ ℂ (dependentGlobalFinEquiv e)), hprod, hprod,
      Matrix.coe_reindexAlgEquiv, reindex_dependentRegionOperatorLift,
      Matrix.coe_reindexAlgEquiv]
  have houtU := (congrArg (dependentGlobalFinIsometry e)
    (regularizedPatchInsertion_self regions a b Ω x j)).symm.trans (hinsU _)
  have hcancel :
      (H * ((x j + b • 1) ^ (-(a j) / 2))⁻¹) *
        ((x j + b • 1) ^ (-(a j) / 2)) = H :=
    Matrix.nonsing_inv_mul_cancel_right _ H
      ((Matrix.isUnit_iff_isUnit_det _).mp
        (((hx j).add_smul_one_posDef hb).rpow (-(a j) / 2)).isUnit)
  have hconj :
      dependentGlobalFinIsometry e (regularizedPatchInsertion regions a b Ω x j H) =
        Matrix.toEuclideanLin
          (Entropy.liftProd ((ell.take (ell.idxOf j)).map F) *
            Entropy.localLift (regions j)
              (Matrix.reindexAlgEquiv ℂ ℂ (dependentRegionFinEquiv e (regions j))
                (H * ((x j + b • 1) ^ (-(a j) / 2))⁻¹)) *
            Entropy.liftProdInv ((ell.take (ell.idxOf j)).map F))
          (dependentGlobalFinIsometry e (regularizedPatchOutput regions a b Ω x)) := by
    rw [hinsU, houtU, ← Entropy.toEuclideanLin_mul_apply']
    apply congrArg (fun M ↦ Matrix.toEuclideanLin M (dependentGlobalFinIsometry e Ω))
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc
      (Entropy.liftProdInv ((ell.take (ell.idxOf j)).map F))
      (Entropy.liftProd ((ell.take (ell.idxOf j)).map F)),
      Entropy.liftProdInv_mul_liftProd hchain, Matrix.one_mul,
      ← Matrix.mul_assoc (Entropy.localLift (regions j)
        (Matrix.reindexAlgEquiv ℂ ℂ (dependentRegionFinEquiv e (regions j))
          (H * ((x j + b • 1) ^ (-(a j) / 2))⁻¹))),
      ← Entropy.localLift_mul,
      ← map_mul (Matrix.reindexAlgEquiv ℂ ℂ (dependentRegionFinEquiv e (regions j))),
      hcancel]
  have hsupport
      (p : Entropy.RegionFilter (fun v ↦ Fintype.card (Out v)))
      (hp : p ∈ (ell.take (ell.idxOf j)).map F) :
      Entropy.IsSupportedOn
        (Entropy.localLift (regions j)
          (Matrix.reindexAlgEquiv ℂ ℂ (dependentRegionFinEquiv e (regions j))
            (H * ((x j + b • 1) ^ (-(a j) / 2))⁻¹))) p.1 :=
    (List.mem_map.mp hp).elim fun k hk ↦ hk.2 ▸
      (Entropy.isSupportedOn_localLift _).mono (hnested (le_of_lt (hgreater k hk.1)))
  by_cases hzero : regularizedPatchOutput regions a b Ω x = 0
  · simp [regularizedPatchObjective, hzero]
  have hscale :
      regularizedPatchOutput regions a b Ω x =
        (regularizedPatchObjective regions a b Ω x : ℂ) •
          normalizedRegularizedPatchOutput regions a b Ω x := by
    have hreal : regularizedPatchOutput regions a b Ω x =
        regularizedPatchObjective regions a b Ω x •
          normalizedRegularizedPatchOutput regions a b Ω x := by
      exact (smul_inv_smul₀ (norm_ne_zero_iff.mpr hzero)
        (regularizedPatchOutput regions a b Ω x)).symm
    exact hreal.trans (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _)
  obtain ⟨σ, -⟩ :=
    Function.ne_iff.mp ((WithLp.ofLp_injective 2).ne hzero)
  have hstrip := Entropy.inner_liftProd_conj
    (dependentGlobalFinEquiv e σ) hchain hsupport
  rw [← (dependentGlobalFinIsometry e).inner_map_map, hconj]
  simp only [hscale, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [hstrip]
  simp only [φ, Matrix.coe_reindexAlgEquiv]
  rw [← dependentGlobalFinIsometry_lift,
    (dependentGlobalFinIsometry e).inner_map_map,
    inner_normalizedRegularizedPatchOutput_lift_eq_trace]
  simp only [pow_two, mul_assoc]

end TNLean.PEPS

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

/-!
# Diagonal variation of an ordered regularized patch objective

A diagonal change of one density leaves the other densities and the order of
all filters fixed. The scalar objective is the square of the norm of that
same ordered product applied to the original vector.

Source: OpenAI, polynomial PEPS manuscript, proof of Proposition 4.1,
`03-patches.tex`, lines 170–200, `eq:patch-simplex-derivative` and
`eq:patch-kkt`, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, Fintype (Out v)]
variable {m : ℕ} (regions : Fin m → Finset V)

open Classical in
/-- Replace one density by a real diagonal matrix in a fixed orthonormal basis.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 170–178. -/
noncomputable def regularizedPatchDiagonalUpdate
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (j : Fin m)
    (U : unitary (Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ))
    (y : ((v : regions j) → Out v.1) → ℝ) :=
  Function.update x j
    ((U : Matrix _ _ ℂ) * diagonal (fun i ↦ (y i : ℂ)) * star (U : Matrix _ _ ℂ))

open Classical in
/-- The squared norm of the original ordered product after one diagonal change.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 170–178. -/
noncomputable def regularizedPatchDiagonalObjective (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (j : Fin m)
    (U : unitary (Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ))
    (y : ((v : regions j) → Out v.1) → ℝ) : ℝ :=
  regularizedPatchObjective regions a b Ω (regularizedPatchDiagonalUpdate regions x j U y) ^ 2

open Classical in
/-- A minimum of the full ordered objective restricts to a minimum on the
probability simplex in any eigenbasis of the selected density.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 170–191.
Neither commutation of filters nor nonsingularity of a density is needed. -/
theorem isMinOn_regularizedPatchDiagonalObjective
    (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions)
    (hmin : IsMinOn (regularizedPatchObjective regions a b Ω)
      (regularizedPatchDomain regions) x)
    (j : Fin m)
    (U : unitary (Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ))
    (s : ((v : regions j) → Out v.1) → ℝ)
    (hxs : x j =
      (U : Matrix _ _ ℂ) * diagonal (fun i ↦ (s i : ℂ)) * star (U : Matrix _ _ ℂ)) :
    IsMinOn (regularizedPatchDiagonalObjective regions a b Ω x j U)
      {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} s := by
  classical
  intro y hy
  have hfeas : regularizedPatchDiagonalUpdate regions x j U y ∈
      regularizedPatchDomain regions := by
    intro k
    by_cases h : k = j
    · subst k
      simp only [regularizedPatchDiagonalUpdate, Function.update_self]
      refine ⟨(Matrix.PosSemidef.diagonal
        (fun i ↦ Complex.zero_le_real.mpr (hy.1 i))).mul_mul_conjTranspose_same _, ?_⟩
      rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
      exact_mod_cast hy.2
    · simpa only [regularizedPatchDiagonalUpdate, Function.update_of_ne h] using hx k
  have hself : regularizedPatchDiagonalUpdate regions x j U s = x :=
    (congrArg (Function.update x j) hxs.symm).trans (Function.update_eq_self j x)
  simpa only [Set.mem_ofPred_eq, regularizedPatchDiagonalObjective, hself,
    regularizedPatchObjective] using
    pow_le_pow_left₀ (norm_nonneg _) (hmin hfeas) 2

end TNLean.PEPS

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, Fintype (Out v)]
variable {m : ℕ} (regions : Fin m → Finset V)

open Classical in
/-- The real Fréchet derivative of the squared norm of the original ordered
product, expressed in a common eigenbasis of the varied density and the
canonical marginal. The larger-index commutations are the auxiliary conclusions
of descending stationarity. The real weights and the input vector are arbitrary.

Source: OpenAI, polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 170–178,
`eq:patch-simplex-derivative`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem hasFDerivAt_regularizedPatchDiagonalObjective_of_outer_commute
    (hnested : Monotone regions) (a : Fin m → ℝ)
    {b : ℝ} (hb : 0 < b)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    {x : ∀ k, Matrix ((v : regions k) → Out v.1) ((v : regions k) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions) (j : Fin m)
    (houter : ∀ k, j < k →
      Commute ((x k + b • 1) ^ (-(a k) / 2))
        (normalizedRegularizedPatchMarginal regions a b Ω x (regions k)))
    (U : unitary (Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ))
    (s p : ((v : regions j) → Out v.1) → ℝ)
    (hxs : x j =
      (U : Matrix _ _ ℂ) * diagonal (fun i ↦ (s i : ℂ)) * star (U : Matrix _ _ ℂ))
    (hρp : normalizedRegularizedPatchMarginal regions a b Ω x (regions j) =
      (U : Matrix _ _ ℂ) * diagonal (fun i ↦ (p i : ℂ)) * star (U : Matrix _ _ ℂ)) :
    ∃ f' : ((((v : regions j) → Out v.1) → ℝ) →L[ℝ] ℝ),
      HasFDerivAt (regularizedPatchDiagonalObjective regions a b Ω x j U) f' s ∧
      ∀ v, f' v = -(a j * regularizedPatchObjective regions a b Ω x ^ 2) *
        ∑ i, p i / (s i + b) * v i := by
  classical
  have hspos : ∀ i, 0 < s i + b := fun i ↦
    add_pos_of_nonneg_of_pos
      (Complex.zero_le_real.mp
        ((Matrix.posSemidef_diagonal_iff.mp
          ((Matrix.IsUnit.posSemidef_star_right_conjugate_iff
            (Unitary.isUnit_coe (U := U))).mp (hxs ▸ (hx j).1))) i)) hb
  have hdiagDiff : DifferentiableAt ℝ
      (fun y : (((v : regions j) → Out v.1) → ℝ) ↦
        (U : Matrix _ _ ℂ) *
          diagonal (fun i ↦ (((y i + b) ^ (-(a j) / 2) : ℝ) : ℂ)) *
          star (U : Matrix _ _ ℂ)) s := by
    apply DifferentiableAt.comp (𝕜 := ℝ)
      (f := fun y : (((v : regions j) → Out v.1) → ℝ) ↦
        fun i ↦ (((y i + b) ^ (-(a j) / 2) : ℝ) : ℂ)) s
      (Entropy.conjDiagonalCLM (U : Matrix _ _ ℂ)).differentiableAt
    fun_prop (disch := first | exact (hspos _).ne' | exact Or.inl (hspos _).ne')
  have hshift (y : (((v : regions j) → Out v.1) → ℝ)) :
      diagonal (fun i ↦ ((y i + b : ℝ) : ℂ)) =
        diagonal (fun i ↦ (y i : ℂ)) + b • (1 : Matrix _ _ ℂ) := by
    ext i k <;> by_cases h : i = k <;> simp [Matrix.diagonal, h]
  done

end TNLean.PEPS
