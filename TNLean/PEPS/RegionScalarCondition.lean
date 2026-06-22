import TNLean.PEPS.RegionComplementComparison
import TNLean.PEPS.RegionBlock.BlockRangeCoincidence

/-!
# The per-vertex scalar condition for region-injective normal PEPS

This file proves the region-injective form of the per-vertex scalar condition of
the normal PEPS Fundamental Theorem (arXiv:1804.04964, Section 3, Theorem 3, the
passage after `eq:inj_equal_edge`, lines 1453--1471 of
`Papers/1804.04964/paper_normal.tex`).

For the injective square-lattice theorem
(`TNLean.PEPS.prod_perVertexScalar_eq_one`) the nonvanishing state coefficient is
supplied by vertex injectivity (`exists_stateCoeff_ne_zero`). The normal theorem
assumes injectivity only *after blocking*, so vertex injectivity is unavailable.
Here the nonvanishing state coefficient is supplied instead by the region-injective
existence lemma `exists_stateCoeff_ne_zero_of_regionInjective`: a single region `R`
together with its set complement, both blocked-tensor injective, with positive
bonds, already forces a nonzero closed state coefficient. The rest of the argument
(substituting the per-vertex relation, factoring out the scalar product, and
cancelling with `applyGauge_stateCoeff`) is identical to the injective case.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Theorem 3,
  lines 1453--1471 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- **The per-vertex scalars multiply to one (region-injective form).**

If the per-vertex scalars `c` relate `A` to the gauge action of the second tensor
family at every vertex (`A_v = c_v · gaugeVertex B Z v`), then under
`SameState A B`, positive bonds, and a single region `R` whose block and complement
block are both blocked-tensor injective, the nonvanishing closed state equality
forces `∏_v c_v = 1`.

This is the region-injective analogue of `prod_perVertexScalar_eq_one`: the
nonvanishing state coefficient comes from region injectivity of `R` and its set
complement (`exists_stateCoeff_ne_zero_of_regionInjective`) rather than from vertex
injectivity. The substitution of the per-vertex relation into the state contraction,
the factoring of `∏_v c_v`, and the cancellation against
`applyGauge_stateCoeff B Z` are the same as in the injective case.

Source: arXiv:1804.04964, Section 3, Theorem 3, the passage after
`eq:inj_equal_edge`, lines 1453--1471 of `Papers/1804.04964/paper_normal.tex`. -/
theorem prod_perVertexScalar_eq_one_of_regionInjective (A B : Tensor G d)
    (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hAB : SameState A B)
    (Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (hbd : A.bondDim = B.bondDim)
    (c : V → ℂ)
    (hPV : ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
      A.component v η σ =
        c v * gaugeVertex B Z v (fun ie => Fin.cast (congr_fun hbd ie.1) (η ie)) σ) :
    (∏ v, c v) = 1 := by
  classical
  have hkey : ∀ σ : V → Fin d,
      stateCoeff A σ = (∏ v, c v) * stateCoeff (applyGauge B Z) σ := by
    intro σ
    have hAcoeff : stateCoeff A σ
        = ∑ η : VirtualConfig A,
            (∏ v, c v) * ∏ v, gaugeVertex B Z v
              (fun ie => Fin.cast (congr_fun hbd ie.1) (η ie.1)) (σ v) := by
      unfold stateCoeff
      refine Finset.sum_congr rfl (fun η _ => ?_)
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun v _ => ?_)
      exact hPV v (fun ie => η ie.1) (σ v)
    rw [hAcoeff, ← Finset.mul_sum]
    have hsum : (∑ η : VirtualConfig A, ∏ v, gaugeVertex B Z v
            (fun ie => Fin.cast (congr_fun hbd ie.1) (η ie.1)) (σ v))
        = stateCoeff (applyGauge B Z) σ := by
      unfold stateCoeff
      refine Fintype.sum_equiv
        (Equiv.piCongrRight (fun e => finCongr (congr_fun hbd e)))
        (fun η : VirtualConfig A => ∏ v, gaugeVertex B Z v
            (fun ie => Fin.cast (congr_fun hbd ie.1) (η ie.1)) (σ v))
        (fun ηB => ∏ v, (applyGauge B Z).component v (fun ie => ηB ie.1) (σ v))
        (fun η => ?_)
      refine Finset.prod_congr rfl (fun v _ => ?_)
      rfl
    rw [hsum]
  obtain ⟨σ, hσ⟩ := exists_stateCoeff_ne_zero_of_regionInjective A R hRA hCA hpos
  have hBσ : stateCoeff (applyGauge B Z) σ = stateCoeff A σ := by
    rw [applyGauge_stateCoeff B Z σ, ← hAB σ]
  have h1 : stateCoeff A σ = (∏ v, c v) * stateCoeff A σ :=
    (hkey σ).trans (by rw [hBσ])
  have h2 : (∏ v, c v) * stateCoeff A σ = 1 * stateCoeff A σ := by
    rw [one_mul]; exact h1.symm
  exact mul_right_cancel₀ hσ h2

end PEPS
end TNLean
