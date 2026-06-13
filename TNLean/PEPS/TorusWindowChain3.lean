import TNLean.PEPS.TorusWindowChain2
import TNLean.PEPS.RegionBlock.UnionInjectivityGeneralBlue

/-!
# Open-boundary chaining and the shared-corner cancellation for the staircase pair

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) closes Step 3 of its proof sketch with an
*open-boundary* cancellation: from the open-boundary equality of inserts on the
staircase patch `P` it cancels the shared injective completed corner to leave the
equality on the staircase end pair `S`.  This file builds the two reusable pieces the
faithful Step 3 needs and assembles them, never inverting the non-injective torus
complement `univ \ S` (the obstruction recorded in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3).

## The corner-extension composition

`extendInsert` composes across nested regions: extending an insert from `R` to `S`
and then from `S` to `P` is extending it directly from `R` to `P`
(`extendInsert_trans`).  The composition is the workhorse of the open-boundary patch
chaining: each consecutive-window open-boundary equality
(`horizontalConsecutiveWindow_extend_eq`, on the union `U`) is extended to the patch
`P` and chained by transitivity into one patch-level insert equality.

## The shared-corner cancellation

`extendInsert (S ⊆ R)` is injective when the added block `R \ S` is blocked-tensor
injective (`extendInsert_injective_of_blueInjective`): the blue-coupling combination
of the added block's blocked weights is inverted by the added block's left inverse,
which needs only the added block's injectivity, never `univ \ S`.  Cancelling the
shared completed corner from the patch equality through this injectivity yields the
end-pair insert equality, the faithful Step 3.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, the corollary and proof
  sketch at lines 2296--2445 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964); the
  filled-in derivation in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

/-! ### Linearity of the bare corner-extended coefficient

The bare corner-extended coefficient `bareExtendInsert hRS C` is linear in the insert
`C`: it contracts `C` against the fixed blue-coupling coefficient, so scaling `C` by a
constant scales the bare coefficient, and adding inserts adds the bare coefficients. -/

omit [DecidableEq V] in
/-- The bare corner-extended coefficient scales with the insert. -/
theorem bareExtendInsert_const_smul {R S : Finset V} (hRS : R ⊆ S) (c : ℂ)
    (C : RegionInsert (G := G) (d := d) A R) :
    bareExtendInsert (G := G) hRS (fun μ σ => c * C μ σ) =
      fun ν σ => c * bareExtendInsert (G := G) hRS C ν σ := by
  funext ν σ
  rw [bareExtendInsert, bareExtendInsert, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [mul_assoc]

end PEPS
end TNLean
