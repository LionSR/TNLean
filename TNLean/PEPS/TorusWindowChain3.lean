import TNLean.PEPS.TorusWindowChain2
import TNLean.PEPS.RegionBlock.UnionInjectivityGeneralBlue

/-!
# Linearity of the corner extension for the open-boundary staircase chaining

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) closes Step 3 of its proof sketch with an
*open-boundary* cancellation: from the open-boundary equality of inserts on the
staircase patch `P` it cancels the shared injective completed corner to leave the
equality on the staircase end pair `S`, never inverting the non-injective torus
complement `univ \ S` (the obstruction recorded in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3).

This file collects the geometry-free algebraic facts that route feeds on: the corner
extension `extendInsert` of `TNLean/PEPS/TorusWindowChain2.lean` is linear in its
insert (`bareExtendInsert_const_smul`, `extendInsert_const_smul`), and the sub-region
restriction composes (`restrictSubRegionσ_restrictSubRegionσ`), the leg identity
behind the corner-extension composition.  The corner-extension composition
`extendInsert (S ⊆ P) (extendInsert (R ⊆ S) C) = extendInsert (R ⊆ P) C` is proved in
`TNLean/PEPS/TorusWindowChain4.lean` as `extendInsert_trans`.  The remaining fiber-gluing
engine the route needs — the shared-corner cancellation (injectivity of
`extendInsert (S ⊆ R)` from injectivity of the added block `R \ S` alone) — is
stated and scoped in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3.

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

omit [DecidableEq V] in
/-- The corner-extended insert scales with the insert: pulling a constant out of `C`
pulls it out of `extendInsert hRS C`.  Used to commute the bare/clean rescaling through
the composition. -/
theorem extendInsert_const_smul {R S : Finset V} (hRS : R ⊆ S) (c : ℂ)
    (C : RegionInsert (G := G) (d := d) A R) :
    extendInsert (G := G) hRS (fun μ σ => c * C μ σ) =
      fun ν σ => c * extendInsert (G := G) hRS C ν σ := by
  funext ν σ
  rw [extendInsert_eq_smul_bare, extendInsert_eq_smul_bare, bareExtendInsert_const_smul]
  ring

omit [Fintype V] [LinearOrder V] [DecidableEq V] in
/-- The restriction to a sub-region composes: restricting from `S` to `R ⊆ S` after
restricting from `P` to `S` is restricting directly from `P` to `R`.  This is the leg
identity behind the corner-extension composition: the inner extension reads the same
`R`-physical leg whether through `S` or directly. -/
theorem restrictSubRegionσ_restrictSubRegionσ {R S P : Finset V} (hRS : R ⊆ S) (hSP : S ⊆ P)
    (σ : RegionPhysicalConfig (V := V) (d := d) P) :
    restrictSubRegionσ (V := V) (d := d) hRS
        (restrictSubRegionσ (V := V) (d := d) hSP σ) =
      restrictSubRegionσ (V := V) (d := d) (hRS.trans hSP) σ := rfl

end PEPS
end TNLean
