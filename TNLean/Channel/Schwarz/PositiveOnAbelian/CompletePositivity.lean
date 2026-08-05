/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.ChoiJamiolkowski
import TNLean.Channel.Schwarz.ChoiCompression
import TNLean.Channel.Schwarz.PositiveOnAbelian.Characterization
import TNLean.Channel.Schwarz.TwoPositive

/-!
# Complete positivity from positivity, commutative side (Wolf Proposition 1.6)

This file proves the finite-dimensional, matrix-algebra form of Wolf's
Proposition 1.6: a positive map is completely positive whenever its range
(the "codomain side"), or its trace-adjoint's range (the "domain side"), is
commutative.

Local source: `Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`,
lines 600--614 (proposition, proof, and the licensing remark discussed
below).

**Scope restriction**: Wolf's Proposition 1.6 is stated for a positive map
`T : 𝒜 → ℬ` between *unital $C^*$-algebras*, with the hypothesis "`𝒜` or `ℬ`
is commutative" read as commutativity of the whole algebra. Wolf's own proof
is given only in finite dimensions and only ever uses that the *outputs of
`T` involved in the argument* commute pairwise (his remark after the proof:
"the algebra structure of `𝒜` was never used, so complete positivity also
holds for positive maps which map an operator system to any commutative
$C^*$-algebra"). `HasCommutingRange` below formalizes exactly this weaker,
range-only hypothesis, which is what the proof actually establishes; it is
implied by (not equivalent to) "the codomain is commutative" when `T`'s
domain and codomain are both taken to be the *full* matrix algebra `M_D(ℂ)`,
since `M_D(ℂ)` itself is commutative only for `D ≤ 1`. Documented in
`docs/paper-gaps/wolf_prop16_cp_positivity_commutative_side.tex`.

## Main definitions

* `PositiveOnAbelian.HasCommutingRange`: every two images of a linear map
  commute — the range-only form of "the codomain is commutative" that
  Wolf's proof of Proposition 1.6 actually uses.

## Main statements

* `PositiveOnAbelian.isCPMap_of_isPositiveMap_of_hasCommutingRange`: Wolf
  Proposition 1.6, commutative-codomain case.
* `PositiveOnAbelian.isCPMap_of_isPositiveMap_of_hasCommutingRange_adjoint`:
  Wolf Proposition 1.6, commutative-domain case, via the duality argument
  Wolf's proof invokes (`T` completely positive iff `T*` is).
* `PositiveOnAbelian.isCPMap_of_isPositiveMap_of_commutingRange_or`: the
  combined "either side" statement.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 1.6]
  [Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset

namespace PositiveOnAbelian

variable {D : ℕ}

/-- Every two images of `T` commute: `T`'s range spans a commutative
subalgebra. This is the range-only form of "the codomain is commutative"
that Wolf's proof of Proposition 1.6 actually uses (see the module
docstring). -/
def HasCommutingRange (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    Prop :=
  ∀ X Y, Commute (T X) (T Y)

/-- If every two images of `T` commute, then the images of any block matrix
`a` under `T` commute pairwise. -/
theorem pairwiseCommuteImages_of_hasCommutingRange
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : HasCommutingRange T) {n : ℕ}
    (a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ)) :
    PairwiseCommuteImages T a :=
  fun i j k l => hT (a i j) (a k l)

/-! ### The Choi matrix as a block quadratic form -/

/-- The `omegaProj`-slice block family is block positive, independently of any
linear map: this is the coefficient family of the Choi matrix of the identity
map, which is `omegaProj D` itself. -/
private theorem blockPositive_bipartiteSlice_omegaProj [NeZero D] :
    BlockPositive (D := D) (fun i j => Matrix.bipartiteSlice (Matrix.omegaProj D) i j) := by
  intro ψ
  have hterm : ∀ i j : Fin D, star (ψ i) ⬝ᵥ
      (Matrix.bipartiteSlice (Matrix.omegaProj D) i j).mulVec (ψ j) =
      (D : ℂ)⁻¹ * (starRingEnd ℂ (ψ i i) * ψ j j) := by
    intro i j
    rw [ChoiJamiolkowski.omegaSlice_eq_single,
      ChoiJamiolkowski.omegaCoeff_eq_inv (Nat.pos_of_ne_zero (NeZero.ne D)),
      Matrix.single_mulVec]
    simp only [dotProduct, Function.update_apply, Pi.zero_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', mem_univ, if_true, Pi.star_apply, one_div, RCLike.star_def]
    ring
  simp only [hterm]
  simp_rw [← Finset.mul_sum]
  set w : ℂ := ∑ i : Fin D, ψ i i with hw
  have hsum : ∑ i : Fin D, (starRingEnd ℂ (ψ i i) * w) = (starRingEnd ℂ w) * w := by
    rw [← Finset.sum_mul, hw, map_sum]
  rw [hsum,
    show (D : ℂ)⁻¹ = ((D : ℝ)⁻¹ : ℝ) from by
      rw [Complex.ofReal_inv, Complex.ofReal_natCast],
    ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul]
  exact_mod_cast mul_nonneg (by positivity : (0:ℝ) ≤ (D : ℝ)⁻¹) (Complex.normSq_nonneg w)

/-- The Choi-matrix quadratic form of `T` at `φ` is the `omegaProj`-slice block
quadratic form of `T` at the reshaping of `φ` into a `Fin D`-indexed family of
vectors. -/
private theorem choiMatrix_dotProduct_mulVec_eq_blockQuadraticForm
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (φ : Fin D × Fin D → ℂ) :
    star φ ⬝ᵥ (ChoiJamiolkowski.choiMatrix T).mulVec φ =
      blockQuadraticForm T (fun i j => Matrix.bipartiteSlice (Matrix.omegaProj D) i j)
        (fun k i₁ => φ (i₁, k)) := by
  simp only [dotProduct, Matrix.mulVec, ChoiJamiolkowski.choiMatrix, Matrix.tensorMapId_apply,
    Pi.star_apply, blockQuadraticForm, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p2 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q2 _ => ?_
  rw [Finset.sum_comm, ← Finset.mul_sum]

/-! ### Wolf Proposition 1.6, commutative side -/

/-- **Wolf Proposition 1.6, commutative-codomain case**: a positive linear
endomorphism of `M_D(ℂ)` whose range is commutative is completely positive.

This formalizes exactly what Wolf's finite-dimensional proof of Proposition
1.6 establishes (see the module docstring for the precise relationship to
the source statement). -/
theorem isCPMap_of_isPositiveMap_of_hasCommutingRange [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hcomm : HasCommutingRange T) : IsCPMap T := by
  rw [ChoiJamiolkowski.cp_iff_choi_posSemidef]
  refine Matrix.posSemidef_of_dotProduct_mulVec_nonneg_complex fun φ => ?_
  rw [choiMatrix_dotProduct_mulVec_eq_blockQuadraticForm]
  exact quadraticForm_nonneg_of_isPositiveMap_of_commuting_images hT
    (fun i j => Matrix.bipartiteSlice (Matrix.omegaProj D) i j)
    blockPositive_bipartiteSlice_omegaProj
    (pairwiseCommuteImages_of_hasCommutingRange hcomm _) _

/-- **Wolf Proposition 1.6, commutative-domain case**: a positive linear
endomorphism of `M_D(ℂ)` whose trace-pairing adjoint has commutative range is
completely positive.

This is the "domain commutative" disjunct of Wolf's Proposition 1.6, obtained
by the duality argument his own proof invokes: `T` is completely positive iff
its trace-pairing adjoint `T*` is, and `T*` has the commutative-codomain
hypothesis established above. -/
theorem isCPMap_of_isPositiveMap_of_hasCommutingRange_adjoint [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hcomm : HasCommutingRange (Matrix.traceAdjointMap T)) :
    IsCPMap T := by
  rw [← isCPMap_traceAdjointMap_iff]
  exact isCPMap_of_isPositiveMap_of_hasCommutingRange hT.traceAdjointMap hcomm

/-- **Wolf Proposition 1.6** (Complete positivity from positivity): a positive
linear endomorphism of `M_D(ℂ)` is completely positive whenever its range, or
its trace-pairing adjoint's range, is commutative.

Local source: `Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`,
lines 600--614. See the module docstring for the precise relationship
between `HasCommutingRange` and Wolf's "commutative" hypothesis. -/
theorem isCPMap_of_isPositiveMap_of_commutingRange_or [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ} (hT : IsPositiveMap T)
    (hcomm : HasCommutingRange T ∨ HasCommutingRange (Matrix.traceAdjointMap T)) :
    IsCPMap T := by
  rcases hcomm with hcomm | hcomm
  · exact isCPMap_of_isPositiveMap_of_hasCommutingRange hT hcomm
  · exact isCPMap_of_isPositiveMap_of_hasCommutingRange_adjoint hT hcomm

end PositiveOnAbelian
