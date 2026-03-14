/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Schwarz.SchwarzNormal

/-!
# Schwarz inequalities for subnormal and commuting dominant operators

This file records the Chapter 5 extensions of the normal-input Schwarz inequality
that appear in Wolf's notes.

## Main declarations

* `KadisonSchwarz.IsSubnormal`
* `KadisonSchwarz.schwarz_inequality_subnormal_operator`
* `KadisonSchwarz.commuting_dominant_right_bound`
* `KadisonSchwarz.kadison_schwarz_commuting_dominant_cp_of_two_sided_bound`
* `KadisonSchwarz.kadison_schwarz_commuting_dominant_cp`
* `KadisonSchwarz.schwarz_inequality_commuting_dominant_operator`

The full positive-map statements are recorded with placeholders for the block-matrix
and subnormal-extension infrastructure.  The CP/Kraus proof is available in the
two-sided-bound variant, where the conclusion is an immediate consequence of the
existing Kadison--Schwarz inequality together with monotonicity of positive maps.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorems 5.5 and 5.6][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Finset

namespace KadisonSchwarz

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- An operator `A` is subnormal if it is the north-west block of a normal
block-upper-triangular operator on a larger space `H ⊕ H⊥`. -/
def IsSubnormal (A : Mat) : Prop :=
  ∃ E : ℕ,
    ∃ B : Matrix (Fin D) (Fin E) ℂ,
      ∃ C : Matrix (Fin E) (Fin E) ℂ,
        let N : Matrix (Fin D ⊕ Fin E) (Fin D ⊕ Fin E) ℂ := Matrix.fromBlocks A B 0 C
        Nᴴ * N = N * Nᴴ

/-- Wolf Thm. 5.5: Schwarz inequality for subnormal operators.

The intended proof composes the given positive subunital map with the north-west
block extraction map on a normal extension of `A`, then applies Wolf Prop. 5.1
(`schwarz_inequality_normal_operator`) to the resulting positive map. -/
theorem schwarz_inequality_subnormal_operator
    (T : Mat →ₗ[ℂ] Mat)
    (hPos : IsPositiveMap T)
    (hSub : T 1 ≤ (1 : Mat))
    (A : Mat)
    (hSubnormal : IsSubnormal A) :
    T (Aᴴ) * T A ≤ T (Aᴴ * A) ∧ T A * T (Aᴴ) ≤ T (Aᴴ * A) := by
  sorry

/-- Linear-map wrapper for the adjoint Kraus map.

This is convenient for reusing the generic positivity/monotonicity API from
`PositiveMapProperties`. -/
noncomputable def krausAdjointMapLinear (K : Fin d → Mat) : Mat →ₗ[ℂ] Mat where
  toFun := krausAdjointMap K
  map_add' := by
    intro X Y
    simp [krausAdjointMap, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c X
    simp [krausAdjointMap, Finset.smul_sum, Matrix.mul_assoc]

/-- The adjoint Kraus map is positive. -/
theorem krausAdjointMapLinear_isPositiveMap (K : Fin d → Mat) :
    IsPositiveMap (krausAdjointMapLinear (d := d) (D := D) K) := by
  intro X hX
  classical
  simpa [krausAdjointMapLinear, krausAdjointMap, Matrix.mul_assoc] using
    Matrix.posSemidef_sum (s := Finset.univ) (x := fun i => (K i)ᴴ * X * K i)
      (fun i _ => by
        simpa [Matrix.mul_assoc] using hX.mul_mul_conjTranspose_same (B := (K i)ᴴ))

/-- The missing order-theoretic step in Wolf Thm. 5.6: if `D ≥ 0` commutes with
`A` and dominates `Aᴴ * A`, then it also dominates `A * Aᴴ`.

Wolf proves this first for invertible `D` using `X = A D^{-1/2}`, and then passes
to the general case by replacing `D` with `D + ε • 1` and letting `ε → 0`. -/
lemma commuting_dominant_right_bound
    (A Dom : Mat)
    (hDomPos : Dom.PosSemidef)
    (hComm : Commute Dom A)
    (hDom : Aᴴ * A ≤ Dom) :
    A * Aᴴ ≤ Dom := by
  sorry

/-- CP/Kraus version of Wolf Thm. 5.6 under both dominant bounds.

Once both inequalities `Aᴴ * A ≤ D` and `A * Aᴴ ≤ D` are available, the proof is
just Kadison--Schwarz for the adjoint Kraus map, followed by monotonicity of the
positive map `X ↦ ∑ᵢ Kᵢ† X Kᵢ`. -/
theorem kadison_schwarz_commuting_dominant_cp_of_two_sided_bound
    (K : Fin d → Mat)
    (h_tp : IsTPKraus K)
    (A Dom : Mat)
    (_hDomPos : Dom.PosSemidef)
    (_hComm : Commute Dom A)
    (hDomLeft : Aᴴ * A ≤ Dom)
    (hDomRight : A * Aᴴ ≤ Dom) :
    krausAdjointMap K (Aᴴ) * krausAdjointMap K A ≤ krausAdjointMap K Dom ∧
      krausAdjointMap K A * krausAdjointMap K (Aᴴ) ≤ krausAdjointMap K Dom := by
  let T : Mat →ₗ[ℂ] Mat := krausAdjointMapLinear (d := d) (D := D) K
  have hPosT : IsPositiveMap T := krausAdjointMapLinear_isPositiveMap (d := d) (D := D) K
  have hKSLeft' : (krausAdjointMap K A)ᴴ * krausAdjointMap K A ≤ krausAdjointMap K (Aᴴ * A) := by
    rw [Matrix.le_iff]
    exact kadison_schwarz_adjoint K h_tp A
  have hKSLeft : krausAdjointMap K (Aᴴ) * krausAdjointMap K A ≤ krausAdjointMap K (Aᴴ * A) := by
    simpa [krausAdjointMap_conjTranspose] using hKSLeft'
  have hDomLeftMap : krausAdjointMap K (Aᴴ * A) ≤ krausAdjointMap K Dom := by
    simpa [T] using hPosT.map_le_map hDomLeft
  have hKSRight' : (krausAdjointMap K (Aᴴ))ᴴ * krausAdjointMap K (Aᴴ) ≤
      krausAdjointMap K (A * Aᴴ) := by
    simpa [conjTranspose_conjTranspose] using
      (show (krausAdjointMap K (Aᴴ))ᴴ * krausAdjointMap K (Aᴴ) ≤ krausAdjointMap K ((Aᴴ)ᴴ * Aᴴ) from by
        rw [Matrix.le_iff]
        exact kadison_schwarz_adjoint K h_tp (Aᴴ))
  have hKSRight : krausAdjointMap K A * krausAdjointMap K (Aᴴ) ≤
      krausAdjointMap K (A * Aᴴ) := by
    simpa [krausAdjointMap_conjTranspose] using hKSRight'
  have hDomRightMap : krausAdjointMap K (A * Aᴴ) ≤ krausAdjointMap K Dom := by
    simpa [T] using hPosT.map_le_map hDomRight
  exact ⟨hKSLeft.trans hDomLeftMap, hKSRight.trans hDomRightMap⟩

/-- Wolf Thm. 5.6 in the CP/Kraus setting.

The only missing ingredient beyond the previous theorem is the right-dominance
lemma `commuting_dominant_right_bound`. -/
theorem kadison_schwarz_commuting_dominant_cp
    (K : Fin d → Mat)
    (h_tp : IsTPKraus K)
    (A Dom : Mat)
    (hDomPos : Dom.PosSemidef)
    (hComm : Commute Dom A)
    (hDom : Aᴴ * A ≤ Dom) :
    krausAdjointMap K (Aᴴ) * krausAdjointMap K A ≤ krausAdjointMap K Dom ∧
      krausAdjointMap K A * krausAdjointMap K (Aᴴ) ≤ krausAdjointMap K Dom := by
  have hDomRight : A * Aᴴ ≤ Dom :=
    commuting_dominant_right_bound (A := A) (Dom := Dom) hDomPos hComm hDom
  exact kadison_schwarz_commuting_dominant_cp_of_two_sided_bound
    (K := K) h_tp A Dom hDomPos hComm hDom hDomRight

/-- Wolf Thm. 5.6: Schwarz inequality for commuting dominant operators.

The proof follows Wolf's normal-block-matrix construction.  One first proves the
auxiliary order lemma `commuting_dominant_right_bound`, then builds a normal block
matrix `N` with `θ(N) = A` and `θ(Nᴴ * N) = D`, and finally applies Wolf Prop. 5.1
through the composed map `T ∘ θ`. -/
theorem schwarz_inequality_commuting_dominant_operator
    (T : Mat →ₗ[ℂ] Mat)
    (hPos : IsPositiveMap T)
    (hSub : T 1 ≤ (1 : Mat))
    (A Dom : Mat)
    (hDomPos : Dom.PosSemidef)
    (hComm : Commute Dom A)
    (hDom : Aᴴ * A ≤ Dom) :
    T (Aᴴ) * T A ≤ T Dom ∧ T A * T (Aᴴ) ≤ T Dom := by
  sorry

end KadisonSchwarz
