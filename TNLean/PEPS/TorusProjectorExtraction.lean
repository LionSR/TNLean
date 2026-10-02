/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusProjectorExpansion
import TNLean.PEPS.RegularTorusCompatibility
import TNLean.Algebra.CharacterProjectorTwirl
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Extraction of the two closure operators from a torus projector state

The trace pairing of SCP10 Lemma 4.6 is applied to every nonseam output bond.
One horizontal and one vertical seam bond are retained as matrix coordinates;
the other seam bonds are evaluated by the sum of the trace pairings. Thus the
same linear map extracts the simultaneous conjugacy sum for every closure pair.
No unitarity of the virtual representation is required.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, proof of Theorem 5.9,
`Papers/1001.3807/paper_v3.tex`, lines 1582–1621, and Lemma 4.6,
lines 1015–1029. The contraction is the actual oriented torus bond network.
-/

open scoped BigOperators Kronecker

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- Contracting the output bonds against specified linear functionals. This
map uses the physical four-leg coordinates of the actual torus network. -/
noncomputable def torusOutputBondPairing
    (Kh Kv : TorusVertex width height → Matrix V V ℂ →ₗ[ℂ] ℂ) :
    ((TorusVertex width height → V × V × V × V) → ℂ) →ₗ[ℂ] ℂ :=
  Fintype.linearCombination ℂ (fun β =>
    ∏ v, Kh v (Matrix.single (β v).2.1 (β v).1 1) *
      Kv v (Matrix.single (β v).2.2.2 (β v).2.2.1 1)) ∘ₗ
    LinearMap.pi (fun β => LinearMap.proj (torusBondSiteLabels β))

/-- A linear functional is the sum of its values on the matrix units, weighted
by the matrix entries. -/
theorem matrixLinearFunctional_eq_sum (f : Matrix V V ℂ →ₗ[ℂ] ℂ)
    (M : Matrix V V ℂ) :
    f M = ∑ i, ∑ j, f (Matrix.single i j 1) * M i j := by
  have h : M = ∑ i, ∑ j, M i j • Matrix.single i j 1 := by
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.matrix_eq_sum_single M
  calc
    f M = f (∑ i, ∑ j, M i j • Matrix.single i j 1) := congrArg f h
    _ = _ := by
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _

/-- The physical output contraction factors into one functional per oriented
bond. In particular, this identity does not assume a factorization of a state. -/
theorem torusOutputBondPairing_bondProduct
    (Kh Kv : TorusVertex width height → Matrix V V ℂ →ₗ[ℂ] ℂ)
    (H K : TorusVertex width height → Matrix V V ℂ) :
    torusOutputBondPairing Kh Kv (fun σ =>
      ∏ v, H v (σ (v.1 + 1, v.2)).2.2.2 (σ v).2.1 *
        K v (σ v).1 (σ (v.1, v.2 + 1)).2.2.1) =
      ∏ v, Kh v (H v) * Kv v (K v) := by
  simp only [torusOutputBondPairing, LinearMap.comp_apply,
    Fintype.linearCombination_apply, LinearMap.pi_apply, LinearMap.proj_apply,
    smul_eq_mul, torusBondSiteLabels, add_sub_cancel_right,
    Prod.eta, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (v : TorusVertex width height) (c : V × V × V × V) =>
    H v c.2.1 c.1 * K v c.2.2.2 c.2.2.1 *
      (Kh v (Matrix.single c.2.1 c.1 1) * Kv v (Matrix.single c.2.2.2 c.2.2.1 1)))]
  apply Finset.prod_congr rfl
  intro v _
  rw [matrixLinearFunctional_eq_sum, matrixLinearFunctional_eq_sum]
  simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  rw [Fintype.sum_last_first_four]
  apply Finset.sum_congr₂
  intro i _ j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr₂
  intro k _ l _
  ring

variable {G : Type*} [Group G] [Fintype G]

/-- The matrix-coordinate form of the trace duality functional from SCP10,
Lemma 4.6, lines 1015–1029. -/
noncomputable def torusDeltaPairing (U : G →* Matrix V V ℂ) (p : G) :
    Matrix V V ℂ →ₗ[ℂ] ℂ :=
  Representation.deltaPairing (Matrix.toLinAlgEquiv'.toMonoidHom.comp U) p ∘ₗ
    Matrix.toLinAlgEquiv'.toLinearMap

/-- The sum of the trace duality functionals evaluates every representation
operator to one. It removes additional seam copies in SCP10 Theorem 5.9. -/
noncomputable def torusSeamPairing (U : G →* Matrix V V ℂ) :
    Matrix V V ℂ →ₗ[ℂ] ℂ := ∑ p, torusDeltaPairing U p

open Classical in
/-- Trace duality in matrix coordinates, without a unitary hypothesis. -/
theorem torusDeltaPairing_apply_rep (U : G →* Matrix V V ℂ)
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    (p k : G) : torusDeltaPairing U p (U k) = if p = k then 1 else 0 := by
  change Representation.deltaPairing (Matrix.toLinAlgEquiv'.toMonoidHom.comp U) p
    ((Matrix.toLinAlgEquiv'.toMonoidHom.comp U) k) = _
  exact Representation.deltaPairing_rep_of_isSemiRegular _ hU p k

/-- Every operator on a seam has value one under the seam-removal functional. -/
theorem torusSeamPairing_apply_rep (U : G →* Matrix V V ℂ)
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    (k : G) : torusSeamPairing U (U k) = 1 := by
  classical
  simp only [torusSeamPairing, LinearMap.sum_apply, torusDeltaPairing_apply_rep U hU]
  simp

/-- The linear functional taking a specified matrix entry. -/
def torusMatrixEntry (i j : V) : Matrix V V ℂ →ₗ[ℂ] ℂ :=
  LinearMap.proj j ∘ₗ LinearMap.proj i

/-- The horizontal output-bond functional: retain the seam in row zero,
remove other seam copies, and apply the trace pairing on nonseam bonds. -/
noncomputable def torusHorizontalExtractionPairing (U : G →* Matrix V V ℂ)
    (i j : V) (v : TorusVertex width height) : Matrix V V ℂ →ₗ[ℂ] ℂ :=
  if v = (-1, 0) then torusMatrixEntry i j
  else if v.1 + 1 = 0 then torusSeamPairing U else torusDeltaPairing U 1

/-- The vertical output-bond functional, retaining the seam in column zero. -/
noncomputable def torusVerticalExtractionPairing (U : G →* Matrix V V ℂ)
    (i j : V) (v : TorusVertex width height) : Matrix V V ℂ →ₗ[ℂ] ℂ :=
  if v = (0, -1) then torusMatrixEntry i j
  else if v.2 + 1 = 0 then torusSeamPairing U else torusDeltaPairing U 1

/-- One explicit linear map on the actual physical four-leg tuples, independent
of the two closure labels. Its two retained output bonds are horizontal, then
vertical, as in SCP10 Theorem 5.9, lines 1582–1621. -/
noncomputable def torusProjectorExtraction (U : G →* Matrix V V ℂ) :
    ((TorusVertex width height → V × V × V × V) → ℂ) →ₗ[ℂ]
      Matrix (V × V) (V × V) ℂ :=
  LinearMap.pi fun i => LinearMap.pi fun j =>
    torusOutputBondPairing (torusHorizontalExtractionPairing U i.1 j.1)
      (torusVerticalExtractionPairing U i.2 j.2)

/-- Evaluating the explicit extraction on a product of bond entries gives the
product of its bond functionals. -/
theorem torusProjectorExtraction_bondProduct (U : G →* Matrix V V ℂ)
    (H K : TorusVertex width height → Matrix V V ℂ) (i j : V × V) :
    torusProjectorExtraction U (fun σ =>
      ∏ v, H v (σ (v.1 + 1, v.2)).2.2.2 (σ v).2.1 *
        K v (σ v).1 (σ (v.1, v.2 + 1)).2.2.1) i j =
      ∏ v, torusHorizontalExtractionPairing U i.1 j.1 v (H v) *
        torusVerticalExtractionPairing U i.2 j.2 v (K v) := by
  exact torusOutputBondPairing_bondProduct _ _ H K

open Classical in
/-- On a nonseam bond the trace functional equates its two group labels. -/
theorem torusDeltaPairing_apply_mul_inv (U : G →* Matrix V V ℂ)
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    (a b : G) : torusDeltaPairing U 1 (U (a * b⁻¹)) =
      if a = b then 1 else 0 := by
  classical
  rw [torusDeltaPairing_apply_rep U hU]
  simp only [eq_comm, mul_inv_eq_one]

omit [NeZero width] [NeZero height] in
/-- If the labels are constant, the horizontal pairing retains precisely one
copy of the conjugated horizontal closure operator. -/
theorem torusHorizontalExtractionPairing_constant (U : G →* Matrix V V ℂ)
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    (x h : G) (i j : V) (v : TorusVertex width height) :
    torusHorizontalExtractionPairing U i j v
      (U (x * torusHorizontalClosureElement h v * x⁻¹)) =
      if v = (-1, 0) then U (x * h * x⁻¹) i j else 1 := by
  classical
  unfold torusHorizontalExtractionPairing
  split_ifs with hv hs
  · subst v
    simp only [torusHorizontalClosureElement, neg_add_cancel, ↓reduceIte]
    rfl
  · exact torusSeamPairing_apply_rep U hU _
  · simp only [torusHorizontalClosureElement, hs, ↓reduceIte, mul_one,
      mul_inv_cancel, map_one]
    simpa using torusDeltaPairing_apply_rep U hU 1 1

omit [NeZero width] [NeZero height] in
/-- The retained vertical seam has the same simultaneous conjugation. -/
theorem torusVerticalExtractionPairing_constant (U : G →* Matrix V V ℂ)
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    (x g : G) (i j : V) (v : TorusVertex width height) :
    torusVerticalExtractionPairing U i j v
      (U (x * torusVerticalClosureElement g v * x⁻¹)) =
      if v = (0, -1) then U (x * g * x⁻¹) i j else 1 := by
  classical
  unfold torusVerticalExtractionPairing
  split_ifs with hv hs
  · subst v
    simp only [torusVerticalClosureElement, neg_add_cancel, ↓reduceIte]
    rfl
  · exact torusSeamPairing_apply_rep U hU _
  · simp only [torusVerticalClosureElement, hs, ↓reduceIte, mul_one,
      mul_inv_cancel, map_one]
    simpa using torusDeltaPairing_apply_rep U hU 1 1

/-- The constant vertex labelling extracts the horizontal and vertical closure
operators as their Kronecker product, including circumference one. -/
theorem torusProjectorExtraction_constant_bondProduct (U : G →* Matrix V V ℂ)
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    (x g h : G) :
    torusProjectorExtraction (width := width) (height := height) U (fun σ => ∏ v,
      U (x * torusHorizontalClosureElement h v * x⁻¹)
        (σ (v.1 + 1, v.2)).2.2.2 (σ v).2.1 *
      U (x * torusVerticalClosureElement g v * x⁻¹)
        (σ v).1 (σ (v.1, v.2 + 1)).2.2.1) =
      U (x * h * x⁻¹) ⊗ₖ U (x * g * x⁻¹) := by
  classical
  ext i j
  rw [torusProjectorExtraction_bondProduct]
  simp only [torusHorizontalExtractionPairing_constant U hU,
    torusVerticalExtractionPairing_constant U hU, Finset.prod_mul_distrib]
  simp

omit [NeZero width] [NeZero height] in
open Classical in
/-- Horizontal nonseam bonds detect equality of neighbouring labels. -/
theorem torusHorizontalExtractionPairing_nonseam (U : G →* Matrix V V ℂ)
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    (q : TorusVertex width height → G) (h : G) (i j : V)
    (v : TorusVertex width height) (hv : v.1 + 1 ≠ 0) :
    torusHorizontalExtractionPairing U i j v
      (U (q (v.1 + 1, v.2) * torusHorizontalClosureElement h v * (q v)⁻¹)) =
      if q (v.1 + 1, v.2) = q v then 1 else 0 := by
  have hn : v ≠ (-1, 0) := by
    intro h
    subst v
    simp at hv
  simp only [torusHorizontalExtractionPairing, hn, ↓reduceIte, hv,
    torusHorizontalClosureElement, mul_one]
  exact torusDeltaPairing_apply_mul_inv U hU _ _

omit [NeZero width] [NeZero height] in
open Classical in
/-- Vertical nonseam bonds detect equality with the upper neighbour. -/
theorem torusVerticalExtractionPairing_nonseam (U : G →* Matrix V V ℂ)
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    (q : TorusVertex width height → G) (g : G) (i j : V)
    (v : TorusVertex width height) (hv : v.2 + 1 ≠ 0) :
    torusVerticalExtractionPairing U i j v
      (U (q v * torusVerticalClosureElement g v * (q (v.1, v.2 + 1))⁻¹)) =
      if q v = q (v.1, v.2 + 1) then 1 else 0 := by
  have hn : v ≠ (0, -1) := by
    intro h
    subst v
    simp at hv
  simp only [torusVerticalExtractionPairing, hn, ↓reduceIte, hv,
    torusVerticalClosureElement, mul_one]
  exact torusDeltaPairing_apply_mul_inv U hU _ _

open Classical in
/-- The output contraction vanishes unless the labels synchronize away from
both seams. Surviving terms are the two conjugated closure operators. -/
theorem torusProjectorExtraction_label_bondProduct (U : G →* Matrix V V ℂ)
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    (q : TorusVertex width height → G) (g h : G) :
    torusProjectorExtraction U (fun σ => ∏ v,
      U (q (v.1 + 1, v.2) * torusHorizontalClosureElement h v * (q v)⁻¹)
        (σ (v.1 + 1, v.2)).2.2.2 (σ v).2.1 *
      U (q v * torusVerticalClosureElement g v * (q (v.1, v.2 + 1))⁻¹)
        (σ v).1 (σ (v.1, v.2 + 1)).2.2.1) =
      if IsTorusNonseamCompatible q then
        U (q (0, 0) * h * (q (0, 0))⁻¹) ⊗ₖ
          U (q (0, 0) * g * (q (0, 0))⁻¹) else 0 := by
  classical
  by_cases hq : IsTorusNonseamCompatible q
  · simp only [hq, ↓reduceIte, hq.eq_origin]
    exact torusProjectorExtraction_constant_bondProduct U hU _ g h
  · simp only [hq, ↓reduceIte]
    ext i j
    rw [torusProjectorExtraction_bondProduct]
    simp only [IsTorusNonseamCompatible, not_forall, not_and_or] at hq
    obtain ⟨v, hv⟩ := hq
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    rcases hv with ⟨hs, hn⟩ | ⟨hs, hn⟩
    · rw [torusHorizontalExtractionPairing_nonseam U hU q h _ _ v hs]
      simp only [hn, ↓reduceIte, zero_mul]
    · rw [torusVerticalExtractionPairing_nonseam U hU q g _ _ v hs]
      simp only [hn, ↓reduceIte, mul_zero]

/-- Summing the synchronized vertex labels gives one simultaneous conjugacy
sum, with the horizontal operator preceding the vertical operator. -/
theorem torusProjectorExtraction_sum_label_bondProduct (U : G →* Matrix V V ℂ)
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    (g h : G) :
    torusProjectorExtraction (width := width) (height := height) U
      (∑ q : TorusVertex width height → G, fun σ => ∏ v,
        U (q (v.1 + 1, v.2) * torusHorizontalClosureElement h v * (q v)⁻¹)
          (σ (v.1 + 1, v.2)).2.2.2 (σ v).2.1 *
        U (q v * torusVerticalClosureElement g v * (q (v.1, v.2 + 1))⁻¹)
          (σ v).1 (σ (v.1, v.2 + 1)).2.2.1) =
      ∑ x : G, U (x * h * x⁻¹) ⊗ₖ U (x * g * x⁻¹) := by
  classical
  rw [map_sum]
  simp only [torusProjectorExtraction_label_bondProduct U hU]
  refine (Fintype.sum_of_injective (fun x : G => fun _ : TorusVertex width height => x)
    (fun x y hxy => congrFun hxy (0, 0)) _ _ ?_ ?_).symm
  · intro q hq
    split_ifs with hc
    · exact (hq ⟨q (0, 0), (funext hc.eq_origin).symm⟩).elim
    · rfl
  · intro x
    have hc : IsTorusNonseamCompatible (fun _ : TorusVertex width height => x) :=
      fun _ => ⟨fun _ => rfl, fun _ => rfl⟩
    simp only [hc, ↓reduceIte]

/-- The same explicit physical extraction sends every actual torus averaging-
projector closure to its simultaneous-conjugacy operator. The scalar is the
product of the normalized local averages. Source: SCP10 Theorem 5.9,
lines 1582–1621. No contracted-state factorization is assumed. -/
theorem torusProjectorExtraction_torusGClosure (U : G →* Matrix V V ℂ)
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    (g h : G) :
    torusProjectorExtraction (width := width) (height := height) U
      (torusGClosure U (averagingSite U) g h) =
      ((Fintype.card G : ℂ)⁻¹ ^ Fintype.card (TorusVertex width height)) •
        (∑ x : G, U (x * h * x⁻¹) ⊗ₖ U (x * g * x⁻¹)) := by
  have hclosure : torusGClosure (width := width) (height := height)
      U (averagingSite U) g h =
      ((Fintype.card G : ℂ)⁻¹ ^ Fintype.card (TorusVertex width height)) •
        (∑ q : TorusVertex width height → G, fun σ => ∏ v,
          U (q (v.1 + 1, v.2) * torusHorizontalClosureElement h v * (q v)⁻¹)
            (σ (v.1 + 1, v.2)).2.2.2 (σ v).2.1 *
          U (q v * torusVerticalClosureElement g v * (q (v.1, v.2 + 1))⁻¹)
            (σ v).1 (σ (v.1, v.2 + 1)).2.2.1) := by
    funext σ
    rw [torusGClosure, torusBondNetwork_averagingSite]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
      torusHorizontalClosure_eq_map_element, torusVerticalClosure_eq_map_element,
      ← map_mul]
  rw [hclosure, map_smul, torusProjectorExtraction_sum_label_bondProduct U hU]

/-- The normalization in the extraction is positive as a real number. -/
theorem torusProjectorExtraction_normalization_pos :
    0 < (Fintype.card G : ℝ)⁻¹ ^ Fintype.card (TorusVertex width height) := by
  exact pow_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)) _

end TNLean.PEPS
