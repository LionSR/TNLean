/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointExtendedBoundary
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointEmbedding
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Rectangular boundary factors of the actual zero-parameter chain

In the extended product at parameter zero, each internal bond carries the
projection onto the first summand. Factoring that projection as `V Vᴴ`
therefore leaves the actual first endpoint tensor at every interior site,
a rectangular first letter, and a rectangular last letter.

The rectangular letters are given explicitly in all physical sectors.
Their inner register lies in the first sector. Their outer register is
free: its first sector gives an `A₀` letter, while its second sector gives
a raw matrix unit with a free exterior `D₁` index. Thus the four outer
sector choices all have the same `A₀` bulk. The algebraic statement is
valid for arbitrary endpoint tensors, without injectivity or gap assumptions.

Source: arXiv:2203.12563, Section 5, `defAgamma`, lines 1586–1601 and
1690–1692. No spectral comparison or identification of orthogonal
projectors is asserted by this coordinate factorization.
-/

open scoped Matrix

namespace MPSTensor
namespace MPOSymmetry

variable {d D E D₀ D₁ : ℕ}

/-- Factoring every inserted matrix as `V Vᴴ` compresses all bulk letters
and leaves two rectangular boundary letters. No isometry condition is
needed for this algebraic identity.
Source context: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem insertedEvalWord_factor_boundary
    (A : MPSTensor d D) (V : Matrix (Fin D) (Fin E) ℂ)
    (i j : Fin d) (w : List (Fin d)) :
    insertedEvalWord A (V * Vᴴ) (i :: (w ++ [j])) =
      (A i * V) * Kraus.evalWord (fun k => Vᴴ * A k * V) w * (Vᴴ * A j) := by
  induction w generalizing i with
  | nil => simp [insertedEvalWord, Kraus.evalWord, Matrix.mul_assoc]
  | cons k w ih =>
      rw [List.cons_append,
        insertedEvalWord_cons_of_ne_nil A (V * Vᴴ) i (by simp), ih]
      simp only [Kraus.evalWord_cons, Matrix.mul_assoc]

/-- Encode the two physical registers in the common physical space.
Source: arXiv:2203.12563, Section 5, `defAgamma`, lines 1586–1601. -/
def mixedEndpointPhysicalIndex
    (a b : Fin D₀ ⊕ Fin D₁) : Fin ((D₀ + D₁) * (D₀ + D₁)) :=
  finProdFinEquiv (finSumFinEquiv a, finSumFinEquiv b)

/-- Include an endpoint physical letter into the first diagonal sector.
Source: arXiv:2203.12563, Section 5, `defAgamma`, lines 1586–1601. -/
def mixedEndpointFirstPhysicalIndex (D₁ : ℕ) (p : Fin (D₀ * D₀)) :
    Fin ((D₀ + D₁) * (D₀ + D₁)) :=
  mixedEndpointPhysicalIndex (.inl (finProdFinEquiv.symm p).1)
    (.inl (finProdFinEquiv.symm p).2)

/-- The first rectangular letter: diagonal physical letters retain `A₀`,
second-to-first letters are raw matrix units, and the second inner sector
vanishes. The exterior row is the free spectator in the mixed sector.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointFirstBoundaryLetter
    (A₀ : MPSTensor (D₀ * D₀) D₀) (a b : Fin D₀ ⊕ Fin D₁) :
    Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀) ℂ :=
  match a, b with
  | .inl a, .inl b => Matrix.fromRows (A₀ (finProdFinEquiv (a, b))) 0
  | .inr a, .inl b => Matrix.single (.inr a) b 1
  | _, .inr _ => 0

/-- The last rectangular letter: diagonal physical letters retain `A₀`,
first-to-second letters are raw matrix units, and the second inner sector
vanishes. The exterior column is the free spectator in the mixed sector.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointLastBoundaryLetter
    (A₀ : MPSTensor (D₀ * D₀) D₀) (a b : Fin D₀ ⊕ Fin D₁) :
    Matrix (Fin D₀) (Fin D₀ ⊕ Fin D₁) ℂ :=
  match a, b with
  | .inl a, .inl b => Matrix.fromCols (A₀ (finProdFinEquiv (a, b))) 0
  | .inl a, .inr b => Matrix.single a (.inr b) 1
  | .inr _, _ => 0

/-- Extracting the first virtual columns of an actual mixed letter gives
exactly the rectangular first boundary letter, in all four sectors.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointBase_mul_firstInclusion
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (a b : Fin D₀ ⊕ Fin D₁) :
    mixedEndpointBase A₀ A₁ (mixedEndpointPhysicalIndex a b) *
        Matrix.coordinateInclusion (Fin.castAddEmb D₁ : Fin D₀ ↪ Fin (D₀ + D₁)) =
      (mixedEndpointFirstBoundaryLetter A₀ a b).submatrix finSumFinEquiv.symm id := by
  rw [Matrix.mul_coordinateInclusion]
  ext i j
  simp only [mixedEndpointBase, mixedEndpointPhysicalIndex, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Fin.castAddEmb_apply,
    finSumFinEquiv_symm_apply_castAdd, id_eq]
  cases a <;> cases b <;> cases finSumFinEquiv.symm i <;>
    simp [mixedEndpointLetter, mixedEndpointFirstBoundaryLetter,
      Matrix.fromBlocks, Matrix.fromRows, Matrix.single_apply] <;> rfl

/-- Extracting the first virtual rows of an actual mixed letter gives
exactly the rectangular last boundary letter, in all four sectors.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem firstInclusion_conjTranspose_mul_mixedEndpointBase
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (a b : Fin D₀ ⊕ Fin D₁) :
    (Matrix.coordinateInclusion (Fin.castAddEmb D₁ : Fin D₀ ↪ Fin (D₀ + D₁)))ᴴ *
        mixedEndpointBase A₀ A₁ (mixedEndpointPhysicalIndex a b) =
      (mixedEndpointLastBoundaryLetter A₀ a b).submatrix id finSumFinEquiv.symm := by
  rw [Matrix.conjTranspose_coordinateInclusion_mul]
  ext i j
  simp only [mixedEndpointBase, mixedEndpointPhysicalIndex, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Fin.castAddEmb_apply,
    finSumFinEquiv_symm_apply_castAdd, id_eq]
  cases a <;> cases b <;> cases finSumFinEquiv.symm j <;>
    simp [mixedEndpointLetter, mixedEndpointLastBoundaryLetter,
      Matrix.fromBlocks, Matrix.fromCols, Matrix.single_apply]

/-- Every interior letter of the projected chain is the actual embedded
first endpoint. Only the two rectangular factors retain an exterior bond.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_insertedEvalWord_boundaryFactors
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (i j : Fin ((D₀ + D₁) * (D₀ + D₁)))
    (w : List (Fin ((D₀ + D₁) * (D₀ + D₁)))) :
    let V := Matrix.coordinateInclusion (Fin.castAddEmb D₁ : Fin D₀ ↪ Fin (D₀ + D₁))
    insertedEvalWord (mixedEndpointBase A₀ A₁) (bondInterpolationMatrix D₀ D₁ 0)
        (i :: (w ++ [j])) =
      (mixedEndpointBase A₀ A₁ i * V) * Kraus.evalWord (mixedEndpointLeftTensor A₀ D₁) w *
        (Vᴴ * mixedEndpointBase A₀ A₁ j) := by
  dsimp only
  rw [← coordinateInclusion_first_projection_eq_bondWeight,
    insertedEvalWord_factor_boundary]
  simp only [mixedEndpointBase_first_compression]

/-- The first-sector physical inclusion recovers the endpoint letter.
Source: arXiv:2203.12563, Section 5, `defAgamma`, lines 1586–1601. -/
@[simp]
theorem mixedEndpointLeftTensor_firstPhysicalIndex
    (A₀ : MPSTensor (D₀ * D₀) D₀) (p : Fin (D₀ * D₀)) :
    mixedEndpointLeftTensor A₀ D₁ (mixedEndpointFirstPhysicalIndex D₁ p) = A₀ p := by
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective p
  simp [mixedEndpointLeftTensor, mixedEndpointFirstPhysicalIndex, mixedEndpointPhysicalIndex]

/-- A word entirely in the first diagonal physical sector is the original
endpoint word, with no additional normalization or virtual weight.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem evalWord_mixedEndpointLeftTensor_firstPhysicalIndex
    (A₀ : MPSTensor (D₀ * D₀) D₀) (w : List (Fin (D₀ * D₀))) :
    Kraus.evalWord (mixedEndpointLeftTensor A₀ D₁)
        (w.map (mixedEndpointFirstPhysicalIndex D₁)) = Kraus.evalWord A₀ w := by
  induction w with
  | nil => simp [Kraus.evalWord]
  | cons p w ih => simp only [List.map_cons, Kraus.evalWord_cons,
      mixedEndpointLeftTensor_firstPhysicalIndex, ih]

/-- Exact sector identification of every extended word of length at least
two. The same statement includes all four outer choices and both excluded
inner sectors. The entire bulk is the actual `A₀` product; only the two
explicitly displayed rectangular factors depend on the outer sectors.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_insertedEvalWord_sectorFactors
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (a b c e : Fin D₀ ⊕ Fin D₁) (w : List (Fin (D₀ * D₀))) :
    insertedEvalWord (mixedEndpointBase A₀ A₁) (bondInterpolationMatrix D₀ D₁ 0)
        (mixedEndpointPhysicalIndex a b ::
          (w.map (mixedEndpointFirstPhysicalIndex D₁) ++ [mixedEndpointPhysicalIndex c e])) =
      (mixedEndpointFirstBoundaryLetter A₀ a b).submatrix finSumFinEquiv.symm id *
        Kraus.evalWord A₀ w *
        (mixedEndpointLastBoundaryLetter A₀ c e).submatrix id finSumFinEquiv.symm := by
  rw [mixedEndpoint_insertedEvalWord_boundaryFactors,
    mixedEndpointBase_mul_firstInclusion, firstInclusion_conjTranspose_mul_mixedEndpointBase,
    evalWord_mixedEndpointLeftTensor_firstPhysicalIndex]

/-- The coefficient of the actual extended boundary map on an arbitrary
outer sector and an all-first-sector bulk has the rectangular factorization
above. This is an identity for the actual `Γ′₀,N`, not for a surrogate map.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_insertedGroundSpaceMap_sectorFactors
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    {N : ℕ} (X : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ)
    (a b c e : Fin D₀ ⊕ Fin D₁) (σ : Cfg (D₀ * D₀) N) :
    insertedGroundSpaceMap (mixedEndpointBase A₀ A₁) (bondInterpolationMatrix D₀ D₁ 0)
        (N + 1 + 1) X
        (Fin.cons (mixedEndpointPhysicalIndex a b)
          (Fin.snoc (fun k => mixedEndpointFirstPhysicalIndex D₁ (σ k))
            (mixedEndpointPhysicalIndex c e))) =
      Matrix.trace
        ((mixedEndpointFirstBoundaryLetter A₀ a b).submatrix finSumFinEquiv.symm id *
          Kraus.evalWord A₀ (List.ofFn σ) *
          (mixedEndpointLastBoundaryLetter A₀ c e).submatrix id finSumFinEquiv.symm * X) := by
  rw [insertedGroundSpaceMap_apply, List.ofFn_cons, List.ofFn_snoc]
  have hword : List.ofFn (fun k => mixedEndpointFirstPhysicalIndex D₁ (σ k)) =
      (List.ofFn σ).map (mixedEndpointFirstPhysicalIndex D₁) := by
    simp only [List.map_ofFn, Function.comp_def]
  rw [hword, mixedEndpoint_insertedEvalWord_sectorFactors]

/-- When both outer registers belong to the second sector, the two outer
indices occur only in the boundary coefficient. The bulk coefficient is
exactly one entry of the `A₀` product. This exhibits the two exterior
spectators without a change of the actual bulk tensor.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpoint_insertedGroundSpaceMap_outerSpectators
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    {N : ℕ} (X : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ)
    (a e : Fin D₁) (b c : Fin D₀) (σ : Cfg (D₀ * D₀) N) :
    insertedGroundSpaceMap (mixedEndpointBase A₀ A₁) (bondInterpolationMatrix D₀ D₁ 0)
        (N + 1 + 1) X
        (Fin.cons (mixedEndpointPhysicalIndex (.inr a) (.inl b))
          (Fin.snoc (fun k => mixedEndpointFirstPhysicalIndex D₁ (σ k))
            (mixedEndpointPhysicalIndex (.inl c) (.inr e)))) =
      Kraus.evalWord A₀ (List.ofFn σ) b c *
        X (finSumFinEquiv (.inr e)) (finSumFinEquiv (.inr a)) := by
  rw [mixedEndpoint_insertedGroundSpaceMap_sectorFactors]
  have hfirst :
      (mixedEndpointFirstBoundaryLetter A₀ (.inr a) (.inl b)).submatrix
          finSumFinEquiv.symm id = Matrix.single (finSumFinEquiv (.inr a)) b 1 := by
    ext i j
    simp only [mixedEndpointFirstBoundaryLetter, Matrix.submatrix_apply, Matrix.single_apply,
      id_eq, Equiv.eq_symm_apply]
  have hlast :
      (mixedEndpointLastBoundaryLetter A₀ (.inl c) (.inr e)).submatrix
          id finSumFinEquiv.symm = Matrix.single c (finSumFinEquiv (.inr e)) 1 := by
    ext i j
    simp only [mixedEndpointLastBoundaryLetter, Matrix.submatrix_apply, Matrix.single_apply,
      id_eq, Equiv.eq_symm_apply]
  rw [hfirst, hlast, Matrix.single_mul_mul_single, Matrix.trace_single_mul]
  simp

end MPOSymmetry
end MPSTensor
