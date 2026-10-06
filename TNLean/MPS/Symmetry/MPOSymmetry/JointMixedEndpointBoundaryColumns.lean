/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointFamily
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointBoundaryFactors
import TNLean.MPS.ParentHamiltonian.BlockGroundSpaceContinuity
import TNLean.MPS.Preparation.MatrixPolar

/-!
# Joint boundary columns of the actual mixed endpoint

The two boundary matrices collect all block labels into a single physical
map. Their columns are \((C_x^iV_x)_{ab}\) and
\((V_x^\dagger C_x^i)_{ce}\). Simultaneous one-site spanning makes both
maps injective. Their polar decompositions therefore give isometries and
positive definite factors on the full joint column spaces. The Gram
matrices retain entries between distinct block labels.

Factoring the zero-parameter insertions leaves the original first endpoint
at every interior site. Only the first and last physical sites carry the
rectangular factors. These identities alone assert no Hamiltonian gap.

Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- Simultaneous one-site spanning makes the joint physical column matrix
injective, including when the finite block-label type is empty.
Source context: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem injective_jointOneSiteColumns_of_wordTupleSpanTop
    (A : (x : Fin r) → MPSTensor d (dim x)) (hA : WordTupleSpanTop A 1) :
    Function.Injective (Matrix.mulVec
      (fun (i : Fin d) (p : (x : Fin r) × (Fin (dim x) × Fin (dim x))) =>
        A p.1 i p.2.1 p.2.2)) := by
  intro v w hvw
  have hmap : blockGroundSpaceMapES A 1 (WithLp.toLp 2 v) =
      blockGroundSpaceMapES A 1 (WithLp.toLp 2 w) := by
    apply PiLp.ext
    intro σ
    simpa [blockGroundSpaceMapES_apply, groundSpaceMap_apply, List.ofFn_succ,
      Kraus.evalWord, Matrix.trace, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_sigma, Fintype.sum_prod_type] using congrFun hvw (σ 0)
  exact congrArg WithLp.ofLp
    (blockGroundSpaceMapES_injective_of_wordTupleSpanTop A hA hmap)

namespace MPOSymmetry

variable {d₀ d₁ : ℕ} {D₀ D₁ : Fin r → ℕ}

/-- Joint first-boundary coordinates: a block label, an enlarged exterior
row, and a first-endpoint interior column.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
abbrev JointMixedFirstBoundaryIndex (D₀ D₁ : Fin r → ℕ) :=
  (x : Fin r) × (Fin (D₀ x + D₁ x) × Fin (D₀ x))

/-- Joint last-boundary coordinates: a block label, a first-endpoint
interior row, and an enlarged exterior column.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
abbrev JointMixedLastBoundaryIndex (D₀ D₁ : Fin r → ℕ) :=
  (x : Fin r) × (Fin (D₀ x) × Fin (D₀ x + D₁ x))

/-- The actual first boundary columns, with one common physical alphabet.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
noncomputable def jointMixedFirstBoundaryColumns
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Matrix (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁))
      (JointMixedFirstBoundaryIndex D₀ D₁) ℂ :=
  fun i p => jointMixedEndpointBase A₀ A₁ p.1 i p.2.1
    (Fin.castAdd (D₁ p.1) p.2.2)

/-- The actual last boundary columns, with one common physical alphabet.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
noncomputable def jointMixedLastBoundaryColumns
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Matrix (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁))
      (JointMixedLastBoundaryIndex D₀ D₁) ℂ :=
  fun i p => jointMixedEndpointBase A₀ A₁ p.1 i
    (Fin.castAdd (D₁ p.1) p.2.1) p.2.2

/-- The first columns are exactly the rectangular factors \(C_x^iV_x\).
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstBoundaryColumns_apply
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (i : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁))
    (x : Fin r) (a : Fin (D₀ x + D₁ x)) (b : Fin (D₀ x)) :
    jointMixedFirstBoundaryColumns A₀ A₁ i ⟨x, a, b⟩ =
      (jointMixedEndpointBase A₀ A₁ x i *
        Matrix.coordinateInclusion (Fin.castAddEmb (D₁ x) :
          Fin (D₀ x) ↪ Fin (D₀ x + D₁ x)) :
          Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x)) ℂ) a b := by
  rw [Matrix.mul_coordinateInclusion]
  rfl

/-- The last columns are exactly the rectangular factors
\(V_x^\dagger C_x^i\).
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastBoundaryColumns_apply
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (i : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁))
    (x : Fin r) (c : Fin (D₀ x)) (e : Fin (D₀ x + D₁ x)) :
    jointMixedLastBoundaryColumns A₀ A₁ i ⟨x, c, e⟩ =
      ((Matrix.coordinateInclusion (Fin.castAddEmb (D₁ x) :
        Fin (D₀ x) ↪ Fin (D₀ x + D₁ x)))ᴴ *
        jointMixedEndpointBase A₀ A₁ x i :
          Matrix (Fin (D₀ x)) (Fin (D₀ x + D₁ x)) ℂ) c e := by
  rw [Matrix.conjTranspose_coordinateInclusion_mul]
  rfl

/-- The joint first Gram matrix includes all pairs of block labels,
including distinct ones. Source: arXiv:2203.12563, Section 5,
lines 1695–1777. -/
theorem jointMixedFirstBoundaryColumns_gram_apply
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (x y : Fin r) (a : Fin (D₀ x + D₁ x)) (b : Fin (D₀ x))
    (c : Fin (D₀ y + D₁ y)) (e : Fin (D₀ y)) :
    ((jointMixedFirstBoundaryColumns A₀ A₁)ᴴ *
        jointMixedFirstBoundaryColumns A₀ A₁) ⟨x, a, b⟩ ⟨y, c, e⟩ =
      ∑ i, star (jointMixedEndpointBase A₀ A₁ x i a (Fin.castAdd (D₁ x) b)) *
        jointMixedEndpointBase A₀ A₁ y i c (Fin.castAdd (D₁ y) e) := by
  rfl

/-- On first-sector exterior rows, the joint Gram matrix is precisely the
original endpoint Gram matrix, with its cross-label terms retained.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstBoundaryColumns_gram_firstSector
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (x y : Fin r) (a b : Fin (D₀ x)) (c e : Fin (D₀ y)) :
    ((jointMixedFirstBoundaryColumns A₀ A₁)ᴴ *
        jointMixedFirstBoundaryColumns A₀ A₁)
        ⟨x, Fin.castAdd (D₁ x) a, b⟩ ⟨y, Fin.castAdd (D₁ y) c, e⟩ =
      ∑ i, star (A₀ x i a b) * A₀ y i c e := by
  classical
  rw [jointMixedFirstBoundaryColumns_gram_apply]
  have hcompress (z : Fin r) (i : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁))
      (u v : Fin (D₀ z)) :
      jointMixedEndpointBase A₀ A₁ z i (Fin.castAdd (D₁ z) u)
          (Fin.castAdd (D₁ z) v) = jointMixedEndpointLeftTensor A₀ d₁ D₁ z i u v := by
    have h := jointMixedEndpointBase_first_compression A₀ A₁ z i
    rw [Matrix.coordinateInclusion_compression] at h
    exact congrArg (fun M => M u v) h
  simp_rw [hcompress]
  rw [Fintype.sum_equiv (Fintype.equivFin (JointMixedPhysical d₀ d₁ D₀ D₁)).symm
    _ (fun p => star (jointMixedEndpointLeftTensor A₀ d₁ D₁ x
      ((Fintype.equivFin _ ) p) a b) * jointMixedEndpointLeftTensor A₀ d₁ D₁ y
        ((Fintype.equivFin _) p) c e) (fun _ => by simp)]
  simp [JointMixedPhysical, jointMixedEndpointLeftTensor, Fintype.sum_sum_type]

/-- The joint last Gram matrix likewise retains every pair of block
labels. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastBoundaryColumns_gram_apply
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (x y : Fin r) (a : Fin (D₀ x)) (b : Fin (D₀ x + D₁ x))
    (c : Fin (D₀ y)) (e : Fin (D₀ y + D₁ y)) :
    ((jointMixedLastBoundaryColumns A₀ A₁)ᴴ *
        jointMixedLastBoundaryColumns A₀ A₁) ⟨x, a, b⟩ ⟨y, c, e⟩ =
      ∑ i, star (jointMixedEndpointBase A₀ A₁ x i (Fin.castAdd (D₁ x) a) b) *
        jointMixedEndpointBase A₀ A₁ y i (Fin.castAdd (D₁ y) c) e := by
  rfl

/-- The first boundary columns are independent jointly across all block
labels. No orthogonality of the endpoint physical blocks is assumed.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstBoundaryColumns_injective
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    Function.Injective (jointMixedFirstBoundaryColumns A₀ A₁).mulVec := by
  let e : JointMixedFirstBoundaryIndex D₀ D₁ ↪
      (x : Fin r) × (Fin (D₀ x + D₁ x) × Fin (D₀ x + D₁ x)) :=
    Function.Embedding.sigmaMap (Function.Embedding.refl _) fun x =>
      (Function.Embedding.refl _).prodMap (Fin.castAddEmb (D₁ x))
  have h := (Matrix.mulVec_injective_iff.mp
    (injective_jointOneSiteColumns_of_wordTupleSpanTop (jointMixedEndpointBase A₀ A₁)
      (wordTupleSpanTop_jointMixedEndpointBase A₀ A₁ h₀ h₁))).comp e e.injective
  exact Matrix.mulVec_injective_iff.mpr h

/-- The last boundary columns are independent jointly across all block
labels. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastBoundaryColumns_injective
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    Function.Injective (jointMixedLastBoundaryColumns A₀ A₁).mulVec := by
  let e : JointMixedLastBoundaryIndex D₀ D₁ ↪
      (x : Fin r) × (Fin (D₀ x + D₁ x) × Fin (D₀ x + D₁ x)) :=
    Function.Embedding.sigmaMap (Function.Embedding.refl _) fun x =>
      (Fin.castAddEmb (D₁ x)).prodMap (Function.Embedding.refl _)
  have h := (Matrix.mulVec_injective_iff.mp
    (injective_jointOneSiteColumns_of_wordTupleSpanTop (jointMixedEndpointBase A₀ A₁)
      (wordTupleSpanTop_jointMixedEndpointBase A₀ A₁ h₀ h₁))).comp e e.injective
  exact Matrix.mulVec_injective_iff.mpr h

/-- The two joint polar factors have orthonormal columns and positive
invertible joint weights. Their factors act on all labels at once.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedBoundaryColumns_polar
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    (Matrix.polarIso (jointMixedFirstBoundaryColumns A₀ A₁)).IsIsometry ∧
      (Matrix.polarPos (jointMixedFirstBoundaryColumns A₀ A₁)).PosDef ∧
      (Matrix.polarIso (jointMixedLastBoundaryColumns A₀ A₁)).IsIsometry ∧
      (Matrix.polarPos (jointMixedLastBoundaryColumns A₀ A₁)).PosDef :=
  ⟨Matrix.isIsometry_polarIso_of_injective _
      (jointMixedFirstBoundaryColumns_injective A₀ A₁ h₀ h₁),
    Matrix.posDef_polarPos_of_injective _
      (jointMixedFirstBoundaryColumns_injective A₀ A₁ h₀ h₁),
    Matrix.isIsometry_polarIso_of_injective _
      (jointMixedLastBoundaryColumns_injective A₀ A₁ h₀ h₁),
    Matrix.posDef_polarPos_of_injective _
      (jointMixedLastBoundaryColumns_injective A₀ A₁ h₀ h₁)⟩

/-- Every joint zero-endpoint word retains the original compressed tensor
at all interior sites and the two actual rectangular factors at its ends.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_insertedEvalWord_boundaryFactors
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (x : Fin r)
    (i j : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁))
    (w : List (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁))) :
    let V := Matrix.coordinateInclusion (Fin.castAddEmb (D₁ x) :
      Fin (D₀ x) ↪ Fin (D₀ x + D₁ x))
    insertedEvalWord (jointMixedEndpointBase A₀ A₁ x)
        (bondInterpolationMatrix (D₀ x) (D₁ x) 0) (i :: (w ++ [j])) =
      (jointMixedEndpointBase A₀ A₁ x i * V) *
        Kraus.evalWord (jointMixedEndpointLeftTensor A₀ d₁ D₁ x) w *
          (Vᴴ * jointMixedEndpointBase A₀ A₁ x j) := by
  dsimp only
  rw [← coordinateInclusion_first_projection_eq_bondWeight,
    insertedEvalWord_factor_boundary]
  simp only [jointMixedEndpointBase_first_compression]

/-- Inclusion of the single shared first-endpoint physical alphabet.
Source: arXiv:2203.12563, Section 5, lines 1695–1704. -/
noncomputable def jointMixedFirstPhysicalIndex (d₁ : ℕ) (D₀ D₁ : Fin r → ℕ)
    (i : Fin d₀) : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁) :=
  Fintype.equivFin (JointMixedPhysical d₀ d₁ D₀ D₁) (.inl i)

/-- The shared physical inclusion recovers the original first endpoint
without a block-dependent physical change.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
@[simp] theorem jointMixedEndpointLeftTensor_firstPhysicalIndex
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x)) (x : Fin r) (i : Fin d₀) :
    jointMixedEndpointLeftTensor A₀ d₁ D₁ x
      (jointMixedFirstPhysicalIndex d₁ D₀ D₁ i) = A₀ x i := by
  simp [jointMixedEndpointLeftTensor, jointMixedFirstPhysicalIndex]

/-- Every interior word in the shared first alphabet is exactly the
original endpoint word. Source: arXiv:2203.12563, Section 5,
lines 1695–1777. -/
theorem evalWord_jointMixedEndpointLeftTensor_firstPhysicalIndex
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x)) (x : Fin r) (w : List (Fin d₀)) :
    Kraus.evalWord (jointMixedEndpointLeftTensor A₀ d₁ D₁ x)
        (w.map (jointMixedFirstPhysicalIndex d₁ D₀ D₁)) = Kraus.evalWord (A₀ x) w := by
  induction w with
  | nil => simp [Kraus.evalWord]
  | cons i w ih =>
      simp only [List.map_cons, Kraus.evalWord_cons,
        jointMixedEndpointLeftTensor_firstPhysicalIndex, ih]

/-- Exact coefficient factorization with the unchanged original endpoint
throughout the interior. The exterior indices of the two columns remain
free. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedEndpoint_insertedEvalWord_originalBulk
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (x : Fin r)
    (i j : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) (w : List (Fin d₀))
    (a e : Fin (D₀ x + D₁ x)) :
    insertedEvalWord (jointMixedEndpointBase A₀ A₁ x)
        (bondInterpolationMatrix (D₀ x) (D₁ x) 0)
        (i :: (w.map (jointMixedFirstPhysicalIndex d₁ D₀ D₁) ++ [j])) a e =
      ∑ c : Fin (D₀ x), ∑ b : Fin (D₀ x),
        jointMixedFirstBoundaryColumns A₀ A₁ i ⟨x, a, b⟩ *
          Kraus.evalWord (A₀ x) w b c *
            jointMixedLastBoundaryColumns A₀ A₁ j ⟨x, c, e⟩ := by
  rw [jointMixedEndpoint_insertedEvalWord_boundaryFactors,
    evalWord_jointMixedEndpointLeftTensor_firstPhysicalIndex]
  simp only [Matrix.mul_coordinateInclusion, Matrix.conjTranspose_coordinateInclusion_mul,
    Matrix.mul_apply, Finset.sum_mul, Matrix.submatrix_apply, id_eq, Fin.castAddEmb_apply,
    jointMixedFirstBoundaryColumns, jointMixedLastBoundaryColumns]

end MPOSymmetry
end MPSTensor
