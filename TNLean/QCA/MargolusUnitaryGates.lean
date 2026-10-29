/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.GNVWIndex
import TNLean.Algebra.MatrixStarEquivSpatial

/-!
# Unitary gates from the actual adjacent support factors

The two adjacent-generation equalities give full matrix equivalences from
physical even pairs to ordered support factors, and from ordered shifted
support factors to physical odd pairs. Spatial implementation supplies
unitary gates on these actual spaces. Their action on a product of factor
observables is the prescribed local rule, rather than an independent
factorization assumption. The gates may depend on the integer position.

Source: Schumacher–Werner, quant-ph/0405174, bruleU and bruleV,
lines 980–1001; GNVW, arXiv:0910.3675v2, AARReven and AARRodd,
lines 1276–1318.

**Scope restriction (homogeneous chain):** The on-site matrix size is one
fixed positive integer; the source also permits site-dependent sizes.
See `docs/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.tex`.
The result here supplies the two finite matrix rules and unitary gates;
it does not assemble the full translation-covariant layer action.
-/

open scoped Matrix Kronecker

namespace SpinChain.PropagatesWithin

variable {d : ℕ} [NeZero d]
  {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}

private noncomputable def equivOfRangeEq
    {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    (f : A →⋆ₐ[ℂ] QuasiLocalAlgebra d) (hf : Function.Injective f)
    (J : StarSubalgebra ℂ (QuasiLocalAlgebra d)) (h : f.range = J) :
    A ≃⋆ₐ[ℂ] J := h ▸ StarAlgEquiv.ofInjective f hf

private theorem equivOfRangeEq_coe
    {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    (f : A →⋆ₐ[ℂ] QuasiLocalAlgebra d) (hf : Function.Injective f)
    (J : StarSubalgebra ℂ (QuasiLocalAlgebra d)) (h : f.range = J) (a : A) :
    (equivOfRangeEq f hf J h a : QuasiLocalAlgebra d) = f a := by
  cases h
  rfl

/-- A coherent presentation of the even support factor of the derived
matrix-size family. Source: GNVW AARReven, lines 1276–1287. -/
noncomputable def evenSupportMatrixEquiv
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    evenSupportAlgebra hω x ≃⋆ₐ[ℂ]
      Matrix (Fin (supportAlgebraMatrixSize hω (2 * x)))
        (Fin (supportAlgebraMatrixSize hω (2 * x))) ℂ :=
  Classical.choice ((supportAlgebraMatrixSize_spec hω).2.1 x)

/-- A coherent presentation of the odd support factor of the same
matrix-size family. Source: GNVW AARRodd, lines 1306–1318. -/
noncomputable def oddSupportMatrixEquiv
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    oddSupportAlgebra hω x ≃⋆ₐ[ℂ]
      Matrix (Fin (supportAlgebraMatrixSize hω (2 * x + 1)))
        (Fin (supportAlgebraMatrixSize hω (2 * x + 1))) ℂ :=
  Classical.choice ((supportAlgebraMatrixSize_spec hω).2.2.1 x)

private noncomputable def inputPairEquiv
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :=
  equivOfRangeEq (ω.toStarAlgHom.comp (quasiLocalObservable d (evenPair x)))
    (ω.injective.comp (quasiLocalObservable_injective d (evenPair x)))
    (embeddedEvenSupportAlgebra hω x ⊔ embeddedOddSupportAlgebra hω x)
    (range_image_evenPair_eq_adjacentSupportJoin hω x)

private noncomputable def outputPairEquiv
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :=
  equivOfRangeEq (quasiLocalObservable d (rightPair x))
    (quasiLocalObservable_injective d (rightPair x))
    (embeddedOddSupportAlgebra hω x ⊔ embeddedEvenSupportAlgebra hω (x + 1))
    (adjacentSupportJoin_eq_range_rightPair hω x).symm

private theorem inputPairEquiv_coe
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ)
    (A : LocalAlgebra d (evenPair x)) :
    (inputPairEquiv hω x A : QuasiLocalAlgebra d) =
      ω (quasiLocalObservable d (evenPair x) A) :=
  equivOfRangeEq_coe _ _ _ _ A

private theorem outputPairEquiv_coe
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ)
    (A : LocalAlgebra d (rightPair x)) :
    (outputPairEquiv hω x A : QuasiLocalAlgebra d) =
      quasiLocalObservable d (rightPair x) A :=
  equivOfRangeEq_coe _ _ _ _ A

/-- The actual even-pair rule in the ordered coordinates of its two
support factors. Source: Schumacher–Werner bruleU, lines 980–990. -/
noncomputable def margolusInputRule
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    Matrix (Config d (evenPair x)) (Config d (evenPair x)) ℂ ≃⋆ₐ[ℂ]
      Matrix (Fin (supportAlgebraMatrixSize hω (2 * x)) ×
        Fin (supportAlgebraMatrixSize hω (2 * x + 1)))
        (Fin (supportAlgebraMatrixSize hω (2 * x)) ×
        Fin (supportAlgebraMatrixSize hω (2 * x + 1))) ℂ :=
  CStarMatrix.ofMatrixStarAlgEquiv.trans <| (inputPairEquiv hω x).trans <|
    (adjacentSupportJoinMatrixEquiv hω x
      (evenSupportMatrixEquiv hω x) (oddSupportMatrixEquiv hω x)).trans
        (Matrix.matrixReindexStarAlgEquiv finProdFinEquiv.symm)

/-- The shifted rule maps the odd factor and the following even factor
back to their actual physical pair. Source: Schumacher–Werner bruleV,
lines 990–1001. -/
noncomputable def margolusOutputRule
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    Matrix (Fin (supportAlgebraMatrixSize hω (2 * x + 1)) ×
        Fin (supportAlgebraMatrixSize hω (2 * (x + 1))))
        (Fin (supportAlgebraMatrixSize hω (2 * x + 1)) ×
        Fin (supportAlgebraMatrixSize hω (2 * (x + 1)))) ℂ ≃⋆ₐ[ℂ]
      Matrix (Config d (rightPair x)) (Config d (rightPair x)) ℂ :=
  (Matrix.matrixReindexStarAlgEquiv finProdFinEquiv).trans <|
    (physicalPairSupportJoinMatrixEquiv hω x
      (oddSupportMatrixEquiv hω x) (evenSupportMatrixEquiv hω (x + 1))).symm.trans <|
      (outputPairEquiv hω x).symm.trans CStarMatrix.ofMatrixStarAlgEquiv.symm

/-- Inverse input coordinates recover the actual product of the two
embedded support observables. Source: Schumacher–Werner bruleU. -/
theorem margolusInputRule_symm_kronecker
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ)
    (a : evenSupportAlgebra hω x) (b : oddSupportAlgebra hω x) :
    ω (matrixToQuasiLocalObservable d (evenPair x)
      ((margolusInputRule hω x).symm
        (evenSupportMatrixEquiv hω x a ⊗ₖ oddSupportMatrixEquiv hω x b))) =
      matrixToQuasiLocalObservable d (leftPair x) a *
        matrixToQuasiLocalObservable d (rightPair x) b := by
  let z : embeddedEvenSupportAlgebra hω x ⊔ embeddedOddSupportAlgebra hω x :=
    ⟨matrixToQuasiLocalObservable d (leftPair x) a *
        matrixToQuasiLocalObservable d (rightPair x) b,
      (embeddedEvenSupportAlgebra hω x ⊔ embeddedOddSupportAlgebra hω x).mul_mem
        (le_sup_left (StarSubalgebra.mem_map.mpr ⟨a, a.2, rfl⟩))
        (le_sup_right (StarSubalgebra.mem_map.mpr ⟨b, b.2, rfl⟩))⟩
  have hz := adjacentSupportJoinMatrixEquiv_apply_product hω x
    (evenSupportMatrixEquiv hω x) (oddSupportMatrixEquiv hω x) a b
  have hcoord : (margolusInputRule hω x).symm
      (evenSupportMatrixEquiv hω x a ⊗ₖ oddSupportMatrixEquiv hω x b) =
      CStarMatrix.ofMatrixStarAlgEquiv.symm ((inputPairEquiv hω x).symm z) := by
    apply (margolusInputRule hω x).injective
    rw [StarAlgEquiv.apply_symm_apply]
    change _ = (Matrix.matrixReindexStarAlgEquiv finProdFinEquiv.symm)
      ((adjacentSupportJoinMatrixEquiv hω x
        (evenSupportMatrixEquiv hω x) (oddSupportMatrixEquiv hω x))
        ((inputPairEquiv hω x)
          (CStarMatrix.ofMatrixStarAlgEquiv
            (CStarMatrix.ofMatrixStarAlgEquiv.symm ((inputPairEquiv hω x).symm z)))))
    rw [StarAlgEquiv.apply_symm_apply, StarAlgEquiv.apply_symm_apply, hz]
    exact ((Matrix.reindex finProdFinEquiv finProdFinEquiv).symm_apply_apply _).symm
  rw [hcoord]
  change ω (quasiLocalObservable d (evenPair x)
    ((inputPairEquiv hω x).symm z)) = (z : QuasiLocalAlgebra d)
  exact (inputPairEquiv_coe hω x _).symm.trans
    (congrArg Subtype.val ((inputPairEquiv hω x).apply_symm_apply z))

/-- The shifted matrix rule recovers the actual product on the odd
physical pair. Source: Schumacher–Werner bruleV. -/
theorem margolusOutputRule_kronecker
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ)
    (a : oddSupportAlgebra hω x) (b : evenSupportAlgebra hω (x + 1)) :
    matrixToQuasiLocalObservable d (rightPair x)
      (margolusOutputRule hω x
        (oddSupportMatrixEquiv hω x a ⊗ₖ evenSupportMatrixEquiv hω (x + 1) b)) =
      matrixToQuasiLocalObservable d (rightPair x) a *
        matrixToQuasiLocalObservable d (leftPair (x + 1)) b := by
  let z : embeddedOddSupportAlgebra hω x ⊔ embeddedEvenSupportAlgebra hω (x + 1) :=
    ⟨matrixToQuasiLocalObservable d (rightPair x) a *
        matrixToQuasiLocalObservable d (leftPair (x + 1)) b,
      (embeddedOddSupportAlgebra hω x ⊔ embeddedEvenSupportAlgebra hω (x + 1)).mul_mem
        (le_sup_left (StarSubalgebra.mem_map.mpr ⟨a, a.2, rfl⟩))
        (le_sup_right (StarSubalgebra.mem_map.mpr ⟨b, b.2, rfl⟩))⟩
  have hz := physicalPairSupportJoinMatrixEquiv_apply_product hω x
    (oddSupportMatrixEquiv hω x) (evenSupportMatrixEquiv hω (x + 1)) a b
  have hcoord : margolusOutputRule hω x
      (oddSupportMatrixEquiv hω x a ⊗ₖ evenSupportMatrixEquiv hω (x + 1) b) =
      CStarMatrix.ofMatrixStarAlgEquiv.symm ((outputPairEquiv hω x).symm z) := by
    unfold margolusOutputRule
    simp only [StarAlgEquiv.trans_apply]
    change CStarMatrix.ofMatrixStarAlgEquiv.symm
      ((outputPairEquiv hω x).symm
        ((physicalPairSupportJoinMatrixEquiv hω x
          (oddSupportMatrixEquiv hω x) (evenSupportMatrixEquiv hω (x + 1))).symm
          (Matrix.reindex finProdFinEquiv finProdFinEquiv
            (oddSupportMatrixEquiv hω x a ⊗ₖ evenSupportMatrixEquiv hω (x + 1) b)))) = _
    rw [← hz, StarAlgEquiv.symm_apply_apply]
  rw [hcoord]
  change quasiLocalObservable d (rightPair x) ((outputPairEquiv hω x).symm z) =
    (z : QuasiLocalAlgebra d)
  exact (outputPairEquiv_coe hω x _).symm.trans
    (congrArg Subtype.val ((outputPairEquiv hω x).apply_symm_apply z))

private theorem symm_eq_conjTranspose
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ) (U : Matrix n m ℂ)
    (hU : U.IsUnitaryBetween) (he : ∀ A, e A = U * A * Uᴴ)
    (B : Matrix n n ℂ) : e.symm B = Uᴴ * B * U := by
  apply e.injective
  rw [StarAlgEquiv.apply_symm_apply, he]
  calc
    B = (U * Uᴴ) * B * (U * Uᴴ) := by
      rw [hU.2, Matrix.one_mul, Matrix.mul_one]
    _ = U * (Uᴴ * B * U) * Uᴴ := by simp only [Matrix.mul_assoc]

/-- Both actual full matrix rules have spatial unitary implementations.
The support presentations, their dimensions and both local rules have
already been derived from nearest-neighbour propagation.
Source: Schumacher–Werner, bruleU and bruleV, lines 980–1001. -/
theorem exists_margolus_unitary_gates
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    ∃ (U : Matrix (Fin (supportAlgebraMatrixSize hω (2 * x)) ×
          Fin (supportAlgebraMatrixSize hω (2 * x + 1)))
          (Config d (evenPair x)) ℂ)
      (V : Matrix (Config d (rightPair x))
          (Fin (supportAlgebraMatrixSize hω (2 * x + 1)) ×
          Fin (supportAlgebraMatrixSize hω (2 * (x + 1)))) ℂ),
      U.IsUnitaryBetween ∧ V.IsUnitaryBetween ∧
      (∀ A, margolusInputRule hω x A = U * A * Uᴴ) ∧
      (∀ B, margolusOutputRule hω x B = V * B * Vᴴ) ∧
      (∀ (a : evenSupportAlgebra hω x) (b : oddSupportAlgebra hω x),
        ω (matrixToQuasiLocalObservable d (evenPair x)
          (Uᴴ * (evenSupportMatrixEquiv hω x a ⊗ₖ oddSupportMatrixEquiv hω x b) * U)) =
          matrixToQuasiLocalObservable d (leftPair x) a *
            matrixToQuasiLocalObservable d (rightPair x) b) ∧
      (∀ (a : oddSupportAlgebra hω x) (b : evenSupportAlgebra hω (x + 1)),
        matrixToQuasiLocalObservable d (rightPair x)
          (V * (oddSupportMatrixEquiv hω x a ⊗ₖ
            evenSupportMatrixEquiv hω (x + 1) b) * Vᴴ) =
          matrixToQuasiLocalObservable d (rightPair x) a *
            matrixToQuasiLocalObservable d (leftPair (x + 1)) b) := by
  obtain ⟨U, hU, hInput⟩ :=
    Matrix.exists_unitary_conj_of_starAlgEquiv_matrix_between (margolusInputRule hω x)
  obtain ⟨V, hV, hOutput⟩ :=
    Matrix.exists_unitary_conj_of_starAlgEquiv_matrix_between (margolusOutputRule hω x)
  refine ⟨U, V, hU, hV, hInput, hOutput, ?_, ?_⟩
  · intro a b
    rw [← symm_eq_conjTranspose (margolusInputRule hω x) U hU hInput]
    exact margolusInputRule_symm_kronecker hω x a b
  · intro a b
    rw [← hOutput]
    exact margolusOutputRule_kronecker hω x a b

end SpinChain.PropagatesWithin
