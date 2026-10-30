/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.MargolusAlternatingLocalRule
import TNLean.QCA.SupportAlgebraCovariance

/-!
# Shared intermediate coordinates for constant Margolus gates

Choose the even and odd support presentations at the cut zero. The next
even presentation is transported through actual translation by two,
rather than chosen independently. A single shifted output rule then
recovers the even factor after translation back by two and the odd
factor directly. These are the common coordinates required to use one
pair of gates at every translated block.

Source: Schumacher–Werner, quant-ph/0405174, defBBq and its translated
support calculation, lines 1199–1226, bruleU/bruleV, lines 980–1001,
and translation compatibility, lines 1033–1041.

**Scope restriction (homogeneous chain):** The physical size is one fixed
positive integer. See
`docs/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.tex`.
Actual translation covariance of the given QCA is used explicitly.
-/

open scoped Matrix Kronecker

namespace SpinChain.PropagatesWithin

variable {d : ℕ} [NeZero d]
  {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}
  (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (hcov : TranslationCovariant ω)

private noncomputable def evenTranslationEquiv :
    embeddedEvenSupportAlgebra hω 0 ≃⋆ₐ[ℂ] embeddedEvenSupportAlgebra hω 1 :=
  ((embeddedEvenSupportAlgebra hω 0).equivMapOfInjective
    (quasiLocalTranslation d 2).toStarAlgHom (quasiLocalTranslation d 2).injective).trans
      (StarSubalgebra.equivOfEq _ _
        (embeddedEvenSupportAlgebra_map_quasiLocalTranslation_two hω hcov 0))

private theorem evenTranslationEquiv_coe (a : embeddedEvenSupportAlgebra hω 0) :
    (evenTranslationEquiv hω hcov a : QuasiLocalAlgebra d) =
      quasiLocalTranslation d 2 (a : QuasiLocalAlgebra d) := rfl

/-- The next even factor uses the cut-zero coordinates transported
through the actual two-site translation. It is not identified with an
independent classical choice of matrix presentation.
Source: Schumacher–Werner defBBq, lines 1199–1226. -/
noncomputable def coherentEvenOneMatrixEquiv :
    evenSupportAlgebra hω 1 ≃⋆ₐ[ℂ]
      Matrix (Fin (supportAlgebraMatrixSize hω 0))
        (Fin (supportAlgebraMatrixSize hω 0)) ℂ :=
  (supportEmbeddingEquiv (leftPair 1) (evenSupportAlgebra hω 1)).trans <|
    (evenTranslationEquiv hω hcov).symm.trans <|
      (supportEmbeddingEquiv (leftPair 0) (evenSupportAlgebra hω 0)).symm.trans
        (evenSupportMatrixEquiv hω 0)

/-- The transported even coordinates preserve the actual ambient
observable after two-site translation. Source: Schumacher–Werner,
translated-support calculation, lines 1218–1226. -/
theorem coherentEvenOneMatrixEquiv_symm_embed
    (A : Matrix (Fin (supportAlgebraMatrixSize hω 0))
      (Fin (supportAlgebraMatrixSize hω 0)) ℂ) :
    matrixToQuasiLocalObservable d (leftPair 1)
      ((coherentEvenOneMatrixEquiv hω hcov).symm A) =
      quasiLocalTranslation d 2
        (matrixToQuasiLocalObservable d (leftPair 0)
          ((evenSupportMatrixEquiv hω 0).symm A)) := by
  let a := (evenSupportMatrixEquiv hω 0).symm A
  let z := evenTranslationEquiv hω hcov
    (supportEmbeddingEquiv (leftPair 0) (evenSupportAlgebra hω 0) a)
  have hcoord : (coherentEvenOneMatrixEquiv hω hcov).symm A =
      (supportEmbeddingEquiv (leftPair 1) (evenSupportAlgebra hω 1)).symm z := by
    apply (coherentEvenOneMatrixEquiv hω hcov).injective
    simp only [StarAlgEquiv.apply_symm_apply, coherentEvenOneMatrixEquiv,
      StarAlgEquiv.trans_apply, StarAlgEquiv.symm_apply_apply, z, a]
  calc
    matrixToQuasiLocalObservable d (leftPair 1)
        ((coherentEvenOneMatrixEquiv hω hcov).symm A) =
        ((supportEmbeddingEquiv (leftPair 1) (evenSupportAlgebra hω 1))
          ((supportEmbeddingEquiv (leftPair 1) (evenSupportAlgebra hω 1)).symm z) :
            QuasiLocalAlgebra d) := by rw [hcoord]; rfl
    _ = (z : QuasiLocalAlgebra d) := by rw [StarAlgEquiv.apply_symm_apply]
    _ = quasiLocalTranslation d 2
        (matrixToQuasiLocalObservable d (leftPair 0)
          ((evenSupportMatrixEquiv hω 0).symm A)) := evenTranslationEquiv_coe hω hcov _

/-- The shifted output rule in common cut-zero odd/even coordinates.
The even input coordinates are the actual translated cut-zero choice.
Source: Schumacher–Werner bruleV and defBBq, lines 980–1001 and 1199–1226. -/
noncomputable def coherentMargolusOutputRule :
    Matrix (Fin (supportAlgebraMatrixSize hω 1) × Fin (supportAlgebraMatrixSize hω 0))
      (Fin (supportAlgebraMatrixSize hω 1) × Fin (supportAlgebraMatrixSize hω 0)) ℂ ≃⋆ₐ[ℂ]
        Matrix (Config d (rightPair 0)) (Config d (rightPair 0)) ℂ :=
  (Matrix.matrixReindexStarAlgEquiv finProdFinEquiv).trans <|
    (physicalPairSupportJoinMatrixEquiv hω 0
      (oddSupportMatrixEquiv hω 0) (coherentEvenOneMatrixEquiv hω hcov)).symm.trans <|
        (outputPairEquiv hω 0).symm.trans CStarMatrix.ofMatrixStarAlgEquiv.symm

/-- The common shifted rule recovers the actual odd and translated-even
product in the same prescribed coordinates. Source: Schumacher–Werner
bruleV and translated-support calculation, lines 980–1001 and 1218–1226. -/
theorem coherentMargolusOutputRule_kronecker
    (A : Matrix (Fin (supportAlgebraMatrixSize hω 1))
      (Fin (supportAlgebraMatrixSize hω 1)) ℂ)
    (B : Matrix (Fin (supportAlgebraMatrixSize hω 0))
      (Fin (supportAlgebraMatrixSize hω 0)) ℂ) :
    matrixToQuasiLocalObservable d (rightPair 0)
      (coherentMargolusOutputRule hω hcov (A ⊗ₖ B)) =
      matrixToQuasiLocalObservable d (rightPair 0)
          ((oddSupportMatrixEquiv hω 0).symm A) *
        quasiLocalTranslation d 2
          (matrixToQuasiLocalObservable d (leftPair 0)
            ((evenSupportMatrixEquiv hω 0).symm B)) := by
  let a := (oddSupportMatrixEquiv hω 0).symm A
  let b := (coherentEvenOneMatrixEquiv hω hcov).symm B
  let z : embeddedOddSupportAlgebra hω 0 ⊔ embeddedEvenSupportAlgebra hω 1 :=
    ⟨matrixToQuasiLocalObservable d (rightPair 0) a *
        matrixToQuasiLocalObservable d (leftPair 1) b,
      (embeddedOddSupportAlgebra hω 0 ⊔ embeddedEvenSupportAlgebra hω 1).mul_mem
        (le_sup_left (StarSubalgebra.mem_map.mpr ⟨a, a.2, rfl⟩))
        (le_sup_right (StarSubalgebra.mem_map.mpr ⟨b, b.2, rfl⟩))⟩
  have hz := physicalPairSupportJoinMatrixEquiv_apply_product hω 0
    (oddSupportMatrixEquiv hω 0) (coherentEvenOneMatrixEquiv hω hcov) a b
  have hcoord : coherentMargolusOutputRule hω hcov (A ⊗ₖ B) =
      CStarMatrix.ofMatrixStarAlgEquiv.symm ((outputPairEquiv hω 0).symm z) := by
    unfold coherentMargolusOutputRule
    simp only [StarAlgEquiv.trans_apply]
    change CStarMatrix.ofMatrixStarAlgEquiv.symm
      ((outputPairEquiv hω 0).symm
        ((physicalPairSupportJoinMatrixEquiv hω 0
          (oddSupportMatrixEquiv hω 0) (coherentEvenOneMatrixEquiv hω hcov)).symm
          (Matrix.reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B)))) = _
    have hz' : physicalPairSupportJoinMatrixEquiv hω 0
        (oddSupportMatrixEquiv hω 0) (coherentEvenOneMatrixEquiv hω hcov) z =
          Matrix.reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B) := by
      simpa only [StarAlgEquiv.apply_symm_apply] using hz
    rw [← hz', StarAlgEquiv.symm_apply_apply]
  rw [hcoord]
  change quasiLocalObservable d (rightPair 0) ((outputPairEquiv hω 0).symm z) = _
  calc
    quasiLocalObservable d (rightPair 0) ((outputPairEquiv hω 0).symm z) =
        (z : QuasiLocalAlgebra d) :=
      (outputPairEquiv_coe hω 0 _).symm.trans
        (congrArg Subtype.val ((outputPairEquiv hω 0).apply_symm_apply z))
    _ = _ := congrArg
      (fun w => matrixToQuasiLocalObservable d (rightPair 0) a * w)
      (coherentEvenOneMatrixEquiv_symm_embed hω hcov B)

end SpinChain.PropagatesWithin
