/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.IntervalChildComposition
import TNLean.MPS.Preparation.PairProduct

/-!
# Joint columns from individually supported logical operators

Individual column identities on the full logical register determine the local
column identities whenever the logical operators are supported on their stated
registers. Their joint columns then follow from the disjoint-register product
formula. All configurations on the remaining registers are retained.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSTensor MPSPreparation
open scoped Kronecker

namespace MPUCircuit

/-- A basis encoding on a placed register and an independent encoding on its complement.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def placedBasisEmbedding {d a n : ℕ} {α τ : Type*}
    (e : Fin a ↪ Fin n) (g : α ↪ Cfg d a) (t : τ ↪ OutsidePlacedConfig d e) :
    (α × τ) ↪ Cfg d n :=
  (g.prodMap t).trans (placedConfigEquiv d e).symm.toEmbedding

open scoped Classical in
/-- The placed initialized inclusion is the tensor product of its two component inclusions.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem initializedBasisMatrix_placedBasisEmbedding {d a n : ℕ} {α τ : Type*}
    (e : Fin a ↪ Fin n) (g : α ↪ Cfg d a) (t : τ ↪ OutsidePlacedConfig d e) :
    (initializedBasisMatrix (placedBasisEmbedding e g t)).submatrix
      (placedConfigEquiv d e).symm id = initializedBasisMatrix g ⊗ₖ initializedBasisMatrix t := by
  classical
  ext p q
  change (if (placedConfigEquiv d e).symm p =
      (placedConfigEquiv d e).symm (g q.1, t q.2) then (1 : ℂ) else 0) =
    (if p.1 = g q.1 then 1 else 0) * (if p.2 = t q.2 then 1 else 0)
  simp only [(placedConfigEquiv d e).symm.injective.eq_iff, Prod.ext_iff]
  split_ifs <;> simp_all

open scoped Classical in
/-- A placed operator is its local matrix tensored with the identity on all remaining sites.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem reindex_embedOp_placedConfigEquiv {d a n : ℕ}
    (e : Fin a ↪ Fin n) (X : Matrix (Cfg d a) (Cfg d a) ℂ) :
    Matrix.reindex (placedConfigEquiv d e) (placedConfigEquiv d e) (embedOp e X) =
      X ⊗ₖ (1 : Matrix (OutsidePlacedConfig d e) (OutsidePlacedConfig d e) ℂ) := by
  classical
  ext p q
  obtain ⟨x, rfl⟩ := (placedConfigEquiv d e).surjective p
  obtain ⟨y, rfl⟩ := (placedConfigEquiv d e).surjective q
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, placedConfigEquiv_fst, embedOp_apply]
  have hAg : AgreeOff e x y ↔ (placedConfigEquiv d e x).2 = (placedConfigEquiv d e y).2 := by
    constructor
    · intro h
      funext s
      exact h s.val (fun i hi ↦ s.2 ⟨i, hi⟩)
    · intro h s hs
      exact congrFun h ⟨s, by rintro ⟨i, hi⟩; exact hs i hi⟩
  simp only [hAg]
  split_ifs <;> simp only [mul_one, mul_zero]

open scoped Classical in
/-- A global initialized-column identity with unrestricted spectator configurations is equivalent
to its local column identity.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem placedColumns_iff_localColumns {d a n : ℕ} [NeZero d] {α γ : Type*} [Fintype γ]
    (e : Fin a ↪ Fin n) (g : α ↪ Cfg d a) (g' : γ ↪ Cfg d a)
    (X : Matrix (Cfg d a) (Cfg d a) ℂ) (V : Matrix γ α ℂ) :
    (embedOp e X) * initializedBasisMatrix
        (placedBasisEmbedding e g (Function.Embedding.refl _)) =
      initializedBasisMatrix (placedBasisEmbedding e g' (Function.Embedding.refl _)) *
        (V ⊗ₖ (1 : Matrix (OutsidePlacedConfig d e) (OutsidePlacedConfig d e) ℂ)) ↔
      X * initializedBasisMatrix g = initializedBasisMatrix g' * V := by
  classical
  have hrepr : Matrix.reindex (placedConfigEquiv d e) (Equiv.refl _)
      ((embedOp e X) * initializedBasisMatrix
        (placedBasisEmbedding e g (Function.Embedding.refl _))) =
        (X * initializedBasisMatrix g) ⊗ₖ
          (1 : Matrix (OutsidePlacedConfig d e) (OutsidePlacedConfig d e) ℂ) := by
    change ((embedOp e X) * initializedBasisMatrix
      (placedBasisEmbedding e g (Function.Embedding.refl _))).submatrix
        (placedConfigEquiv d e).symm id = _
    rw [← Matrix.submatrix_mul_equiv _ _ (placedConfigEquiv d e).symm
      (placedConfigEquiv d e).symm id]
    change Matrix.reindex (placedConfigEquiv d e) (placedConfigEquiv d e)
      (embedOp e X) *
      (initializedBasisMatrix (placedBasisEmbedding e g (Function.Embedding.refl _))).submatrix
        (placedConfigEquiv d e).symm id = _
    rw [reindex_embedOp_placedConfigEquiv, initializedBasisMatrix_placedBasisEmbedding]
    simp only [initializedBasisMatrix, Function.Embedding.coe_refl, Matrix.submatrix_id_id,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have hrepr' : Matrix.reindex (placedConfigEquiv d e) (Equiv.refl _)
      (initializedBasisMatrix (placedBasisEmbedding e g' (Function.Embedding.refl _)) *
        (V ⊗ₖ (1 : Matrix (OutsidePlacedConfig d e) (OutsidePlacedConfig d e) ℂ))) =
        (initializedBasisMatrix g' * V) ⊗ₖ
          (1 : Matrix (OutsidePlacedConfig d e) (OutsidePlacedConfig d e) ℂ) := by
    change (initializedBasisMatrix (placedBasisEmbedding e g' (Function.Embedding.refl _)) *
      (V ⊗ₖ (1 : Matrix (OutsidePlacedConfig d e) (OutsidePlacedConfig d e) ℂ))).submatrix
        (placedConfigEquiv d e).symm id = _
    rw [← Matrix.submatrix_mul_equiv _ _ (placedConfigEquiv d e).symm (Equiv.refl _) id]
    change (initializedBasisMatrix
      (placedBasisEmbedding e g' (Function.Embedding.refl _))).submatrix
        (placedConfigEquiv d e).symm id *
          (V ⊗ₖ (1 : Matrix (OutsidePlacedConfig d e) (OutsidePlacedConfig d e) ℂ)) = _
    rw [initializedBasisMatrix_placedBasisEmbedding]
    simp only [initializedBasisMatrix, Function.Embedding.coe_refl, Matrix.submatrix_id_id,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  constructor
  · intro h
    have hh := congrArg (Matrix.reindex (placedConfigEquiv d e) (Equiv.refl _)) h
    rw [hrepr, hrepr'] at hh
    ext i j
    simpa [Matrix.kroneckerMap_apply] using
      congrArg (fun M ↦ M (i, (0 : OutsidePlacedConfig d e)) (j, 0)) hh
  · intro h
    apply (Matrix.reindex (placedConfigEquiv d e) (Equiv.refl _)).injective
    rw [hrepr, hrepr', h]

open scoped Classical in
/-- Disjoint support and the two individual global column identities imply the joint columns. No
joint column identity or local matrix is supplied.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem jointPlacedColumns_of_supported_individual {d a b n : ℕ} [NeZero d]
    {α β γ δ τ : Type*} [Fintype γ] [Fintype δ] [Fintype τ]
    (e : Fin a ↪ Fin n) (f : Fin b ↪ Fin n)
    (h : Disjoint (Set.range e) (Set.range f))
    (g : α ↪ Cfg d a) (k : β ↪ Cfg d b)
    (g' : γ ↪ Cfg d a) (k' : δ ↪ Cfg d b)
    (t : τ ↪ OutsidePlacedConfig d (Fin.Embedding.append h))
    (X Y : Matrix (Cfg d n) (Cfg d n) ℂ)
    (V : Matrix γ α ℂ) (W : Matrix δ β ℂ)
    (hSX : X ∈ supportedOperators d (Set.range e))
    (hSY : Y ∈ supportedOperators d (Set.range f))
    (hX : X * initializedBasisMatrix (placedBasisEmbedding e g (Function.Embedding.refl _)) =
      initializedBasisMatrix (placedBasisEmbedding e g' (Function.Embedding.refl _)) *
        (V ⊗ₖ (1 : Matrix (OutsidePlacedConfig d e) (OutsidePlacedConfig d e) ℂ)))
    (hY : Y * initializedBasisMatrix (placedBasisEmbedding f k (Function.Embedding.refl _)) =
      initializedBasisMatrix (placedBasisEmbedding f k' (Function.Embedding.refl _)) *
        (W ⊗ₖ (1 : Matrix (OutsidePlacedConfig d f) (OutsidePlacedConfig d f) ℂ))) :
    (X * Y) * initializedBasisMatrix (jointPlacedBasisEmbedding e f h g k t) =
      initializedBasisMatrix (jointPlacedBasisEmbedding e f h g' k' t) *
        ((V ⊗ₖ W) ⊗ₖ (1 : Matrix τ τ ℂ)) := by
  classical
  obtain ⟨X₀, rfl⟩ := exists_embedOp_eq_of_mem_supportedOperators e.injective hSX
  obtain ⟨Y₀, rfl⟩ := exists_embedOp_eq_of_mem_supportedOperators f.injective hSY
  exact jointPlacedColumns_of_individual e f h g k g' k' t X₀ Y₀ V W
    ((placedColumns_iff_localColumns e g g' X₀ V).mp hX)
    ((placedColumns_iff_localColumns f k k' Y₀ W).mp hY)

end MPUCircuit
