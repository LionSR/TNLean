/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.Basic

/-!
# Left columns of a finite family

A finite family of vectors on the left configurations and a bond of dimension `m` supplies
at most its cardinality times `m` left columns. If every vector is fixed by the projection
onto `Span(S)` on the left factor, all these columns lie in `Span(S)`.

This is the column construction and counting step of Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, Claim `c:2`, lines 520–527. The finite set is constructed
from the supplied family; no Hamiltonian or ground vector enters its definition.
-/

open Matrix
open scoped Kronecker

namespace TNLean.MPS.AreaLaw

variable {ι : Type*} {L q k m : ℕ}

/-- The union of the `m` left columns of each vector indexed by `I`, as in LVV13,
`algo53.tex`, the size-trimming step and Claim `c:2`, lines 472–477 and 520–527. -/
noncomputable def leftColumns (I : Finset ι)
    (u : ι → EuclideanSpace ℂ (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m)) :
    Finset (LeftBlockVector L q k) := by
  classical
  exact (I ×ˢ Finset.univ).image fun p ↦
    WithLp.toLp 2 ((schmidtCoeffMatrix (WithLp.ofLp (u p.1))).col p.2)

/-- Each indexed vector contributes at most `m` columns (LVV13, `algo53.tex`,
Claim `c:2`, lines 520–527). Equal or zero columns are retained only once in the finite set. -/
theorem card_leftColumns_le (I : Finset ι)
    (u : ι → EuclideanSpace ℂ (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m)) :
    (leftColumns I u).card ≤ I.card * m := by
  classical
  exact Finset.card_image_le.trans (by simp)

/-- Fixing each vector by the left projection places every retained column in `Span(S)`.
This is the support assertion in LVV13, `algo53.tex`, Claim `c:2`, lines 520–527. -/
theorem leftColumns_subset_span (S : Set (LeftBlockVector L q k)) (I : Finset ι)
    (u : ι → EuclideanSpace ℂ (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m))
    (hfix : ∀ i ∈ I, (spanProjection S ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ
      WithLp.ofLp (u i) = WithLp.ofLp (u i)) :
    (leftColumns I u : Set (LeftBlockVector L q k)) ⊆ Submodule.span ℂ S := by
  classical
  intro v hv
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hv
  have hM := congrArg schmidtCoeffMatrix (hfix i (Finset.mem_product.mp hij).1)
  rw [schmidtCoeffMatrix_kronecker_one_mulVec] at hM
  have hcol := congrArg (fun M ↦ M.col j) hM
  rw [Matrix.col_mul_eq_mulVec_col] at hcol
  apply (Submodule.starProjection_eq_self_iff).mp
  rw [← toLp_spanProjection_mulVec, hcol]

end TNLean.MPS.AreaLaw
