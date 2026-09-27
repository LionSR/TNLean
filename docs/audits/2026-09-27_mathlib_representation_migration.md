# Migration of local representation-side notions to Mathlib

This audit records the declarations that the refactor of PR #8343 removes, and
their replacements. Each removed notion duplicated a Mathlib structure: the
action of a monoid on a set, the action of an algebra on a module, the average
of a representation over a finite group, and semisimplicity of a module. No
compatibility aliases are retained, following the removal policy in
`docs/project_conventions.md`. All non-`Archive` call sites are migrated, and no
blueprint `\lean{...}` tag cites a removed name.

## Exact mapping

| Removed declaration | Replacement |
|---|---|
| `TNLean.Algebra.unitaryMatrixRepresentation` | none; the linear representation is formed inside the proof of `TNLean.Algebra.isStarProjection_inv_card_smul_sum` and passed to Mathlib's `Representation.averageMap` |
| `TNLean.Algebra.finiteGroupUnitaryAverage` | the explicit average `(Fintype.card G : ℂ)⁻¹ • ∑ g, (ρ g : Matrix ι ι ℂ)`, identified there with the matrix of `Representation.averageMap` |
| `TNLean.Algebra.isStarProjection_finiteGroupUnitaryAverage` | `TNLean.Algebra.isStarProjection_inv_card_smul_sum` |
| `TNLean.Algebra.isOrthogonalProjection_finiteGroupUnitaryAverage` | `TNLean.Algebra.isOrthogonalProjection_inv_card_smul_sum` |
| `Matrix.mulVecInvtSubalgebra`, `Matrix.mem_mulVecInvtSubalgebra` | none; a subspace invariant under a star-subalgebra `S` is a `Submodule S.toSubalgebra` of the coordinate space |
| `Matrix.forall_mulVec_mem_of_mem_adjoin` | none; its one use, in `MPSTensor.isSemisimpleModule_wordModule_of_conjTranspose_mem_adjoin`, is now an `Algebra.adjoin_induction` inside that proof |
| `Matrix.exists_isCompl_forall_mulVec_mem` | `StarSubalgebra.isSemisimpleModule`, which concludes Mathlib's `IsSemisimpleModule` |
| `WordAlgebra.actAlgHom`, `WordAlgebra.actAlgHom_apply` | Mathlib's `Algebra.lsmul ℂ ℂ M` and its `apply` lemma |
| `MPSTensor.FlagData.actAlgHom_mem_cflag` | `MPSTensor.FlagData.lsmul_mem_cflag` |
| `MPSTensor.actAlgHom_wordModule_ofWord` | `MPSTensor.lsmul_wordModule_ofWord` |
| `MPSTensor.OnSiteSymmetry` | a Mathlib `MulAction G (Fin d)`; the unused matrix field `u` has no replacement |
| `MPSTensor.TwistedTensor S A g` | `MPSTensor.TwistedTensor A g`, with the action supplied by the `MulAction` instance |
| `MPSTensor.TwistedTensor_apply`, `MPSTensor.TwistedTensor_one`, `MPSTensor.TwistedTensor_mul` | the same names, without the structure argument and without the hypotheses `σ 1 = id` and `σ (g * h) = σ g ∘ σ h`, which are now the `MulAction` axioms |
