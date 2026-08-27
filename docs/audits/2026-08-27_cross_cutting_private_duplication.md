# Cross-cutting private duplication: single owners for five repeated lemmas

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style for five statements that had been proved
more than once, each copy `private` to its own module. In every case the copies
were verbatim or differed only in tactic spelling, and every module holding a
copy already sat in the import closure of the module that now owns the survivor.
No `@[deprecated] alias` is warranted: every removed name was `private`, so it
had no external surface, and none of the removed names encodes misleading
terminology.

| Removed | Replacement |
|---|---|
| `MPSTensor.overlap_tendsto_zero_of_not_mpvBlockPhaseEquiv` (private, `TNLean/MPS/CanonicalForm/BNTCharacterization.lean`) | `MPSTensor.overlap_tendsto_zero_of_not_mpvBlockPhaseEquiv`, new public theorem in `TNLean/MPS/Overlap/NormalTensorDichotomy.lean` beside `IsNormalTensor.mpv_phase_alternative`, of which it is the contrapositive |
| `MPSTensor.overlap_tendsto_zero_of_not_mpvBlockPhaseEquiv` (private, `TNLean/MPS/RFP/BeigiLoopBNTIdentification.lean`) | the same new public theorem in `TNLean/MPS/Overlap/NormalTensorDichotomy.lean` |
| `MPOTensor.equivReindexMap_symm_apply_self` (private, `TNLean/MPS/MPDO/RFPViaTSBlocking.lean`) | `MPOTensor.equivReindexMap_symm_apply_self`, moved from `TNLean/MPS/MPDO/BNTChannelComposition.lean` to their common ancestor `TNLean/MPS/MPDO/PhysicalBlocking.lean` under the same fully qualified name |
| `MPOTensor.KatoDeformedRFPObstruction.negMulLog_pow_inv_mul` (private, `TNLean/MPS/MPDO/KatoDeformedRFPObstruction.lean`) | `Real.mul_negMulLog_inv`, new public theorem in `TNLean/Algebra/NegMulLog.lean` |
| `MPOTensor.CPSVExample412Literal.negMulLog_pow_inv_mul` (private, `TNLean/MPS/MPDO/CPSVExample412Literal.lean`) | `Real.mul_negMulLog_inv` in `TNLean/Algebra/NegMulLog.lean` |
| `MPSTensor.compressedTensor_adjointTransferMap_primitive_and_irreducible_of_corner` (private, `TNLean/MPS/CanonicalForm/SectorComparison/CyclicSectorDecomposition.lean`) | `MPSTensor.compressedTensor_adjointTransferMap_cornerBridge` (`TNLean/MPS/CanonicalForm/CyclicSectors/CornerBridge.lean`), which the removed wrapper forwarded to with an identical argument list |
| `MPSTensor.mpv_twoBlockTensor_eq` (private, `TNLean/MPS/CanonicalForm/Reduction.lean`) | `MPSTensor.mpv_twoBlockTensor_eq` in `TNLean/MPS/Structure/InvariantSubspaceDecomp.lean`, now public — the module that owns `twoBlockTensor` and `twoBlockBlocks` |

## What was checked

**Normal-tensor phase contrapositive.** The two private copies stated the same
implication: two normal tensors that are not related by a matrix-product-vector
phase equivalence have overlap tending to zero. Both derived it from
`IsNormalTensor.mpv_phase_alternative`, which lives in
`TNLean/MPS/Overlap/NormalTensorDichotomy.lean`; both holders import that module
directly. The survivor is stated there, next to the alternative it negates, and
uses the file's own `variable {d D₁ D₂ : ℕ}` binders and `nhds` spelling. The four
call sites in `BNTCharacterization.lean` and the two in
`BeigiLoopBNTIdentification.lean` resolve to it unchanged.

**Reindexing round trip.** The statement that reindexing a matrix by an
equivalence and then by the inverse equivalence returns the original matrix
appeared once as a public theorem and once as a private lemma, with byte-identical
proofs. Both `BNTChannelComposition.lean` and `RFPViaTSBlocking.lean` import
`TNLean.MPS.MPDO.PhysicalBlocking`, so the declaration moved there, keeping the
fully qualified name `MPOTensor.equivReindexMap_symm_apply_self`. The
`\lean{...}` payload of `thm:mpdo_absorbed_bnt_channel_assembly` in
`blueprint/src/chapter/ch21_mpdo_rfp_simple_local_refinement_channels_physical_coordinates.tex`
names that fully qualified name and needed no redirect; `leanblueprint checkdecls`
confirms it still resolves.

**Negated multiplication by a logarithm.** The identity relating a nonzero real
multiplied by the negated-multiply-logarithm of its inverse to the logarithm of
the real itself was proved twice, in two modules that both import
`TNLean/MPS/MPDO/AreaLaw.lean`. The survivor is stated in `TNLean/Algebra/NegMulLog.lean`, in the `Real`
namespace where the Mathlib lemmas it composes live; it is upstreamable, since
Mathlib's `Analysis/SpecialFunctions/Log/NegMulLog.lean` has no lemma of this
shape. Both consuming modules import the lightweight owner directly.

**Corner-bridge wrapper.** The private theorem in `CyclicSectorDecomposition.lean`
restated the signature of `compressedTensor_adjointTransferMap_cornerBridge` and
applied it to its own arguments in order. Binder names, binder order, and the
positive-dimension instance slot agree between the two, so the sole call site
needed only the name change; the import that made the wrapper's own proof
elaborate is still needed and untouched.

**Two-block matrix-product-vector formula.** The formula expressing the vector of a
two-block tensor as the sum of the vectors of its blocks was proved in
`Reduction.lean` and again in `InvariantSubspaceDecomp.lean`. The latter owns
`twoBlockTensor` and `twoBlockBlocks` and is imported by the former, so it keeps
the statement, with the `private` modifier dropped; its existing docstring means
making it public raises no documentation-linter complaint. Both call sites, one in
each file, resolve unchanged — the survivor's binders `n`, `m`, `N` are implicit and
the named arguments used at the second site remain valid.

## Verification

Root `lake build` completes successfully with the package lean options, so the
linters that see three newly public declarations ran. `check_forbidden_lean_tokens.py`,
`check_reader_facing_prose.py`, `check_numbered_lean_files.py`,
`check_oversized_lean_files.py` and `generate_import_aggregators.py --check` are
clean, and `leanblueprint checkdecls` resolves every tag.
