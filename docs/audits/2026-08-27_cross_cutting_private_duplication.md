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
| `MPSTensor.cyclic_projection_mem_multiplicativeDomain` (private, `TNLean/MPS/CanonicalForm/SectorComparison/CyclicSectorDecomposition.lean`) | `MPSTensor.cyclic_projection_mem_multiplicativeDomain`, the same statement now public in `TNLean/MPS/Periodic/SectorIrreducibility/HLift.lean` |
| `MPSTensor.cyclic_projection_mul_left` (private, same file) | `MPSTensor.cyclic_projection_mul_left` in `TNLean/MPS/Periodic/SectorIrreducibility/HLift.lean` |
| `MPSTensor.cyclic_projection_mul_right` (private, same file) | `MPSTensor.cyclic_projection_mul_right` in `TNLean/MPS/Periodic/SectorIrreducibility/HLift.lean` |
| `MPSTensor.fin_cyclic_induction` (private, `TNLean/MPS/Periodic/Overlap/SectorMatch/Propagation.lean`) | `Fin.cyclic_induction`, new public theorem in `TNLean/Algebra/FinCyclicInduction.lean` |
| `PEPS.fin_cyclic_induction` (private, `TNLean/PEPS/CycleMPSChainOverlapCapstone.lean`) | the same `Fin.cyclic_induction` in `TNLean/Algebra/FinCyclicInduction.lean` |
| `MPSTensor.selfOverlap_tendsto_one_of_irreducible_primitive_TP` (private, `TNLean/MPS/Periodic/Overlap/SectorMatch/Propagation.lean`) | `MPSTensor.overlap_tendsto_one_of_peripheralPrimitive_of_irreducible` in `TNLean/MPS/Overlap/PeripheralToTransferMapGap.lean` |

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

**Multiplicativity on cyclic-sector projections.** Three statements about a
cyclic-sector decomposition of the adjoint transfer map — that each sector
projection lies in the multiplicative domain of the Kraus family of adjoint
letters, and that the map is therefore multiplicative against that projection on
the left and on the right — existed in three places at once. Two were the
`private` theorems of `CyclicSectorDecomposition.lean`; the other two were
inline re-derivations of the same Kadison–Schwarz argument, one inside
`MPSTensor.sectorFixedPointAlgebraRigidity_of_irreducible_tp` in
`TNLean/MPS/Periodic/SectorIrreducibility/HLift.lean` and one inside
`MPSTensor.cornerRestriction_primitive_and_irreducible_of_cyclicDecomp` in
`TNLean/MPS/Periodic/Overlap/SelfOverlapSetup.lean`. The two inline copies
differed from the named ones only in spelling the transfer map through a local
abbreviation.

The survivors are stated in `HLift.lean`, the module that owns the two theorems
consuming this multiplicativity as a hypothesis pair, and the two other holders
reach it through `TNLean.MPS.Periodic.SectorIrreducibility`, which they already
import. Both inline re-derivations are replaced by two `have`s naming the
survivors; because the survivors are stated directly in terms of the transfer
map rather than a local abbreviation, the replacement is a tighter match for the
call sites that consume them than the locals it replaces. Dropping the
Kadison–Schwarz argument from `CyclicSectorDecomposition.lean` left no
multiplicative-domain name in that file, so its `open KadisonSchwarz` line and
its `QICLean.Channel.Schwarz.MultiplicativeDomainFull` import were removed too.

This is the second time these three statements have been given a single owner.
`docs/audits/2026-04-23_issue448_self_overlap_cases.md` records an earlier round
in which the duplicated copies were removed from the self-overlap module in
favour of shared declarations exported from the assembly module that has since
become `CyclicSectorDecomposition.lean`; the duplication returned as inline
re-derivations rather than as re-declared names, which is why a name search did
not catch it. Keeping the survivors public, in the module whose theorems take
them as hypotheses, is what makes the regression visible next time.

**Cyclic induction on a finite index.** The induction principle stating that a
predicate on a nonempty finite cyclic index set which holds at zero and passes
from each index to its successor holds everywhere was proved twice, once in the
periodic sector-match propagation module and once in the site-dependent
closed-chain capstone of the two-dimensional development. The two proofs agree
line for line up to indentation. The holders sit in unrelated import closures
whose only shared ancestor under `TNLean/Algebra` is the trace-pairing module,
so neither could own the survivor and a new lightweight module was the right
home; it imports only the basic finite-index file of Mathlib, which supplies the
one non-core lemma the proof needs. The statement is upstreamable: Mathlib
carries only the successor-shaped induction on an index set of positive size and
no cyclic principle. The survivor is named in the `Fin` namespace with the
underscore-separated spelling the two local copies already used.

**Self-overlap limit under peripheral primitivity.** The propagation module
re-proved privately, from the spectral-gap corollary, that the self-overlap of an
irreducible trace-preserving tensor with primitive peripheral spectrum tends to
one. The public statement of exactly that fact already lives in the overlap
directory, with the same binders, the same hypothesis order and the same
conclusion, and reaches the propagation module through the gauge-phase module it
already imports, so no import change was needed. Its two call sites take the
same argument lists unchanged. The blueprint tag for the surviving public
theorem in the Wielandt appendix is untouched.

## Verification

Root `lake build` completes successfully with the package lean options, so the
linters that see three newly public declarations ran. `check_forbidden_lean_tokens.py`,
`check_reader_facing_prose.py`, `check_numbered_lean_files.py`,
`check_oversized_lean_files.py` and `generate_import_aggregators.py --check` are
clean, and `leanblueprint checkdecls` resolves every tag.
