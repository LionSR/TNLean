# MPDO physical-support shadow retirement

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style for the physical-support transport modules
under `TNLean/MPS/MPDO`. Four declarations are removed: one restatement of a
lemma the QICLean companion library already exports, and three private helpers
that shadow Mathlib lemmas.

| Removed | Replacement |
|---|---|
| `Matrix.partialTraceRight_singleKraus_kronecker_isometry` (`TNLean/MPS/MPDO/PhysicalSupportSALTransport.lean`) | `Matrix.partialTraceRight_kronecker_conj_of_right_isometry` (QICLean, `QICLean/Channel/PartialTrace.lean`) |
| `MPOTensor.PhysicalSupportRestrictionData.product_isHermitian_of_comm` (private, `TNLean/MPS/MPDO/PhysicalSupportBondCommutativity.lean`) | `Matrix.IsHermitian.commute_iff` (Mathlib, `Mathlib/LinearAlgebra/Matrix/Hermitian.lean:301`), forward direction |
| `MPOTensor.PhysicalSupportRestrictionData.commute_of_product_isHermitian` (private, same file) | `Matrix.IsHermitian.commute_iff` composed with `Commute.eq`, reverse direction |
| `MPOTensor.list_prod_eq_one_of_forall` (private, `TNLean/MPS/MPDO/PhysicalSupportProductTransport.lean`) | `List.prod_eq_one` (Mathlib, `Mathlib/Algebra/BigOperators/Group/List/Basic.lean:161`) |

## What was checked

**QICLean residue.** The body of
`Matrix.partialTraceRight_singleKraus_kronecker_isometry` was a bare `exact` of
`Matrix.partialTraceRight_kronecker_conj_of_right_isometry` on the same four
explicit arguments, with the same hypothesis on the discarded factor. The
QICLean lemma is already in the import closure of the file through
`TNLean.MPS.MPDO.AreaLaw`, so no import changed. The wrapper had exactly one
Lean consumer, the proof of
`MPOTensor.blockReducedState_singleKraus_sitewise` in the same file, which now
names the QICLean lemma directly with the argument list unchanged. This residue
belongs to the split record at
`blueprint/qiclean_split_residual.json:317-327`, the entry
`lem:partial_trace_product_isometry`, which already lists the survivor as the
declaration owning the statement.

**Hermitian-product helpers.** The two private helpers in
`PhysicalSupportBondCommutativity.lean` were the two directions of Mathlib's
`Matrix.IsHermitian.commute_iff`, transcribed with the commutation written as
an equation rather than as `Commute`. Since `Commute A B` unfolds to
`A * B = B * A` definitionally, the forward direction is applied directly to
the existing `hcomm` hypothesis, and the reverse direction is wrapped in
`Commute.eq` so that the goal matches syntactically. Both helpers were used
twice each, in `liftedBond_three_zero_one_comm` and
`liftedBond_two_zero_one_comm`; the surrounding proofs, including the three
bullets supplying Hermitianity of each factor and Hermitianity of the ambient
product, are unchanged.

**List-product helper.** `list_prod_eq_one_of_forall` restated Mathlib's
`List.prod_eq_one` with the list made explicit and the induction written out.
Both of its consumers sit inside
`list_prod_eq_of_mem_idempotent` in the same file and were rewritten to the
Mathlib spelling, whose list argument unifies from the goal.

## Blueprint

The proof node of `thm:mpdo_block_reduced_state_single_kraus_sitewise` in
`blueprint/src/chapter/ch21_mpdo_rfp_gsnnch_definitions.tex` cited the removed
wrapper in a `\lean{...}` tag; it is redirected to the QICLean survivor in the
same change. The theorem node's own tag,
`MPOTensor.blockReducedState_singleKraus_sitewise`, is untouched, and the
`\leanok` status of both nodes is unchanged. None of the three private helpers
appears in any `\lean{...}` tag under `blueprint/src`.

## Transition declarations

Three of the four removed names are `private`, and the fourth is a
zero-content forwarder whose sole consumer is migrated in the same change; no
surviving blueprint `\lean{...}` tag cites a removed spelling. No deprecation
alias is warranted under the pass-through exception.
