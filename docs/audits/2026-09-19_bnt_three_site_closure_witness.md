# Bundling the three-site closure data of the BNT sector projectors

Issue: #6855, item 1 (bare existentials restated over witness structures).
Source baseline: `a1ff86dc2`.

## The duplication

The chain of sector-projector theorems for the four-site marginal of a tensor
saturating the area law consists of

- `MPOTensor.exists_bntSectorProjectors_four_of_sameMPV₂Pos_isSAL`
  (`TNLean/MPS/MPDO/BNTSourceSectorProjectors.lean`),
- `MPOTensor.exists_bntProjectorSelection_positiveLength_of_sameMPV₂Pos_isSAL`
  (`TNLean/MPS/MPDO/BNTProjectorSelection.lean`), and
- `MPOTensor.exists_bntSeparatingProjectors_of_sameMPV₂Pos_isSAL_of_weight_copy_independent`
  (`TNLean/MPS/MPDO/BNTSeparatingProjectors.lean`),

each importing the previous one. All three stated the same comparison data in
the same way: a reindexed three-site marginal bound by a `let`, a simultaneous
left inverse `C` of the one-site slices of the basis representatives with its
left-inverse property, a Hayashi--Markov decomposition of the marginal, and two
further `let` bindings naming the two halves of
`MPOTensor.reducedBlockState_four_threeSiteFamilyClosure_nonzero_closing`.
The preamble was byte-identical in the first two statements and differed only
by one binder offset in the third. Each of the three proofs then re-derived the
same two halves of the closure theorem, and the two downstream proofs in
`TNLean/MPS/MPDO/BNTSectorAreaLaw.lean` and
`TNLean/MPS/MPDO/BNTSectorAnalyticProperties.lean` re-derived them once more
after discarding the entire conclusion of the theorem they invoked.

## The witness structure

`MPOTensor.ThreeSiteClosureWitness M S`, in
`TNLean/MPS/MPDO/BNTSourceSectorProjectors.lean`, names the comparison data of
a tensor `M` and a sector decomposition `S`: the simultaneous left inverse `C`
and its defining property `hC`, the family closure `hρ` of the normalized
three-site marginal with the normalized three-site closing matrices, the
nonvanishing `hR` of those closing matrices, and a Hayashi--Markov
decomposition `hη` of the same marginal. The projections
`bntSectorProjection W.hC W.hρ W.hη W.hR` and
`completedBntSectorProjection W.hC W.hρ W.hη W.hR s₀` are then written from one
name.

The three theorems keep their names, their hypothesis lists, and their
mathematical content; each conclusion is now an existential over a witness. The
closure theorem is invoked exactly once in the whole chain, inside the proof of
the first theorem, and the witness is passed along by the two sequels and the
two downstream consumers.

The family closure and the nonvanishing of the closing matrices are fields of
the structure rather than definitions derived from the ambient hypotheses. The
derived form would require the four hypotheses `hM`, `hWeight`, `hnonNil` and
`hSAL` as structure parameters, used by nothing in the structure itself and
repeated at every mention of the type. Both fields are propositions about data
already fixed by `M` and `S`, so storing them asserts exactly what deriving
them would prove, and the existential statements are unchanged in strength.

## What was checked

- The three theorem names, their hypothesis lists, and the conclusions'
  mathematical content are unchanged, so the blueprint tags in
  `blueprint/src/chapter/ch21_mpdo_rfp_simple_local_markov_bnt_compression.tex`
  and the references in `docs/paper-gaps/` need no redirect. The blueprint
  statements already read as bundled existentials.
- Every use of the three theorems in the library was migrated: the two sequel
  proofs, the standing-context theorem
  `exists_bntSeparatingProjectors_of_horizontalCF_isSourceZCL_isSAL`, and the
  two absorbed-representative proofs
  `commonWeightAbsorbedBasisMPOTensor_isSAL_of_sameMPV₂Pos` and
  `commonWeightAbsorbedBasisMPOTensor_isMPDO_of_sameMPV₂Pos_isSAL`.
- No declaration was removed and no name was changed, so no deprecation alias
  question arises.

## What is retained

The pointwise projector lemmas keep their five separate hypotheses
(`hC`, `hρ`, `hη`, `hR` and the ambient data). They are stated for an arbitrary
family closure of an arbitrary family of tensors, are used far from this
four-site chain, and would lose that generality if rewritten over the witness.
The closure theorem itself is unchanged and remains the only source of the
`hρ` and `hR` fields.

## What is deferred

The remaining bare existentials and hypothesis telescopes listed in the same
issue are untouched.
