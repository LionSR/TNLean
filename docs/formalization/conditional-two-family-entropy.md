# Labelled conditional two-family integration

The existing `OrderedTwoFamilyPartition` induces each family's creation order.
Its `conditionalMutualInformation_le_sum` method consumes the generic QICLean
conditional two-family theorem with exactly the exterior disjointness conditions
`Disjoint G B`, `Disjoint G C`, and `Disjoint B C`. Family zero is tested against
`C ∪ B ∪ earlierSameFamily`; family one against `(G ∪ B)ᶜ ∪ earlierSameFamily`.

The second form agrees exactly with the QIC theorem because
`C ∪ (G ∪ B ∪ C)ᶜ = (G ∪ B)ᶜ`. No conditioning monotonicity is assumed.

`regionalEntropy_conditional_le_residual_add_sum` rewrites the result using the
four existing finite-domain regional entropy terms. It introduces no new CMI,
state, or partition definition. Canonical tripartite CMI API identification remains
separate; the native four-entropy statement is independently meaningful now.

This is only the entropy step in the proof of the PEPS cell-information lemma.
It proves no collars, geometric partition, dimension/site-count transport or
polylogarithmic cell estimate. Its blueprint label is separate from the full
source lemma. All code is independently written from the paper and existing APIs.
