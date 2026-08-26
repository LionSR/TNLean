# RFP Appendix B commuting-bridge pass-through retirement

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style. The declaration below was the middle link
of a three-step forwarding chain: it re-exported the extraction structure's own
commutation theorem under a spelled-out hypothesis list, and its single
non-`Archive` consumer was migrated in the same change.

| Removed | Replacement |
|---|---|
| `MPSTensor.commuting_twoSite_localTerms_of_rfp_of_appendixBExtraction` (`TNLean/MPS/RFP/AppendixBStructuralData.lean`) | `MPSTensor.AppendixBProductPairExtraction.commuting_twoSite_localTerms` (same file); the removed theorem's proof body was exactly `hExtract.commuting_twoSite_localTerms N hN` |

## What was checked

The removed theorem took `A`, `hNT`, `hRFP`, `hLeft` only to name the
structural datum `AppendixBStructuralData.ofRFP A hNT hRFP hLeft` inside the
type of its extraction hypothesis; the conclusion is the extraction structure's
own commutation statement, so those four binders are recovered from the
extraction hypothesis at any call site.

Its only non-`Archive` consumer was
`MPSTensor.rfp_implies_nncph_of_appendixBExtraction`
(`TNLean/MPS/RFP/CommutingBridge.lean`), whose body now reads
`hExtract.commuting_twoSite_localTerms N hN`. That theorem's signature is
unchanged: all four binders remain in use inside the type of `hExtract`, so no
unused-variable warning appears.

## Blueprint

The remark `rem:product_pair_projectors`
(`blueprint/src/chapter/ch13_parent_hamiltonian_commuting_gap_all_chain_sector_graph.tex`)
is a bundle node carrying many `\lean{...}` tags. The single tag naming the
removed declaration was deleted; the redirect target
`MPSTensor.AppendixBProductPairExtraction.commuting_twoSite_localTerms` was
already tagged on the same node, as is the surviving consumer
`MPSTensor.rfp_implies_nncph_of_appendixBExtraction`. The node keeps its
`\leanok`: every statement it asserts remains formalized.

## What is retained

The docstring of `rfp_implies_nncph_of_appendixBExtraction` is untouched,
including its sentence recording that the direct chain-transport theorem
`rfp_implies_nncph_of_leftCanonical` removes the extraction hypothesis for the
commutation conclusion. That remains accurate.
