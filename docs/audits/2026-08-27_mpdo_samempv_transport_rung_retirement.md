# MPDO same-MPV transport rung retirement

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style. The two removed declarations were
intermediate rungs of the hypothesis ladder leading to representative-grouped
Lemma L: each carried an auxiliary injectivity or common-block-length premise
and forwarded, in one `exact`, to the corresponding premise-free variant with
the same-MPV transport applied to the first-site hypothesis.

| Removed | Replacement |
|---|---|
| `MPSTensor.IsBNTCanonicalForm.insertedTensor_basis_eq_of_sameMPV₂Pos_firstSiteActionAgree_of_basis_injective` (`TNLean/MPS/MPDO/PostBlockedRepresentativeSpan.lean`) | `MPSTensor.IsBNTCanonicalForm.insertedTensor_basis_eq_of_sameMPV₂Pos_firstSiteActionAgree` (same file) |
| `MPSTensor.IsBNTCanonicalForm.insertedTensor_basis_eq_of_sameMPV₂Pos_firstSiteActionAgree_of_common_blockInjective` (`TNLean/MPS/MPDO/PostBlockedRepresentativeSpan.lean`) | `MPSTensor.IsBNTCanonicalForm.insertedTensor_basis_eq_of_sameMPV₂Pos_firstSiteActionAgree` (same file) |

The survivor reaches the same conclusion — equality of the inserted tensors on
every basis representative — from strictly fewer hypotheses: it derives the
common block-injectivity length internally from irreducibility,
left-canonicality, and normalized self-overlap, rather than taking it as input.
Any consumer of a removed name therefore uses the survivor unchanged, dropping
the injectivity argument it used to supply.

## What was checked

Neither removed name had a Lean consumer anywhere in `TNLean/`. Their only
references outside their own declarations were two `\lean{}` tags on
`thm:postblocked_representative_grouped_insert_eq` in
`blueprint/src/chapter/ch20_mpdo_canonical_forms_representative_marked.tex`,
dropped in the same change. That entry already tags the survivor, and the
survivor is what carries the entry's same-MPV sentences, so `\leanok` stays
correct and no `\uses` edge is redirected. The premise-carrying siblings that
take a first-site hypothesis directly rather than through same-MPV transport —
`..._of_firstSiteActionAgree_of_basis_injective` and
`..._of_firstSiteActionAgree_of_common_blockInjective` — are live and untouched.

## Net effect

`TNLean/MPS/MPDO/PostBlockedRepresentativeSpan.lean` goes from 409 to 366
lines, plus the two dropped blueprint tag lines.
