# Sheet permutation lemma renames (2026-10-20)

Two lemmas about moving the sheet of one index of a family to the front of a list of sheets are
plain statements about `List.Perm`; they use no frames, holes or positions. They move from
`TNLean/PEPS/Approximation/DyadicProtocolStack.lean` to `TNLean/Lattice/Sheet/Stack.lean`, so that
the one-dimensional chain can use them without importing two-dimensional code. Statements and
proofs are unchanged; only the namespace changes:

| Removed | Replacement |
| --- | --- |
| `TNLean.PEPS.EncodedFrame.perm_map_cons` | `TNLean.Lattice.perm_map_cons` |
| `TNLean.PEPS.EncodedFrame.perm_map_update_cons` | `TNLean.Lattice.perm_map_update_cons` |

All uses outside `Archive` were in `DyadicProtocolStack.lean` and have been migrated, and the
blueprint `\lean` tags in `ch24_peps_sheet_stacks.tex` now cite the new names. No alias is kept.
