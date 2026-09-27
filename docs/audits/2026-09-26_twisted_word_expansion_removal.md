# Twisted word expansion folded into blocking of physical maps

This audit records the removal of one theorem. It is the audit note required by
`docs/project_conventions.md` §Style. All non-`Archive` uses are migrated, no
blueprint `\lean{...}` tag cites the removed name, and no compatibility alias is
kept.

## Removed declaration and its replacement

In `TNLean/MPS/Symmetry/Defs.lean`:

- `MPSTensor.evalWord_twistedTensor_ofFn`, the expansion of a word of the
  twisted tensor `twistedTensor A U g` as a sum over intermediate words with
  coefficients `∏ k, U g (b k) (v k)`.

Its only use was the proof of `MPSTensor.twistedTensor_blockTensor_comm`. That
theorem is now the case `W = U g` of `MPSTensor.blockTensor_rotatePhysical`
(moved to `TNLean/MPS/Core/Blocking.lean`), because `twistedTensor A U g` is
definitionally `rotatePhysical (U g) A` and `blockKronAction L U g` is
definitionally `blockKron L (U g)`. The word expansion itself survives in
general form as `MPSTensor.evalWord_rotatePhysical_ofFn`
(`TNLean/MPS/Core/PhysicalRotation.lean`), which the proof of
`blockTensor_rotatePhysical` uses.

The blueprint entry `lem:eval_word_twisted_tensor` is removed with the
declaration; the new entry `thm:block_tensor_rotate_physical` carries the
word-expansion argument.
