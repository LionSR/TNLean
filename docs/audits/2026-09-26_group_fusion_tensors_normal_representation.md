# Group fusion tensors stated for normal representations

This audit records the removal of one theorem. It is the audit note required by
`docs/project_conventions.md` §Style. All non-`Archive` uses are migrated, no
blueprint `\lean{...}` tag cites the removed name, and no compatibility alias is
kept.

## Removed declaration and its replacement

In `TNLean/MPS/FundamentalTheorem/Reduction/MPOProduct.lean`:

- `MPOTensor.GroupFamily.IsRepresentation.exists_fusionTensors`, replaced by
  `MPOTensor.GroupFamily.IsNormalRepresentation.exists_fusionTensors`.

The two theorems have the same conclusion. The removed theorem assumed the
matrix product unitary representation bundle `GroupFamily.IsRepresentation`,
which adds unitarity on every positive-length chain, simplicity of every tensor,
and the identity law `U_e = 1`. The proof used none of these. The replacement
assumes only `GroupFamily.IsNormalRepresentation`: every doubled-index tensor is
normal, and `U_g U_h = U_{gh}` holds on every nonempty chain. That is the
hypothesis of the lemma of Garre-Rubio, Lootens and Molnár, arXiv:2203.12563,
`Papers/2203.12563/REsubmission.tex` line 1211, which asks for an injective, not
necessarily unitary, representation, since injective tensors are normal. The old
statement is recovered as
`hF.isNormalRepresentation.exists_fusionTensors g h`.

## Moved declarations

`GroupFamily.IsNormalRepresentation`, `GroupFamily.IsRepresentation.isNormalRepresentation`,
`GroupFamily.IsNormalRepresentation.sameMPV₂Pos_mulTensor`, and
`MPOTensor.sameMPV₂Pos_toMPSTensor_of_mpo_eq` moved unchanged from
`TNLean/MPS/Symmetry/MPOSymmetry/Associator.lean` to `MPOProduct.lean`, which
`Associator.lean` imports. Their names are unchanged.
