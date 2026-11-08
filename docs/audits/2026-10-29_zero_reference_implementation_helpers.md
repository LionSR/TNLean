# Two unused implementation helpers

Scope: proof-debt issue #9881, ledger S2. Base:
`c7d2992c89c16d85237e18557ff292979b3a67b4`.

Remove only:

- `TNLean.Lattice.mem_labelClass_symm`, in `LowEnergyBasisIteration.lean`:
  an unused symmetry projection for the internal label-class relation. The
  stronger `labelClass_eq_of_mem`, membership characterization, self-membership
  and all source-facing iteration estimates remain.
- `EncodedFrame.exists_mem_tagSample_of_mem_patchSquares`, in
  `PatchRewriteExpansion.lean`: an unused recursive unpacking of membership in
  the selected-square union. The union definition, live containment statements,
  wire classification and complete rewrite conclusions remain.

The tracked Lean, Blueprint, documentation, script, note and paper corpus has
only the first helper's declaration, and the second helper's declaration and
self-recursive call. Neither carries an automation attribute or a Blueprint
anchor. The default fixed-point scan identifies both; direct searches use each
final name separately and retain receiver-notation matches. Searches of their
introduction history found no earlier removal or rollback. Neither name is a
module headline or a separately source-cited mathematical statement.

No replacement declarations or compatibility aliases are added. TNLean's
unstable-API policy permits removing unused implementation helpers. The exact
production delta is minus 14 lines: 12 declaration/proof lines and two separating
blank lines. Every remaining byte in both source files is unchanged. The
separate three-helper Circuit/PartyChain slice in #10296 is untouched.

Validation: direct reference census, retained-byte comparison, generated-import
check, full Blueprint/source synchronization, reader-facing prose, forbidden-token
and whitespace checks. These are source/native checks. The user requested no
local Lean elaboration or build; hosted validation and repository integration
remain pending, and #9881 stays open. No public source bound, worked example,
QCA/MPU file or Blueprint entry is removed.
