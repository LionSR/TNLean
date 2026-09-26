# Single-slot index sets folded into `MPSTensor.oneSlot`

This audit records the removal of four abbreviations. Each of them restated the
one-element slot set, or its unique member, that
`TNLean/MPS/FundamentalTheorem/Reduction/ExplicitGauge.lean` already provides as
`MPSTensor.oneSlot` and `MPSTensor.oneSlotMem`. It is the audit note required by
`docs/project_conventions.md` §Style. All non-`Archive` uses are migrated, no
blueprint `\lean{...}` tag cites a removed name, and no compatibility alias is
kept.

## Removed declarations and their replacements

In `TNLean/MPS/Examples/Z3Anomalous/Z3AnomalousFusion.lean`, which is also used
by `Z3AnomalousInverseFusion.lean` and `Z3AnomalyClass.lean`:

- `Z3Anomalous.singleSlot : Finset Unit := Finset.univ`, replaced by
  `MPSTensor.oneSlot : Finset Unit := {()}`;
- `Z3Anomalous.theSlot : {s // s ∈ singleSlot}`, replaced by
  `MPSTensor.oneSlotMem : {s // s ∈ oneSlot}`.

In `TNLean/MPS/Examples/CZX/CZXSquare.lean`, which is also used by
`CZXAnomaly.lean`:

- `CZXCompression.squareSlots : Finset Unit := {()}`, replaced by
  `MPSTensor.oneSlot`;
- `CZXCompression.squareSlot : {s // s ∈ squareSlots}`, replaced by
  `MPSTensor.oneSlotMem`.

Over `Unit` the sets `Finset.univ` and `{()}` are equal, so every statement
about the compression data (block indices, block spaces, the multi-block
compression datum and its dimension identities) keeps its content with the
shared slot set in place of the local one.

The unrelated `Z3Anomalous.squareSlots : Finset (Fin 3 × Fin 3)` in
`Z3AnomalousDefectCompression.lean` indexes nine slots and is unchanged.
