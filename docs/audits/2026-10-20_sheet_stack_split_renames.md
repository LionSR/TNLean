# Sheet-stack split renames (2026-10-20)

At the start of the stacked protocol each party splits its whole private memory into the
registers of the sheets it holds. This splitting does not use the holes of an encoded frame.
#9773 moves it, with the rest of the stack layer, into `TNLean/Lattice/Sheet/`, which imports
nothing from `TNLean.PEPS` or `TNLean.MPS`. The declarations keep their statements and proofs;
only the namespace changes, from `TNLean.PEPS.EncodedFrame` to `TNLean.Lattice`:

| Removed (`TNLean.PEPS.EncodedFrame`) | Replacement (`TNLean.Lattice`) |
| --- | --- |
| `splitMap` | `splitMap` |
| `splitMap_tmul_one` | `splitMap_tmul_one` |
| `norm_splitMap_le` | `norm_splitMap_le` |
| `splitCircuit` | `splitCircuit` |
| `nonprivateCount_splitCircuit` | `nonprivateCount_splitCircuit` |
| `isExpansionBounded_splitCircuit` | `isExpansionBounded_splitCircuit` |
| `isMonomialBounded_splitCircuit` | `isMonomialBounded_splitCircuit` |
| `participants_splitCircuit_subset` | `participants_splitCircuit_subset` |
| `eval_splitCircuit` | `eval_splitCircuit` |

All uses outside `Archive` were in the stack files and have been migrated, and the blueprint
`\lean` tags in `ch24_peps_sheet_stacks.tex` now cite the new names. No alias is kept.
