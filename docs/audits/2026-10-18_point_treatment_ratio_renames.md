# Point-treatment ratio renames (2026-10-18)

#9708 replaces the existential footprint threshold of the point treatments by the explicit
ratio `pointTreatmentRatio ε₀ = min(ε₀, 1) / 20000` (issue #9659). Four intermediate theorems
stated `∃ ν' > 0, ∀ ν, 0 < ν → ν ≤ ν' → …`. Each is replaced by the same statement with
`ν' = pointTreatmentRatio ε₀`, under an `_of_le` name:

| Removed | Replacement |
| --- | --- |
| `exists_pointTreatment_footprintRatio_homogenize_reading` | `pointTreatment_footprintRatio_homogenize_reading_of_le` |
| `exists_pointTreatment_step_reading_isSourceBounded` | `pointTreatment_step_reading_isSourceBounded_of_le` |
| `exists_pointTreatment_step_reading` | `pointTreatment_step_reading_of_le` |
| `exists_pointTreatment_step_supplied` | `pointTreatment_step_supplied_of_le` |

All uses outside `Archive` were in this chain and have been migrated, and the blueprint `\lean`
tags in `ch24_peps_guide_frames.tex` and `ch24_peps_encoded_frames.tex` now cite the new names.
`exists_template_footprintRatio_reading` and `exists_pointTreatment_hasSourceBoundedChange` keep
their names and statements. They are now corollaries at the explicit ratio.

`IsLocallyInLines.preimage_affine`, `HasLineWalls.comp_affine` and `finite_wallNormals` move
unchanged, with the same names, from `DyadicReadingFootprints.lean` to `DyadicWallSlopes.lean`.
