# Rounded clearance: the duplicate shell-safety lemma (2026-10-11)

`TNLean/PEPS/AreaLaw/Scan/RoundedClearance.lean` carried
`TNLean.PEPS.AreaLaw.IsSafe.cappedDyadicPartition_shell`, which reproved the
shell-cell safety of
`TNLean.PEPS.AreaLaw.IsSafe.isSafe_cappedDyadicPartition_shell`
(`TNLean/PEPS/AreaLaw/WeakRectangleShellSafety.lean`) under the budget
`(D₀ + 1) * L ≤ D₀ * Q.size` instead of the equal `D₀ * L + L ≤ D₀ * Q.size`.
Its only consumer was `Scan.exists_safe_shell_cells_of_rounded_scales` in the
same file, plus one regression example and one axiom check in
`TNLeanTest/RoundedClearance.lean`. It carried no `sorry` or `axiom` (#9137).

## Removed declarations and their replacements

| Removed declaration | Replacement |
|---|---|
| `TNLean.PEPS.AreaLaw.IsSafe.cappedDyadicPartition_shell` | `TNLean.PEPS.AreaLaw.IsSafe.isSafe_cappedDyadicPartition_shell`, with the budget rewritten by `add_one_mul` |

## Prose repointed

- `thm:area_law_rounded_safe_shell_cells` in
  `ch24_peps_rounded_rectangle_clearance.tex` now states only the rounded-scale
  result that its remaining tag
  `Scan.exists_safe_shell_cells_of_rounded_scales` proves. The unrestricted
  shell-cell safety is `thm:area_law_rectangle_shell_safe_cells`, which the
  proof cites and which already tags the surviving lemma.
- The regression example in `TNLeanTest/RoundedClearance.lean` applies the
  surviving lemma, and the axiom check drops the removed name.
