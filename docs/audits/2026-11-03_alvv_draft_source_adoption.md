# Source adoption for the ALVV continuation

The dependent drafts tracked in #10533 retain the mathematical contributions
of the earlier soft-MPO, recursive-space and low-energy interval drafts
#10514, #10515 and #10523. They preserve current main's Lean/Mathlib 4.36.0-rc1
toolchain. Verification of the new heads is tracked separately in #10534.

The seven shared modules compared against the earlier interval draft are
`FiveRegionTruncationResidual`, `IndependentPhysicalDGPower`,
`IntervalSamplingTree`, `PhysicalDGGlobalApproximation`,
`PhysicalDGIntervalTree`, `PhysicalDGSampledNode` and
`PhysicalDGTreeParameters`, under `TNLean/MPS/AreaLaw/`.
Their adopted mathematical contents are those of the checked continuation
at `d5c2f758dda114f66280fea1ae77b019170918c0`.

The independent-threshold residual is now
`exists_five_region_independent_truncation_residual` in
`IndependentFiveRegionResidual`; the old residual module specializes it to
the equal-scale case. The two earlier low-energy callers are migrated to
the public independent-threshold result with their statements unchanged.
The six draft-only low-energy modules and their mathematical chapters are
retained; their replacement by the newer low-density results is not assumed.
The short-region spanning-family helper remains public under its earlier
active name, as required by the retained low-energy interval construction.

The filter construction retains its actual operator and tensor factors
before specializing to ordered words. The earlier fixed-radius node and
tree statements remain active corollaries of versions allowing a smaller
common radius. Four private approximation estimates are supplied by shared
owners rather than duplicated in the global approximation module.

The historical exact pair with QICLean
`32b5f3e04e232bb9ee2ee34a7bf5078b263b85b3` completed the full local build
and the recorded 909-declaration foundation audit on 4.35.0-rc3. Those facts
do not certify the newly reconciled 4.36 draft heads. The primitive physical
resampling construction and selected-image energy estimate are distinct
components; their final energy induction is tracked in #10535. Source
corrections remain in the cited `docs/paper-gaps/alvv16_*.tex` notes.

The mathematical sources are ALVV, arXiv:1602.08828v2, hard truncation
(lines 873-1041), low-density area laws (1096-1128), soft truncation
(1131-1302), and the degenerate-ground-space construction (1779-1818).
No running-time conclusion is asserted by this source adoption.
