# Isolated integration with main 83108aec

Candidate: 207cc00e5e8e83447d0c965a12b1cc2de8f4f1e7.
Initial main: 5a1b680f6e1e627e3c5ebcb07523ba8f272fdc37.
Final main: 83108aec814ead604485848df1d0f6161ebd3a70.
The final main advance changes only the ALVV campaign config (two lines);
it adds no Lean, selector, blueprint or bibliography delta.
Actual merge base: 34b883ede92ae61398238cfc6e69a7298bda087c.
Main contains squash c727b509b of the 10879 refactor. No external branch or PR
was modified by this integration. Validation checkpoint inspected:
5f3c92e78fd061faa00ab4e3abd11c3e24f66df8.

## Resolution evidence

The ordinary merge reported 85 conflict files. In 84, the main blob is exactly
the original 10879 head 4c32f124c7e1b774adb65936a049c4c7be3e1623 blob.
Preserving the candidate there retains its independently reviewed subsequent
scope repairs without losing a later main edit. text-resolution.json records
the exact per-file blobs. The sole exception, EfficientSoftLowDensityCore,
retains main's canonical supportedOperators/cfc proof spelling; its theorem
signature is unchanged and the alternate candidate proof is equivalent in scope.

Automatic merges also needed six reviewed adjustments: preserve the candidate's
arbitrary-Aux omit in SpectatorOscillationSupport; preserve Set membership
elimination in RegisterTree rather than Finset.mem_filter; and remove duplicate
ManyBody.interval opens in EfficientSoftLowDensityCalibration,
EfficientSoftLowDensityFamily, LowDensityTreeAlgorithm and PhysicalLDSampledTree.
Those six final files are byte-identical to the candidate. No blanket side
selection was applied to files carrying new main content.

All twelve changed Lean files relative to the candidate are byte-identical to
main. Three are comment-only. Nine have code/import differences, including the
new DG node/tree chain, shared MergeRounds and canonical honeycomb edge references.
Main's DG imports, reference updates and paper-gap corrections are retained.
Candidate scope repairs, all regression scripts, the extra selector test, and
historical F12/F4 audit content are retained. Dependency pins and Lean options
are unchanged. ci_lean_checks.py is unchanged from both parents.

## Validation and reuse boundary

MergeRounds passed strict Lean flags. Import layers, 84 selector tests, roles
and whitespace checks passed. Full Blueprint sync passed. No full build or duplicate production-validation batch was run.
The remaining new-main code targets lack substantial local dependency caches.

The file-level reverse closure is 119 modules. Excluding comment-only changes,
the code-level closure is 15 modules (code-affected15.txt); eight belong to the
previous reverse658 list (code-impact.json). Those eight require new-head
validation even if their old-head batch passes. The other old results can be
reused subject to identical sources, pins and options; the prior 89 targets and
three final fixtures have no code-dependency intersection with the new delta.
This does not claim complete new-head CI or independent mathematical approval.

Suggested publication order: finish and record the old-head evidence, validate
the 15-module new-main closure on this merged tree, obtain review of the merge
resolution, then update the authorized shared PR branch and retarget to main.
Retargeting should follow the head update so the displayed PR covers only the
remaining repairs after main's squash. Recheck current main and required checks
before any eventual merge; do not bypass protections or close broader issues.
