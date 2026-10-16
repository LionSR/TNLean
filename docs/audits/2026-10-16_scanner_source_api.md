# The direct scanner theorem and the former conditional declarations

The direct theorem `TNLean.PEPS.AreaLaw.Scan.CollarScan.scannerStatement` replaces
`TNLean.PEPS.AreaLaw.Scan.CollarScan.scannerStatement_of_scanInputsSupply` and the
predicate `TNLean.PEPS.AreaLaw.Scan.CollarScan.ScanInputsSupply`. The former theorem
assumed that the transport and norm-comparison estimates were already supplied.
The direct theorem derives them from the original physical, geometric and entropy
hypotheses and applies all four comparisons at the same selected charge and parameter.
The sharp comparisons retain their marginal smallness condition.

The source is Proposition 9.2 (`prop:scanner`), `08-scanner.tex`, lines 349–397 and
399–533, together with Proposition 8.1 (`prop:comparators`), `07-comparators.tex`,
lines 125–214, at manuscript revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The input entropy coefficient is retained. The positive output energy and density
coefficients may be enlarged after it is fixed, as explained in
[the coefficient note](../paper-gaps/arealaw2d_scanner_inputs.tex).

## References and removal

A source search found no production caller of the removed predicate or theorem
outside `TNLean/PEPS/AreaLaw/Scan/SourceScanner.lean`. Their external references were
confined to `TNLeanTest/PEPS/AreaLaw/Scan/SourceScannerAxioms.lean` and
`blueprint/src/chapter/ch24_peps_area_law_source_scanner.tex`. The imported test
now names the direct theorem; the blueprint states its four-comparison conclusion
and removes the former conditional entry.

No compatibility alias is retained, in accordance with
[the local API convention](../project_conventions.md). The abstract `ScanInputs`,
`ScanData`, `scanner_estimate` and the declarations in `PhysicalScanner` are not
removed or renamed. The existing aggregate import and test discovery remain sufficient.

## Verification boundary

The imported test checks that the exact direct theorem exists and that its logical
dependencies are precisely `propext`, `Classical.choice` and `Quot.sound`.
Its actual result and the ordinary production build must be recorded in the
accompanying pull request. This note supplies no independent claim that those
checks have completed.
