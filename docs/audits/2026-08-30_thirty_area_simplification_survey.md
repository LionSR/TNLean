# Three-pass, ninety-area simplification survey

This note records three successive repository-wide applications of the
`find-simplification` audit on 2026-08-30. The non-Archive development was
first divided into thirty broad areas and then into thirty narrower areas for
an independent second pass. A third pass divided the development into thirty
cross-repository structural slices. Each area was checked against the current
Blueprint declaration set, the open proof-debt ledger, open and closed cleanup
issues, the glossary and paper-gap records, and the newest relevant dated
audits.

The three passes found three bounded deletion batches and one stale ledger
status. The batches remove seven declarations and 52 net Lean lines. Five
forwarding theorems in `PiAlgebra` account for 26 lines, while one deferred
inverse gauge construction in `PEPS` accounts for 12 net lines after its module description
is shortened, and one attribute-carrying MPDO projection accounts for 14 lines.
No new proof-debt issue is needed: all three batches are further
evidence for S2 and issue #4564.

## New evidence for S2 and issue #4564

Five forwarding theorems in
`TNLean/PiAlgebra/CanonicalFormSepAux.lean` had no production Lean consumer
and no Blueprint tag:

- `MPSTensor.IsCanonicalForm.toHasInjectiveBlocks` (line 236), whose direct
  replacement is `HasInjectiveBlocks.ofForall hCF.block_injective`;
- `MPSTensor.IsCanonicalForm.toIsLeftCanonicalBlockFamily` (line 240), whose
  direct replacement is
  `IsLeftCanonicalBlockFamily.ofForall hCF.leftCanonical`;
- `MPSTensor.IsCanonicalForm.toHasNormalizedSelfOverlap` (line 245), whose
  direct replacement is
  `HasNormalizedSelfOverlap.ofForall hCF.overlap_tendsto_one`;
- `MPSTensor.IsNormalCanonicalForm.toHasPrimitiveBlocks` (line 300), whose
  direct replacement is `HasPrimitiveBlocks.ofForall hNCF.block_primitive`;
- `MPSTensor.IsNormalCanonicalForm.toHasNormalizedSelfOverlap` (line 337),
  whose direct replacement is
  `HasNormalizedSelfOverlap.ofForall hNCF.overlap_tendsto_one`.

The first four names occurred in the sanctioned-bridge lists in
`docs/glossary.md`; these were documentation references rather than Lean
consumers and have been replaced by the direct constructors or structure
fields. The similarly named normal-form
projections to irreducibility and left-canonical data remain live through
`TNLean/MPS/BNT/Construction.lean` and are not candidates.

This batch is an instance of the existing zero-reference debt S2 and issue
#4564, not a new debt. Its implementation deletes exactly 26 Lean lines and
rewrites six glossary lines in place, so the glossary migration is line-neutral.

## Second-pass evidence for S2 and issue #4564

The narrower second pass independently reconfirmed the five `PiAlgebra`
forwarders and found one further zero-reference declaration:
`TNLean.PEPS.edgeGaugeOfCycleGauge` in
`TNLean/PEPS/CycleMPSFundamentalTheorem.lean`. This construction had already
been isolated for a follow-up in
`docs/audits/2026-08-26_peps_normal_cycle_zero_reference_deletion.md` after its
round-trip theorem was removed. A fresh search found no production Lean
consumer, Blueprint tag, or paper-gap citation. The deletion removes its
seven-line declaration. Shortening the module description deletes seven more
lines and adds two replacement lines, for 12 net Lean lines in this file.

The surviving direction `cycleGaugeOfEdgeGauge` remains load-bearing: it
appears in `cycleGauge_component_iff_matrix` and in the graph-to-matrix
presentation described by the module. Thus this batch removes only the unused
inverse construction, not the cycle-gauge conversion used by the Fundamental
Theorem.

## Third-pass evidence for S2 and issue #4564

The third pass found one attribute-carrying declaration whose name had no
production consumer and whose simplification attribute did not fire in the
linter-bearing module build:
`MPOTensor.BNTFusionTensorClause.retainedMultiplicityWeightEntry_verticalCopyCoordinateEquiv_symm`
in
`TNLean/MPS/MPDO/TopologicalMultiplicityEnergy.lean`. It was a projection
wrapper over the corresponding retained-multiplicity coordinate formula and
had no Blueprint tag. Deleting it removes exactly 14 Lean lines, as measured by
`git diff --numstat` for the file.

The linter-bearing verification
`lake build TNLean.MPS.MPDO.TopologicalMultiplicityEnergy` passed after the
deletion. Thus the build, rather than name counting alone, confirms that the
`@[simp]` declaration was not used implicitly within the checked module. This
batch is recorded under S2 rather than as a new issue.

## Ledger correction

Ledger item S12 was still marked open although commit `f3ae05159` (#7218)
already consolidated both named spectral-split developments. The strict
two-block decomposition now uses the shared private theorem
`exists_twoBlock_decomp_of_lowerZero_aux`, and cyclic-sector compression now
uses the support-isometry route. Follow-ups #7224 and #7237 completed the
review. The ledger status is therefore corrected to burned down.

## First-pass area disposition

The thirty areas were:

1. Algebra;
2. MPS definitions and top-level files;
3. MPS Core;
4. MPS Chain;
5. MPS Overlap;
6. MPS Examples;
7. MPS SharedInfra and Tactic;
8. MPS Irreducible;
9. MPS Symmetry;
10. MPS Periodic;
11. MPS FundamentalTheorem;
12. MPS CanonicalForm root;
13. CanonicalForm CyclicSectors;
14. CanonicalForm NormalReduction;
15. CanonicalForm SectorComparison;
16. MPS BNT;
17. MPS Structure;
18. MPS MPU;
19. ParentHamiltonian root;
20. ParentHamiltonian Martingale;
21. MPDO root, alphabetic range A--L;
22. MPDO root, alphabetic range M--Z;
23. MPDO BiCFDerivation;
24. MPDO GSNNCHFourCycleMarkov;
25. MPS RFP;
26. PEPS root and EdgeMiddlePhysical;
27. PEPS FundamentalTheorem and TwoInjectiveComparison;
28. PEPS RegionBlock and TorusWindowPeeling;
29. PEPS VertexComplement and the remaining PEPS subareas; and
30. PiAlgebra, QCA, Spectral, and Wielandt.

Apart from the five PiAlgebra forwarders, no new candidate survived. Apparent
candidates were rejected because they were Blueprint-cited, had production
consumers, stated substantive source mathematics, belonged to advertised
counterexample modules, or were already owned by S2, S3, S5, D5, D7, or the
dated simplification campaigns of 2026-08-26 through 2026-08-30. In
particular, the left/right MPU families remain distinct source cuts, the
ParentHamiltonian and periodic low-reference statements remain load-bearing,
and the heavily swept MPDO/RFP and PEPS areas yielded no unrecorded deletion.

## Second-pass area disposition

The second pass divided the same development into thirty narrower slices,
emphasizing private helper closures, import ownership, definition and field
surfaces, suffix ladders, staged routes, mirrored examples, and Mathlib or
QICLean shadows. It covered Algebra; the MPS Core, Chain, Overlap,
Fundamental-Theorem, Canonical-Form, BNT, Structure, Irreducible, Periodic, MPU,
Parent-Hamiltonian, MPDO, and RFP layers; PEPS; QCA; PiAlgebra; Spectral; and
Wielandt.

Apart from `edgeGaugeOfCycleGauge` and the independently reconfirmed PiAlgebra
batch, no candidate survived. In particular, the second pass found that the
remaining private helpers lie in live proof closures, the remaining
SectorBNT suffixes encode source-facing hypotheses or paper-gap boundaries,
the MPU left/right statements are distinct source cuts, the RFP
counterexample closures advertise the witnesses they construct, and the
surviving Spectral and Wielandt statements are either upstream-owned already
or have production consumers. These dispositions agree with the focused
cleanup records from 2026-08-26 through 2026-08-30 and with the open and closed
cleanup-issue inventory.

## Third-pass area disposition

Areas 61--80 revisited the largest remaining MPDO and PEPS proof surfaces,
including carrier projections, coordinate transports, counterexample modules,
private helper closures, import ownership, and attribute-carrying declarations.
The only surviving candidate was the MPDO projection wrapper recorded above.
The other apparent leaves were Blueprint-exposed, belonged to advertised
counterexamples, were used through structure fields or simplification
attributes, or had already been settled by the focused cleanup campaign of
2026-08-26 through 2026-08-30.

Areas 81--90 covered, respectively: exact Algebra/Spectral/Wielandt upstream
shadows; the MPS Core/Chain/Overlap closure; Fundamental-Theorem,
Canonical-Form, and BNT projection wrappers and suffix ladders; private clones
in Structure/Irreducible/Periodic; MPU example and private duplication;
Parent-Hamiltonian unused fields and private clones; RFP/QCA zero-reference
closures and imports; remaining PiAlgebra forwards and imports; duplicate
fully qualified names and cross-file private redeclarations; and a
repository-wide attribute-carrying and unused-import batch.

No further candidate survived areas 81--90. Exact upstream shadows and private
clones had already been consolidated by the 2026-08-27 audits; live proof
closures accounted for the remaining private helpers; source-facing suffixes
were protected by their Blueprint or paper-gap role; the MPU left/right
families remained distinct source cuts; and the import candidates had already
been proved live by downstream consumers in the root-build import audit. The
fully-qualified-name census found no genuine collision. A larger pool of
name-level zero-reference `@[simp]` declarations remains suitable only for
future build-checked S2 batches: a read-only name search cannot decide whether
their attributes fire inside unnamed simplification calls.

## Repository census and limitations

The census at the time of the survey was 307,948 Lean lines, 913 duplicated
ten-line windows, 38 numbered-sequel files containing 17,396 lines, nine files
in the 900--1000-line warning band, 1,940 degenerate-case sites, and one
`sorry`. The Blueprint exposure census contained 6,917 unique direct Lean
references.

The surveys were discovery passes. The three deletion batches were
subsequently implemented in the same working tree, together with the glossary
migration; no issue was opened. The linter-bearing MPDO target build passed.
The combined change still requires the root build and the ordinary repository
checks prescribed by the project before it is merged.
