# Collar and amplification scope restoration

Base: `b61f2bce4a934184b5acaa67ef640f7069c38ca2`.
Historical comparison: `ae0e697a` → `4c32f124` → the base above.

The four predicates in `TNLean/PEPS/AreaLaw/BoundaryTheorem.lean` and the conditional
helpers below originally accepted every real gap parameter. Replacing the old
state package by a one-dimensional ground-space premise removed degenerate
zero-gap inputs. Their hypotheses now state, separately:

- the state has norm one;
- the projector defect `H − E₀ I − Δ (I − |Ω⟩⟨Ω|)` is positive semidefinite;
- the state belongs to `ManyBody.groundSpace H E₀`.

This is the historical projector inequality and eigenvector condition, with the
unique canonical ground-space definition. No new gap predicate is introduced.
In particular, no positivity of Δ or uniqueness is added to a conditional helper.
The formulas, constants, thresholds and order of the state quantifiers are retained.

The four predicates are `SublinearCollarBound`, `SublinearCollarBoundAt`,
`AmplificationBound` and `AmplificationBoundAt`. The additional generic helpers
are in the following files:

- `AreaLaw/CollarInformation.lean`
- `AreaLaw/AmplificationCutClearance.lean`
- `Approximation/AngularWholeCellInformationFromCollar.lean`
- `Approximation/SquareCellConditionalInformation.lean`
- `Approximation/CoarseInformation.lean`
- `Approximation/CellConditionalInformation.lean`
- `AreaLaw/Scan/TemplateSourceEntropy.lean`
- `AreaLaw/Amplification/ConstraintWordTruncation.lean`
- `AreaLaw/Amplification/LatticeChannelSpatialOmission.lean`

Paths in this list are relative to `TNLean/PEPS/`. Positive-gap consumers use
`ManyBody.isGapped_and_groundSpace_eq_span_iff` or its projector-inequality
consequence at the boundary between these conditional statements and the physical
proof. The existing positive-gap state hypotheses and conclusions are retained. The rectangular
coordinate change reuses `projectorGap_toAreaLawHamiltonian` from the base patch.

`scripts/generic_gap_boundary_regression.lean` constructs a zero Hamiltonian on a
single two-level site, proves that its ground space is not the line through its
normalized zero configuration, and specializes the conditional collar and
amplification statements without a uniqueness hypothesis. The existing generic
CI selector includes this regression by filename and dependency closure.

This change does not assert an unconditional area law at zero or negative gap.
For negative Δ, the restored algebraic hypotheses need not make E₀ the lowest
energy: the canonical subspace at E₀ is its eigenspace, as in the historical
condition. No extra spectral-minimum assumption is added.
It does not validate the separate geometry, configuration or core gap batches.

The necessary call-site changes additionally cover `PhysicalCollarInformation`,
`AmplificationProof`, `AreaLawExplicitConstant`, `Scan/TemplateFinalInformation`,
`CoarseInformationFromGap`, `CellConditionalInformationFromGap`,
`AngularInformationFromCollar`, and `AngularSingleScaleReset`. In the last two,
the base patch's local conversion to a singleton ground space is no longer needed
when passing the existing projector inequality and membership to the generalized
cell helper. Other base-patch changes in those files remain intact.

`affected-sources.txt` records the direct-reference validation targets. It includes
one unchanged production consumer, `AngularInformationFromGap`, in addition to
the eighteen scope-restoration production files and the preparatory rectangular
specialization fix.

A separate preparatory commit, `d8eb12b0c`, repairs
`AreaLaw/RectangularSpecialization.lean`. At the base, its square-state consumer
passed the restored projector inequality where the positive-gap rectangular
bound expected a canonical spectral gap. The repair uses the existing strictly
positive Δ hypothesis and the canonical equivalence, retaining the entire
rectangular and square conclusion. It is separate so integration can omit it if
another base-validation task supplies the same fix.

The separate preparatory commit `1a44b4fe5` explicitly supplies the already chosen
`angularScale` and `angularThreshold` in the final angular existence wrapper.
This fixes its base-patch elaboration failure without changing either constant.

Validation on the final source snapshot:

- `lake build` on the twenty modules in `affected-sources.txt`: passed, 10.80 seconds.
- Strict elaboration of those twenty sources and the regression: all 21 passed,
  33.57 seconds with three workers. Flags and per-file results are in `validation.json`.
- Kernel dependency inspection of eighteen central declarations: only
  `propext`, `Classical.choice`, and `Quot.sound`.

Earlier iterations failed and are not counted as successes: the initial four-owner
attempt lacked the complex order scope (45.21 seconds); the successful corrected
four-target slice took 15.50 seconds. A targeted dependency preparation run took
524.27 seconds and exposed wrapper issues; the first nineteen-target consumer run
took 268.00 seconds and exposed the two separately committed base consumers.
During those builds, work continued on consumer adaptation, the persistent
regression, source comparison, and policy checks. The workspace initially had
9.6 GiB free and retained the Mathlib cache; the physical scanner and replica
transport dependencies were not all warm. No full-library build was requested.

The full reverse import closure, combined A/B/core-gap snapshot, PDF/web rendering,
and remote full CI were not run here. This is bounded source validation of the
listed production consumers and the persistent boundary regression.

The persistent zero-gap fixture directly exercises the four generic collar and
amplification predicates, with its imports tied to `CollarInformation` and
`AmplificationCutClearance`. It is not a zero-gap regression for every restored
owner. In particular it does not establish range-square, rectangular-coordinate
transport, zero-floor, box-entropy, or ThreeWaySplitting boundary coverage.
Those owners need their own direct boundary fixtures; passing the consumer
builds is not a substitute for those examples.

The rectangular Blueprint entry additionally tags the existing arbitrary-Δ
`projectorGap_toAreaLawHamiltonian` theorem. The glossary states the actual
`BondLayer` input as `β → Finset ι`; the general set-valued geometry interface
remains separate.

Final document verification passed: full Blueprint/source synchronization with
duplicate-tag checking (94.67 seconds), declaration resolution for the newly
referenced coordinate-transport theorem, Blueprint roles, reader-facing prose,
forbidden-token scanning, and whitespace checks. Import layers, generated
aggregators and the pass-through ratchet also passed. CI selection reports
19 changed production sources and the new regression script; the local strict
run additionally checked the unchanged direct consumer.
