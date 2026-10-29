# A basis for the actual locally truncated Gaussian filters

The contribution transfers two preserved proofs at TNLean
`1659116509dc8cec5d4a2aec8ddd131cc88da31d`: LowEnergyObservableDecay and
LowEnergyBasisTruncatedUniform. It follows the full-Hamiltonian checkpoint
`900f39ace4fa8b60177fd0ac8a4482f027801b61` and shared QICLean
ApproximateDiagonalization proof source `1690919b1c9e01ceab1daaef7f01937110b48fb9`
(documentation successor `4a838eec6ab738edaa50190f34c5dc6d5eb78345`).
The common providers remained read-only at TNLean 7f87bdc8f1b2354be4950ad515dedda7ee9bec96
and QICLean ec3434f7d6fbdfc5318dc55934feb9532e239b81. This source-only
checkpoint changes no dependency pin or package checkout.

## Statement and proof review

The actual local Hamiltonian is the sum of the original terms with labels in
s_i, and M_i is the Gaussian filter of h_i under that Hamiltonian. It is not
replaced by filtering under the full Hamiltonian. Hermiticity, support in K_i,
and norm at most ||h_i|| are derived from the actual filter. The geometric
inputs say that K_i contains the original support X_i and every support of a
retained term, with displayed diameter and cardinality bounds.

The separate-observable estimate applies a second filter under the original
Hamiltonian. It assumes neither a gap nor a ground projector for a truncated
Hamiltonian. The original generator range and cardinality determine the
velocity. The larger observable cardinality enters the prefactor; its diameter
enters the conversion from support separation to anchor distance. The existing
norm, leakage, locality and scalar time-window estimates prove the actual
compressed-commutator bound. Disconnected components give zero mutual kernel.

The weighted recursive basis theorem is then applied to those actual compressed
operators. The weights remain the original ||h_i||, so the original sitewise
interaction budget suffices. No new budget for the enlarged observables is
assumed. The basis, spectral refinement, anchor list and their bounds are
constructed; no supplied basis, separated spectrum, condition-number estimate
or assumed commutator estimate is used.

The result has rate gamma/2^n and the explicit coefficient
sqrt(n^3 C(1+2n^3)^n). Uniformity in the number of sites requires fixed ground
space dimension, original local parameters, gap, polynomial sphere-growth
constants, and localization support bounds. It does not assert uniformity
along a growing localization radius or the source's sharper prefactor. The
separate blueprint statement includes these restrictions. The physical note
cites the QIC-owned cross-term correction by its published URL.

The mathematical tree-counterexample note is unchanged from the parent. No
partial certificate or full tree-family theorem is added, and no kernel-verified
counterexample is claimed.

## Imported source dependencies

GraphDegreeTail and GaussianTruncationDecayBound are immutable checked parents
from the separate physical hierarchy contribution. They were read through
/tmp/tnlean-hastings-physical-reconcile-20261029/overrides.json, whose SHA256 is
d9d376f97a4743eea8ed236647b43afcac2be9819ce07e29aa51f19fc444a48f. Their actual
source and object hashes are included in the selected-import guard below.
They are not duplicated in this patch. Other frozen basis parents use their
actual checked private objects in place, without copies.

The existing TranslationSupercellTruncated definition of truncatedTerm is
reused unchanged. Support preservation in GaussianFilteredTruncation is the
direct convex-integral argument for supported conjugations. Neither new proof
calls ProductForm, even though a broad existing import transitively includes
that module. No ProductForm assertion enters a hypothesis or proof step here.

## Verification

Both actual named modules pass private strict checks with disabled implicit
variables, Mathlib standard linters and warnings as errors. All three public
theorems were imported and inspected; only propext, Classical.choice and
Quot.sound occur. All 126 selected imported source/object pairs, including
frozen generic and physical parents, were hashed before and after checks.
The exact new-chapter tags equal the audited declaration names.

Production wall times were 30.80 and 29.16 seconds; imported inspection took
44.60 seconds under continuing host contention. These are retained as evidence,
not quiet benchmarks. Ordinary/full-library checks, compiled blueprint checks
and the mandatory quiet changed-module timing gate remain integration tasks.
No timing-only repeat or increased threshold was used.

Source blueprint synchronization, added-prose checks and whitespace checks pass.
No ordinary build was started, no Mathlib source was built, no Lake environment
was initialized, and no shared source, cache or artifact was mutated or copied.
Only temporary output objects and read-only artifact links were used.

Evidence: /tmp/tnlean-hastings-truncated-basis-private-checks.log,
/tmp/tnlean-hastings-truncated-basis-foundation-audit.log,
/tmp/tnlean-hastings-truncated-basis-provider-guard.json, and
/tmp/tnlean-hastings-truncated-basis-blueprint-sync.json.
The new chapter follows ch35_hastings_uniform_ground_basis.

## Checked source hashes

- `TNLean/Lattice/LowEnergyBasisTruncatedUniform.lean`: `6e9d860bd8f7ff754c8bed559bd21b5639bb7392e93285435eb01601e02429d3`
- `TNLean/Lattice/LowEnergyObservableDecay.lean`: `5200ac888014eb17039d0cbc00c54287ed516d3320b96dfa984c6220453b7245`
