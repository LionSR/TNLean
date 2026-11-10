# Verified physical sampling, low-energy filtering and robustness

The common mathematical snapshot is TNLean
`22519023a42896c04763ad0497970964481daaff`, with companion revision
`637184a66a8c2215adec3bd28fc1a872ca382836`. The preceding source contribution is
`cec1f26381`; the later refactor reuses one companion spectral-coordinate lemma
in seven proofs. The Lean and Mathlib versions remain v4.35.0-rc3.
All changes remain on local branches. The primary worktree and other sessions'
unrelated drafts were preserved.

## The mathematical conclusions

The LVV power construction now returns one actual sample with both norm
approximations, every letter-count bound and the operator Schmidt-rank bound
at every cut. The norm and rank conclusions concern the same operator. With
sample count ell and count threshold u, its rank is at most ell q^(2u).
At a specified ground energy, the same operator yields cut factors chosen
before every input viable family; these improve half-viability to prescribed
error, with cardinality and internal MPS bonds derived from the same sample.
The input ground vector still precedes sampling in this statement.

The sample count explicitly retains exp(2 E0 log(Q)/Delta). An estimate uniform
in unknown ground energy or with energy-independent polynomial degree is not
asserted. The independently checked Gaussian energy-mesh construction remains
the route used by the existing successive polynomial viable families. The new
power sampler is not substituted for that construction without an energy-selection
argument. The source-version and normalization corrections remain visible in
`docs/paper-gaps/lvv13_sampling_ground_energy.tex` and the witness-normalization
note. A representative-independent sampled statement is a separate next step.

For Hastings' area law, the graph estimate gives numerical prefactor four and
arbitrary finite second support. Writing c_R = 2(R+1)2^(2R+1) exp(2R), the
velocity V = 40 c_R J is independent of the gap and the length is
Xi = max(2 V / Delta, 80). At this constructed admissible pair the positive
semidefinite factorization has error at most K Xi^3 exp(-l/(6 Xi)). The actual
entropy of every prefix is at most
c_0 (6 Xi) log(6 Xi) log(q) 2^((6 Xi) log(q)), with c_0 depending only on R.
The factor of two in the doubling exponent at the smaller fixed length is
retained. The statement uses the intended length convention and the semidefinite
positivity justified by the source's note added; it does not mark the literal
strictly positive body formulation as proved. See
`docs/paper-gaps/hastings07_lemma1_decay_length.tex`.

The AKLV construction uses the original positive-contraction nearest-neighbour
terms. It constructs genuine regional minima and a normalized ground energy
E0 in [0,6], then clips the two actual enlarged exterior sums. For windows
with at least six interactions and the actual original first excited gap g,
t >= (1024/g)(E0/g+1) gives an actual phase-aligned unit truncated ground
vector, truncated gap at least 9g/10, and squared error at most exp(-t/16)/100.
The original upper bound g <= 1 is derived from the physical chain. No
truncated vector, spectral cluster, residual or gap cap is supplied as input.
The original bounded-term source context is retained; an arbitrary-exterior
extension is not presented as part of this theorem. The support and middle
energy-shift corrections, and the remaining finite-window restriction, are
recorded in `docs/paper-gaps/aklv13_two_block_robustness.tex`.

For ALVV low-energy targets, one actual clipped Hamiltonian supplies both
buffered comparisons and a common polynomial family with at most D^2 terms,
D = (q ell^2)^(20 ell). The family, actual degree-ell^2 polynomial and tensor
factors precede the viable input subspace. The nested clipped targets have
loss Delta/(1-delta)^2. For the original windows E0+eta and E0+eta-3w,
composing both spectral comparisons gives loss
2 (Delta/[1-2(delta+epsilon)]^2 + epsilon), when delta >= 0 and
2(delta+epsilon) < 1. The result retains interior geometry and 3w < eta.
It neither assumes a gap between the two low-energy cutoffs nor identifies
the clipped ground energy with the original one. See
`docs/paper-gaps/alvv16_low_energy_family_buffers.tex`.

## Verification

The exact mathematical snapshot passed all of the following:

- Ordinary full TNLean library build: 15,081 jobs.
- Strict checks of all 18 changed production source files, with package options,
  standard linters, warnings as errors and a 50-second limit.
- The five existing regression files selected by the repository's check script.
- A manual audit through the actual root import of 43 public declarations from
  changed production files. Only `propext`, `Classical.choice` and `Quot.sound`
  occur; no additional axiom or unchecked placeholder occurs.
- Blueprint source synchronization and compiled declaration checks.
- Added reader-facing prose, forbidden-token and compilation-time checks.

The full build compiled no Mathlib source. Its only job above the 25-second
warning threshold was `ActualClippedPolynomialFamily` at 26 seconds; no job
reached the 50-second failure threshold. The ordinary build of the new physical
low-energy module took 18 seconds. Private direct checks had varied between
roughly 25 and 44 seconds and are not used as substitutes for this combined check.

The build and cache operations used the repository lock. The common worktree
had been seeded according to the exact hot-main protocol; the dependency
advances used immutable Git source revisions and the existing prebuilt Mathlib
cache. No build cache was copied from a modified worktree. The companion power
sampler and Euclidean helper separately passed ordinary full builds of 10,347
and 10,348 jobs, strict source checks, imported foundation audits and compiled
blueprint checks. Their completion record is in QICLean's
`docs/audits/2026-10-29_physical_power_sampling_and_eigenvectors.md`.

The new Hastings exposition was rendered separately and inspected visually;
its equations have no overfull boxes. References to other chapters are outside
that isolated rendering. The complete declaration check, rather than this
visual check, verifies the book's declaration references.

Local verification records are `/tmp/tnlean-physical-constructions-gates.json`,
`/tmp/qiclean-physical-sampling-gates.json`, and
`/tmp/qiclean-euclidean-eigenvector-gates.json`. A direct coordinate check that
started before its new dependency object existed failed for that reason; after
the ordinary dependency target finished, the unchanged proof passed. The final
combined source and strict checks passed. No failed attempt is counted as
verification evidence.

The subsequent completion marks in the low-energy chapter change documentation
only. Source synchronization and compiled declaration checks are repeated for
those marks; the Lean sources and dependency inputs are unchanged.

## Remaining mathematical work

The goal remains active. The next bounded steps are the sampled construction
with the family before every normalized ground representative, the actual
clipped-Hamiltonian Chebyshev filter for AKLV, and the ALVV interior source
parameter substitution with the required D^12 Delta bound. Further work includes
AKLV's favorable parameters and moving-ground-state approximation sequence,
ALVV's short and boundary regions, low-density induction, corrected soft
truncation and sampled tree, and the remaining source-level quantitative and
algorithmic comparisons. No one of the area laws or single-vector approximation
results is counted as that tree or as a running-time theorem.
