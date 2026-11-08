# Arbitrary-interaction block degeneracy

Baseline: main `6da5dd6c4` (including #10327). Issue: #7684.
Source: PGVWC07, `Papers/quant-ph_0608197/MPSarchive.tex`, Theorem 11
(`2blocks.1`), lines 1407–1422; standing block hypotheses at 1314–1330.

## Actual result

The interaction is any positive operator on L sites. It need not equal a
parent projector or have a prescribed local kernel. Its periodic Hamiltonian
is the existing `periodicInteractionHamiltonianES`, rather than a second
local-Hamiltonian model.

The general result begins with a simultaneous word span on the N−L
complementary sites. If the Hamiltonian annihilates a sum of the actual
periodic block vectors with nonzero coefficients, it annihilates every block
vector. A corresponding local result needs no positivity and permits zero
coefficients. At each cut the actual periodic state has active-block boundary
matrix equal to the complementary word. Compose the weighted joint boundary
map with the interaction, extend vanishing from the spanning word tuples by
Mathlib `LinearMap.ext_on_range`, then use `LinearMap.lsum_piSingle` to isolate
a block. QICLean `WeightedPositiveKernel.apply_sum_eq_zero_iff` supplies the
local annihilation equations from the positive Hamiltonian equation.

For `PGVWC07CanonicalFormData`, common C1 at L₀>0 and separated blocks derive
the span at exactly the source bound N≥3(b−1)(L₀+1)+L, b≥2. The actual canonical
weights give nonzero coefficients. The same direct-sum span at N makes the
block vectors linearly independent; the kernel dimension is therefore at
least b. No local annihilation, complementary-span or density premise is added
to this canonical specialization.

Two general existing lemmas, `periodicLocalInteractionES_zero` and
`periodicLocalInteractionES_isPositive`, move unchanged from the mixed-MPO
symmetry consumer to the defining periodic-interaction module. The old
consumer already imports that owner transitively. This avoids both a duplicate
positivity proof and an import from parent Hamiltonians into the symmetry layer.
Their names, signatures and existing Blueprint ownership are unchanged.

## Faithfulness boundary

Gauge-phase inequivalence is stronger than the source's literal inequality
of weighted finite-ring vectors. This is the existing distinction documented
by `PGVWC07CutRank.lean` and
`docs/paper-gaps/pgvwc07_direct_sum_input.tex`. The canonical result has a module
scope marker and a separately scoped Blueprint statement; it is not recorded
as an unrestricted formalization of Theorem 11. The note now explains the
same restriction for arbitrary interactions. Theorem 9, the varying-bond OBC
unique-ground-state theorem, is not addressed here.

## Verification

Hosted CI built every new module, and the blueprint entries and proofs now
carry `\leanok`. Source review independently checked the cyclic trace
orientation, pinned Mathlib linear-extension and lsum signatures, and the
positive-sum kernel API.
Source integrity, imports, width, pinned TeX formatting, ChkTeX, dependency
references, duplicate ownership and diff checks pass. New tactic usage is
recorded in the ledger.

The newly merged #10327 introduced unrelated theorem-role inconsistencies in
`ch35_aklv_energy_truncation.tex`. Draft #10359 repairs the registry and the two
supporting environments while conserving statements and declaration ownership.
This branch includes that isolated documentation prerequisite; the global role
check passes after it.
