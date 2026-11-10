# Preservation of the actual LVV sampled-projector probability theorem

## Authoritative upstream result

The source is `origin/main` revision
`efa3070d3060aa49df30530b9eda1b6484c668f2`, containing
`TNLean/MPS/AreaLaw/ViableSet/SampledProjector.lean` from the upstream
sampled-projector development. Its original complete-file SHA-256 is
`0715c025f88d494b3ad97a713b7bba8cb7a0394d9fe6bd87956a64d51b9ad4b9`.
The restored mathematical declarations, instance proofs and theorem proofs
are byte-identical to that upstream file, from its first namespace-level
opening onward. Only the module documentation changes, to identify the
published correction and the existing consolidated ground-energy note.

The exact upstream module first passed a strict private check unchanged
in 10.58 seconds. The reconciled production file passed in 10.38 seconds,
within the changed-module timing policy; no splitting or replacement
family of declarations was needed.

## Probability space and theorem

For $n=L\ge1$, the actual sampling space is
$\{0,\ldots,n-1\}^{\ell\times m}$ with the product-uniform measure.
Each of the $\ell$ words has $m$ independent uniform letters, and all the
words are independent. The last letter is the identity padding letter of
the exact power expansion.
For fixed physical ground data, put
$C=(1-E_0/n)^{-1}$, $A=(C(I-H/n))^m$ and
$K=C^m\ell^{-1}\sum_jP_{I_j}$.
The ground-energy range $0\le E_0\le n-1$ is derived from the original
positive contractions and unit ground vector; it is not supplied as an
extra hypothesis.

For any $\eta>0$, set $R=C^m+1$ and choose
$\ell=\lceil(2R^2+2R\eta/3)\eta^{-2}\log(8q^n n^3)\rceil+1$ and
$\kappa=\lceil2m/n+2\log(4\ell n^4)\rceil$.
`one_sub_le_measureReal_sampledProjector` proves that the actual joint
success event has probability at least $1-1/(2n^3)$.
`one_sub_inv_pow_three_le_measureReal_sampledProjector` explicitly derives
the source's lower bound $1-1/n^3$ under the same sampling law.
The event is $\|K-A\|<\eta$ together with at most $\kappa$ occurrences
of each letter in every word. The matrix-norm failure and the all-word
multiplicity failure are each bounded by $1/(4n^3)$, and are combined under
that same measure.

The explicit word count and multiplicity bound are production definitions.
`exists_sampledProjector` derives an actual good family at those counts,
the ground-projector approximation at the stated logarithmic power, and
operator-Schmidt rank at most $q^{2\kappa}$ for every sampled word at every
internal cut. The probability theorem is proved first; existence is its
consequence, rather than an input or a substitute for the measure estimate.

## Source faithfulness and reconciliation

The original LVV source is arXiv:1307.5143v1, `algo53.tex`, Definition
`d:sagsp`, Theorem `t:mcb` and Corollary `c:agsp`, lines 606–649.
The local source `References/1307.5143/algo53.tex` has SHA-256
`bd0f43bdd66d5cdacc7d7e7eaec34c98a6cf7a2fbd65116af8a9f1391a41fbe0`.
The source sampling law, normalization and high success probability are
preserved. The explicit finite count retains the ground-energy dependence
through $C^m$. It does not assert the preprint's false energy-independent
polynomial sample count at extensive ground energy.

The published Nature Physics Methods, Proposition 1 and its preceding
normalization discussion, author PDF page 6, retain that energy dependence.
The restored module now cites the existing note
`docs/paper-gaps/lvv13_sampling_ground_energy.tex`, which records the
published correction and the unknown-energy selection boundary. The obsolete
separate runtime note is not restored. The bibliography entry identifies the
published Methods, without attributing the argument to a separate supplement.

The existing `IntervalPowerSampling.lean` remains unchanged. It chooses one
scalar-free sample from a supplied width-one energy bracket, before the
bracketed ground data, and does not prove this high-probability event.
Conversely the restored fixed-ground-data probability theorem does not
choose unknown-energy trials or supply a valid acceptance and termination
argument. Neither result subsumes that missing selection argument, and
neither proves an energy-independent sampling runtime.

The restored blueprint chapter reuses the already existing matrix Bernstein
entry and its declaration tag, rather than duplicate that theorem and label.
It preserves the sampled operator, probability, multiplicity and rank entries,
and cites the consolidated published-version note.

## Verification

Private checks used fully verified TN mathematical snapshot
`da3ab8dcc9f9149cbbdcc56cae817ff783825f24`, documentation-only successor
`f93bc77b3dddcc292125eea18b96af153225251b`, with exact QIC package
`4276de2eeb5c4122f4482ef5e4fa205be5b71bd9`.
The selected import roots had zero pending dependencies. A fresh guard
covered 188 imported TN/QIC source and ordinary-object pairs. The two TN
imports, `PowerProjector` and `MatrixL2Contraction`, are byte-identical to
the authoritative upstream revision.

The actual production module passed with both automatic implicit options
disabled, strict Mathlib standard linters and warnings as errors.
An imported foundation audit inspected all 25 public definitions, lemmas
and theorems and found only `propext`, `Classical.choice`, and `Quot.sound`
(or a subset). The manual audit lives under the system temporary directory;
no repository fixture is introduced.

Provider sources and artifacts remained read-only. Only new temporary
private objects were written; no artifact was copied, no Mathlib source
was built and no ordinary build was queued. Ordinary build and compiled
blueprint verification remain integration gates. The chapter belongs after
`ch35_lvv_power_projector.tex`; generated aggregators and registration are
excluded from this contribution.

### Preserved source hashes

- Reconciled production source: `850f3db637cef637ff7edfee85f736efc599a5cfd95d3a1bd33e9bd698a9c3e6`.
- Byte-identical mathematical declaration/proof suffix: `1a3acbbdfcacf65e1a08c32c8f204ed5012aed7673c28c88a5ed016085f4b486`.
