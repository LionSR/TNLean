# Literal physical interleaved iteration

`exists_physical_dg_interleaved_interval_iterates` constructs the actual
physical family and common reference before every input space and radius,
then proves convergence of its literal current-space image and collective
trim. The initial space has dimension at most s and is (1-a)-viable for the
actual clipped target. The proof does not replace this sequence by operator
words with only one final trim, nor by independently selected viable spaces.

The source is ALVV, arXiv:1602.08828v2, Figure fig:merge-prime, lines 1668–1670,
and the induction in lines 1797–1805. The current-space assignment and larger
integer number of rounds are local corrections recorded in
[the approximation parameter note](../paper-gaps/alvv16_approximation_parameters.tex).
The interval must have length greater than 4ell; quantitative dependence
retains g=min(gamma,1). The initial successful sample is still a separate
mathematical input. No adaptive probability or running time is asserted.

## Actual construction and bounds

Use the calibrated physical count D and s, with

    a=3/(32D^12 s^5), Delta=1/(200000D^12), tau=a^2/2^20,
    k=clog_D(D^2 s), e(0)=1-a,
    e(j+1)=Delta e(j)/(1-e(j)+Delta e(j))+a/16.

The same actual clipped target, family F, common reference and positive
threshold xi are used throughout. At each j the actual iterate is e(j)-viable
for that target, with 0<=e(j)<1. The scalar stopping theorem pays the additive
trim loss, proves geometric growth until success reaches sqrt(Delta), and
reserves one final exit round. At k the actual space is 1/200-viable for the
clipped target and 3/200-viable for the original full ground space.

Dimension is at most N^k dim(S0)<=(D^k)^2 s<=D^6 s^3. Its actual final
collective trim records at most that many spanning vectors, each with
xi^2 times its internal-cut Schmidt rank at most the same count. This is a
bound on recorded vectors, not every vector of their span. The whole exterior
reference rank remains Dref^2. No desired post-trim viability, supplied
numerical filter condition or stopping assumption appears in this physical
auxiliary; only the legitimate incoming-space viability is assumed.

## Verification

The exact immutable provider was TNLean
478e8a08f8d97cec4064070a29170a0953362d3e with its own QICLean dependency
9578336a5123a76001a1218e271132091c828de2, following its full ordinary build.
The only private dependency overrides were the two newly checked scalar
modules in QICLean commit 731e9c2ffec00be39fef8fe6d68072ea7ccbba72.

The actual-name strict module check passed in 11.996 seconds with 739 protected
source/object pairs. The imported public-declaration inspection passed in
8.101 seconds with 740 pairs and only propext, Classical.choice and Quot.sound.
Its temporary source was deleted. Selected source/object and root-input
hashes, the unchanged Mathlib artifact and changed-importer provenance were
guarded. No provider or dependency artifact was modified or copied.

Blueprint/source coverage with read-only pinned companion sources, roles,
reader-facing prose, generated imports, forbidden-token and whitespace checks
passed. The tactic scan found no new repetition requiring promotion. Ordinary
combined builds and compiled blueprint checking remain integration gates.
