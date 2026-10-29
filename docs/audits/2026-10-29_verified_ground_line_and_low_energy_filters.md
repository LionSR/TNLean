# Verified ground-line sampling and physical filter parameters

The checked mathematical revision is TNLean
`5cec1958d1a56d1f20cfdbd1161ef946a410f41c`, with QICLean
`cc9e79084d26336c95e843c13928a3963a9debb2`. It extends the previously
verified common construction at `22519023a4`. The changes remain on local
branches; no publication or merge has occurred. The primary worktree's
unrelated work was preserved.

## One sampled family before every ground representative

At a specified energy E0, the existence of one unit ground vector with
positive lower gap suffices to choose a sample before every normalized vector
at that energy. The positive gap identifies all of these vectors with scalar
multiples of the internally chosen reference; unit normalization gives equal
rank-one projections. Each cut's left and right factors are also chosen before
every normalized ground vector and every viable input family.

The same actual sample supplies both norm approximations, simultaneous letter
counts and all spatial ranks. With r = ell q^(2u), there are at most r factors
at a cut, and their internal ranks are at most r. They take a half-viable family
of size s and bond b to error delta, size at most r s and bond at most
r max(1,b). No successful sample, cut decomposition or projection-equality
hypothesis is supplied.

The theorem still specifies E0 in its word length and sample budget. The
published Methods explicitly permits omission of an overall nonzero scalar
after output normalization; that scalar is not the remaining obstruction.
Selecting word lengths and relative-error sample budgets without exact energy
is a further statement. The source theorem has an energy-dependent complexity
exponent, rather than an unprinted bounded-energy hypothesis. The independent
Gaussian energy-mesh construction already supplies the earlier conservative
successive polynomial viable families. The original sampler is not assigned
an energy-independent degree. These distinctions are recorded in
`docs/paper-gaps/lvv13_sampling_ground_energy.tex`.

## The filter of the actual clipped Hamiltonian

For the original positive-contraction nearest-neighbour chain, the two clipped
exteriors and s-2 retained interactions give a supported shorter window with
exactly the original central cut. The actual clipped Hamiltonian B is positive
and has norm at most 2t+s. Its actual unit ground vector phi, ground energy E,
projector gap at least 9g/10 and phase-aligned approximation to the original
unit ground vector are derived from the physical data.

For every degree ell, the actual Chebyshev polynomial p satisfies p(E)=1,
fixes phi, and has norm error at most
2 exp(-2 ell sqrt((9g/10)/(2t+s))). At the same cut its rank is at most
[q(ell+1)]^[32(floor(ell/s)+floor(sqrt(ell))+1)]. The norm ceiling, spatial
decomposition and projector gap are proved, rather than input hypotheses.

The statement retains s >= 6 and the source-shaped sufficient threshold
t >= (1024/g)(E0/g+1). It must not be applied below that threshold. The
stronger logarithmic robustness estimate available from the spectral-cluster
inequality is a next step needed for the favorable entropy parameters. A
fixed-vector entropy theorem for phi does not by itself bound the original
ground vector through a sequence of changing truncations.

## Interior low-energy parameters

At fixed density bandwidth eta_LD > 0, one constant A precedes the chain,
local dimension, buffer coefficient mu, target bandwidth and Hamiltonian.
For w = mu/(3 log L), g = min(w,1), u = 1+log q+log(1/g) and
ell = ceil(A u^2/g), the actual interior family has at most D^2 terms,
D = (q ell^2)^(20 ell), and satisfies the strict clipped-filter tradeoff
D^12 Delta < 10^(-5). Its explicit logarithmic count retains the cap g.
The proof compares the actual count with the larger auxiliary exponent
22 ell and uses the positive physical contraction.

The actual regional minima, ground data, prescribed threshold, norm bound and
original-window family are retained. Its output error is
2 (Delta/[1-2(delta+1/200)]^2 + 1/200), with delta >= 0 and
2(delta+1/200) < 1. This is distinct from the clipped-filter parameter.
The additive contribution is already 1/100, so a final original-window error
of 1/100 requires retuning the comparison precision. No such final error is
claimed. Interior geometry remains explicit; the full low-density theorem,
short and boundary region construction, and sampled tree remain separate.

## Verification and source provenance

At the exact mathematical revision above, all of the following passed:

- Ordinary full TNLean library build: 15,086 jobs.
- Strict checks of all 10 changed production files, with standard linters,
  warnings as errors and the unchanged 50-second limit.
- Five existing regression files selected by the repository's check script.
- Imported foundation audit of 13 public declarations from changed sources,
  using only `propext`, `Classical.choice` and `Quot.sound`.
- Blueprint source synchronization and compiled declaration checks.
- Added-prose, forbidden-token and compilation-time checks.

No job in this full build reached the 25-second warning threshold, and no
Mathlib source was compiled. The existing prebuilt Mathlib cache was used;
normal builds and cache operations ran under the repository lock. Private
contributions used read-only provider objects and private outputs, with no
cache copies from modified worktrees. No permanent Lean fixture was added.

The existing QICLean scalar rank-one identity was made public with its
statement and proof unchanged, and replaces the private TNLean copy and the
third repeated calculation. That companion change, and the later citation
correction, separately passed full 10,348-job builds, strict checks, imported
foundation audits and compiled blueprint checks. The corrected source
references point to the accessible author PDF's published Methods, Proposition 1,
page 6. They do not attribute an unverified passage to the separate supplement.
The source report is `/tmp/lvv_specified_energy_source_analysis.txt`.

The local complete record is `/tmp/tnlean-ground-line-filters-gates.json`;
companion records are `/tmp/qiclean-rank-one-scalar-gates.json` and
`/tmp/qiclean-source-citations-gates.json`. Subsequent interior-chapter
completion marks change documentation only. Source synchronization and
compiled declaration checks are repeated for those marks; the Lean sources
and build inputs remain byte-identical to the checked revision.

The goal remains active. The next bounded tasks are logarithmic-threshold
AKLV robustness, a sampler whose budgets precede the exact energy within a
known bracket, and the source-scale count and arbitrary-region ALVV family.
These are followed by the respective favorable-parameter, low-density and
sampled-tree arguments. The stated partial results are not counted as those
remaining constructions or as a running-time theorem.
