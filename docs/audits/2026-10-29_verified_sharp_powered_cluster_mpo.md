# Verified sharp AKLV approximation, regional gap, powered families and cluster MPOs

The mathematical revision is TNLean `28e38efedb8621056c907c8ad20e1edd24003a20`, with exact QICLean
pin `ec3434f7d6fbdfc5318dc55934feb9532e239b81`. All contributions remain local. The three broader
area-law programmes are not complete.

## Mathematical conclusions

The AKLV development constructs one actual sequence of changing-target filtered
states, then accuracy-dependent same-cut approximants including short-chain
and boundary alternatives. The actual original square-root degree is retained.
With u=1+log q+log(1/g) and z=log(2048(L+1)/ε²), a universal constant C gives

    log D ≤ C [u³/g + (z³/g)^(1/4) (u+log(z+1))].

The actual Schmidt tails at all cuts feed the normalized ordered product of
leading regional spectral projections, which is a global MPS at distance at
most ε. No independent MPS-existence theorem is used. The actual first excited
energy remains specified; local dimension at least two and gap at most one
follow from the physical hypotheses independently of a fitting window.
The sharper entropy summation remains a further task.

For the actual regional frustration-free truncation, the nonzero spectrum lies
above γ/[3(4+γ)] whenever the original nonzero spectrum lies above γ>0.
The proof uses the original detectability product on the whole common-kernel
complement. It imposes neither uniqueness nor an upper bound on γ. The
printed additive rank constant remains false; the corrected bound q²+3 still
requires a formal proof. Its exact eight-qubit counterexample remains recorded
in `docs/paper-gaps/alvv16_frustration_free_truncation_rank.tex`.

For the degenerate-space construction, collective trimming and adjacent merging
now use actual interval tensor coordinates with the entire exterior retained.
The common physical reference is chosen before all intervals and viable spaces.
The two-boundary internal rank bound is the square of its global cut bound.
Adjacent child spaces preserve one possibly entangled global target; their
viability errors add and their dimensions multiply.

Actual ordered words in the same improving operator family supply every power
before every viable input. Their suppression is Δ₀^k and their cardinality is
at most D₀^(2k). The logarithmic power choice gives output dimension at most
D₀⁶s³. Its explicit sampling-scale error estimate cancels the powers of D₀.
This is not yet the sampled-node probability theorem or the tree induction.

The corrected cluster expansion is spatially factored for actual nearest-neighbour
interactions. Its operator Schmidt rank is at most r²q^r at every cut. Actual
site-dependent MPO tensors of that uniform bond dimension represent the same
truncated operator. For Hermitian interactions of norm at most one, H≥λI,
β≥0 and b=2(exp β−1)≤1, this same MPO has energy-normalized error at most
exp(N²b^r)−1. The cutoff counts interaction labels. Neither an assumed tensor
decomposition nor a supplied rank bound occurs in the physical theorem.
The false printed cluster estimate is not asserted.

The upstream LVV sampled-projector probability theorem is retained: the actual
two-level product-uniform law succeeds with probability at least 1−1/(2L³),
hence at least 1−1/L³, for the explicit counts. Its ground energy is fixed
before sampling. Selecting the energy bracket and proving a full running-time
bound remain separate tasks.

## Verification

TNLean passed the full 15185-job build. Strict checks: 44 changed source file(s), 5 test file(s).
The imported foundation audit covers 163 public declarations;
only propext, Classical.choice and Quot.sound occur. Source synchronization,
compiled blueprint declaration checks, prose, proof integrity, changed-module
timings, paper-gap registration and the tactic-pattern scan all passed.

QICLean passed the full 10376-job build. Strict checks: 15 changed source file(s), 2 test file(s).
Its imported foundation audit covers 51 public declarations,
with the same standard foundations. Source synchronization, compiled blueprint
declaration checks, prose, integrity and changed-module timings all passed.

The existing 25-second warning and 50-second failure thresholds were retained.
The full build contains timing warnings for changed physical modules; no changed
module reached the failure threshold. Detailed timings and logs are retained in
`/tmp/tnlean-powered-sharp-mpo-gates.json` and
`/tmp/qiclean-powered-sharp-mpo-gates.json`.

The updated AKLV source note renders as four pages without LaTeX warnings.
All four pages were visually inspected. Its margins were adjusted to keep
the complete argument legible and avoid a nearly empty final page.

All five TNLean companion pin entries and the actual package checkout agree.
Mathlib was not rebuilt from source. Its cached artifact hash is unchanged,
no modified-worktree artifacts were copied, and no permanent Lean test fixture
was added. Build and pin mutations used TNLean's repository lock. The primary
checkout and its preservation records were untouched.

The remaining tasks include the sharp AKLV entropy conclusion, the corrected
regional rank theorem, soft truncation with independent order and scale and
polynomial MPO bounds, sampled nodes and the binary tree, the low-density
induction, and the remaining Hastings 2006 hierarchy and basis constructions.
