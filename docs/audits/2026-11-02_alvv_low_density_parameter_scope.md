# Fixed bandwidth in the ALVV low-density parameters

The source is ALVV, arXiv:1602.08828v2, local source
`References/1602.08828/local_alg_arxiv_v2.tex`, SHA256
`19d37facb8bf8da6ea5555cd7185c054d251ad4a06c2f44fcb92593235ad6b92`.
Assumption (LD), lines 281–284, fixes a positive constant energy bandwidth.
The improving-family theorem, line 1027, ranges over narrower cutoffs.
The entropy theorem, lines 1096–1102, displays the dependence on the
interior margin but no separate bandwidth factor. The bootstrap proof,
line 1112, writes its envelope coefficient as C(d,n), without an explicit
bandwidth argument.

Under the usual fixed-parameter reading of an asymptotic estimate, hidden
constants may depend on parameters declared fixed before the asymptotic
variable. A statement with one coefficient uniform over all positive
bandwidths is stronger. The cited passage does not expressly distinguish
these readings. The parameter theorem therefore keeps the order

    for every etaLD>0, there exists A(etaLD),
    before all chain lengths, Hamiltonians, numerical count bases and margins.

This is the order used by the finite scalar construction. It does not add
an upper bound on the bandwidth, assume a spectral gap or introduce a
projector premise. Its coefficient is uniform in the physical data and
narrower width once the bandwidth is fixed.

No source error or unfaithful-proof marker follows merely from retaining
that dependence. A later identification with the full entropy theorem
must examine the exact final quantifiers and comparable uses of asymptotic
notation in the source. At this stage only the fixed-bandwidth parameter
auxiliary is stated; neither the low-density area law nor a stronger
bandwidth-uniform conclusion is marked complete.

The local dimension is also declared constant at source line 267, while
its logarithmic dependence is kept explicit in the later bounds. Thus a
fixed-parameter reading should not silently erase quantitative dependence
that the source explicitly displays. The present auxiliary retains both
the displayed count-base dependence and its fixed-bandwidth coefficient.

## Verified scalar auxiliary

The new parameter theorem is checked against fully verified TNLean
`5fc343a57d70eefd2902780107851ab9b0753a82` and its own QICLean package
`ba01733099b5a18bed5c9bfb62f95f175b4c9b57`. One constant A(etaLD), selected
before every count base and width, simultaneously gives ell>=19+etaLD,
the residual comparison budget and the count-suppression estimate at the
same actual natural degree. There is no supplied physical projector,
residual or gap premise. The actual physical family remains a subsequent
construction using the shared independent-cutoff regional theorem.

Actual-name strict private checking passed in 7.476 seconds. An imported
inspection of the public theorem passed in 4.776 seconds and reports only
`propext`, `Classical.choice` and `Quot.sound`. Selected source/object
hashes, both package configurations and the warmed Mathlib sentinel were
guarded before and after compilation. All new outputs remain under
`/tmp/tnlean-fixed-bandwidth-ld-20261102`. The temporary diagnostic source
and commands were deleted after use; there is no permanent fixture.

No provider artifact or cache was changed, no ordinary build or Mathlib
source compilation was started, and the source worktree has no Lake
directory. Ordinary integration and compiled blueprint verification remain
pending. No physical low-density area-law completion follows from the
scalar lemma alone.

Blueprint source/declaration coverage, generated imports, reader-facing prose
and whitespace checks pass. The new supporting result is a lemma. The
global role checker reports 41 discrepancies; the diagnostic output is
byte-identical when the changed chapter is replaced in memory by its
accepted-main source, so this contribution introduces no role discrepancy.
The unrelated baseline entries are not changed here.
