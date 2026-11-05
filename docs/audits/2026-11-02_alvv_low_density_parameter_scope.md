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
