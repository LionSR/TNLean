# Frustration-free scalar parameters by a fixed gap rescaling

Source: AKLV, arXiv:1301.1162v1, Section 4, proof of `t:ent`,
`1dfrustrated34.tex:810–846`:
<https://arxiv.org/html/1301.1162v1#S4>.
The exact source archive used in the bounded rate audit is
<https://arxiv.org/src/1301.1162v1>.

This is one scalar specialization of the existing favorable parameter theorem,
not a second logarithmic-absorption proof or a physical-filter theorem.
Its base is #10433 head `a2c707dd22476dd85028bc9c8f24e45399e23eff`, which already
contains the #10404 scalar theorem and the reviewed QIC candidate snapshot.
No clipping proof is copied from #10430, and no pin changes.

## Exact choice and comparison

Choose the existing universal A ≥ 21 before q,g, and invoke
`Real.exists_aklv_favorable_scalar_parameters` at g₀ = g/8192.
For q ≥ 2 and 0 < g ≤ 1, define

    u = 1 + log q + log(1/g),
    u₀ = 1 + log q + log(1/g₀),
    s = ceil(A u₀²/g₀),  ell = s²,
    t = 1024/g,  R = 2t+s,
    D = (q(s²+1))^(32(2s+1)),
    δ = 4 exp(−4 ell sqrt((g/2)/R)).

The existing theorem supplies s ≥ 21, the exact quotient ell/s = s and
integer square root sqrt(ell) = s. Its lower ceiling estimate implies
s ≥ 1/g. Write R₀ = 2(1024+16 log(1/g₀))+s and δ₀ for the delegated theorem's
ceiling and squared shrinking coefficient. Then

    R ≤ 2049s ≤ 2049R₀,
    (9g₀/10)·2049 ≤ g/2,
    (9g₀/10)/R₀ ≤ (g/2)/R.

Square-root and negative-exponential monotonicity give δ ≤ δ₀, so the actual
frustration-free numerical tradeoff is Dδ ≤ 10⁻⁵ < 1/256.

Since u ≥ 1 and u₀ = u+log8192 ≤ (1+log8192)u, the same delegated upper ceiling
and rank estimates yield

    s ≤ [8192(A+1)(1+log8192)²]/g · u²,
    log D ≤ [8192·198(A+1)(6+2log(A+1))(1+log8192)³]/g · u³.

Both coefficients depend only on the universal A and are positive. No actual
excited spectral value, physical normalization, available chain window, filter,
rank certificate, or entropy bound is supplied. The separate physical client
uses the actual cutoff 1024/g and preserved gap g/2. The existing accepted
regional favorable-entropy theorem needs no new entropy or coordinate wrapper.

## Rate boundary

The inverse-gap logarithms remain explicit. This auxiliary does not formalize
the printed sharper log³(q)/g entropy rate. The existing note
`docs/paper-gaps/aklv13_two_block_robustness.tex` records the retained logarithmic
scope; no duplicate paper-gap note is introduced.

The source's stated rank estimate is at line 590; its older commented estimate
is at lines 703–706 and is reused at lines 831–836. Lines 840–843 pass from a
cost containing log(s²+s) to a parameter claim omitting inverse-gap logarithms.
For the currently certified budget, ell proportional to s² gives log D of
order s(log q+log s). At fixed q and s proportional to 1/g, this certificate
has logarithmic cost of order g⁻¹ log(1/g), while the certified negative log
shrinking is only of order g⁻¹. This is an insufficiency of these certificates
for that parameter choice, not a lower bound on the actual operator rank or a
counterexample to the area-law theorem.

## Review and native checks

Root and an independent reviewer read the complete scalar proof and exact
parent API. Both reviews passed the rescaled ceiling, logarithm identity,
positive denominator comparison, exponential orientation, tradeoff and uniform
quadratic/cubic cost bounds. The final documentation adds the one self-contained
rate restriction marker and retains the paper's exact label and source lines.

Native generated imports, full Blueprint/source synchronization and reverse
coverage, duplicate tags, theorem roles, active references, ChkTeX, source
width/size and integrity, repeated-tactic scan, prose and whitespace checks are
recorded at publication. The one new supporting Blueprint entry and its proof
are `notready`. No local Lean, Lake, elaboration, build or compiled Blueprint
check runs, and no exact-head hosted success is asserted from source review.
